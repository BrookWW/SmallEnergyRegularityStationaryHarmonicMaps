module

public import StationaryHarmonicMaps.Analysis.CorrectedGrandPieces
public import StationaryHarmonicMaps.Analysis.SigmaSeriesWindowUniqueness
public import StationaryHarmonicMaps.Analysis.PositiveCoefficientSummability
public import StationaryHarmonicMaps.Analysis.NormalizedAtomL1

/-!
# Actual normalized atoms from the original finite smooth grand field

The original corrected pieces have proved positive-radius supports,
AE amplitude bounds and zero integrals. Their actual positive masses
normalize them to genuine L1 atoms. The original dyadic support costs
produce real summable coefficients. Actual absolute convergence and
uniqueness of the original two-sided L1 windows identify the original
function with the same full sigma-indexed atomic series almost
everywhere; no decomposition premise is introduced.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original integrable scalar data and their actual finite literal grand maximal integral produce a genuine normalized atomic series with original AE reconstruction and summable original coefficients. -/

@[expose] noncomputable def normalizedGrandAtomConstant (n : ℕ) : ℝ :=
  correctedGrandPieceConstant n * (2 * (70 : ℝ)^n)

theorem exists_normalized_atoms_of_finite_grand_kernel_explicit (n : ℕ) (hn : 0<n) :
    ∃ C : ℝ,0<C ∧ C = normalizedGrandAtomConstant n ∧ ∀ (f : Domain n → ℝ),Integrable f volume →
      let J := fun a => ⨆ s : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a s.val),
        ⨆ (_ : ∀ x∈Metric.ball a s.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤s.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      (∫⁻ x,J x)<(∞ : ℝ≥0∞) →
        let S := fun j : ℤ=>{x | ENNReal.ofReal ((2 : ℝ)^j)<J x}
        let r := fun j a=>Metric.infDist a (S j)ᶜ/20
        ∃ U : ℤ → Set (Domain n),(∀ j,(U j).Countable ∧ ∀ a : U j,0<r j a.val) ∧
          ∃ (w : (Σ j,U j) → ℝ) (a : (Σ j,U j) → Domain n → ℝ),
            (∀ p,0<w p ∧ Integrable (a p) volume ∧ (∫ x,a p x)=0 ∧
              Function.support (a p)⊆Metric.ball p.2.val (70*r p.1 p.2.val) ∧
              (∀ᵐ x ∂volume,|a p x|≤(volume.real (Metric.ball p.2.val (70*r p.1 p.2.val)))⁻¹) ∧
              (∫ x,|a p x|)≤1) ∧
            Summable w ∧ (∑' p,w p)≤C*(∫⁻ x,J x).toReal ∧
            (∀ᵐ x ∂volume,Summable (fun p=>|w p*a p x|)) ∧
            f=ᵐ[volume](fun x=>∑' p,w p*a p x) := by
  classical
  obtain ⟨K,hK,hKFormula,Hpieces⟩ := exists_corrected_grand_dyadic_pieces_explicit n hn
  let C := K*(2*(70 : ℝ)^n)
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_,?_⟩
  · dsimp only [C, normalizedGrandAtomConstant]
    rw [hKFormula]
  intro f hf J hJ S r
  obtain ⟨U,hU,θ,hPieces,_hFinite,hWindows,hApprox,hCost⟩ := Hpieces f hf hJ
  letI (j : ℤ) : Countable (U j) := (hU j).1.to_subtype
  let c := fun j (i : U j)=>(∫ x,θ j i x*f x)/(∫ x,θ j i x)
  let b := fun j i x=>θ j i x*(f x-c j i)
  let e := fun j (i : U j) (k : U (j+1))=>(∫ x,θ j i x*b (j+1) k x)/(∫ x,θ (j+1) k x)
  let P := fun j i x=>b j i x-(∑' k,θ j i x*b (j+1) k x)+(∑' k,e j i k*θ (j+1) k x)
  let B := fun p : Σ j,U j=>Metric.ball p.2.val (70*r p.1 p.2.val)
  let w := fun p : Σ j,U j=>K*(2 : ℝ)^p.1*volume.real (B p)
  let a := fun (p : Σ j,U j) (x : Domain n)=>P p.1 p.2 x/w p
  have hBallPos (p : Σ j,U j) : 0<volume (B p) := Metric.measure_ball_pos volume p.2.val
    (mul_pos (by norm_num) ((hU p.1).2 p.2))
  have hMassPos (p : Σ j,U j) : 0<volume.real (B p) := ENNReal.toReal_pos (hBallPos p).ne' measure_ball_ne_top
  have hwPos (p : Σ j,U j) : 0<w p := mul_pos (mul_pos hK (zpow_pos (by norm_num) _)) (hMassPos p)
  have hPInt (p : Σ j,U j) : Integrable (P p.1 p.2) volume := (hPieces p.1 p.2).1
  have hAtomEq (p : Σ j,U j) (x : Domain n) : w p*a p x=P p.1 p.2 x := by
    dsimp only [a]
    field_simp [(hwPos p).ne']
  have hAtomSupp (p : Σ j,U j) : Function.support (a p)⊆B p := by
    intro x hx
    apply (hPieces p.1 p.2).2.2.1
    intro hPZero
    change P p.1 p.2 x=0 at hPZero
    exact hx (by change P p.1 p.2 x/w p=0;rw [hPZero,zero_div])
  have hAtomBound (p : Σ j,U j) : ∀ᵐ x ∂volume,|a p x|≤(volume.real (B p))⁻¹ := by
    filter_upwards [(hPieces p.1 p.2).2.2.2] with x hx
    change |P p.1 p.2 x/w p|≤_
    rw [abs_div,abs_of_pos (hwPos p)]
    apply (div_le_div_of_nonneg_right hx (hwPos p).le).trans_eq
    dsimp only [w]
    field_simp [hK.ne',(zpow_pos (by norm_num : (0 : ℝ)<2) p.1).ne',(hMassPos p).ne']
  have hAtomL1 (p : Σ j,U j) : Integrable (a p) volume ∧ (∫ x,|a p x|)≤1 :=
    normalized_supported_atom_integrable_abs_le_one volume (B p) (hBallPos p).ne' measure_ball_ne_top (a p)
      ((hPInt p).div_const (w p)).aestronglyMeasurable.restrict (hAtomSupp p)
      ((hAtomBound p).filter_mono (ae_mono Measure.restrict_le_self))
  have hAtomMean (p : Σ j,U j) : (∫ x,a p x)=0 := by
    change (∫ x,P p.1 p.2 x/w p)=0
    rw [integral_div,(hPieces p.1 p.2).2.1,zero_div]
  have hwENN (p : Σ j,U j) : ENNReal.ofReal (w p)=
      ENNReal.ofReal K*ENNReal.ofReal ((2 : ℝ)^p.1)*volume (B p) := by
    change ENNReal.ofReal (K*(2 : ℝ)^p.1*(volume (B p)).toReal)=_
    rw [ENNReal.ofReal_mul (mul_nonneg hK.le (zpow_pos (by norm_num) _).le),
      ENNReal.ofReal_mul hK.le,ENNReal.ofReal_toReal measure_ball_ne_top]
  have hCoeffEq : (∑' p : Σ j,U j,ENNReal.ofReal (w p))=
      ENNReal.ofReal K*(∑' j : ℤ,ENNReal.ofReal ((2 : ℝ)^j)*(∑' i : U j,volume (B ⟨j,i⟩))) := by
    rw [ENNReal.tsum_sigma']
    calc
      _ = ∑' j : ℤ,ENNReal.ofReal K*(ENNReal.ofReal ((2 : ℝ)^j)*(∑' i : U j,volume (B ⟨j,i⟩))) := by
        apply tsum_congr
        intro j
        simp_rw [hwENN]
        rw [ENNReal.tsum_mul_left,mul_assoc]
      _ = _ := ENNReal.tsum_mul_left
  have hCoeffBound : (∑' p : Σ j,U j,ENNReal.ofReal (w p))≤ENNReal.ofReal C*(∫⁻ x,J x) := by
    rw [hCoeffEq]
    exact (mul_le_mul_of_nonneg_left hCost zero_le).trans_eq (by
      dsimp only [C]
      rw [ENNReal.ofReal_mul hK.le,mul_assoc])
  obtain ⟨hSummable,hRealBound⟩ := summable_nonnegative_coefficients_of_extended_bound w
    (fun p=>(hwPos p).le) C hC.le (∫⁻ x,J x) hJ.ne hCoeffBound
  have hNormPiece (p : Σ j,U j) : (∫⁻ x,ENNReal.ofReal |P p.1 p.2 x|)≤ENNReal.ofReal (w p) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hPInt p).abs (Eventually.of_forall fun _=>abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = ∫ x,w p*|a p x| := integral_congr_ae (Eventually.of_forall fun x=>by rw [← hAtomEq p x,abs_mul,abs_of_pos (hwPos p)])
      _ = w p*(∫ x,|a p x|) := integral_const_mul _ _
      _ ≤ w p*1 := mul_le_mul_of_nonneg_left (hAtomL1 p).2 (hwPos p).le
      _ = w p := mul_one _
  have hNormFinite : (∑' p : Σ j,U j,∫⁻ x,ENNReal.ofReal |P p.1 p.2 x|)<(∞ : ℝ≥0∞) :=
    (ENNReal.tsum_le_tsum hNormPiece).trans_lt (hCoeffBound.trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ))
  have hRepresentation : f=ᵐ[volume](fun x=>∑' p : Σ j,U j,P p.1 p.2 x) :=
    ae_eq_sigma_series_of_strong_L1_windows volume (fun j=>U j) P (fun j i=>(hPieces j i).1)
      hNormFinite f hf (fun N=>(hWindows N).1) hApprox
  obtain ⟨hSeries,_hAbsI,_hSumI,_hIntegral⟩ := integrable_tsum_of_finite_lintegral_abs_sum volume
    (fun p : Σ j,U j=>P p.1 p.2) hPInt hNormFinite
  refine ⟨U,hU,w,a,fun p=>⟨hwPos p,(hAtomL1 p).1,hAtomMean p,hAtomSupp p,hAtomBound p,(hAtomL1 p).2⟩,
    hSummable,hRealBound,?_,?_⟩
  · filter_upwards [hSeries] with x hx
    simpa only [hAtomEq] using hx.1
  · filter_upwards [hRepresentation] with x hx
    exact hx.trans (tsum_congr fun p=>(hAtomEq p x).symm)

theorem exists_normalized_atoms_of_finite_grand_kernel (n : ℕ) (hn : 0<n) :
    ∃ C : ℝ,0<C ∧ ∀ (f : Domain n → ℝ),Integrable f volume →
      let J := fun a => ⨆ s : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a s.val),
        ⨆ (_ : ∀ x∈Metric.ball a s.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤s.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      (∫⁻ x,J x)<(∞ : ℝ≥0∞) →
        let S := fun j : ℤ=>{x | ENNReal.ofReal ((2 : ℝ)^j)<J x}
        let r := fun j a=>Metric.infDist a (S j)ᶜ/20
        ∃ U : ℤ → Set (Domain n),(∀ j,(U j).Countable ∧ ∀ a : U j,0<r j a.val) ∧
          ∃ (w : (Σ j,U j) → ℝ) (a : (Σ j,U j) → Domain n → ℝ),
            (∀ p,0<w p ∧ Integrable (a p) volume ∧ (∫ x,a p x)=0 ∧
              Function.support (a p)⊆Metric.ball p.2.val (70*r p.1 p.2.val) ∧
              (∀ᵐ x ∂volume,|a p x|≤(volume.real (Metric.ball p.2.val (70*r p.1 p.2.val)))⁻¹) ∧
              (∫ x,|a p x|)≤1) ∧
            Summable w ∧ (∑' p,w p)≤C*(∫⁻ x,J x).toReal ∧
            (∀ᵐ x ∂volume,Summable (fun p=>|w p*a p x|)) ∧
            f=ᵐ[volume](fun x=>∑' p,w p*a p x) := by
  obtain ⟨C,hC,_hFormula,H⟩ := exists_normalized_atoms_of_finite_grand_kernel_explicit n hn
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end
