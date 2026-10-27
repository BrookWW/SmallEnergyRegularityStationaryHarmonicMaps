module

public import StationaryHarmonicMaps.Analysis.StrongGrandDyadicFamily
public import StationaryHarmonicMaps.Analysis.WhitneyCompensationCoefficient
public import StationaryHarmonicMaps.Analysis.CompensationColumnCancellation
public import StationaryHarmonicMaps.Analysis.CorrectedPieceIntegral
public import StationaryHarmonicMaps.Analysis.CorrectedPieceSupport
public import StationaryHarmonicMaps.Analysis.CorrectedPieceReconstruction
public import StationaryHarmonicMaps.Analysis.DyadicGoodReconstruction
public import StationaryHarmonicMaps.Analysis.DyadicLevelSummability

/-!
# Actual corrected grand-level pieces from the original scalar data

One joint quantitative partition family is chosen at every integer
level of the original grand field. The actual mass-normalized cross
coefficients produce integrable zero-mean corrected pieces with literal
seventyfold supports and genuine AE amplitude bounds. Their actual
finite pointwise sums reconstruct the same good-function differences,
and the original two-ended L1 limits reconstruct the original function.
All actual support-ball costs are controlled by the original grand
integral through the proved full integer level-mass sum.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original finite grand data produce actual corrected bounded zero-mean pieces, their same-family strong L1 window reconstruction and true summable support-ball costs. -/
theorem exists_corrected_grand_dyadic_pieces (n : ℕ) (hn : 0<n) :
    ∃ K : ℝ,0<K ∧ ∀ (f : Domain n → ℝ),Integrable f volume →
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
          ∃ θ : (j : ℤ) → U j → Domain n → ℝ,
          let c := fun j (a : U j)=>(∫ x,θ j a x*f x)/(∫ x,θ j a x)
          let b := fun j a x=>θ j a x*(f x-c j a)
          let e := fun j (i : U j) (a : U (j+1))=>(∫ x,θ j i x*b (j+1) a x)/(∫ x,θ (j+1) a x)
          let P := fun j i x=>b j i x-(∑' a,θ j i x*b (j+1) a x)+(∑' a,e j i a*θ (j+1) a x)
          (∀ j (i : U j),Integrable (P j i) volume ∧ (∫ x,P j i x)=0 ∧
            Function.support (P j i)⊆Metric.ball i.val (70*r j i.val) ∧
            (∀ᵐ x ∂volume,|P j i x|≤K*(2 : ℝ)^j)) ∧
          (∀ j x,Function.HasFiniteSupport (fun i=>P j i x)) ∧
          (∀ N : ℕ,Integrable (fun x=>∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),∑' i,P j i x) volume ∧
            (∫ x,(∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),∑' i,P j i x))=0) ∧
          Tendsto (fun N : ℕ=>∫ x,|f x-∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),∑' i,P j i x|)
            atTop (𝓝 (0 : ℝ)) ∧
          (∑' j : ℤ,ENNReal.ofReal ((2 : ℝ)^j)*(∑' i : U j,volume (Metric.ball i.val (70*r j i.val))))≤
            ENNReal.ofReal (2*(70 : ℝ)^n)*(∫⁻ x,J x) := by
  classical
  obtain ⟨B,D,A,hB,hD,hA,Hfamily⟩ := exists_strong_grand_dyadic_family n hn
  obtain ⟨C,hC,Hcoefficient⟩ := exists_whitney_compensation_coefficient_bound n B hB
  let K := 4*D+C+2*A
  have hK : 0<K := by dsimp only [K];positivity
  refine ⟨K,hK,?_⟩
  intro f hf J hJ S r
  obtain ⟨U,θ,hProps,hStats,hLow,hHigh⟩ := Hfamily f hf hJ
  have hCount (j : ℤ) : (U j).Countable := (hProps j).2.2.2.1
  letI (j : ℤ) : Countable (U j) := (hCount j).to_subtype
  let c := fun j (a : U j)=>(∫ x,θ j a x*f x)/(∫ x,θ j a x)
  let b := fun j a x=>θ j a x*(f x-c j a)
  let g := fun j x=>f x-∑' a,b j a x
  let e := fun j (i : U j) (a : U (j+1))=>(∫ x,θ j i x*b (j+1) a x)/(∫ x,θ (j+1) a x)
  let P := fun j i x=>b j i x-(∑' a,θ j i x*b (j+1) a x)+(∑' a,e j i a*θ (j+1) a x)
  have hData (j : ℤ) := (hProps j).2.2.2.2.2.2.2.2.2.2
  have hPart (j : ℤ) := (hProps j).2.2.2.2.2.2.2.2.2.1
  have hFiniteθ (j : ℤ) := (hProps j).2.2.2.2.2.2.2.2.1
  have hNested (j : ℤ) : S (j+1)⊆S j := by
    intro x hx
    have hPow : (2 : ℝ)^(j+1)=2*(2 : ℝ)^j := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_one,mul_comm]
    have hLe : (2 : ℝ)^j≤(2 : ℝ)^(j+1) := by rw [hPow];have H := zpow_pos (by norm_num : (0 : ℝ)<2) j;linarith
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hLe) hx
  have hMassPos (j : ℤ) (a : U j) : 0<(∫ x,θ j a x) := by
    obtain ⟨_hr,_hs,_hcomp,_hBall,_hS,_hb,_hd,_hm,_hGood,hMass,_hc,_hI,_hz⟩ := hData j a
    exact hMass
  have hSmooth (j : ℤ) (a : U j) : ContDiff ℝ ∞ (θ j a) := (hData j a).2.1
  have hCompact (j : ℤ) (a : U j) : HasCompactSupport (θ j a) := (hData j a).2.2.1
  have hBall (j : ℤ) (a : U j) : tsupport (θ j a)⊆Metric.ball a.val (10*r j a.val) := (hData j a).2.2.2.1
  have hSupp (j : ℤ) (a : U j) : tsupport (θ j a)⊆S j := (hData j a).2.2.2.2.1
  have hBounds (j : ℤ) (a : U j) (x : Domain n) : 0≤θ j a x ∧ θ j a x≤1 := (hData j a).2.2.2.2.2.1 x
  have hBI (j : ℤ) (a : U j) : Integrable (b j a) volume := by
    obtain ⟨_hr,_hs,_hcomp,_hBall,_hS,_hb,_hd,_hm,_hGood,_hMass,_hc,hI,_hz⟩ := hData j a
    exact hI
  have hBMean (j : ℤ) (a : U j) : (∫ x,b j a x)=0 := by
    obtain ⟨_hr,_hs,_hcomp,_hBall,_hS,_hb,_hd,_hm,_hGood,_hMass,_hc,_hI,hz⟩ := hData j a
    exact hz
  have hc (j : ℤ) (a : U j) : |c j a|≤D*(2 : ℝ)^j := by
    obtain ⟨_hr,_hs,_hcomp,_hBall,_hS,_hb,_hd,_hm,_hGood,_hMass,hc,_hI,_hz⟩ := hData j a
    exact hc
  have hECoeff (j : ℤ) (i : U j) (a : U (j+1)) : |e j i a|≤C*(2 : ℝ)^j := by
    obtain ⟨hrlo,hslo,hclo,hblo,_hslo,hvLo,hdLo,_hmLo,_hgLo,_hpLo,_hcLo,_hiLo,_hzLo⟩ := hData j i
    obtain ⟨hrhi,hshi,hchi,hbhi,_hshi,hvHi,hdHi,hmHi,⟨y,_hy,hNear,hGood⟩,_hpHi,_hcHi,_hiHi,_hzHi⟩ := hData (j+1) a
    have hPow : (2 : ℝ)^(j+1)=2*(2 : ℝ)^j := by rw [zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_one,mul_comm]
    rw [hPow] at hGood
    obtain ⟨_hm,_hc,_hDp,_hI,he⟩ := Hcoefficient f hf (S j) (S (j+1)) (hNested j) (hProps j).2.2.1
      i.val a.val hrhi y ((2 : ℝ)^j) (zpow_pos (by norm_num) j).le hNear.le hGood
      (θ j i) (θ (j+1) a) hslo hclo hshi hchi hblo hbhi hvLo hvHi hdLo hdHi hmHi
    exact he
  have hColumns (j : ℤ) (a : U (j+1)) : Function.HasFiniteSupport (fun i=>e j i a) ∧ (∑' i,e j i a)=0 := by
    have hBadSupp : Function.support (b (j+1) a)⊆tsupport (θ (j+1) a) := by
      intro x hx
      apply subset_tsupport (θ (j+1) a)
      intro hZero
      exact hx (by change θ (j+1) a x*(f x-c (j+1) a)=0;rw [hZero,zero_mul])
    have H := finite_compensation_column_sum_zero (S j) (U j) (hProps j).1 (hProps j).2.2.1
      (hProps j).2.2.2.2.2.1 (θ j) (hSmooth j) (hBall j) (hBounds j) (hPart j)
      (tsupport (θ (j+1) a)) (hCompact (j+1) a) ((hSupp (j+1) a).trans (hNested j))
      (b (j+1) a) (hBI (j+1) a) hBadSupp (hBMean (j+1) a) (∫ x,θ (j+1) a x)
    exact ⟨H.2.1,H.2.2⟩
  have hIntegral (j : ℤ) (i : U j) : Integrable (P j i) volume ∧ (∫ x,P j i x)=0 :=
    integrable_corrected_compensation_piece_integral_zero volume (b (j+1)) (θ (j+1)) (hBI (j+1))
      (hStats (j+1)).1 (hStats (j+1)).2.1
      (fun a=>(hSmooth (j+1) a).continuous.integrable_of_hasCompactSupport (hCompact (j+1) a))
      (fun a x=>(hBounds (j+1) a x).1) (hMassPos (j+1)) (θ j i)
      (hSmooth j i).continuous.aestronglyMeasurable
      (fun x=>by rw [abs_of_nonneg (hBounds j i x).1];exact (hBounds j i x).2) (b j i) (hBI j i) (hBMean j i)
  have hSupportP (j : ℤ) (i : U j) : Function.support (P j i)⊆Metric.ball i.val (70*r j i.val) :=
    support_corrected_whitney_piece_subset (S j) (S (j+1)) (hNested j) (hProps j).2.2.1
      i.val (fun a : U (j+1)=>a.val) (θ j i) (θ (j+1)) (hBall j i) (hBall (j+1)) f (c j i) (c (j+1))
  have hReconstruct (j : ℤ) : (∀ x,Function.HasFiniteSupport (fun i=>P j i x)) ∧
      (∀ x,(∑' i,P j i x)=g (j+1) x-g j x) :=
    corrected_partition_pieces_reconstruct_good_difference (S j) (S (j+1)) (hNested j) (θ j) (θ (j+1))
      (hFiniteθ j) (hFiniteθ (j+1)) (fun a=>(subset_tsupport (θ (j+1) a)).trans (hSupp (j+1) a)) (hPart j)
      f (c j) (c (j+1)) (e j) (fun a=>(hColumns j a).1) (fun a=>(hColumns j a).2)
  have hAmplitude (j : ℤ) (i : U j) : ∀ᵐ x ∂volume,|P j i x|≤K*(2 : ℝ)^j := by
    have hCapHi := (hStats (j+1)).2.2.2.2.2.2.2.1
    filter_upwards [hCapHi] with x hxCap
    have hPow : (2 : ℝ)^(j+1)=2*(2 : ℝ)^j := by rw [zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_one,mul_comm]
    have hLevel : 0<(2 : ℝ)^j := zpow_pos (by norm_num) j
    by_cases hx : x∈S (j+1)
    · have H := abs_corrected_piece_le_on_partition (fun a=>θ (j+1) a x) (c (j+1)) (e j i)
        (hFiniteθ (j+1) x) (fun a=>(hBounds (j+1) a x).1) (hPart (j+1) x hx)
        (f x) (θ j i x) (c j i) (D*(2 : ℝ)^j) (D*(2 : ℝ)^(j+1)) (C*(2 : ℝ)^j)
        (hBounds j i x).1 (hBounds j i x).2 (hc j i) (hc (j+1)) (hECoeff j i)
      apply H.trans
      rw [hPow]
      dsimp only [K]
      nlinarith only [mul_pos hD hLevel,mul_pos hA hLevel]
    · have hZeroHi (a : U (j+1)) : θ (j+1) a x=0 := image_eq_zero_of_notMem_tsupport (fun H=>hx (hSupp (j+1) a H))
      have hOutside : g (j+1) x=f x := (hStats (j+1)).2.2.2.2.2.2.1 x (le_of_not_gt hx)
      have hValue : |f x|≤A*(2 : ℝ)^(j+1) := by
        have H := hxCap.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) zero_le)
        rw [← ENNReal.ofReal_mul hA.le] at H
        change ENNReal.ofReal |g (j+1) x|≤ENNReal.ofReal (A*(2 : ℝ)^(j+1)) at H
        rw [hOutside] at H
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp H
      have H := abs_corrected_piece_le_off_partition (fun a=>θ (j+1) a x) (c (j+1)) (e j i) hZeroHi
        (f x) (θ j i x) (c j i) (D*(2 : ℝ)^j) (A*(2 : ℝ)^(j+1))
        (hBounds j i x).1 (hBounds j i x).2 (hc j i) hValue
      apply H.trans
      rw [hPow]
      dsimp only [K]
      nlinarith only [mul_pos hD hLevel,mul_pos hC hLevel]
  obtain ⟨_hDifferences,hWindows,hLimit⟩ := symmetric_good_differences_strong_L1_reconstruct volume f hf g
    (fun j=>(hStats j).2.2.2.2.1) (fun j=>(hStats j).2.2.2.2.2.1) hLow hHigh
  have hVolume70 (j : ℤ) (i : U j) : volume (Metric.ball i.val (70*r j i.val))=
      ENNReal.ofReal ((70 : ℝ)^n)*volume (Metric.ball i.val (r j i.val)) := by
    have hr : 0<r j i.val := (hData j i).1
    rw [Measure.addHaar_ball_of_pos volume i.val (by positivity),Measure.addHaar_ball_of_pos volume i.val hr]
    simp only [finrank_euclideanSpace,Fintype.card_fin,mul_pow,
      ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ)≤70) n),mul_assoc]
  have hVolumeBound (j : ℤ) : (∑' i : U j,volume (Metric.ball i.val (70*r j i.val)))≤
      ENNReal.ofReal ((70 : ℝ)^n)*volume (S j) := by
    simp_rw [hVolume70]
    rw [ENNReal.tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hProps j).2.2.2.2.2.2.2.1 zero_le
  have hCost : (∑' j : ℤ,ENNReal.ofReal ((2 : ℝ)^j)*(∑' i : U j,volume (Metric.ball i.val (70*r j i.val))))≤
      ENNReal.ofReal (2*(70 : ℝ)^n)*(∫⁻ x,J x) := by
    calc
      _ ≤ ∑' j : ℤ,ENNReal.ofReal ((2 : ℝ)^j)*(ENNReal.ofReal ((70 : ℝ)^n)*volume (S j)) :=
        ENNReal.tsum_le_tsum (fun j=>mul_le_mul_of_nonneg_left (hVolumeBound j) zero_le)
      _ = ENNReal.ofReal ((70 : ℝ)^n)*(∑' j : ℤ,ENNReal.ofReal ((2 : ℝ)^j)*volume (S j)) := by
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro j
        ac_rfl
      _ ≤ ENNReal.ofReal ((70 : ℝ)^n)*(2*(∫⁻ x,J x)) := mul_le_mul_of_nonneg_left
        (tsum_dyadic_superlevel_mass_le_lintegral volume J (lowerSemicontinuous_measurable_smooth_grand_kernel f).2) zero_le
      _ = _ := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),ENNReal.ofReal_ofNat]
        simp only [mul_assoc,mul_left_comm]
  refine ⟨U,fun j=>⟨hCount j,fun i=>(hData j i).1⟩,θ,fun j i=>⟨(hIntegral j i).1,(hIntegral j i).2,hSupportP j i,hAmplitude j i⟩,
    fun j=>(hReconstruct j).1,?_,?_,hCost⟩
  · intro N
    change Integrable (fun x=>∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),∑' i,P j i x) volume ∧
      (∫ x,(∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),∑' i,P j i x))=0
    have hSumEq (j : ℤ) (x : Domain n) : (∑' i,P j i x)=g (j+1) x-g j x := (hReconstruct j).2 x
    simpa only [hSumEq] using hWindows N
  · change Tendsto (fun N : ℕ=>∫ x,|f x-∑ j∈Finset.Icc (-(N : ℤ)) (N : ℤ),∑' i,P j i x|) atTop (𝓝 (0 : ℝ))
    have hSumEq (j : ℤ) (x : Domain n) : (∑' i,P j i x)=g (j+1) x-g j x := (hReconstruct j).2 x
    simpa only [hSumEq] using hLimit

end StationaryHarmonicMaps.Analysis

end
