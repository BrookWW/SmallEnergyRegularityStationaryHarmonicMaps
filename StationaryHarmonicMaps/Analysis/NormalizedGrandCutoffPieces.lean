module

public import StationaryHarmonicMaps.Analysis.WhitneyPartitionQuantitative
public import StationaryHarmonicMaps.Analysis.GrandKernelLocalization
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Actual normalized grand-superlevel cancellation pieces

The original finite grand maximal integral produces its open bad set
and its actual normalized smooth Whitney partition. The new cutoff
averages are defined from the normalized cutoffs themselves. Their true
mass lower bounds and true derivative bounds yield the original level
bound; the corresponding original pieces are integrable and have
exactly zero integral.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original finite grand maximal data produce a genuine normalized bad-set partition with newly computed controlled averages and original zero-mean pieces. -/
theorem exists_normalized_grand_superlevel_pieces (n : ℕ) (hn : 0<n) :
    ∃ D : ℝ,0<D ∧ ∀ (f : Domain n → ℝ),Integrable f volume →
      let J := fun a => ⨆ r : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a r.val),
        ⨆ (_ : ∀ x∈Metric.ball a r.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤r.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      (∫⁻ a,J a)<(∞ : ℝ≥0∞) → ∀ L : ℝ,0<L →
        let S := {a | ENNReal.ofReal L<J a}
        let r := fun a=>Metric.infDist a Sᶜ/20
        ∃ U : Set (Domain n),U.Countable ∧ U⊆S ∧
          U.PairwiseDisjoint (fun a=>Metric.ball a (r a)) ∧ S=⋃ a : U,Metric.ball a.val (5*r a.val) ∧
          ∃ θ : U → Domain n → ℝ,(∀ x,Function.HasFiniteSupport (fun a=>θ a x)) ∧
            (∀ x∈S,∑' a,θ a x=1) ∧ ∀ a,
              ContDiff ℝ ∞ (θ a) ∧ HasCompactSupport (θ a) ∧
              tsupport (θ a)⊆Metric.ball a.val (10*r a.val) ∧ tsupport (θ a)⊆S ∧
              (∀ x,0≤θ a x ∧ θ a x≤1) ∧
              0<(∫ x,θ a x) ∧
              let c := (∫ x,θ a x*f x)/(∫ x,θ a x)
              |c|≤D*L ∧ Integrable (fun x=>θ a x*(f x-c)) volume ∧
                (∫ x,θ a x*(f x-c))=0 ∧
                Function.support (fun x=>θ a x*(f x-c))⊆Metric.ball a.val (10*r a.val) := by
  classical
  obtain ⟨B,hB,Hpartition⟩ := exists_quantitative_whitney_smooth_partition n hn
  let N : ℝ := (60 : ℝ)^n
  have hN : 0<N := pow_pos (by norm_num) _
  let V : ℝ := volume.real (Metric.ball (0 : Domain n) 1)
  have hV : 0<V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume (0 : Domain n) (by norm_num : (0 : ℝ)<1)).ne' measure_ball_ne_top
  let D : ℝ := B*(40 : ℝ)^(n+1)*N/((5 : ℝ)^n*V)
  have hD : 0<D := by dsimp only [D];positivity
  refine ⟨D,hD,?_⟩
  intro f hf J hJ L hL S r
  obtain ⟨hLS,hMeas⟩ := lowerSemicontinuous_measurable_smooth_grand_kernel f
  have hOpen : IsOpen S := hLS.isOpen_preimage (ENNReal.ofReal L)
  have hSubset : S⊆{a | ENNReal.ofReal L≤J a} := by
    intro a ha
    change ENNReal.ofReal L<J a at ha
    exact ha.le
  have hMeasure : volume S≤(∫⁻ a,J a)/ENNReal.ofReal L := (measure_mono hSubset).trans
    (meas_ge_le_lintegral_div hMeas.aemeasurable (ENNReal.ofReal_pos.mpr hL).ne' ENNReal.ofReal_ne_top)
  have hFinite : volume S≠(∞ : ℝ≥0∞) := (hMeasure.trans_lt (by
    rw [div_eq_mul_inv]
    exact ENNReal.mul_lt_top hJ (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hL)))).ne
  obtain ⟨U,hCount,hUS,hDisj,hCover,θ,hFiniteθ,hθData,hPart⟩ := Hpartition S hOpen hFinite
  obtain ⟨_R,_hR,_hCap,hComp⟩ := exists_ball_radius_cap_of_finite_volume n hn S hFinite
  have hRpos (a : U) : 0<r a.val := div_pos
    ((hOpen.isClosed_compl.notMem_iff_infDist_pos hComp).mp (not_not_intro (hUS a.property))) (by norm_num)
  refine ⟨U,hCount,hUS,hDisj,hCover,θ,hFiniteθ,hPart,?_⟩
  intro a
  have hra := hRpos a
  have hMassLower := (hθData a).2.2.2.2.2.2
  have hMass : ((5*r a.val)^n*V)/N≤∫ x,θ a x := by
    rw [HolderToCK.ball_volume_real a.val (mul_pos (by norm_num) hra)] at hMassLower
    exact hMassLower
  have hMassPos : 0<(∫ x,θ a x) := (div_pos (mul_pos (pow_pos (by positivity) _) hV) hN).trans_le hMass
  obtain ⟨y,hy,hDist⟩ := hOpen.isClosed_compl.exists_infDist_eq_dist hComp a.val
  have hyGood : J y≤ENNReal.ofReal L := le_of_not_gt hy
  have hNear : dist a.val y=20*r a.val := by rw [← hDist];dsimp only [r];ring
  have hSuppY : tsupport (θ a)⊆Metric.ball y (40*r a.val) := by
    intro x hx
    have hxa : dist x a.val<10*r a.val := (hθData a).2.2.1 hx
    have hTri := dist_triangle x a.val y
    change dist x y<40*r a.val
    rw [hNear] at hTri
    linarith only [hxa,hTri,hra]
  have hCoordinate (x : Domain n) (_hx : x∈Metric.ball y (40*r a.val)) (i : Fin n) :
      |fderiv ℝ (θ a) x (EuclideanSpace.single i 1)|≤B/r a.val := by
    calc
      _ = ‖fderiv ℝ (θ a) x (EuclideanSpace.single i 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ (θ a) x‖*‖EuclideanSpace.single i (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (θ a) x‖ := by simp
      _ ≤ _ := (hθData a).2.2.2.2.2.1 x
  have hPair := smooth_grand_kernel_localized_pairing_le f y (40*r a.val) (B/r a.val)
    (by positivity) (div_pos hB hra) (θ a) (hθData a).1 (hθData a).2.1 hSuppY hCoordinate
  have hENN : ENNReal.ofReal |∫ x,θ a x*f x|≤ENNReal.ofReal (((B/r a.val)*(40*r a.val)^(n+1))*L) := by
    calc
      _ ≤ ENNReal.ofReal ((B/r a.val)*(40*r a.val)^(n+1))*J y := hPair
      _ ≤ ENNReal.ofReal ((B/r a.val)*(40*r a.val)^(n+1))*ENNReal.ofReal L :=
        mul_le_mul_of_nonneg_left hyGood zero_le
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hRaw : |∫ x,θ a x*f x|≤((B/r a.val)*(40*r a.val)^(n+1))*L :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hENN
  have hScale : ((B/r a.val)*(40*r a.val)^(n+1))*L=(D*L)*(((5*r a.val)^n*V)/N) := by
    dsimp only [D]
    rw [mul_pow,mul_pow,pow_succ (r a.val)]
    field_simp [hra.ne',hV.ne',hN.ne']
  rw [hScale] at hRaw
  have hAverage : |(∫ x,θ a x*f x)/(∫ x,θ a x)|≤D*L := by
    rw [abs_div,abs_of_pos hMassPos,div_le_iff₀ hMassPos]
    exact hRaw.trans (mul_le_mul_of_nonneg_left hMass (mul_nonneg hD.le hL.le))
  have hθI : Integrable (θ a) volume := (hθData a).1.continuous.integrable_of_hasCompactSupport (hθData a).2.1
  have hθfI : Integrable (fun x=>θ a x*f x) volume := hf.bdd_mul (hθData a).1.continuous.aestronglyMeasurable
    (Eventually.of_forall fun x=>by rw [Real.norm_of_nonneg ((hθData a).2.2.2.2.1 x).1];exact ((hθData a).2.2.2.2.1 x).2)
  obtain ⟨hBadI,hZero⟩ := integrable_zero_mean_cutoff_piece volume f (θ a) hθI hθfI hMassPos.ne'
  refine ⟨(hθData a).1,(hθData a).2.1,(hθData a).2.2.1,(hθData a).2.2.2.1,
    (hθData a).2.2.2.2.1,hMassPos,hAverage,hBadI,hZero,?_⟩
  intro x hx
  apply (hθData a).2.2.1
  apply subset_tsupport (θ a)
  intro hZeroθ
  exact hx (by dsimp only;rw [hZeroθ,zero_mul])

end StationaryHarmonicMaps.Analysis

end
