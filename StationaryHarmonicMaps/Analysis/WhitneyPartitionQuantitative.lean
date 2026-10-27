module

public import StationaryHarmonicMaps.Analysis.WhitneyNormalizedDerivative

/-!
# Quantitative actual normalized Whitney cutoffs

The original open finite-volume set produces the same normalized smooth
partition. Its derivative bound is proved for the actual quotient, and
the original fivefold ball on which the numerator equals one gives the
true normalized mass lower bound. Both estimates precede use of the
new normalized cutoff averages.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original open finite-volume data produce the same true normalized partition with genuine uniform derivatives and positive normalized masses. -/

@[expose] noncomputable def whitneyPartitionDerivativeConstant (n : ℕ) : ℝ :=
  ((1 + 3 * (60 : ℝ)^n) * (2 : ℝ)^22) / 5

theorem exists_quantitative_whitney_smooth_partition_explicit (n : ℕ) (hn : 0<n) :
    ∃ B : ℝ,0<B ∧ B = whitneyPartitionDerivativeConstant n ∧ ∀ S : Set (Domain n),IsOpen S → volume S≠(∞ : ℝ≥0∞) →
      let r := fun a=>Metric.infDist a Sᶜ/20
      ∃ U : Set (Domain n),U.Countable ∧ U⊆S ∧
        U.PairwiseDisjoint (fun a=>Metric.ball a (r a)) ∧ S=⋃ a : U,Metric.ball a.val (5*r a.val) ∧
        ∃ θ : U → Domain n → ℝ,
          (∀ x,Function.HasFiniteSupport (fun a=>θ a x)) ∧
          (∀ a,ContDiff ℝ ∞ (θ a) ∧ HasCompactSupport (θ a) ∧
            tsupport (θ a)⊆Metric.ball a.val (10*r a.val) ∧ tsupport (θ a)⊆S ∧
            (∀ x,0≤θ a x ∧ θ a x≤1) ∧ (∀ x,‖fderiv ℝ (θ a) x‖≤B/r a.val) ∧
            volume.real (Metric.ball a.val (5*r a.val))/(60 : ℝ)^n≤∫ x,θ a x) ∧
          (∀ x∈S,∑' a,θ a x=1) := by
  classical
  obtain ⟨C,hC,hCFormula,Hpartition⟩ := exists_whitney_normalized_smooth_partition_explicit n hn
  let N : ℝ := (60 : ℝ)^n
  have hN : 0<N := pow_pos (by norm_num) _
  let B : ℝ := ((1+3*N)*C)/5
  have hB : 0<B := by dsimp only [B];positivity
  refine ⟨B,hB,?_,?_⟩
  · dsimp only [B, N, whitneyPartitionDerivativeConstant]
    rw [hCFormula]
  intro S hOpen hFinite r
  obtain ⟨U,hCount,hUS,hDisj,hCover,η,hηData,hFiniteη,hPBounds,hFiniteθ,hθData,hθBounds,hPartition⟩ :=
    Hpartition S hOpen hFinite
  obtain ⟨_R,_hR,_hCap,hComp⟩ := exists_ball_radius_cap_of_finite_volume n hn S hFinite
  let P := fun x=>∑' a,η a x
  let θ := fun a x=>η a x/P x
  have hRpos (a : U) : 0<r a.val := div_pos
    ((hOpen.isClosed_compl.notMem_iff_infDist_pos hComp).mp (not_not_intro (hUS a.property))) (by norm_num)
  have hDθ := norm_fderiv_whitney_normalized_cutoff_le S U hOpen hComp hUS hDisj η
    (fun a=>(hηData a).1) (fun a=>(hηData a).2.1) (fun a=>(hηData a).2.2.1)
    (fun a=>(hηData a).2.2.2.2.2.1) C hC (fun a=>(hηData a).2.2.2.2.2.2)
    (fun x hx=>(hPBounds x hx).1)
  have hMass (a : U) : volume.real (Metric.ball a.val (5*r a.val))/N≤∫ x,θ a x := by
    have hθI : Integrable (θ a) volume := (hθData a).1.continuous.integrable_of_hasCompactSupport (hθData a).2.1
    have hLower (x : Domain n) (hx : x∈Metric.ball a.val (5*r a.val)) : 1/N≤θ a x := by
      have hOne : η a x=1 := (hηData a).2.2.2.2.1 x (Metric.ball_subset_closedBall hx)
      have hxS : x∈S := (hηData a).2.2.2.1 (subset_tsupport (η a) (by change η a x≠0;rw [hOne];exact one_ne_zero))
      have hPx := hPBounds x hxS
      have hPpos : 0<P x := zero_lt_one.trans_le hPx.1
      change 1/N≤η a x/P x
      rw [hOne]
      exact (div_le_div_iff₀ hN hPpos).mpr (by simpa only [one_mul] using hPx.2)
    letI : IsFiniteMeasure (volume.restrict (Metric.ball a.val (5*r a.val))) :=
      isFiniteMeasure_restrict.mpr measure_ball_ne_top
    calc
      _ = ∫ _x in Metric.ball a.val (5*r a.val),(1/N) := by
        simp only [integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply MeasurableSet.univ,univ_inter]
        ring
      _ ≤ ∫ x in Metric.ball a.val (5*r a.val),θ a x := integral_mono_ae (integrable_const _)
        hθI.integrableOn (by filter_upwards [ae_restrict_mem measurableSet_ball] with x hx;exact hLower x hx)
      _ ≤ ∫ x,θ a x := integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall fun x=>(hθBounds a x).1) hθI
  refine ⟨U,hCount,hUS,hDisj,hCover,θ,hFiniteθ,?_,hPartition⟩
  intro a
  refine ⟨(hθData a).1,(hθData a).2.1,(hθData a).2.2.1,(hθData a).2.2.2,hθBounds a,?_,hMass a⟩
  intro x
  exact (hDθ a x).trans_eq (by dsimp only [B,N];ring)

theorem exists_quantitative_whitney_smooth_partition (n : ℕ) (hn : 0<n) :
    ∃ B : ℝ,0<B ∧ ∀ S : Set (Domain n),IsOpen S → volume S≠(∞ : ℝ≥0∞) →
      let r := fun a=>Metric.infDist a Sᶜ/20
      ∃ U : Set (Domain n),U.Countable ∧ U⊆S ∧
        U.PairwiseDisjoint (fun a=>Metric.ball a (r a)) ∧ S=⋃ a : U,Metric.ball a.val (5*r a.val) ∧
        ∃ θ : U → Domain n → ℝ,
          (∀ x,Function.HasFiniteSupport (fun a=>θ a x)) ∧
          (∀ a,ContDiff ℝ ∞ (θ a) ∧ HasCompactSupport (θ a) ∧
            tsupport (θ a)⊆Metric.ball a.val (10*r a.val) ∧ tsupport (θ a)⊆S ∧
            (∀ x,0≤θ a x ∧ θ a x≤1) ∧ (∀ x,‖fderiv ℝ (θ a) x‖≤B/r a.val) ∧
            volume.real (Metric.ball a.val (5*r a.val))/(60 : ℝ)^n≤∫ x,θ a x) ∧
          (∀ x∈S,∑' a,θ a x=1) := by
  obtain ⟨B, hB, _hFormula, H⟩ := exists_quantitative_whitney_smooth_partition_explicit n hn
  exact ⟨B, hB, H⟩

end StationaryHarmonicMaps.Analysis

end
