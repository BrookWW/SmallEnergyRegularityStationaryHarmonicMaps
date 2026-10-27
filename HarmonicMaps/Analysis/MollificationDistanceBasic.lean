module

public import HarmonicMaps.Analysis.BallVariance
public import HarmonicMaps.Analysis.MollificationJensen
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Probability variance and distance to an almost-everywhere target

The mean minimizes the squared-distance integral. Almost-everywhere target
values then bound the squared distance of that same mean to the target.
-/

public section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace HarmonicMaps

/-- The probability mean minimizes the quadratic variance. -/
theorem probability_variance_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → E}
    (hf : MemLp f 2 μ) (b : E) :
    (∫ x, ‖f x - ∫ y, f y ∂μ‖ ^ 2 ∂μ) ≤ ∫ x, ‖f x - b‖ ^ 2 ∂μ := by
  let m := ∫ y, f y ∂μ
  let g : α → E := fun x => f x - m
  have hg : MemLp g 2 μ := hf.sub (memLp_const _)
  have hgi : Integrable g μ := hg.integrable (by norm_num)
  have hgsq : Integrable (fun x => ‖g x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hz : (∫ x, g x ∂μ) = 0 := by
    simpa only [g, m, average_eq_integral] using integral_sub_average μ f
  have hi : Integrable (fun x => 2 * inner ℝ (m - b) (g x)) μ :=
    (hgi.const_inner _).const_mul 2
  have hsum : Integrable (fun x => ‖g x‖ ^ 2 + 2 * inner ℝ (m - b) (g x)) μ :=
    hgsq.add hi
  have heq (x : α) : f x - b = g x + (m - b) := by
    dsimp only [g]
    abel
  have hidentity : (∫ x, ‖f x - b‖ ^ 2 ∂μ) =
      (∫ x, ‖g x‖ ^ 2 ∂μ) + ‖m - b‖ ^ 2 := by
    have hcomm (x : α) : inner ℝ (g x) (m - b) = inner ℝ (m - b) (g x) :=
      real_inner_comm _ _
    simp_rw [heq, norm_add_sq_real, hcomm]
    rw [integral_add hsum (integrable_const _), integral_add hgsq hi,
      integral_const_mul, integral_inner hgi, hz, inner_zero_right, mul_zero,
      add_zero, integral_const, probReal_univ, one_smul]
  rw [hidentity]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- AE target membership controls the squared distance of the probability mean. -/
theorem probability_infDist_sq_le_variance {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {q : ℕ} {f : α → Ambient q}
    (hf : MemLp f 2 μ) (S : Set (Ambient q)) (hS : ∀ᵐ x ∂μ, f x ∈ S) :
    Metric.infDist (∫ x, f x ∂μ) S ^ 2 ≤
      ∫ x, ‖f x - ∫ y, f y ∂μ‖ ^ 2 ∂μ := by
  have hsq : Integrable (fun x => ‖f x - ∫ y, f y ∂μ‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm
      (hf.sub (memLp_const _)).aestronglyMeasurable).mp (hf.sub (memLp_const _))
  calc
    _ = ∫ x : α, Metric.infDist (∫ y, f y ∂μ) S ^ 2 ∂μ := by
      rw [integral_const, probReal_univ, one_smul]
    _ ≤ _ := integral_mono_ae (integrable_const _) hsq (hS.mono fun x hx => by
      have Hd : Metric.infDist (∫ y, f y ∂μ) S ≤ dist (∫ y, f y ∂μ) (f x) :=
        Metric.infDist_le_dist_of_mem hx
      have H := pow_le_pow_left₀ Metric.infDist_nonneg Hd 2
      simpa only [dist_eq_norm, norm_sub_rev] using H)

/-- Unit-ball weighted integrability gives actual kernel-probability integrability. -/
theorem fixedMollifierProbability_integrable_of_integrableOn {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Domain n → E}
    (hf : IntegrableOn (fun y => fixedMollifierKernel n y • f y)
      (Metric.ball (0 : Domain n) 1) volume) :
    Integrable f (fixedMollifierProbability n) := by
  apply fixedMollifierProbability_integrable
  have hi := hf.integrable_indicator measurableSet_ball
  have heq : (Metric.ball (0 : Domain n) 1).indicator
      (fun y => fixedMollifierKernel n y • f y) =
      (fun y => fixedMollifierKernel n y • f y) := by
    funext y
    by_cases hy : y ∈ Metric.ball (0 : Domain n) 1
    · exact Set.indicator_of_mem hy _
    · rw [Set.indicator_of_notMem hy,
        fixedMollifierKernel_zero_of_not_mem_unitBall hy, zero_smul]
  rw [heq] at hi
  exact hi

/-- The probability integral is the literal source unit-ball integral. -/
theorem fixedMollifierProbability_integral_eq_setIntegral {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Domain n → E) :
    (∫ y, f y ∂fixedMollifierProbability n) =
      ∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y • f y := by
  rw [fixedMollifierProbability_integral]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [fixedMollifierKernel_zero_of_not_mem_unitBall hy, zero_smul]

/-- Unit-ball AE data transfer to the supported kernel probability. -/
theorem ae_fixedMollifierProbability_of_ae_unitBall {n : ℕ} {p : Domain n → Prop}
    (hp : ∀ᵐ y ∂volume.restrict (Metric.ball (0 : Domain n) 1), p y) :
    ∀ᵐ y ∂fixedMollifierProbability n, p y := by
  change ∀ᵐ y ∂volume.withDensity
    (fun y => ENNReal.ofReal (fixedMollifierKernel n y)), p y
  apply (ae_withDensity_iff
    (fixedMollifierKernel_contDiff n).continuous.measurable.ennreal_ofReal).mpr
  rw [ae_restrict_iff' measurableSet_ball] at hp
  filter_upwards [hp] with y hy hφ
  have hym : y ∈ Metric.ball (0 : Domain n) 1 := by
    by_contra hym
    rw [fixedMollifierKernel_zero_of_not_mem_unitBall hym,
      ENNReal.ofReal_zero] at hφ
    exact hφ rfl
  exact hy hym

end HarmonicMaps
