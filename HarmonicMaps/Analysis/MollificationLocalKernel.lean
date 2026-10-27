module

public import HarmonicMaps.Analysis.MollificationChangeVariables

/-!
# Local kernel bounds for fixed-radius mollification

The fixed normalized kernel has an explicit positive bound depending only on
the dimension. Change of variables requires integrability only on the sampled
ball and gives its exact scale factor.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps

noncomputable section

/-- An explicit upper bound for the fixed normalized kernel. -/
def fixedMollifierKernelBound (n : ℕ) : ℝ :=
  (∫ z, rawMollifierKernel n z)⁻¹

/-- The explicit kernel bound is positive. -/
theorem fixedMollifierKernelBound_pos (n : ℕ) : 0 < fixedMollifierKernelBound n :=
  inv_pos.mpr (rawMollifierKernel_integral_pos n)

/-- The bound holds on the whole domain of the actual fixed kernel. -/
theorem fixedMollifierKernel_le_bound (n : ℕ) (y : Domain n) :
    fixedMollifierKernel n y ≤ fixedMollifierKernelBound n := by
  change rawMollifierKernel n y / (∫ z, rawMollifierKernel n z) ≤ _
  simpa only [fixedMollifierKernelBound, one_div, rawMollifierKernel] using
    div_le_div_of_nonneg_right (Real.smoothTransition.le_one _)
      (rawMollifierKernel_integral_pos n).le

/-- Positive affine sampling maps the unit ball exactly onto the local ball. -/
theorem mollification_sampling_mem_ball_iff {n : ℕ} (h : PositiveRadius)
    (x y : Domain n) :
    x - h.val • y ∈ Metric.ball x h.val ↔ y ∈ Metric.ball (0 : Domain n) 1 := by
  rw [Metric.mem_ball, dist_eq_norm', sub_sub_cancel, norm_smul,
    Real.norm_eq_abs, abs_of_pos h.property, Metric.mem_ball, dist_zero_right]
  constructor
  · intro hy
    exact lt_of_mul_lt_mul_left (by simpa only [mul_one] using hy) h.property.le
  · intro hy
    simpa only [mul_one] using mul_lt_mul_of_pos_left hy h.property

private theorem sampled_indicator_eq {n : ℕ} {E : Type*} [Zero E]
    (h : PositiveRadius) (x : Domain n) (g : Domain n → E) :
    (fun y => (Metric.ball x h.val).indicator g (x - h.val • y)) =
      (Metric.ball (0 : Domain n) 1).indicator (fun y => g (x - h.val • y)) := by
  funext y
  by_cases hy : y ∈ Metric.ball (0 : Domain n) 1
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem
      ((mollification_sampling_mem_ball_iff h x y).mpr hy)]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem
      (fun hz => hy ((mollification_sampling_mem_ball_iff h x y).mp hz))]

/-- Local integrability suffices for the unweighted sampled integrand. -/
theorem mollification_shift_integrableOn {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {g : Domain n → E}
    (h : PositiveRadius) (x : Domain n)
    (hg : IntegrableOn g (Metric.ball x h.val) volume) :
    IntegrableOn (fun y => g (x - h.val • y))
      (Metric.ball (0 : Domain n) 1) volume := by
  have hi := ((hg.integrable_indicator measurableSet_ball).comp_sub_left x).comp_smul
    h.property.ne'
  rw [sampled_indicator_eq] at hi
  exact (integrable_indicator_iff measurableSet_ball).mp hi

/-- Local Lp data transfer under the same positive affine sampling map. -/
theorem mollification_shift_memLp {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {g : Domain n → E} {p : ℝ≥0∞}
    (h : PositiveRadius) (x : Domain n)
    (hg : MemLp g p (volume.restrict (Metric.ball x h.val))) :
    MemLp (fun y => g (x - h.val • y)) p
      (volume.restrict (Metric.ball (0 : Domain n) 1)) := by
  have hi := (memLp_indicator_iff_restrict measurableSet_ball).mpr hg
  have ht : MemLp (fun z => (Metric.ball x h.val).indicator g (x - z)) p volume :=
    hi.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
  have hmap : MemLp (fun z => (Metric.ball x h.val).indicator g (x - z)) p
      (Measure.map (fun y : Domain n => h.val • y) volume) := by
    rw [Measure.map_addHaar_smul volume h.property.ne']
    exact ht.smul_measure ENNReal.ofReal_ne_top
  have hs := hmap.comp_of_map (measurable_const_smul h.val).aemeasurable
  change MemLp (fun y => (Metric.ball x h.val).indicator g (x - h.val • y)) p volume at hs
  rw [sampled_indicator_eq] at hs
  exact (memLp_indicator_iff_restrict measurableSet_ball).mp hs

/-- The literal unweighted local integral has the exact positive-radius scale. -/
theorem mollification_shift_integral_eq {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : PositiveRadius) (x : Domain n) (g : Domain n → E) :
    (∫ y in Metric.ball (0 : Domain n) 1, g (x - h.val • y)) =
      (h.val ^ n)⁻¹ • ∫ z in Metric.ball x h.val, g z := by
  calc
    _ = ∫ y, (Metric.ball x h.val).indicator g (x - h.val • y) := by
      rw [sampled_indicator_eq, integral_indicator measurableSet_ball]
    _ = (h.val ^ n)⁻¹ • ∫ z, (Metric.ball x h.val).indicator g (x - z) := by
      rw [Measure.integral_comp_smul_of_nonneg volume
        (fun z => (Metric.ball x h.val).indicator g (x - z)) h.val
        (hR := h.property.le), finrank_euclideanSpace_fin]
    _ = _ := by
      rw [integral_sub_left_eq_self, integral_indicator measurableSet_ball]

/-- Local almost-everywhere properties transfer under actual affine sampling. -/
theorem ae_mollification_sampling_ball {n : ℕ} {p : Domain n → Prop}
    (h : PositiveRadius) (x : Domain n)
    (hp : ∀ᵐ z ∂volume.restrict (Metric.ball x h.val), p z) :
    ∀ᵐ y ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      p (x - h.val • y) := by
  rw [ae_restrict_iff' measurableSet_ball] at hp
  have hs := ((Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.comp
    (Measure.quasiMeasurePreserving_smul volume h.property.ne')).ae hp
  have hs' : ∀ᵐ y ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      x - h.val • y ∈ Metric.ball x h.val → p (x - h.val • y) :=
    Filter.Eventually.filter_mono ae_restrict_le hs
  filter_upwards [hs', ae_restrict_mem measurableSet_ball] with y hy hym
  exact hy ((mollification_sampling_mem_ball_iff h x y).mpr hym)

/-- Nonnegative local data remain nonnegative under the sampled affine map. -/
theorem mollification_shift_nonneg_ae {n : ℕ} {g : Domain n → ℝ}
    (h : PositiveRadius) (x : Domain n)
    (hg : ∀ᵐ z ∂volume.restrict (Metric.ball x h.val), 0 ≤ g z) :
    ∀ᵐ y ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      0 ≤ g (x - h.val • y) :=
  ae_mollification_sampling_ball h x hg

/-- A fixed-kernel majorant bounds the literal weighted local integral. -/
theorem mollification_local_kernel_estimate {n : ℕ} {g : Domain n → ℝ}
    (h : PositiveRadius) (x : Domain n)
    (hg : IntegrableOn g (Metric.ball x h.val) volume)
    (hgnonneg : ∀ᵐ z ∂volume.restrict (Metric.ball x h.val), 0 ≤ g z)
    {K : ℝ} (hK : ∀ y : Domain n, fixedMollifierKernel n y ≤ K) :
    IntegrableOn (fun y => fixedMollifierKernel n y * g (x - h.val • y))
      (Metric.ball (0 : Domain n) 1) volume ∧
      (∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y * g (x - h.val • y)) ≤
        K * (h.val ^ n)⁻¹ * ∫ z in Metric.ball x h.val, g z := by
  have hi := mollification_shift_integrableOn h x hg
  have hweighted : IntegrableOn
      (fun y => fixedMollifierKernel n y * g (x - h.val • y))
      (Metric.ball (0 : Domain n) 1) volume :=
    hi.bdd_smul K
      (fixedMollifierKernel_contDiff n).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (fixedMollifierKernel_nonneg n y)]
        exact hK y)
  refine ⟨hweighted, ?_⟩
  calc
    _ ≤ ∫ y in Metric.ball (0 : Domain n) 1, K * g (x - h.val • y) := by
      apply integral_mono_ae hweighted (hi.const_mul K)
      filter_upwards [mollification_shift_nonneg_ae h x hgnonneg] with y hy
      exact mul_le_mul_of_nonneg_right (hK y) hy
    _ = _ := by
      rw [integral_const_mul, mollification_shift_integral_eq, smul_eq_mul]
      ring

end
end HarmonicMaps

end
