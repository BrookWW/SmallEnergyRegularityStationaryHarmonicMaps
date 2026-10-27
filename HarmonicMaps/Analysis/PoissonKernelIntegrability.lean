module

public import HarmonicMaps.Analysis.BallPolarIntegralNormalization
public import HarmonicMaps.Energy
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Integrable ball kernels with canonical polar angular measure

The radius-scaled measure here is the pushforward of the canonical angular
measure with polar weight R^(n-1). Its identification with Hausdorff surface
measure is not asserted. The kernel is integrable for actual smooth input and
an interior evaluation point. The center constant calculation fixes the
coefficient relative to this measure; harmonicity and boundary convergence
remain separate obligations.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

private theorem scaledUnitSphere_norm {n : ℕ} (R : PositiveRadius)
    (θ : Metric.sphere (0 : Domain n) 1) : ‖R.val • θ.val‖ = R.val := by
  have hθ : ‖θ.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  rw [norm_smul, Real.norm_of_nonneg R.property.le, hθ, mul_one]

private theorem scaledUnitSphere_closedEmbedding {n : ℕ} (R : PositiveRadius) :
    Topology.IsClosedEmbedding
      (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val) := by
  exact (Homeomorph.smulOfNeZero R.val R.property.ne').isClosedEmbedding.comp
    Metric.isClosed_sphere.isClosedEmbedding_subtypeVal

/-- Smooth input on a neighborhood of the closed ball gives actual
integrability of the nonsingular boundary kernel at every interior point. -/
theorem poisson_boundary_integrable {n q : ℕ} (R : PositiveRadius)
    (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
    Integrable (fun θ : Metric.sphere (0 : Domain n) 1 =>
      (‖x - R.val • θ.val‖ ^ n)⁻¹ • m (R.val • θ.val))
      (volume : Measure (Domain n)).toSphere := by
  have hmap : Continuous (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val) :=
    (continuous_const : Continuous (fun _ : Metric.sphere (0 : Domain n) 1 => R.val)).smul
      continuous_subtype_val
  have hmem (θ : Metric.sphere (0 : Domain n) 1) : R.val • θ.val ∈ U := by
    apply hclosed
    rw [Metric.mem_closedBall, dist_zero_right, scaledUnitSphere_norm]
  have hnonzero (θ : Metric.sphere (0 : Domain n) 1) :
      ‖x - R.val • θ.val‖ ^ n ≠ 0 := by
    apply pow_ne_zero
    apply norm_ne_zero_iff.mpr
    apply sub_ne_zero.mpr
    intro heq
    have hnorm : ‖x‖ < R.val := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    rw [heq, scaledUnitSphere_norm] at hnorm
    exact (lt_irrefl R.val) hnorm
  have hboundary : Continuous (fun θ : Metric.sphere (0 : Domain n) 1 =>
      m (R.val • θ.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (hm.contDiffAt (hU.mem_nhds (hmem θ))).continuousAt.comp
      (f := fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val) hmap.continuousAt
  have hkernel : Continuous (fun θ : Metric.sphere (0 : Domain n) 1 =>
      (‖x - R.val • θ.val‖ ^ n)⁻¹ • m (R.val • θ.val)) :=
    (((continuous_const.sub hmap).norm.pow n).inv₀ hnonzero).smul hboundary
  exact hkernel.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Actual integrability survives the nonzero radial embedding and its exact
polar surface weight. -/
theorem poisson_scaledPolar_integrable {n q : ℕ} (R : PositiveRadius)
    (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
    Integrable (fun y : Domain n => (‖x - y‖ ^ n)⁻¹ • m y)
      (Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
        (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) := by
  apply (scaledUnitSphere_closedEmbedding R).measurableEmbedding.integrable_map_iff.mpr
  exact (poisson_boundary_integrable R U hU hclosed m hm x hx).smul_measure
    ENNReal.ofReal_ne_top

/-- Exact radius-weight algebra transforms the literal coefficient to angular
coordinates. This theorem does not identify the measure with Hausdorff dS. -/
theorem poisson_scaledPolar_formula_eq_angular {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
    ((R.val ^ 2 - ‖x‖ ^ 2) /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
      (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m y
        ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
          (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) =
    (((R.val ^ 2 - ‖x‖ ^ 2) * R.val ^ (n - 2)) /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1))) •
      (∫ θ : Metric.sphere (0 : Domain n) 1,
        (‖x - R.val • θ.val‖ ^ n)⁻¹ • m (R.val • θ.val)
          ∂(volume : Measure (Domain n)).toSphere) := by
  have hInt := poisson_scaledPolar_integrable R U hU hclosed m hm x hx
  rw [integral_map (scaledUnitSphere_closedEmbedding R).measurableEmbedding.measurable.aemeasurable
      hInt.aestronglyMeasurable,
    integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg R.property.le _), smul_smul]
  apply congrArg (fun c : ℝ => c • (∫ θ : Metric.sphere (0 : Domain n) 1,
    (‖x - R.val • θ.val‖ ^ n)⁻¹ • m (R.val • θ.val)
      ∂(volume : Measure (Domain n)).toSphere))
  have hexp : n - 1 = (n - 2) + 1 := by omega
  rw [hexp, pow_succ]
  field_simp [R.property.ne']
  ring

/-- The literal coefficient reproduces constant vector data at the center for
the exact scaled canonical polar measure. -/
theorem poisson_constant_at_center {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (c : Ambient q) :
    (R.val ^ 2 /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
      (∫ y : Domain n, (‖(0 : Domain n) - y‖ ^ n)⁻¹ • c
        ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
          (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) = c := by
  rw [(scaledUnitSphere_closedEmbedding R).integral_map,
    integral_smul_measure, ENNReal.toReal_ofReal (pow_nonneg R.property.le _)]
  have hnorm (θ : Metric.sphere (0 : Domain n) 1) :
      ‖(0 : Domain n) - R.val • θ.val‖ = R.val := by
    rw [zero_sub, norm_neg, scaledUnitSphere_norm]
  simp_rw [hnorm]
  rw [integral_const,
    (volume : Measure (Domain n)).toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_smul]
  have hnzero : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hball : (volume : Measure (Domain n)).real (Metric.ball 0 1) ≠ 0 := by
    apply ne_of_gt
    apply ENNReal.toReal_pos
    · exact Metric.isOpen_ball.measure_ne_zero volume (Metric.nonempty_ball.mpr (by norm_num))
    · exact measure_ball_ne_top
  have hexp : n = (n - 1) + 1 := by omega
  have hpower : R.val ^ n = R.val ^ (n - 1) * R.val := by
    conv_lhs => rw [hexp, pow_succ]
  have hscalar : R.val ^ 2 /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val) *
      (R.val ^ (n - 1) *
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) *
          (R.val ^ n)⁻¹)) = 1 := by
    rw [hpower]
    field_simp [hnzero, hball, R.property.ne']
  rw [hscalar, one_smul]

/-- A smaller closed ball has a positive uniform separation from every actual
boundary point, giving the exact reciprocal kernel bound. -/
theorem poisson_boundary_separation {n : ℕ} (R : PositiveRadius)
    (r : ℝ) (_hr : 0 ≤ r) (hrR : r < R.val)
    (x : Domain n) (hx : x ∈ Metric.closedBall (0 : Domain n) r)
    (θ : Metric.sphere (0 : Domain n) 1) :
    0 < R.val - r ∧ R.val - r ≤ ‖x - R.val • θ.val‖ ∧
      (‖x - R.val • θ.val‖ ^ n)⁻¹ ≤ ((R.val - r) ^ n)⁻¹ := by
  have hgap : 0 < R.val - r := sub_pos.mpr hrR
  have hnorm : ‖x‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hsep : R.val - r ≤ ‖x - R.val • θ.val‖ := by
    calc
      R.val - r ≤ R.val - ‖x‖ := sub_le_sub_left hnorm _
      _ = ‖R.val • θ.val‖ - ‖x‖ := by rw [scaledUnitSphere_norm]
      _ ≤ ‖R.val • θ.val - x‖ := norm_sub_norm_le _ _
      _ = ‖x - R.val • θ.val‖ := norm_sub_rev _ _
  have hbase : 0 ≤ R.val - r := hgap.le
  exact ⟨hgap, hsep, inv_anti₀ (pow_pos hgap n) (pow_le_pow_left₀ hbase hsep n)⟩

/-- For each actual boundary value, the pointwise kernel is smooth in the
interior evaluation point. This does not differentiate an integral. -/
theorem poisson_boundaryKernel_contDiffOn {n q : ℕ} (R : PositiveRadius)
    (m : Domain n → Ambient q) (θ : Metric.sphere (0 : Domain n) 1) :
    ContDiffOn ℝ ∞ (fun x : Domain n =>
      (‖x - R.val • θ.val‖ ^ n)⁻¹ • m (R.val • θ.val))
      (Metric.ball (0 : Domain n) R.val) := by
  have hne (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
      x - R.val • θ.val ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have hnorm : ‖x‖ < R.val := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    rw [heq, scaledUnitSphere_norm] at hnorm
    exact (lt_irrefl R.val) hnorm
  have hnorm : ContDiffOn ℝ ∞ (fun x : Domain n => ‖x - R.val • θ.val‖)
      (Metric.ball (0 : Domain n) R.val) :=
    (contDiffOn_id.sub contDiffOn_const).norm ℝ hne
  exact ((hnorm.pow n).inv (fun x hx => pow_ne_zero n (norm_ne_zero_iff.mpr (hne x hx)))).smul
    contDiffOn_const

end HarmonicMaps
