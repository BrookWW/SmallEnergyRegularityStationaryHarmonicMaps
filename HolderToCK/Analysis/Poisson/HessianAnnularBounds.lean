module

public import HolderToCK.Analysis.Poisson.KernelCancellation
public import HolderToCK.Analysis.Poisson.KernelBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Absolute Hessian kernel bounds on positive annuli

The radial power of degree minus the dimension integrates to the sphere area
times the logarithm of the radius ratio. This controls translated outer shells.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace HolderToCK

theorem inverseDimensionPower_integrableOn_annulus {n : ℕ} {a b : ℝ}
    (ha : 0 < a) :
    IntegrableOn (fun z : Domain n => ‖z‖ ^ (-(n : ℝ)))
      (Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a) := by
  have hc : ContinuousOn (fun z : Domain n => ‖z‖ ^ (-(n : ℝ)))
      (Metric.closedBall (0 : Domain n) b \ Metric.ball (0 : Domain n) a) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hzero
      exact hz.2 (by rw [hzero]; exact Metric.mem_ball_self ha)
    exact (continuous_norm.continuousAt.rpow_const
      (Or.inl (norm_ne_zero_iff.mpr hz0))).continuousWithinAt
  exact (hc.integrableOn_compact ((isCompact_closedBall _ _).diff Metric.isOpen_ball)).mono_set
    (fun _ hz => ⟨Metric.ball_subset_closedBall hz.1, hz.2⟩)

theorem inverseDimensionPower_integral_annulus {n : ℕ} (hn : 0 < n)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ z : Domain n in Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a,
      ‖z‖ ^ (-(n : ℝ))) = euclideanSphereArea n * Real.log (b / a) := by
  rw [integral_annulus_eq_polar hn ha hab (inverseDimensionPower_integrableOn_annulus ha)]
  have heq : (∫ r in a..b, r ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1, ‖0 + r • θ.val‖ ^ (-(n : ℝ))
        ∂(volume : Measure (Domain n)).toSphere) =
      ∫ r in a..b, euclideanSphereArea n * r⁻¹ := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
    have hrp : 0 < r := ha.trans_le hr'.1
    have hnorm (θ : Metric.sphere (0 : Domain n) 1) : ‖0 + r • θ.val‖ = r := by
      have hθ : ‖θ.val‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
      rw [zero_add, norm_smul, Real.norm_of_nonneg hrp.le, hθ, mul_one]
    simp_rw [hnorm]
    rw [integral_const, smul_eq_mul]
    change r ^ (n - 1) * (euclideanSphereArea n * r ^ (-(n : ℝ))) = _
    have hpower : r ^ (n - 1) * r ^ (-(n : ℝ)) = r⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hrp]
      have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      rw [hn1, show (n : ℝ) - 1 + -(n : ℝ) = -1 by ring, Real.rpow_neg_one]
    calc
      _ = euclideanSphereArea n * (r ^ (n - 1) * r ^ (-(n : ℝ))) := by ring
      _ = _ := by rw [hpower]
  rw [heq, intervalIntegral.integral_const_mul,
    integral_inv_of_pos ha (ha.trans_le hab)]

theorem hessianKernelExpression_annulus_norm_integral_bound {n : ℕ} (hn : 0 < n)
    (i j : Fin n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ z in Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a,
      ‖hessianKernelExpression i j z‖) ≤ ((n : ℝ) + 1) * Real.log (b / a) := by
  have hC : 0 ≤ ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ :=
    mul_nonneg (by positivity) (inv_nonneg.mpr (euclideanSphereArea_pos hn).le)
  calc
    _ ≤ ∫ z in Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a,
        (((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹) * ‖z‖ ^ (-(n : ℝ)) := by
      apply setIntegral_mono_on (hessianKernelExpression_integrableOn_annulus i j ha).norm
        ((inverseDimensionPower_integrableOn_annulus ha).const_mul _)
        (measurableSet_ball.diff measurableSet_ball)
      intro z hz
      rw [Real.norm_eq_abs]
      have hz0 : z ≠ 0 := by
        intro hzero
        exact hz.2 (by rw [hzero]; exact Metric.mem_ball_self ha)
      exact hessianKernelExpression_bound hn i j z hz0
    _ = _ := by
      rw [integral_const_mul, inverseDimensionPower_integral_annulus hn ha hab]
      have hS : euclideanSphereArea n ≠ 0 := (euclideanSphereArea_pos hn).ne'
      rw [mul_assoc ((n : ℝ) + 1), ← mul_assoc (euclideanSphereArea n)⁻¹,
        inv_mul_cancel₀ hS, one_mul]

end HolderToCK
end
