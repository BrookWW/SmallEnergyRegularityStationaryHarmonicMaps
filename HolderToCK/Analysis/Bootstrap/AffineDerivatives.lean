module

public import HolderToCK.Foundation.HolderBounds
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Topology.Algebra.Module.Equiv

/-! # All-order affine derivative and Holder scaling

Positive dilations multiply the actual multilinear derivative of order k by
the kth power of the dilation. The inverse affine map therefore gives the
exact radius powers for derivative norms and Holder seminorms.
-/

public section

open HarmonicMaps Set
open scoped ContDiff

namespace HolderToCK

theorem iteratedFDeriv_comp_affine {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Domain n → E) (a : Domain n) {r : ℝ} (hr : r ≠ 0) (k : ℕ) (x : Domain n) :
    iteratedFDeriv ℝ k (fun z => u (a + r • z)) x =
      r ^ k • iteratedFDeriv ℝ k u (a + r • x) := by
  let e : Domain n ≃L[ℝ] Domain n := ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)
  have h := e.iteratedFDerivWithin_comp_right (fun z => u (a + z))
    uniqueDiffOn_univ (mem_univ (e x)) k
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  change iteratedFDeriv ℝ k (fun z => u (a + r • z)) x =
    (iteratedFDeriv ℝ k (fun z => u (a + z)) (r • x)).compContinuousLinearMap
      (fun _ => e.toContinuousLinearMap) at h
  rw [h, iteratedFDeriv_comp_add_left]
  ext v
  change (iteratedFDeriv ℝ k u (a + r • x)) (fun j => r • v j) =
    r ^ k • (iteratedFDeriv ℝ k u (a + r • x)) v
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

theorem iteratedFDeriv_comp_inverseAffine {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Domain n → E) (a : Domain n) (R : PositiveRadius) (k : ℕ) (x : Domain n) :
    iteratedFDeriv ℝ k (fun z => u (R.val⁻¹ • (z - a))) x =
      (R.val⁻¹) ^ k • iteratedFDeriv ℝ k u (R.val⁻¹ • (x - a)) := by
  have heq : (fun z => u (R.val⁻¹ • (z - a))) =
      (fun z => u (-(R.val⁻¹ • a) + R.val⁻¹ • z)) := by
    funext z
    rw [smul_sub, sub_eq_add_neg, add_comm]
  rw [heq, iteratedFDeriv_comp_affine u _ (inv_ne_zero R.property.ne')]
  rw [smul_sub, sub_eq_add_neg, add_comm (R.val⁻¹ • x)]

theorem norm_iteratedFDeriv_comp_inverseAffine {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Domain n → E) (a : Domain n) (R : PositiveRadius) (k : ℕ) (x : Domain n) :
    ‖iteratedFDeriv ℝ k (fun z => u (R.val⁻¹ • (z - a))) x‖ =
      Real.rpow R.val (-(k : ℝ)) *
        ‖iteratedFDeriv ℝ k u (R.val⁻¹ • (x - a))‖ := by
  rw [iteratedFDeriv_comp_inverseAffine, norm_smul,
    Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr R.property.le) k)]
  change (R.val⁻¹) ^ k * ‖iteratedFDeriv ℝ k u (R.val⁻¹ • (x - a))‖ =
    R.val ^ (-(k : ℝ)) * ‖iteratedFDeriv ℝ k u (R.val⁻¹ • (x - a))‖
  rw [Real.rpow_neg R.property.le, Real.rpow_natCast, inv_pow]

theorem dist_inverseAffine {n : ℕ} (a x y : Domain n) (R : PositiveRadius) :
    dist (R.val⁻¹ • (x - a)) (R.val⁻¹ • (y - a)) = R.val⁻¹ * dist x y := by
  rw [dist_eq_norm, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr R.property.le), dist_eq_norm]

theorem inverseAffine_mem_ball_iff {n : ℕ} (a x : Domain n) (R : PositiveRadius) (s : ℝ) :
    R.val⁻¹ • (x - a) ∈ Metric.ball (0 : Domain n) s ↔ x ∈ Metric.ball a (R.val * s) := by
  rw [Metric.mem_ball, Metric.mem_ball, dist_zero_right, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr R.property.le)]
  rw [← div_eq_inv_mul, div_lt_iff₀ R.property, dist_eq_norm, mul_comm s R.val]

theorem HolderBoundOn.comp_inverseAffine {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : Domain n → E} {s : Set (Domain n)} {γ H : ℝ}
    (hu : HolderBoundOn s u γ H) (a : Domain n) (R : PositiveRadius) :
    HolderBoundOn ((fun x => R.val⁻¹ • (x - a)) ⁻¹' s)
      (fun x => u (R.val⁻¹ • (x - a))) γ (H * Real.rpow R.val (-γ)) := by
  intro x hx y hy
  have h := hu (R.val⁻¹ • (x - a)) hx (R.val⁻¹ • (y - a)) hy
  change ‖u (R.val⁻¹ • (x - a)) - u (R.val⁻¹ • (y - a))‖ ≤
    H * (dist (R.val⁻¹ • (x - a)) (R.val⁻¹ • (y - a))) ^ γ at h
  rw [dist_inverseAffine, Real.mul_rpow (inv_nonneg.mpr R.property.le) dist_nonneg,
    Real.inv_rpow R.property.le, ← Real.rpow_neg R.property.le, ← mul_assoc] at h
  exact h

theorem iteratedFDeriv_inverseAffine_holderBoundOn {n q : ℕ}
    {u : Domain n → Ambient q} {s : Set (Domain n)} {γ H : ℝ}
    (k : ℕ) (hu : HolderBoundOn s (iteratedFDeriv ℝ k u) γ H)
    (a : Domain n) (R : PositiveRadius) :
    HolderBoundOn ((fun x => R.val⁻¹ • (x - a)) ⁻¹' s)
      (iteratedFDeriv ℝ k (fun x => u (R.val⁻¹ • (x - a)))) γ
      (H * Real.rpow R.val (-((k : ℝ) + γ))) := by
  intro x hx y hy
  rw [iteratedFDeriv_comp_inverseAffine, iteratedFDeriv_comp_inverseAffine,
    ← smul_sub, norm_smul, Real.norm_of_nonneg
      (pow_nonneg (inv_nonneg.mpr R.property.le) k)]
  have h := (hu.comp_inverseAffine a R) x hx y hy
  have hscale : (R.val⁻¹) ^ k = Real.rpow R.val (-(k : ℝ)) := by
    change (R.val⁻¹) ^ k = R.val ^ (-(k : ℝ))
    rw [Real.rpow_neg R.property.le, Real.rpow_natCast, inv_pow]
  calc
    _ ≤ (R.val⁻¹) ^ k * ((H * Real.rpow R.val (-γ)) * Real.rpow (dist x y) γ) :=
      mul_le_mul_of_nonneg_left h (pow_nonneg (inv_nonneg.mpr R.property.le) k)
    _ = H * Real.rpow R.val (-((k : ℝ) + γ)) * Real.rpow (dist x y) γ := by
      change (R.val⁻¹) ^ k * ((H * R.val ^ (-γ)) * (dist x y) ^ γ) =
        H * R.val ^ (-((k : ℝ) + γ)) * (dist x y) ^ γ
      change (R.val⁻¹) ^ k = R.val ^ (-(k : ℝ)) at hscale
      rw [hscale, neg_add, Real.rpow_add R.property]
      ring

end HolderToCK
end
