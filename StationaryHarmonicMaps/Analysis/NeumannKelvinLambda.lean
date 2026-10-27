module

public import StationaryHarmonicMaps.Analysis.NeumannKelvinDerivative
public import StationaryHarmonicMaps.Geometry.UnitInversion
import StationaryHarmonicMaps.Analysis.NeumannKelvinAdjointDerivative

/-!
# Actual dilation-parameter formulas for Neumann reflection

The radial change of variable t = r λ turns the correction into genuine
nonsingular dilations on every fixed exterior annulus. The identities use
the original field and its original derivative throughout.
-/

public section

open HarmonicMaps MeasureTheory Set Filter EuclideanGeometry
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The actual radial integral equals its dilation-parameter integral, for every real exponent. -/
theorem neumann_radial_integral_eq_dilation {n : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p : ℝ) (f : Domain n → G) (x : Domain n) (r : ℝ) (hr : 0 < r) :
    (∫ t in r⁻¹..1, t ^ p • f (t • (r⁻¹ • x))) =
      r ^ (p+1) • (∫ s in (r^2)⁻¹..r⁻¹, s ^ p • f (s • x)) := by
  let F := fun t : ℝ => t ^ p • f (t • (r⁻¹ • x))
  have H := intervalIntegral.smul_integral_comp_mul_left
    (a := (r^2)⁻¹) (b := r⁻¹) F r
  have hA : r*(r^2)⁻¹ = r⁻¹ := by field_simp
  have hB : r*r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  rw [hA,hB] at H
  have hPoint (s : ℝ) (hs : s ∈ uIcc (r^2)⁻¹ r⁻¹) :
      F (r*s) = r^p • (s^p • f (s • x)) := by
    have hspos : 0 < s := (lt_min (inv_pos.mpr (sq_pos_of_pos hr)) (inv_pos.mpr hr)).trans_le hs.1
    have hSample : (r*s) • (r⁻¹ • x) = s • x := by
      rw [smul_smul]
      congr 1
      field_simp
    dsimp only [F]
    rw [hSample, Real.mul_rpow hr.le hspos.le, mul_smul]
  rw [intervalIntegral.integral_congr hPoint, intervalIntegral.integral_smul, smul_smul] at H
  have hPow : r*r^p = r^(p+1) := (mul_comm _ _).trans (Real.rpow_add_one hr.ne' p).symm
  rw [hPow] at H
  exact H.symm

/-- The original Neumann reflection value has the true annular dilation formula. -/
theorem neumannKelvinReflection_eq_dilation {n q : ℕ}
    (u : Domain n → Ambient q) (x : Domain n) (hx : x ≠ 0) :
    neumannKelvinRay 1 u (‖x‖⁻¹ • x) ‖x‖ =
      ‖x‖ ^ (2-(n : ℝ)) • u (inversion (0 : Domain n) 1 x) +
        ((n : ℝ)-2) • (‖x‖ ^ ((n : ℝ)-2) •
          (∫ s in (‖x‖^2)⁻¹..‖x‖⁻¹, s ^ ((n : ℝ)-3) • u (s • x))) := by
  have hI : ‖x‖⁻¹ • (‖x‖⁻¹ • x) = inversion (0 : Domain n) 1 x := by
    rw [inversion_def]
    simp only [dist_zero_right, one_div, vsub_eq_sub, sub_zero, smul_smul, vadd_eq_add, add_zero]
    congr 1
    simp only [pow_two]
  rw [neumannKelvinRay, hI,
    neumann_radial_integral_eq_dilation ((n : ℝ)-3) u x ‖x‖ (norm_pos_iff.mpr hx)]
  have hExp : (n : ℝ)-3+1 = (n : ℝ)-2 := by ring
  rw [hExp]


/-- The actual reflected derivative is a Kelvin derivative plus its true dilation integral. -/
theorem neumannKelvinReflection_fderiv_eq_dilation {n q : ℕ}
    (u : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u)
    (x v : Domain n) (hx : x ≠ 0) :
    let r := ‖x‖
    let P := fun w : Domain n => w - (inner ℝ x w / r^2) • x
    fderiv ℝ (fun y : Domain n => neumannKelvinRay 1 u (‖y‖⁻¹ • y) ‖y‖) x v =
      r ^ (2-(n : ℝ)) • fderiv ℝ u (inversion (0 : Domain n) 1 x)
        (fderiv ℝ (inversion (0 : Domain n) 1) x v) +
      ((n : ℝ)-2) • (r ^ ((n : ℝ)-2) •
        (∫ s in (r^2)⁻¹..r⁻¹, s ^ ((n : ℝ)-2) • fderiv ℝ u (s • x) (P v))) := by
  intro r P
  let θ := r⁻¹ • x
  have hr : 0 < r := norm_pos_iff.mpr hx
  have hP : P v = v - (inner ℝ θ v) • θ := by
    simp only [P, θ, real_inner_smul_left, smul_smul, div_eq_mul_inv, ← inv_pow]
    congr 2
    ring
  have H := neumannKelvinReflection_fderiv_apply 1 (by norm_num : (0 : ℝ)<1) u hu x v hx
  change fderiv ℝ (fun y : Domain n => neumannKelvinRay 1 u (‖y‖⁻¹ • y) ‖y‖) x v =
    r ^ (-(n : ℝ)) • fderiv ℝ u (r⁻¹ • θ) (v - (2*inner ℝ θ v) • θ) +
      (((n : ℝ)-2)/r) •
        (∫ t in r⁻¹..1, t ^ ((n : ℝ)-2) • fderiv ℝ u (t • θ) (v-(inner ℝ θ v) • θ)) at H
  rw [neumann_adjoint_first_derivative_term u x v hx, ← hP] at H
  have hTransform := neumann_radial_integral_eq_dilation ((n : ℝ)-2)
    (fun y => fderiv ℝ u y (P v)) x r hr
  change (∫ t in r⁻¹..1, t ^ ((n : ℝ)-2) • fderiv ℝ u (t • θ) (P v)) =
    r ^ (((n : ℝ)-2)+1) •
      (∫ s in (r^2)⁻¹..r⁻¹, s ^ ((n : ℝ)-2) • fderiv ℝ u (s • x) (P v)) at hTransform
  rw [hTransform] at H
  have hWeight : (((n : ℝ)-2)/r) * r ^ (((n : ℝ)-2)+1) = ((n : ℝ)-2) * r ^ ((n : ℝ)-2) := by
    rw [Real.rpow_add_one hr.ne', div_eq_mul_inv]
    field_simp
  rw [smul_smul, hWeight, ← smul_smul] at H
  exact H

private theorem clm_columns {n q : ℕ} (L : Domain n →L[ℝ] Ambient q) (v : Domain n) :
    L v = ∑ j : Fin n, v j • L (EuclideanSpace.single j 1) := by
  nth_rw 1 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]

/-- Actual directional derivative integration agrees with the finite sum of the original columns. -/
theorem neumann_dilation_integral_fderiv_columns {n q : ℕ}
    (p : ℝ) (u : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u)
    (x v : Domain n) (r : ℝ) (hr : 0 < r) :
    (∫ s in (r^2)⁻¹..r⁻¹, s ^ p • fderiv ℝ u (s • x) v) =
      ∑ j : Fin n, v j • (∫ s in (r^2)⁻¹..r⁻¹,
        s ^ p • fderiv ℝ u (s • x) (EuclideanSpace.single j 1)) := by
  have hI (j : Fin n) : IntervalIntegrable (fun s : ℝ =>
      v j • (s ^ p • fderiv ℝ u (s • x) (EuclideanSpace.single j 1))) volume (r^2)⁻¹ r⁻¹ := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    have hspos : 0 < s := (lt_min (inv_pos.mpr (sq_pos_of_pos hr)) (inv_pos.mpr hr)).trans_le hs.1
    exact (((show ContinuousAt (fun _ : ℝ => v j) s from continuousAt_const)).smul ((Real.continuousAt_rpow_const s p (Or.inl hspos.ne')).smul
      (((hu.continuous_fderiv (by simp)).continuousAt.comp
        (continuousAt_id.smul continuousAt_const)).clm_apply continuousAt_const))).continuousWithinAt
  have hPoint (s : ℝ) : s ^ p • fderiv ℝ u (s • x) v =
      ∑ j : Fin n, v j • (s ^ p • fderiv ℝ u (s • x) (EuclideanSpace.single j 1)) := by
    rw [clm_columns, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ => smul_comm _ _ _)
  rw [intervalIntegral.integral_congr (fun s _ => hPoint s),
    intervalIntegral.integral_finsetSum (fun j _ => hI j)]
  simp only [intervalIntegral.integral_smul]

/-- The actual smooth reflected columns have exactly the original-column dilation formula used by native L2 transport. -/
theorem neumannKelvinReflection_fderiv_column_dilation {n q : ℕ}
    (u : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u)
    (x : Domain n) (hx : x ≠ 0) (i : Fin n) :
    let r := ‖x‖
    let I := inversion (0 : Domain n) 1
    let P := fun v : Domain n => v - (inner ℝ x v / r^2) • x
    fderiv ℝ (fun y : Domain n => neumannKelvinRay 1 u (‖y‖⁻¹ • y) ‖y‖) x (EuclideanSpace.single i 1) =
      r ^ (2-(n : ℝ)) • (∑ j : Fin n,
        (fderiv ℝ I x (EuclideanSpace.single i 1)) j • fderiv ℝ u (I x) (EuclideanSpace.single j 1)) +
      ((n : ℝ)-2) • (∑ j : Fin n, (P (EuclideanSpace.single i 1)) j •
        (r ^ ((n : ℝ)-2) • (∫ s in (r^2)⁻¹..r⁻¹,
          s ^ ((n : ℝ)-2) • fderiv ℝ u (s • x) (EuclideanSpace.single j 1)))) := by
  intro r I P
  rw [neumannKelvinReflection_fderiv_eq_dilation u hu x _ hx, clm_columns,
    neumann_dilation_integral_fderiv_columns ((n : ℝ)-2) u hu x _ r (norm_pos_iff.mpr hx), Finset.smul_sum]
  congr 1
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact smul_comm (r ^ ((n : ℝ)-2)) ((P (EuclideanSpace.single i 1)) j) _

end StationaryHarmonicMaps.Analysis

end
