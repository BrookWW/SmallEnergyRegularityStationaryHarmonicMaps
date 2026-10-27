/- Copyright (c) 2026. All rights reserved. -/
module

public import HolderToCK.Analysis.Poisson.InteriorLocalizationAffine
public import HolderToCK.Analysis.Bootstrap.AffineDerivatives

/-! # Exact scaling of Poisson interior bounds

The original solution is recovered through the inverse affine map. Derivative
norms and the full Holder exponent acquire the exact radius powers.
-/

public section

open HarmonicMaps Set
open scoped ContDiff

namespace HolderToCK

theorem HolderBoundOn.mono_const {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {s : Set (Domain n)} {g : Domain n → E} {γ A B : ℝ}
    (hg : HolderBoundOn s g γ A) (hAB : A ≤ B) : HolderBoundOn s g γ B := by
  intro x hx y hy
  exact (hg x hx y hy).trans
    (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg dist_nonneg γ))

theorem affine_unit_inverse {n : ℕ} (a x : Domain n) (R : PositiveRadius) :
    a + R.val • (R.val⁻¹ • (x - a)) = x := by
  rw [smul_smul, mul_inv_cancel₀ R.property.ne', one_smul]
  exact add_sub_cancel _ _

theorem affine_unit_mapsTo {n : ℕ} (a : Domain n) (R : PositiveRadius) :
    MapsTo (fun x : Domain n => a + R.val • x)
      (Metric.ball (0 : Domain n) 1) (Metric.ball a R.val) := by
  intro x hx
  have h := (affineBall_mem_ball_iff a (0 : Domain n) R.property R.val x).mpr
    (by simpa only [div_self R.property.ne'] using hx)
  simpa only [sub_zero] using h

theorem affine_unit_contDiffOn {n q : ℕ} {v : Domain n → Ambient q}
    (a : Domain n) (R : PositiveRadius)
    (hv : ContDiffOn ℝ 2 (fun z => v (a + R.val • z))
      (Metric.ball (0 : Domain n) (1 / 2))) :
    ContDiffOn ℝ 2 v (Metric.ball a (R.val / 2)) := by
  have hmap : MapsTo (fun x : Domain n => R.val⁻¹ • (x - a))
      (Metric.ball a (R.val / 2)) (Metric.ball (0 : Domain n) (1 / 2)) := by
    intro x hx
    apply (inverseAffine_mem_ball_iff a x R (1 / 2)).mpr
    simpa only [mul_one_div] using hx
  have hi : ContDiff ℝ 2 (fun x : Domain n => R.val⁻¹ • (x - a)) := by
    fun_prop
  have hcomp := hv.comp hi.contDiffOn hmap
  exact hcomp.congr fun x _ => by
    change v x = v (a + R.val • (R.val⁻¹ • (x - a)))
    rw [affine_unit_inverse]

theorem affine_unit_iteratedFDeriv_norm_bound {n q : ℕ}
    {v : Domain n → Ambient q} (a : Domain n) (R : PositiveRadius)
    (c : Ambient q) {A : ℝ} (j : ℕ)
    (hv : ∀ z ∈ Metric.ball (0 : Domain n) (1 / 2),
      ‖iteratedFDeriv ℝ j (fun y => v (a + R.val • y) - c) z‖ ≤ A) :
    ∀ x ∈ Metric.ball a (R.val / 2),
      ‖iteratedFDeriv ℝ j (fun y => v y - c) x‖ ≤
        Real.rpow R.val (-(j : ℝ)) * A := by
  have heq : (fun y => v y - c) =
      (fun y => (v (a + R.val • (R.val⁻¹ • (y - a))) - c)) := by
    funext y
    rw [affine_unit_inverse]
  intro x hx
  have hz : R.val⁻¹ • (x - a) ∈ Metric.ball (0 : Domain n) (1 / 2) := by
    apply (inverseAffine_mem_ball_iff a x R (1 / 2)).mpr
    simpa only [mul_one_div] using hx
  rw [heq, norm_iteratedFDeriv_comp_inverseAffine
    (fun y => v (a + R.val • y) - c) a R j x]
  exact mul_le_mul_of_nonneg_left (hv _ hz) (Real.rpow_nonneg R.property.le _)

theorem affine_unit_hessian_holderBound {n q : ℕ}
    {v : Domain n → Ambient q} (a : Domain n) (R : PositiveRadius)
    {γ A : ℝ}
    (hv : HolderBoundOn (Metric.ball (0 : Domain n) (1 / 2))
      (iteratedFDeriv ℝ 2 (fun z => v (a + R.val • z))) γ A) :
    HolderBoundOn (Metric.ball a (R.val / 2)) (iteratedFDeriv ℝ 2 v) γ
      (A * Real.rpow R.val (-(2 + γ))) := by
  have heq : v = (fun y => v (a + R.val • (R.val⁻¹ • (y - a)))) := by
    funext y
    rw [affine_unit_inverse]
  have h := iteratedFDeriv_inverseAffine_holderBoundOn 2 hv a R
  intro x hx y hy
  have hz (z : Domain n) (hz : z ∈ Metric.ball a (R.val / 2)) :
      R.val⁻¹ • (z - a) ∈ Metric.ball (0 : Domain n) (1 / 2) := by
    apply (inverseAffine_mem_ball_iff a z R (1 / 2)).mpr
    simpa only [mul_one_div] using hz
  rw [heq]
  exact h x (hz x hx) y (hz y hy)

theorem affine_unit_forcing_holderBound {n q : ℕ}
    {f : Domain n → Ambient q} (a : Domain n) (R : PositiveRadius)
    {γ H : ℝ} (hf : HolderBoundOn (Metric.ball a R.val) f γ H) :
    HolderBoundOn (Metric.ball (0 : Domain n) 1)
      (fun z => R.val ^ 2 • f (a + R.val • z)) γ
      (Real.rpow R.val (2 + γ) * H) := by
  have h := hf.affineBall_pullback (0 : Domain n) R.property
  intro x hx y hy
  have hx' : x ∈ Metric.ball (0 : Domain n) (R.val / R.val) := by
    simpa only [div_self R.property.ne'] using hx
  have hy' : y ∈ Metric.ball (0 : Domain n) (R.val / R.val) := by
    simpa only [div_self R.property.ne'] using hy
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (sq_nonneg R.val)]
  have hscale : R.val ^ 2 * Real.rpow R.val γ = Real.rpow R.val (2 + γ) := by
    change R.val ^ 2 * R.val ^ γ = R.val ^ (2 + γ)
    rw [Real.rpow_add R.property, Real.rpow_two]
  calc
    _ ≤ R.val ^ 2 * ((H * Real.rpow R.val γ) * Real.rpow (dist x y) γ) := by
      simpa only [sub_zero] using mul_le_mul_of_nonneg_left (h x hx' y hy')
        (sq_nonneg R.val)
    _ = (Real.rpow R.val (2 + γ) * H) * Real.rpow (dist x y) γ := by
      rw [← hscale]
      ring

theorem poisson_affine_amplitude_le {r γ M L H : ℝ}
    (hr : 0 ≤ r) (hM : 0 ≤ M) (hL : 0 ≤ L) (hH : 0 ≤ H) :
    M + r ^ 2 * L + Real.rpow r (2 + γ) * H ≤
      (1 + r ^ 2 + Real.rpow r (2 + γ)) * (M + L + H) := by
  have hMT : M ≤ M + L + H := by linarith only [hL, hH]
  have hLT : L ≤ M + L + H := by linarith only [hM, hH]
  have hHT : H ≤ M + L + H := by linarith only [hM, hL]
  have hrpow : 0 ≤ Real.rpow r (2 + γ) := Real.rpow_nonneg hr _
  calc
    _ ≤ (M + L + H) + r ^ 2 * (M + L + H) +
        Real.rpow r (2 + γ) * (M + L + H) :=
      add_le_add (add_le_add hMT (mul_le_mul_of_nonneg_left hLT (sq_nonneg r)))
        (mul_le_mul_of_nonneg_left hHT hrpow)
    _ = _ := by ring

theorem poisson_affine_derivative_scale_le {r : ℝ} (hr : 0 < r)
    (j : ℕ) (hj : j ≤ 2) :
    Real.rpow r (-(j : ℝ)) ≤ 1 + Real.rpow r (-1) + Real.rpow r (-2) := by
  have h1 : 0 ≤ Real.rpow r (-1) := Real.rpow_nonneg hr.le _
  have h2 : 0 ≤ Real.rpow r (-2) := Real.rpow_nonneg hr.le _
  interval_cases j
  · simp only [Nat.cast_zero, neg_zero]
    rw [Real.rpow_eq_pow r 0, Real.rpow_zero]
    linarith only [h1, h2]
  · simp only [Nat.cast_one]
    linarith only [h2]
  · norm_num only [Nat.cast_ofNat]
    linarith only [h1]

end HolderToCK
end
