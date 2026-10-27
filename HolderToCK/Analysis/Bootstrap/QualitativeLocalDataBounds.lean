module

public import HolderToCK.Analysis.Bootstrap.AffineDerivatives
public import HolderToCK.Analysis.Bootstrap.DerivativeProducts
public import HolderToCK.Analysis.Bootstrap.FirstDerivativeHolder

/-! # Finite bounds on the initial qualitative ball

Holder control of the actual first derivative bounds its norm on a local ball.
Positive affine dilation transports its native seminorm exactly. On the fixed
convex initial ball, a first derivative bound controls the centered map and its
lower Holder seminorm.
-/

public section

open HarmonicMaps Set
open scoped ContDiff

namespace HolderToCK

theorem HolderBoundOn.norm_le_on_ball {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : Domain n → E} {a : Domain n} {r γ H : ℝ}
    (h : HolderBoundOn (Metric.ball a r) f γ H)
    (hr : 0 < r) (hγ : 0 ≤ γ) (hH : 0 ≤ H) :
    ∀ x ∈ Metric.ball a r, ‖f x‖ ≤ ‖f a‖ + H * Real.rpow r γ := by
  intro x hx
  have hpower := Real.rpow_le_rpow dist_nonneg
    (show dist x a ≤ r from hx.le) hγ
  calc
    ‖f x‖ ≤ ‖f x - f a‖ + ‖f a‖ := norm_le_norm_sub_add _ _
    _ ≤ H * Real.rpow r γ + ‖f a‖ :=
      add_le_add ((h x hx a (Metric.mem_ball_self hr)).trans
        (mul_le_mul_of_nonneg_left hpower hH)) le_rfl
    _ = _ := add_comm _ _

theorem norm_iteratedFDeriv_one_comp_affine {n q : ℕ}
    (u : Domain n → Ambient q) (a : Domain n) (r : PositiveRadius) (z : Domain n) :
    ‖iteratedFDeriv ℝ 1 (fun z => u (a + r.val • z)) z‖ =
      r.val * ‖fderiv ℝ u (a + r.val • z)‖ := by
  rw [iteratedFDeriv_comp_affine u a r.property.ne', norm_smul,
    pow_one, Real.norm_of_nonneg r.property.le, norm_iteratedFDeriv_one]

theorem HolderBoundOn.iteratedFDeriv_one_comp_affine {n q : ℕ}
    {s : Set (Domain n)} {u : Domain n → Ambient q} {γ H : ℝ}
    (h : HolderBoundOn s (fderiv ℝ u) γ H) (a : Domain n) (r : PositiveRadius) :
    HolderBoundOn ((fun z => a + r.val • z) ⁻¹' s)
      (iteratedFDeriv ℝ 1 (fun z => u (a + r.val • z))) γ
      (r.val * (H * Real.rpow r.val γ)) := by
  intro x hx y hy
  rw [iteratedFDeriv_comp_affine u a r.property.ne',
    iteratedFDeriv_comp_affine u a r.property.ne', pow_one, ← smul_sub,
    norm_smul, Real.norm_of_nonneg r.property.le,
    ← norm_iteratedFDeriv_fderiv_sub u 0, norm_iteratedFDeriv_zero_sub]
  have hdist : dist (a + r.val • x) (a + r.val • y) = r.val * dist x y := by
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
      norm_smul, Real.norm_of_nonneg r.property.le, dist_eq_norm]
  have hh := h _ hx _ hy
  rw [hdist] at hh
  simp only [Real.rpow_eq_pow] at hh
  rw [Real.mul_rpow r.property.le dist_nonneg] at hh
  calc
    _ ≤ r.val * (H * (Real.rpow r.val γ * Real.rpow (dist x y) γ)) :=
      mul_le_mul_of_nonneg_left hh r.property.le
    _ = _ := by ring

theorem qualitative_c1_finite_initial_bounds {n q : ℕ}
    {v : Domain n → Ambient q} {γ C D : ℝ}
    (hv : ContDiffOn ℝ 1 v (Metric.ball (0 : Domain n) (5 / 8)))
    (hγ : 0 < γ) (hγOne : γ < 1) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hNativeC : ∀ z ∈ Metric.ball (0 : Domain n) (5 / 8),
      ‖iteratedFDeriv ℝ 1 v z‖ ≤ C)
    (hNativeHolder : HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
      (iteratedFDeriv ℝ 1 v) γ D) :
    ∃ M : ℝ, ∃ S : PositiveRadius, 0 < M ∧
      (∀ z ∈ Metric.ball (0 : Domain n) (5 / 8), v z ∈ Metric.closedBall (v 0) S.val) ∧
      (∀ z ∈ Metric.ball (0 : Domain n) (5 / 8), ‖v z - v 0‖ ≤ M) ∧
      (∀ z ∈ Metric.ball (0 : Domain n) (5 / 8), ‖fderiv ℝ v z‖ ≤ M) ∧
      (∀ z ∈ Metric.ball (0 : Domain n) (5 / 8), ‖iteratedFDeriv ℝ 1 v z‖ ≤ M) ∧
      HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8)) (fderiv ℝ v) γ M ∧
      HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8)) (iteratedFDeriv ℝ 1 v) γ M ∧
      HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8)) v γ M := by
  let L : ℝ := C * Real.rpow 2 (1 - γ)
  have hL : 0 ≤ L := mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  let M : ℝ := C + D + L + 1
  have hM : 0 < M := by dsimp only [M]; linarith only [hC, hD, hL]
  have hCM : C ≤ M := by dsimp only [M]; linarith only [hD, hL]
  have hDM : D ≤ M := by dsimp only [M]; linarith only [hC, hL]
  have hLM : L ≤ M := by dsimp only [M]; linarith only [hC, hD]
  let S : PositiveRadius := ⟨M + 1, by linarith only [hM]⟩
  have hDerivativeC : ∀ z ∈ Metric.ball (0 : Domain n) (5 / 8), ‖fderiv ℝ v z‖ ≤ C := by
    intro z hz
    simpa only [norm_iteratedFDeriv_one] using hNativeC z hz
  have hDerivativeHolderV : HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
      (fderiv ℝ v) γ M := by
    intro x hx y hy
    rw [← norm_iteratedFDeriv_zero_sub (fderiv ℝ v), norm_iteratedFDeriv_fderiv_sub]
    exact (hNativeHolder x hx y hy).trans
      (mul_le_mul_of_nonneg_right hDM (Real.rpow_nonneg dist_nonneg _))
  have hNativeHolderM : HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
      (iteratedFDeriv ℝ 1 v) γ M := by
    intro x hx y hy
    exact (hNativeHolder x hx y hy).trans
      (mul_le_mul_of_nonneg_right hDM (Real.rpow_nonneg dist_nonneg _))
  have hCenteredC : ∀ z ∈ Metric.ball (0 : Domain n) (5 / 8), ‖v z - v 0‖ ≤ C := by
    intro z hz
    have h0 : (0 : Domain n) ∈ Metric.ball (0 : Domain n) (5 / 8) :=
      Metric.mem_ball_self (by norm_num)
    have hLip := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun x hx => (hv.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt one_ne_zero)
      hDerivativeC (convex_ball (0 : Domain n) (5 / 8)) h0 hz
    have hnormOne : ‖z - (0 : Domain n)‖ ≤ 1 := by
      simpa only [sub_zero, dist_zero_right] using
        (show dist z 0 < (5 / 8 : ℝ) from hz).le.trans (by norm_num)
    exact hLip.trans ((mul_le_mul_of_nonneg_left hnormOne hC).trans_eq (mul_one C))
  have hDiameter : ∀ x ∈ Metric.ball (0 : Domain n) (5 / 8),
      ∀ y ∈ Metric.ball (0 : Domain n) (5 / 8), dist x y ≤ 2 := by
    intro x hx y hy
    have ht := dist_triangle x (0 : Domain n) y
    have hx0 : dist x 0 < (5 / 8 : ℝ) := hx
    have hy0 : dist y 0 < (5 / 8 : ℝ) := hy
    rw [dist_comm (0 : Domain n) y] at ht
    linarith only [ht, hx0, hy0]
  have hvHolder : HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8)) v γ M := by
    have hh := c1_holderBoundOn_of_diameter (ballDomain (0 : Domain n) (5 / 8))
      hv (convex_ball _ _) hC hγ.le hγOne.le hDerivativeC hDiameter
    intro x hx y hy
    exact (hh x hx y hy).trans
      (mul_le_mul_of_nonneg_right hLM (Real.rpow_nonneg dist_nonneg _))
  refine ⟨M, S, hM, ?_, ?_, ?_, ?_, hDerivativeHolderV, hNativeHolderM, hvHolder⟩
  · intro z hz
    change dist (v z) (v 0) ≤ M + 1
    rw [dist_eq_norm]
    exact (hCenteredC z hz).trans (hCM.trans (by linarith only))
  · exact fun z hz => (hCenteredC z hz).trans hCM
  · exact fun z hz => (hDerivativeC z hz).trans hCM
  · exact fun z hz => (hNativeC z hz).trans hCM

end HolderToCK
end
