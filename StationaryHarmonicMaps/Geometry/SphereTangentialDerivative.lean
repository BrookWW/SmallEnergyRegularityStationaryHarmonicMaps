module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Actual tangential differentiation of a vanishing sphere restriction

An explicit normalized curve stays on the unit sphere and has the chosen
tangential velocity. The ordinary ambient derivative therefore vanishes
in that direction for any differentiable map whose sphere restriction is zero.
-/

public section

open HarmonicMaps Metric
open scoped Topology

namespace StationaryHarmonicMaps

/-- The actual ambient derivative in a sphere-tangent direction vanishes when the whole sphere restriction vanishes. -/
theorem fderiv_eq_zero_of_zero_on_unitSphere {n q : ℕ}
    (F : Domain n → Ambient q) (hzero : ∀ y ∈ sphere (0 : Domain n) 1, F y = 0)
    (x v : Domain n) (hx : ‖x‖ = 1) (hv : inner ℝ x v = 0)
    (hF : DifferentiableAt ℝ F x) : fderiv ℝ F x v = 0 := by
  let b : ℝ → ℝ := fun t => 1 + t^2 * ‖v‖^2
  let c : ℝ → ℝ := fun t => (Real.sqrt (b t))⁻¹
  let γ : ℝ → Domain n := fun t => c t • (x+t • v)
  have hbpos (t : ℝ) : 0 < b t := by dsimp only [b]; positivity
  have hnorm (t : ℝ) : ‖x+t • v‖ = Real.sqrt (b t) := by
    have hs : ‖x+t • v‖ ^ 2 = b t := by
      rw [norm_add_sq_real, hx, real_inner_smul_right, hv, mul_zero, norm_smul, Real.norm_eq_abs]
      simp only [mul_pow, sq_abs, one_pow, mul_zero, add_zero, b]
    rw [← hs, Real.sqrt_sq (norm_nonneg _)]
  have hγsphere (t : ℝ) : γ t ∈ sphere (0 : Domain n) 1 := by
    change dist (γ t) 0 = 1
    rw [dist_zero_right]
    change ‖c t • (x+t • v)‖ = 1
    rw [norm_smul, Real.norm_eq_abs, hnorm]
    dsimp only [c]
    rw [abs_inv, abs_of_pos (Real.sqrt_pos.2 (hbpos t)), inv_mul_cancel₀ (Real.sqrt_pos.2 (hbpos t)).ne']
  have hb : HasDerivAt b 0 0 := by
    convert ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖v‖^2))) using 1 <;> first | rfl | norm_num [b]
  have hc : HasDerivAt c 0 0 := by
    convert (hb.sqrt (by simp [b])).inv (by simp [b]) using 1 <;> first | rfl | norm_num [c, b]
  have hline : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x using 1 <;> first | rfl | norm_num
  have hγ : HasDerivAt γ v 0 := by
    convert hc.smul hline using 1 <;> first | rfl | norm_num [γ, c, b]
  have hγ0 : γ 0 = x := by simp [γ, c, b]
  have hfun : F ∘ γ = (fun _t : ℝ => (0 : Ambient q)) := by
    funext t
    exact hzero (γ t) (hγsphere t)
  have hDF : HasFDerivAt F (fderiv ℝ F x) (γ 0) := by rw [hγ0]; exact hF.hasFDerivAt
  have H := hDF.comp_hasDerivAt 0 hγ
  have Hz : HasDerivAt (F ∘ γ) (0 : Ambient q) 0 := by rw [hfun]; exact hasDerivAt_const _ _
  exact H.unique Hz

end StationaryHarmonicMaps

end
