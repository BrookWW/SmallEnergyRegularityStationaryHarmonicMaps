module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform smooth ball cutoffs from one actual fixed profile

The fixed bump with radii one and three halves is pulled back by the true
positive affine dilation. A global bound for its actual compact derivative
scales by r inverse. The construction works in source dimension zero and
does not require the identity operator to have norm one.
-/

public section

open HarmonicMaps Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- One dimension-dependent constant supplies the actual cutoffs at every center and positive radius. -/
theorem exists_scaled_ball_cutoff (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Domain n) (r : ℝ), 0 < r →
      ∃ κ : Domain n → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
        tsupport κ ⊆ Metric.ball a (2*r) ∧
        (∀ x ∈ Metric.closedBall a r, κ x=1) ∧
        (∀ x, 0 ≤ κ x ∧ κ x ≤ 1) ∧
        (∀ x, ‖fderiv ℝ κ x‖ ≤ C/r) := by
  let χ : ContDiffBump (0 : Domain n) := ⟨1,3/2,by norm_num,by norm_num⟩
  have hχ : ContDiff ℝ ∞ (χ : Domain n → ℝ) := χ.contDiff
  obtain ⟨M,hM⟩ := (χ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hχ.continuous_fderiv (by simp))
  let C : ℝ := 1+|M|
  have hC : 0 < C := by dsimp only [C]; positivity
  have hMC (x : Domain n) : ‖fderiv ℝ (χ : Domain n → ℝ) x‖ ≤ C :=
    (hM x).trans (by dsimp only [C]; linarith only [le_abs_self M])
  refine ⟨C,hC,?_⟩
  intro a r hr
  let F : Domain n → Domain n := fun x => r⁻¹ • (x-a)
  let κ : Domain n → ℝ := fun x => χ (F x)
  have hF : ContDiff ℝ ∞ F := (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have hκ : ContDiff ℝ ∞ κ := hχ.comp hF
  have hNorm (x : Domain n) : ‖F x‖=‖x-a‖/r := by
    simp only [F,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr,div_eq_mul_inv,mul_comm]
  have hSupport : Function.support κ ⊆ Metric.closedBall a ((3/2 : ℝ)*r) := by
    intro x hx
    have hx' : F x ∈ Function.support (χ : Domain n → ℝ) := hx
    rw [χ.support_eq] at hx'
    have H : ‖x-a‖/r < (3/2 : ℝ) := by
      simpa only [χ,Metric.mem_ball,dist_zero_right,hNorm] using hx'
    exact show dist x a ≤ (3/2 : ℝ)*r by
      rw [dist_eq_norm]
      exact ((div_lt_iff₀ hr).mp H).le
  have hts : tsupport κ ⊆ Metric.closedBall a ((3/2 : ℝ)*r) :=
    closure_minimal hSupport Metric.isClosed_closedBall
  have hcκ : HasCompactSupport κ :=
    (isCompact_closedBall a ((3/2 : ℝ)*r)).of_isClosed_subset (isClosed_tsupport _) hts
  refine ⟨κ,hκ,hcκ,hts.trans (Metric.closedBall_subset_ball (by linarith)),?_,?_,?_⟩
  · intro x hx
    apply χ.one_of_mem_closedBall
    change dist (F x) 0 ≤ (1 : ℝ)
    rw [dist_zero_right,hNorm,div_le_iff₀ hr,one_mul]
    exact show ‖x-a‖ ≤ r from hx
  · intro x
    exact ⟨χ.nonneg,χ.le_one⟩
  · intro x
    have hFD : HasFDerivAt F (r⁻¹ • ContinuousLinearMap.id ℝ (Domain n)) x :=
      ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const a).const_smul r⁻¹
    have hKD := (hχ.differentiable (by simp) (F x)).hasFDerivAt.comp x hFD
    change HasFDerivAt κ ((fderiv ℝ (χ : Domain n → ℝ) (F x)).comp
      (r⁻¹ • ContinuousLinearMap.id ℝ (Domain n))) x at hKD
    rw [hKD.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hC.le hr.le)
    intro v
    change ‖fderiv ℝ (χ : Domain n → ℝ) (F x) (r⁻¹ • v)‖ ≤ (C/r)*‖v‖
    calc
      _ ≤ ‖fderiv ℝ (χ : Domain n → ℝ) (F x)‖ * ‖r⁻¹ • v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖r⁻¹ • v‖ := mul_le_mul_of_nonneg_right (hMC _) (norm_nonneg _)
      _ = _ := by rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]; ring

end StationaryHarmonicMaps.Analysis

end
