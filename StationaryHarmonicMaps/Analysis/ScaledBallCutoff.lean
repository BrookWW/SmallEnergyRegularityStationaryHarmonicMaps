module

public import HarmonicMaps.Sobolev
public import StationaryHarmonicMaps.Analysis.EffectiveBallCutoff
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform smooth ball cutoffs from one actual fixed profile

The literal smooth transition of the squared norm with radii one and three
halves is pulled back by a positive affine dilation. Its explicit derivative
bound scales by inverse radius, including in source dimension zero.
-/

public section

open HarmonicMaps Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The literal cutoff gives one fixed numerical constant at every center and positive radius. -/
theorem exists_scaled_ball_cutoff_explicit (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ C = (2 : ℝ)^22 ∧ ∀ (a : Domain n) (r : ℝ), 0 < r →
      ∃ κ : Domain n → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
        tsupport κ ⊆ Metric.ball a (2*r) ∧
        (∀ x ∈ Metric.closedBall a r, κ x=1) ∧
        (∀ x, 0 ≤ κ x ∧ κ x ≤ 1) ∧
        (∀ x, ‖fderiv ℝ κ x‖ ≤ C/r) := by
  let χ : Domain n → ℝ := effectiveRadialCutoff 1 (3/2)
  have hχ : ContDiff ℝ ∞ χ := effectiveRadialCutoff_contDiff _ _
  let C : ℝ := (2 : ℝ)^22
  have hC : 0 < C := by norm_num [C]
  have hMC (x : Domain n) : ‖fderiv ℝ χ x‖ ≤ C := by
    calc
      _ ≤ 2*(3/2 : ℝ)*(2 : ℝ)^20/((3/2 : ℝ)^2-1^2) :=
        effectiveRadialCutoff_fderiv_bound (by norm_num) (by norm_num) x
      _ ≤ C := by norm_num [C]
  refine ⟨C,hC,rfl,?_⟩
  intro a r hr
  let F : Domain n → Domain n := fun x => r⁻¹ • (x-a)
  let κ : Domain n → ℝ := fun x => χ (F x)
  have hF : ContDiff ℝ ∞ F := (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have hκ : ContDiff ℝ ∞ κ := hχ.comp hF
  have hNorm (x : Domain n) : ‖F x‖=‖x-a‖/r := by
    simp only [F,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr,div_eq_mul_inv,mul_comm]
  have hSupport : Function.support κ ⊆ Metric.closedBall a ((3/2 : ℝ)*r) := by
    intro x hx
    have hx' : χ (F x) ≠ 0 := hx
    have hxNorm : ‖F x‖ < (3/2 : ℝ) := by
      apply lt_of_not_ge
      intro h
      exact hx' (effectiveRadialCutoff_eq_zero (by norm_num) (by norm_num) h)
    have H : ‖x-a‖/r < (3/2 : ℝ) := by
      simpa only [hNorm] using hxNorm
    exact show dist x a ≤ (3/2 : ℝ)*r by
      rw [dist_eq_norm]
      exact ((div_lt_iff₀ hr).mp H).le
  have hts : tsupport κ ⊆ Metric.closedBall a ((3/2 : ℝ)*r) :=
    closure_minimal hSupport Metric.isClosed_closedBall
  have hcκ : HasCompactSupport κ :=
    (isCompact_closedBall a ((3/2 : ℝ)*r)).of_isClosed_subset (isClosed_tsupport _) hts
  refine ⟨κ,hκ,hcκ,hts.trans (Metric.closedBall_subset_ball (by linarith)),?_,?_,?_⟩
  · intro x hx
    apply effectiveRadialCutoff_eq_one (by norm_num) (by norm_num)
    rw [hNorm,div_le_iff₀ hr,one_mul]
    exact show ‖x-a‖ ≤ r from hx
  · intro x
    exact effectiveRadialCutoff_mem_Icc 1 (3/2) (F x)
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

/-- The explicit numerical cutoff bound without an existential constant. -/
theorem scaled_ball_cutoff_explicit (n : ℕ) :
    ∀ (a : Domain n) (r : ℝ), 0 < r →
      ∃ κ : Domain n → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
        tsupport κ ⊆ Metric.ball a (2*r) ∧
        (∀ x ∈ Metric.closedBall a r, κ x=1) ∧
        (∀ x, 0 ≤ κ x ∧ κ x ≤ 1) ∧
        (∀ x, ‖fderiv ℝ κ x‖ ≤ (2 : ℝ)^22/r) := by
  obtain ⟨C,_hC,hEq,H⟩ := exists_scaled_ball_cutoff_explicit n
  exact hEq ▸ H

/-- One dimension-dependent constant supplies the actual cutoffs at every center and positive radius. -/
theorem exists_scaled_ball_cutoff (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Domain n) (r : ℝ), 0 < r →
      ∃ κ : Domain n → ℝ, ContDiff ℝ ∞ κ ∧ HasCompactSupport κ ∧
        tsupport κ ⊆ Metric.ball a (2*r) ∧
        (∀ x ∈ Metric.closedBall a r, κ x=1) ∧
        (∀ x, 0 ≤ κ x ∧ κ x ≤ 1) ∧
        (∀ x, ‖fderiv ℝ κ x‖ ≤ C/r) := by
  obtain ⟨C,hC,_hEq,H⟩ := exists_scaled_ball_cutoff_explicit n
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end
