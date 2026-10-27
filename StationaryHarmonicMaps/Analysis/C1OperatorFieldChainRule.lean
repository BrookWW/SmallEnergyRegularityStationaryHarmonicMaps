module

public import StationaryHarmonicMaps.Analysis.C1SobolevPostcompositionLocal
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# C¹ operator fields along Sobolev maps

Applying an ambient operator field to a fixed vector gives the actual weak
chain-rule columns. This avoids identifying the operator norm with a
Hilbert--Schmidt coefficient norm.
-/

public section

open HarmonicMaps MeasureTheory
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Applying a C¹ operator field to a fixed vector has the displayed derivative. -/
theorem fderiv_operatorField_apply_const {q : ℕ}
    {G : Ambient q → Ambient q →L[ℝ] Ambient q} (hG : ContDiff ℝ 1 G)
    (v y : Ambient q) :
    fderiv ℝ (fun z => G z v) y = (fderiv ℝ G y).flip v := by
  simpa using ((hG.differentiable (by simp) y).hasFDerivAt.clm_apply
    (hasFDerivAt_const v y)).fderiv

/-- A uniform operator-derivative bound controls each fixed-vector field. -/
theorem norm_fderiv_operatorField_apply_const_le {q : ℕ}
    {G : Ambient q → Ambient q →L[ℝ] Ambient q} (hG : ContDiff ℝ 1 G)
    {L : ℝ} (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L) (v y : Ambient q) :
    ‖fderiv ℝ (fun z => G z v) y‖ ≤ L * ‖v‖ := by
  have hL : 0 ≤ L := (norm_nonneg (fderiv ℝ G y)).trans (hDG y)
  rw [fderiv_operatorField_apply_const hG]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hL (norm_nonneg _))
  intro z
  change ‖(fderiv ℝ G y z) v‖ ≤ L * ‖v‖ * ‖z‖
  calc
    _ ≤ ‖fderiv ℝ G y z‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (L * ‖z‖) * ‖v‖ := mul_le_mul_of_nonneg_right
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hDG y) (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by ring

/-- The fixed-vector evaluations of the field have genuine local Sobolev chain rules. -/
theorem memW12Loc_operatorField_apply_const {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    {G : Ambient q → Ambient q →L[ℝ] Ambient q} (hG : ContDiff ℝ 1 G)
    {L : ℝ} (hDG : ∀ y, ‖fderiv ℝ G y‖ ≤ L) (v : Ambient q) :
    MemW12Loc Ω (fun x => G (u x) v)
      (fun x i => (fderiv ℝ G (u x) (Du x i)) v) := by
  have hF : ContDiff ℝ 1 (fun y => G y v) := hG.clm_apply contDiff_const
  have H := memW12Loc_postcompose_c1 hu (fun y => G y v) hF (L * ‖v‖)
    (norm_fderiv_operatorField_apply_const_le hG hDG v)
  have heq : (fun x i => fderiv ℝ (fun y => G y v) (u x) (Du x i)) =
      (fun x i => (fderiv ℝ G (u x) (Du x i)) v) := by
    funext x i
    rw [fderiv_operatorField_apply_const hG]
    rfl
  rw [heq] at H
  exact H

end StationaryHarmonicMaps.Analysis

end
