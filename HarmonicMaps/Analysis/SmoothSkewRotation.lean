module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth orthogonal flows from real skew-adjoint operators

The operator exponential gives the actual orthogonal flow and its source
velocity. Its joint smoothness allows differentiation of rotated boundary data.
-/

public section

open scoped ContDiff

namespace HarmonicMaps

/-- Every real skew-adjoint operator has the literal exponential orthogonal
flow, jointly smooth in time and point, with the actual initial velocity. -/
theorem smoothSkewRotation_exists {n : ℕ}
    (A : Domain n →L[ℝ] Domain n) (hA : star A = -A) :
    ∃ T : ℝ → Domain n ≃ₗᵢ[ℝ] Domain n,
      (∀ t x, T t x = NormedSpace.exp (t • A) x) ∧
      T 0 = LinearIsometryEquiv.refl ℝ (Domain n) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Domain n => T p.1 p.2) ∧
      ∀ x : Domain n, HasDerivAt (fun t : ℝ => T t x) (A x) 0 := by
  have hunitary (t : ℝ) : NormedSpace.exp (t • A) ∈ unitary (Domain n →L[ℝ] Domain n) := by
    letI : NormedAlgebra ℚ (Domain n →L[ℝ] Domain n) :=
      NormedAlgebra.restrictScalars ℚ ℝ _
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    rw [skewAdjoint.mem_iff, star_smul, hA]
    simp only [star_trivial, smul_neg]
  let T : ℝ → Domain n ≃ₗᵢ[ℝ] Domain n := fun t =>
    Unitary.linearIsometryEquiv ⟨NormedSpace.exp (t • A), hunitary t⟩
  have hformula (t : ℝ) (x : Domain n) : T t x = NormedSpace.exp (t • A) x := rfl
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp :
      (Domain n →L[ℝ] Domain n) → (Domain n →L[ℝ] Domain n)) :=
    AnalyticOnNhd.contDiff (fun _ _ => NormedSpace.exp_analytic (𝕂 := ℝ) _)
  refine ⟨T, hformula, ?_, ?_, ?_⟩
  · apply LinearIsometryEquiv.ext
    intro x
    rw [hformula]
    change NormedSpace.exp (0 • A) x = x
    simp only [zero_smul ℝ A, NormedSpace.exp_zero, one_apply_eq_self]
  · have htime : ContDiff ℝ ∞ (fun p : ℝ × Domain n => p.1 • A) :=
      contDiff_fst.smul contDiff_const
    exact (hexp.comp htime).clm_apply contDiff_snd
  · intro x
    have hderiv := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0).clm_apply
      (hasDerivAt_const (0 : ℝ) x)
    have hd0 : NormedSpace.exp ((0 : ℝ) • A) * A = A := by
      rw [zero_smul ℝ A, NormedSpace.exp_zero, one_mul]
    simpa only [hformula, hd0, map_zero, add_zero] using hderiv

end HarmonicMaps
end
