module

public import StationaryHarmonicMaps.Analysis.OrthogonalCoefficientBounds
public import Mathlib.Analysis.CStarAlgebra.Basic

/-! # Actual contraction bounds for orthogonal operator frames -/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps.Analysis

/-- The actual orthogonality constraint preserves every vector norm. -/
theorem norm_apply_orthogonal {q : ℕ} (P : Ambient q →L[ℝ] Ambient q)
    (hP : star P * P = 1) (v : Ambient q) : ‖P v‖ = ‖v‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (norm_sq_apply_orthogonal P hP v)

/-- The operator norm bound includes the zero-dimensional target. -/
theorem orthogonal_opNorm_le_one {q : ℕ} (P : Ambient q →L[ℝ] Ambient q)
    (hP : star P * P = 1) : ‖P‖ ≤ 1 := by
  apply P.opNorm_le_bound zero_le_one
  intro v
  rw [norm_apply_orthogonal P hP, one_mul]

/-- The genuine inverse frame acts contractively on every vector. -/
theorem norm_star_apply_orthogonal_le {q : ℕ} (P : Ambient q →L[ℝ] Ambient q)
    (hP : star P * P = 1) (v : Ambient q) : ‖star P v‖ ≤ ‖v‖ := by
  calc
    _ ≤ ‖star P‖ * ‖v‖ := (star P).le_opNorm _
    _ = ‖P‖ * ‖v‖ := by
      have hn : ‖star P‖ = ‖P‖ :=
        (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Ambient q) (F := Ambient q)).norm_map P
      rw [hn]
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right (orthogonal_opNorm_le_one P hP) (norm_nonneg _)
    _ = _ := one_mul _

end StationaryHarmonicMaps.Analysis

end
