module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Actual weakly convergent subsequences in a real separable Hilbert space

The Riesz isometry sends the bounded sequence into the weak dual's closed
ball. Sequential Banach-Alaoglu supplies an actual increasing subsequence,
and the inverse Riesz isometry recovers its Hilbert-space limit and norm
bound. Weak convergence is stated as convergence of every true inner product.
-/

public section

open Set Metric Filter
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Every actually bounded sequence in a real separable Hilbert space has a weak subsequence. -/
theorem exists_weak_hilbert_subsequence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) {M : ℝ} (hbound : ∀ k, ‖u k‖ ≤ M) :
    ∃ v : H, ‖v‖ ≤ M ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ w : H, Tendsto (fun k => inner ℝ (u (σ k)) w) atTop (𝓝 (inner ℝ v w)) := by
  let R := InnerProductSpace.toDual ℝ H
  let f : ℕ → WeakDual ℝ H := fun k => StrongDual.toWeakDual (R (u k))
  have hf (k : ℕ) : f k ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) M := by
    change dist (R (u k)) 0 ≤ M
    rw [dist_zero_right, R.norm_map]
    exact hbound k
  obtain ⟨l, hl, σ, hσ, hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ H 0 M) hf
  let v : H := R.symm (WeakDual.toStrongDual l)
  have hv : ‖v‖ ≤ M := by
    change dist (WeakDual.toStrongDual l) 0 ≤ M at hl
    rw [dist_zero_right] at hl
    exact (R.symm.norm_map _).trans_le hl
  refine ⟨v, hv, σ, hσ, ?_⟩
  intro w
  have heval := ((WeakDual.eval_continuous w).tendsto l).comp hlim
  have hvw : inner ℝ v w = l w := InnerProductSpace.toDual_symm_apply
  simpa only [Function.comp_def, f, R, StrongDual.toWeakDual_apply,
    InnerProductSpace.toDual_apply_apply, ← hvw] using heval

end StationaryHarmonicMaps.Analysis

end
