module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.Sequences

/-!
# Compactness from actual uniform approximating families

Finite covers of a uniformly close precompact family give finite covers
of the original family. Completeness then produces a strictly increasing
convergent subsequence. The approximations must be supplied with their
actual uniform metric error and their proved total boundedness.
-/

public section

open Set Metric Filter
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Uniform approximation by genuinely precompact families preserves total boundedness. -/
theorem totallyBounded_range_of_uniform_approximation {I X : Type*}
    [PseudoMetricSpace X] (f : I → X)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : I → X,
      TotallyBounded (range g) ∧ ∀ i, dist (f i) (g i) < ε) :
    TotallyBounded (range f) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := happrox (ε / 2) (half_pos hε)
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hg (ε / 2) (half_pos hε)
  refine ⟨t, ht, ?_⟩
  rintro x ⟨i, rfl⟩
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (hcover (mem_range_self i))
  apply mem_iUnion₂.mpr
  refine ⟨y, hyt, ?_⟩
  change dist (f i) y < ε
  calc
    _ ≤ dist (f i) (g i) + dist (g i) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hfg i) hy
    _ = ε := add_halves ε

/-- Actual uniform approximations and completeness produce an increasing convergent subsequence. -/
theorem exists_subsequence_limit_of_uniform_approximation {X : Type*}
    [PseudoMetricSpace X] [CompleteSpace X] (f : ℕ → X)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : ℕ → X,
      TotallyBounded (range g) ∧ ∀ i, dist (f i) (g i) < ε) :
    ∃ x : X, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (f ∘ φ) atTop (𝓝 x) := by
  have hTB := totallyBounded_range_of_uniform_approximation f happrox
  have hcompact : IsCompact (closure (range f)) :=
    hTB.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨x, _hx, φ, hφ, hlim⟩ :=
    hcompact.tendsto_subseq (fun k => subset_closure (mem_range_self k))
  exact ⟨x, φ, hφ, hlim⟩

end StationaryHarmonicMaps.Analysis

end
