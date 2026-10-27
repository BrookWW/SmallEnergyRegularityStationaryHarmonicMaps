module

public import StationaryHarmonicMaps.Analysis.OrthogonalCoefficientBounds
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Closed target constraints under actual strong L2 convergence

An actual L2 limit has an almost-everywhere convergent subsequence.
Closedness therefore preserves the original constraint almost everywhere.
The orthogonal-frame instance uses the true continuous decoder and adjoint
equation, without assuming orthogonality of the limit.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual strong L2 convergence preserves membership in every closed Euclidean target. -/
theorem ae_mem_closed_of_L2_limit {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (f : ℕ → X → Ambient q) (v : X → Ambient q)
    (hf : ∀ k, MemLp (f k) 2 μ) (hv : MemLp v 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - v) 2 μ) atTop (𝓝 0))
    (S : Set (Ambient q)) (hS : IsClosed S)
    (hmem : ∀ k, ∀ᵐ x ∂μ, f k x ∈ S) : ∀ᵐ x ∂μ, v x ∈ S := by
  have hmeasure : TendstoInMeasure μ f atTop v :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun k => (hf k).aestronglyMeasurable) hv.aestronglyMeasurable hconv
  obtain ⟨σ, _hσ, hseq⟩ := hmeasure.exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ k, f k x ∈ S := ae_all_iff.mpr hmem
  filter_upwards [hseq, hall] with x hx htarget
  exact hS.mem_of_tendsto hx (Eventually.of_forall fun k => htarget (σ k))

/-- Orthogonality of the actual decoded operators passes to their original strong L2 limit. -/
theorem ae_decoded_orthogonal_of_L2_limit {X : Type*} [MeasurableSpace X] {m q : ℕ}
    (μ : Measure X) (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (p : ℕ → X → Ambient m) (v : X → Ambient m)
    (hp : ∀ k, MemLp (p k) 2 μ) (hv : MemLp v 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (p k - v) 2 μ) atTop (𝓝 0))
    (horth : ∀ k, ∀ᵐ x ∂μ, star (R (p k x)) * R (p k x) = 1) :
    ∀ᵐ x ∂μ, star (R (v x)) * R (v x) = 1 := by
  have hadj : Continuous (fun z : Ambient m => star (R z)) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Ambient q) (F := Ambient q)).continuous.comp R.continuous
  have hclosed : IsClosed {z : Ambient m | star (R z) * R z = 1} :=
    isClosed_eq (hadj.mul R.continuous) continuous_const
  exact ae_mem_closed_of_L2_limit μ p v hp hv hconv _ hclosed horth

end StationaryHarmonicMaps.Analysis

end
