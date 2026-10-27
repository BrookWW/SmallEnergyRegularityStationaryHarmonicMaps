module

public import StationaryHarmonicMaps.Analysis.WeakHilbertSubsequence
public import HolderToCK.Analysis.L2PairingContinuity
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Actual weak L2 limits of Euclidean fields

Separable measure supplies the actual L2 space's separability. The Hilbert
subsequence theorem gives a representative in L2 with the original uniform
energy bound and convergence against every genuine L2 vector field.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem integral_norm_sq_eq_L2_norm_sq {n q : ℕ} {μ : Measure (Domain n)}
    (f : Domain n → Ambient q) (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simpa only [real_inner_self_eq_norm_sq] using HolderToCK.integral_inner_eq_L2_inner hf hf

/-- Uniform actual L2 energy produces a weakly convergent subsequence and an actual L2 limit. -/
theorem exists_weak_L2_subsequence {n q : ℕ} (μ : Measure (Domain n)) [IsSeparable μ]
    (f : ℕ → Domain n → Ambient q) (hf : ∀ k, MemLp (f k) 2 μ)
    {M : ℝ} (hM : 0 ≤ M) (henergy : ∀ k, (∫ x, ‖f k x‖ ^ 2 ∂μ) ≤ M) :
    ∃ (v : Domain n → Ambient q), MemLp v 2 μ ∧
      (∫ x, ‖v x‖ ^ 2 ∂μ) ≤ M ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∀ (g : Domain n → Ambient q), MemLp g 2 μ →
          Tendsto (fun k => ∫ x, inner ℝ (f (σ k) x) (g x) ∂μ) atTop
            (𝓝 (∫ x, inner ℝ (v x) (g x) ∂μ)) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let F (k : ℕ) : Lp (Ambient q) 2 μ := (hf k).toLp (f k)
  have hF (k : ℕ) : ‖F k‖ ≤ Real.sqrt M := by
    have H := Real.sqrt_le_sqrt (henergy k)
    rw [integral_norm_sq_eq_L2_norm_sq, Real.sqrt_sq (norm_nonneg _)] at H
    exact H
  obtain ⟨v, hv, σ, hσ, hweak⟩ := exists_weak_hilbert_subsequence F hF
  have hvLp : MemLp (v : Domain n → Ambient q) 2 μ := Lp.memLp v
  have hvenergy : (∫ x, ‖v x‖ ^ 2 ∂μ) ≤ M := by
    rw [integral_norm_sq_eq_L2_norm_sq _ hvLp, Lp.toLp_coeFn]
    have H := (sq_le_sq₀ (norm_nonneg v) (Real.sqrt_nonneg M)).mpr hv
    simpa only [Real.sq_sqrt hM] using H
  refine ⟨v, hvLp, hvenergy, σ, hσ, ?_⟩
  intro g hg
  have H := hweak (hg.toLp g)
  simp_rw [HolderToCK.integral_inner_eq_L2_inner (hf (σ _)) hg,
    HolderToCK.integral_inner_eq_L2_inner hvLp hg, Lp.toLp_coeFn]
  exact H

end StationaryHarmonicMaps.Analysis

end
