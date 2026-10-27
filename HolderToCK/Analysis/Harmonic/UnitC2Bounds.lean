module

public import HolderToCK.Analysis.Harmonic.HigherHolderEstimates

/-! # Joint harmonic C2 bounds at fixed interior radii -/

public section

open HarmonicMaps Set
open scoped ContDiff

namespace HolderToCK

theorem harmonic_unit_c2_bounds (n : ℕ) (hn : 2 ≤ n) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγOne : γ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (f : Domain n → Ambient q) (M : ℝ),
      0 ≤ M → ContDiffOn ℝ ∞ f (Metric.ball (0 : Domain n) (5 / 8)) →
      (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), Laplacian.laplacian f x = 0) →
      (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ‖f x‖ ≤ M) →
      (∀ k : ℕ, k ≤ 2 → ∀ x ∈ Metric.ball (0 : Domain n) (1 / 2),
        ‖iteratedFDeriv ℝ k f x‖ ≤ C * M) ∧
      HolderBoundOn (Metric.ball (0 : Domain n) (1 / 2))
        (iteratedFDeriv ℝ 2 f) γ (C * M) := by
  obtain ⟨C₀, hC₀, h₀⟩ := harmonic_iteratedFDeriv_inner_sup_bound n 0 hn
  obtain ⟨C₁, hC₁, h₁⟩ := harmonic_iteratedFDeriv_inner_sup_bound n 1 hn
  obtain ⟨C₂, hC₂, h₂⟩ := harmonic_iteratedFDeriv_inner_sup_bound n 2 hn
  obtain ⟨C₃, hC₃, h₃⟩ := harmonic_iteratedFDeriv_inner_holderBound n 2 hn
  let C : ℝ := C₀ + 8 * C₁ + 64 * C₂ + 512 * C₃
  have hC : 0 ≤ C := by positivity
  have h0C : C₀ ≤ C := by dsimp only [C]; linarith only [hC₁, hC₂, hC₃]
  have h1C : C₁ * 8 ≤ C := by dsimp only [C]; linarith only [hC₀, hC₂, hC₃]
  have h2C : C₂ * 64 ≤ C := by dsimp only [C]; linarith only [hC₀, hC₁, hC₃]
  have h3C : C₃ * 512 ≤ C := by dsimp only [C]; linarith only [hC₀, hC₁, hC₂]
  refine ⟨C, hC, ?_⟩
  intro q f M hM hf hh hnorm
  let R : PositiveRadius := ⟨5 / 8, by norm_num⟩
  refine ⟨?_, ?_⟩
  · intro k hk x hx
    interval_cases k
    · have h := h₀ q 0 R (1 / 2) f M (by norm_num [R]) hf hh hnorm x hx
      norm_num [R] at h
      rw [norm_iteratedFDeriv_zero]
      exact h.trans (mul_le_mul_of_nonneg_right h0C hM)
    · have h := h₁ q 0 R (1 / 2) f M (by norm_num [R]) hf hh hnorm x hx
      norm_num [R] at h
      rw [norm_iteratedFDeriv_one]
      exact h.trans (mul_le_mul_of_nonneg_right h1C hM)
    · have h := h₂ q 0 R (1 / 2) f M (by norm_num [R]) hf hh hnorm x hx
      norm_num [R] at h
      exact h.trans (mul_le_mul_of_nonneg_right h2C hM)
  · have h := h₃ q 0 R (1 / 2) γ M f (by norm_num) (by norm_num [R])
      hγ hγOne hM hf hh hnorm
    norm_num [R] at h
    intro x hx y hy
    exact (h x hx y hy).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3C hM)
        (Real.rpow_nonneg dist_nonneg _))

end HolderToCK
end
