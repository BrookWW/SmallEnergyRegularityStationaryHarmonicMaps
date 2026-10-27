module

public import HolderToCK.Analysis.Poisson.ForcingCutoff

/-! # Uniform compact localization of Holder forcing

One constant for the fixed cutoff is chosen before the forcing and its bounds.
The localized function agrees with the original forcing on the inner ball.
-/

public section

open HarmonicMaps Set

namespace HolderToCK

theorem schauderForcing_localization_bounds (n : ℕ) (γ : ℝ)
    (hγ : 0 < γ) (hγOne : γ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (f : Domain n → Ambient q) (L H : ℝ),
      0 ≤ L → 0 ≤ H →
      (∀ x ∈ Metric.ball (0 : Domain n) 1, ‖f x‖ ≤ L) →
      HolderBoundOn (Metric.ball (0 : Domain n) 1) f γ H →
      HasCompactSupport (schauderForcing f) ∧
      tsupport (schauderForcing f) ⊆ Metric.closedBall (0 : Domain n) (3 / 4) ∧
      (∀ x, ‖schauderForcing f x‖ ≤ L) ∧
      HolderBoundOn univ (schauderForcing f) γ (C * (L + H)) ∧
      EqOn (schauderForcing f) f (Metric.closedBall (0 : Domain n) (5 / 8)) := by
  obtain ⟨B, hB⟩ := schauderCutoff_lipschitz n
  let C : ℝ := (B : ℝ) + 9
  have hC : 0 ≤ C := by positivity
  refine ⟨C, hC, ?_⟩
  intro q f L H hL hH hnorm hHolder
  have hG : H + ((B : ℝ) + 8) * L ≤ C * (L + H) := by
    have hBH : 0 ≤ (B : ℝ) * H := mul_nonneg B.property hH
    dsimp only [C]
    nlinarith only [hBH, hL, hH]
  have hglobal := schauderForcing_holderBound hγ hγOne hH hL hnorm hHolder hB
  refine ⟨schauderForcing_hasCompactSupport f, schauderForcing_tsupport_subset f,
    schauderForcing_norm_bound hL hnorm, ?_, fun x hx => schauderForcing_eq f hx⟩
  intro x hx y hy
  exact (hglobal x hx y hy).trans
    (mul_le_mul_of_nonneg_right hG (Real.rpow_nonneg dist_nonneg _))

end HolderToCK
end
