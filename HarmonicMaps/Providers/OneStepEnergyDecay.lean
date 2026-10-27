module

public import HarmonicMaps
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import HarmonicMaps.Analysis.DecayThreshold

/-! # OneStepEnergyDecay proof implementation

The exact original declaration follows from the complete source threshold.
Finite energy permits the real comparison to be transported to the extended
nonnegative normalized energy without changing the original gradient.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps.Providers.OneStepEnergyDecay

theorem result
    {n q : ℕ} (hn : 2 ≤ n) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ε : ℝ, ∃ τ : PositiveRadius,
      0 < ε ∧ τ.val < (1 / 8 : ℝ) ∧
      ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
        MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
        TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
        IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du →
        dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal ε →
        normalizedEnergy Du (0 : Domain n) τ ≤
          (1 / 2 : ℝ≥0∞) * dirichletEnergy Du (Metric.ball (0 : Domain n) 1) := by
  obtain ⟨C₂, ε, _, hε, _, hThreshold⟩ := decay_threshold_complete n hn q N
  obtain ⟨htau, htauSmall, _, _, _, hMaps⟩ := hThreshold ε hε le_rfl
  let tau : PositiveRadius := ⟨ε ^ (1 / (64 * ((n : ℝ) - 1))), htau⟩
  refine ⟨ε, tau, hε, htauSmall, ?_⟩
  intro u Du hu hN hmin hsmall
  have hreal := (hMaps u Du hu hN hmin hsmall).2
  have hfinite : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  have hBall : Metric.ball (0 : Domain n) tau.val ⊆ Metric.ball 0 1 :=
    Metric.ball_subset_ball (htauSmall.le.trans (by norm_num))
  have hEnergyMono : dirichletEnergy Du (Metric.ball (0 : Domain n) tau.val) ≤
      dirichletEnergy Du (Metric.ball (0 : Domain n) 1) := lintegral_mono_set hBall
  have hLocalFinite := ne_top_of_le_ne_top hfinite hEnergyMono
  have hNormFinite := normalizedEnergy_ne_top_of_dirichletEnergy_ne_top
    (a := (0 : Domain n)) (r := tau) hLocalFinite
  have hRHSFinite : (1 / 2 : ℝ≥0∞) * dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hfinite
  apply (ENNReal.toReal_le_toReal hNormFinite hRHSFinite).mp
  rw [normalizedEnergy, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (zpow_pos tau.property _).le, ENNReal.toReal_mul]
  have hHalf : (1 / 2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by norm_num
  rw [hHalf]
  exact hreal

end HarmonicMaps.Providers.OneStepEnergyDecay
end
