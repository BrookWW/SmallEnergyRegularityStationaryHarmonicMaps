module

public import HarmonicMaps.Analysis.CenteredEnergyGrowth
public import HarmonicMaps.Analysis.MorreyRepresentative

/-!
# The unit-ball regularity representative

The proved centered growth supplies Morrey's hypothesis with the original
weak gradient. A single threshold, exponent and constant precede every map.
The representative is pointwise target valued and unique among all
continuous representatives on the open half-unit ball.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace HarmonicMaps

/-- Small unit-ball energy gives the full target-valued Hölder representative,
including uniqueness among all continuous almost-everywhere representatives. -/
theorem unitBallRegularity_complete (n : ℕ) (hn : 2 ≤ n)
    (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    ∃ epsilon alpha : ℝ, ∃ C : ℝ≥0, 0 < epsilon ∧ 0 < alpha ∧ alpha < 1 ∧
    ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
      TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
      IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du →
      dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal epsilon →
      ∃ w : Metric.ball (0 : Domain n) (1 / 2) → Ambient q,
        IsContinuousRepresentative (ballDomain (0 : Domain n) (1 / 2)) u w ∧
        (∀ x, w x ∈ N.carrierSet) ∧
        (∀ x y : Metric.ball (0 : Domain n) (1 / 2),
          ‖w x - w y‖ ≤ (C : ℝ) *
            Real.sqrt (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal *
            Real.rpow (dist (x : Domain n) (y : Domain n)) alpha) ∧
        ∀ v : Metric.ball (0 : Domain n) (1 / 2) → Ambient q,
          IsContinuousRepresentative (ballDomain (0 : Domain n) (1 / 2)) u v → v = w := by
  obtain ⟨epsilonDec, tau, _hDec, _hTau, hEpsilon, hAlpha, hAlphaOne, hGrowth⟩ :=
    centeredEnergyGrowth_complete n hn q N
  let epsilon : ℝ := (2 : ℝ) ^ (2 - (n : ℤ)) * epsilonDec
  let alpha : ℝ := Real.log 2 / (2 * Real.log (1 / tau.val))
  let K : ℝ := (2 : ℝ) ^ ((n : ℝ) - 1 + 2 * alpha)
  have hK : 0 ≤ K := Real.rpow_nonneg (by norm_num) _
  obtain ⟨CM, hMorrey⟩ := morrey_representative n hn alpha hAlpha hAlphaOne
  let C : ℝ≥0 := CM * ⟨Real.sqrt K, Real.sqrt_nonneg _⟩
  refine ⟨epsilon, alpha, C, hEpsilon, hAlpha, hAlphaOne, ?_⟩
  intro u Du hu hN hmin hsmall
  have hEfinite : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  have hfinite := hu.memW12_unitBall_of_finiteEnergy N hN hEfinite
  let E : ℝ := (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal
  have hM : 0 ≤ K * E := mul_nonneg hK ENNReal.toReal_nonneg
  have hActualGrowth : ∀ (x : Domain n), x ∈ Metric.ball (0 : Domain n) (1 / 2) →
      ∀ (r : PositiveRadius), r.val ≤ (1 / 2 : ℝ) →
        (∫ y in Metric.ball x r.val, hsNormSq (Du y)) ≤
          (K * E) * Real.rpow r.val ((n : ℝ) - 2 + 2 * alpha) := by
    intro x hx r hr
    exact (hGrowth u Du hu hN hmin hsmall x hx).2 r hr
  obtain ⟨w, hw, _hMeans, hHolder, hUnique, hTarget⟩ :=
    hMorrey q u Du hfinite (K * E) hM hActualGrowth
  refine ⟨w, hw, hTarget N.carrierSet N.isCompact.isClosed hN, ?_, hUnique⟩
  intro x y
  have hCoefficient : (CM : ℝ) * Real.sqrt (K * E) = (C : ℝ) * Real.sqrt E := by
    rw [Real.sqrt_mul hK]
    change (CM : ℝ) * (Real.sqrt K * Real.sqrt E) =
      ((CM : ℝ) * Real.sqrt K) * Real.sqrt E
    exact (mul_assoc _ _ _).symm
  simpa only [hCoefficient] using hHolder x y

end HarmonicMaps
end
