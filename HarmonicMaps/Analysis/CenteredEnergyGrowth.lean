module

public import HarmonicMaps.Analysis.EnergyIteration
public import HarmonicMaps.Analysis.FiniteEnergySobolev

/-!
# Uniform centered energy growth

The source threshold `epsilon_reg = 2^(2-n) * epsilon_dec` puts every
half-radius ball about an inner point below the same decay threshold.
All-radius iteration gives the exact HS growth coefficient
`2^(n-1+2*alpha)` for the original weak gradient.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps

private theorem growth_coefficient (n : ℕ) (hn : 2 ≤ n) (alpha E r : ℝ)
    (hr : 0 < r) :
    (2 * (r / (1 / 2)) ^ (2 * alpha) * ((2 : ℝ) ^ (n - 2) * E)) * r ^ (n - 2) =
      (2 : ℝ) ^ ((n : ℝ) - 1 + 2 * alpha) * E * r ^ ((n : ℝ) - 2 + 2 * alpha) := by
  have hnCast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hRadius : r ^ ((n : ℝ) - 2 + 2 * alpha) = r ^ (n - 2) * r ^ (2 * alpha) := by
    rw [← hnCast, Real.rpow_add hr, Real.rpow_natCast]
  have hTwo : (2 : ℝ) ^ ((n : ℝ) - 1 + 2 * alpha) =
      (2 : ℝ) ^ (n - 2) * 2 * (2 : ℝ) ^ (2 * alpha) := by
    rw [show (n : ℝ) - 1 + 2 * alpha = ((n - 2 : ℕ) : ℝ) + 1 + 2 * alpha by
      rw [hnCast]; ring]
    rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
      Real.rpow_natCast, Real.rpow_one]
  rw [show r / (1 / 2) = r * 2 by ring, Real.mul_rpow hr.le (by norm_num), hRadius, hTwo]
  ring

/-- The same source decay witnesses produce the reduced regularity threshold
and the complete centered HS growth estimate from original unit-ball data. -/
theorem centeredEnergyGrowth_complete (n : ℕ) (hn : 2 ≤ n)
    (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    ∃ epsilonDec : ℝ, ∃ tau : PositiveRadius, 0 < epsilonDec ∧ tau.val < 1 / 8 ∧
    let epsilonReg := (2 : ℝ) ^ (2 - (n : ℤ)) * epsilonDec
    let alpha := Real.log 2 / (2 * Real.log (1 / tau.val))
    0 < epsilonReg ∧ 0 < alpha ∧ alpha < 1 ∧
    ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
      TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
      IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du →
      dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal epsilonReg →
    ∀ (x : Domain n), x ∈ Metric.ball (0 : Domain n) (1 / 2) →
      normalizedEnergy Du x ⟨1 / 2, by norm_num⟩ ≤ ENNReal.ofReal epsilonDec ∧
      ∀ r : PositiveRadius, r.val ≤ (1 / 2 : ℝ) →
        (∫ y in Metric.ball x r.val, hsNormSq (Du y)) ≤
          (2 : ℝ) ^ ((n : ℝ) - 1 + 2 * alpha) *
            (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal *
            r.val ^ ((n : ℝ) - 2 + 2 * alpha) := by
  obtain ⟨epsilonDec, tau, hEpsilon, hTau, hAlpha, hAlphaOne, _hPower, hIteration⟩ :=
    energyIteration_complete n hn q N
  refine ⟨epsilonDec, tau, hEpsilon, hTau,
    mul_pos (zpow_pos (by norm_num) _) hEpsilon, hAlpha, hAlphaOne, ?_⟩
  intro u Du hu hN hmin hsmall x hx
  have hhalf : Metric.closedBall x (1 / 2) ⊆ (ballDomain (0 : Domain n) 1).val := by
    apply Metric.closedBall_subset_ball'
    have hx0 : dist x (0 : Domain n) < 1 / 2 := hx
    linarith only [hx0]
  have hSub : Metric.ball x (1 / 2) ⊆ Metric.ball (0 : Domain n) 1 :=
    Metric.ball_subset_closedBall.trans hhalf
  have hEnergyOrder : dirichletEnergy Du (Metric.ball x (1 / 2)) ≤
      dirichletEnergy Du (Metric.ball (0 : Domain n) 1) :=
    lintegral_mono' (Measure.restrict_mono_set volume hSub) le_rfl
  have hCancel : (1 / 2 : ℝ) ^ (2 - (n : ℤ)) * (2 : ℝ) ^ (2 - (n : ℤ)) = 1 := by
    rw [← mul_zpow]
    norm_num
  have hCenter : normalizedEnergy Du x ⟨1 / 2, by norm_num⟩ ≤ ENNReal.ofReal epsilonDec := by
    calc
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (2 - (n : ℤ))) *
          ENNReal.ofReal ((2 : ℝ) ^ (2 - (n : ℤ)) * epsilonDec) :=
        mul_le_mul_right (hEnergyOrder.trans hsmall) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (zpow_pos (by norm_num) _).le, ← mul_assoc, hCancel, one_mul]
  refine ⟨hCenter, ?_⟩
  intro r hrhalf
  have hclosed : Metric.closedBall x r.val ⊆ (ballDomain (0 : Domain n) 1).val :=
    (Metric.closedBall_subset_closedBall hrhalf).trans hhalf
  have hi := hu.integrable_hsNormSq_ball hclosed
  have hiHalf := hu.integrable_hsNormSq_ball hhalf
  have hEfinite : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  have hAll := (hIteration _ u Du hu hN hmin x ⟨1 / 2, by norm_num⟩ hhalf hCenter).2 r hrhalf
  have hCoefficientNonneg : 0 ≤
      2 * (r.val / (1 / 2)) ^ (2 * (Real.log 2 / (2 * Real.log (1 / tau.val)))) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (div_pos r.property (by norm_num)).le _)
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (normalizedEnergy_ne_top_of_dirichletEnergy_ne_top (hu.dirichletEnergy_ne_top_ball hhalf))) hAll
  rw [normalizedEnergy_toReal hi, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hCoefficientNonneg, normalizedEnergy_toReal hiHalf] at hreal
  have hexp : 2 - (n : ℤ) = -((n - 2 : ℕ) : ℤ) := by omega
  simp only [hexp, zpow_neg, zpow_natCast] at hreal
  have hHalfInv : ((1 / 2 : ℝ) ^ (n - 2))⁻¹ = (2 : ℝ) ^ (n - 2) := by
    rw [← inv_pow]
    norm_num
  rw [hHalfInv] at hreal
  have hHalfReal : (∫ y in Metric.ball x (1 / 2), hsNormSq (Du y)) ≤
      (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
    rw [← dirichletEnergy_toReal hiHalf]
    exact ENNReal.toReal_mono hEfinite hEnergyOrder
  have hbound : (∫ y in Metric.ball x r.val, hsNormSq (Du y)) / r.val ^ (n - 2) ≤
      2 * (r.val / (1 / 2)) ^ (2 * (Real.log 2 / (2 * Real.log (1 / tau.val)))) *
        ((2 : ℝ) ^ (n - 2) * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal) := by
    calc
      _ = (r.val ^ (n - 2))⁻¹ * ∫ y in Metric.ball x r.val, hsNormSq (Du y) :=
        div_eq_inv_mul _ _
      _ ≤ _ := hreal.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hHalfReal (by positivity)) hCoefficientNonneg)
  exact ((div_le_iff₀ (pow_pos r.property _)).mp hbound).trans_eq
    (growth_coefficient n hn _ _ r.val r.property)

end HarmonicMaps
end
