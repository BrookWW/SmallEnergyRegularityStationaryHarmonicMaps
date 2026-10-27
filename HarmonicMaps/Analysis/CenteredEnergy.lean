module

public import HarmonicMaps.Analysis.Monotonicity

/-!
# Centered small-ball energy

The half ball about an interior point has closure inside the unit ball.
The accepted monotonicity theorem at that center yields the exact source
factor for every positive smoothing radius at most one quarter.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps

/-- The source centered-energy estimate follows from actual local minimality
and finite unit-ball energy, with the same displayed weak gradient. -/
theorem IsLocallyEnergyMinimizing.centered_energy_bound {n q : ℕ} (hn : 2 ≤ n)
    (N : CompactSmoothEmbeddedTarget q) (u : Domain n → Ambient q)
    (Du : Domain n → Gradient n q)
    (hu : MemW12Loc (ballDomain (0 : Domain n) 1) u Du)
    (hN : TakesValuesIn N (ballDomain (0 : Domain n) 1) u)
    (hmin : IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du)
    (hE : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤)
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2))
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    IntegrableOn (fun z => hsNormSq (Du z)) (Metric.ball x h.val) volume ∧
      (∫ z in Metric.ball x h.val, hsNormSq (Du z)) ≤
        (2 : ℝ) ^ (n - 2) * h.val ^ (n - 2) *
          (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
  have hhalf : Metric.closedBall x (1 / 2) ⊆ (ballDomain (0 : Domain n) 1).val := by
    apply Metric.closedBall_subset_ball'
    have hxd : dist x (0 : Domain n) < 1 / 2 := hx
    linarith only [hxd]
  have hhhalf : h.val < 1 / 2 := lt_of_le_of_lt hh (by norm_num)
  have hsmall : Metric.closedBall x h.val ⊆ (ballDomain (0 : Domain n) 1).val :=
    (Metric.closedBall_subset_closedBall hhhalf.le).trans hhalf
  have hi := hu.integrable_hsNormSq_ball hsmall
  have hiHalf := hu.integrable_hsNormSq_ball hhalf
  have hsOrder := (hmin.monotonicity hn hu hN (by norm_num : (0 : ℝ) < 1 / 2)
    hhalf h.property hhhalf le_rfl).2.2
  have hrFinite := normalizedEnergy_ne_top_of_dirichletEnergy_ne_top
    (r := (⟨1 / 2, by norm_num⟩ : PositiveRadius)) (hu.dirichletEnergy_ne_top_ball hhalf)
  have hreal := ENNReal.toReal_mono hrFinite hsOrder
  rw [normalizedEnergy_toReal hi, normalizedEnergy_toReal hiHalf] at hreal
  have hexp : 2 - (n : ℤ) = -((n - 2 : ℕ) : ℤ) := by omega
  simp only [hexp, zpow_neg, zpow_natCast] at hreal
  have hHalfInv : ((1 / 2 : ℝ) ^ (n - 2))⁻¹ = 2 ^ (n - 2) := by
    rw [← inv_pow]
    norm_num
  rw [hHalfInv] at hreal
  have heOrder : dirichletEnergy Du (Metric.ball x (1 / 2)) ≤
      dirichletEnergy Du (Metric.ball (0 : Domain n) 1) :=
    lintegral_mono' (Measure.restrict_mono_set volume
      (Metric.ball_subset_closedBall.trans hhalf)) le_rfl
  have heReal : (∫ z in Metric.ball x (1 / 2), hsNormSq (Du z)) ≤
      (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
    rw [← dirichletEnergy_toReal (U := Metric.ball x (1 / 2)) hiHalf]
    exact ENNReal.toReal_mono hE heOrder
  have hbound : (∫ z in Metric.ball x h.val, hsNormSq (Du z)) / h.val ^ (n - 2) ≤
      2 ^ (n - 2) * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
    calc
      _ = (h.val ^ (n - 2))⁻¹ * ∫ z in Metric.ball x h.val, hsNormSq (Du z) :=
        div_eq_inv_mul _ _
      _ ≤ 2 ^ (n - 2) * ∫ z in Metric.ball x (1 / 2), hsNormSq (Du z) := hreal
      _ ≤ _ := mul_le_mul_of_nonneg_left heReal (by positivity)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ (2 ^ (n - 2) * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal) *
        h.val ^ (n - 2) := (div_le_iff₀ (pow_pos h.property _)).mp hbound
    _ = _ := by ring

end HarmonicMaps
