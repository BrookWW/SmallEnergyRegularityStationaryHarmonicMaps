module

public import HarmonicMaps.Analysis.DecayComparison
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Uniform source decay threshold

The source dimension fixes every exponent. A single positive threshold, chosen
before the actual parameter or map, combines the geometric comparison range
with the vanishing power coefficient. The argument never divides by the map's
energy and applies also when the source dimension is two.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace HarmonicMaps

private theorem decay_exponents (n : ℕ) (hn : 2 ≤ n) :
    let gamma := 1 / (64 * ((n : ℝ) - 1))
    0 < gamma ∧ 2 * gamma ≤ 7 / 64 ∧
      1 / 8 - gamma * ((n : ℝ) - 1) = 7 / 64 ∧
      15 / 64 ≤ 1 / 4 - gamma * ((n : ℝ) - 2) ∧
      2 * gamma ≤ 1 / 4 - gamma * ((n : ℝ) - 2) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < 64 * ((n : ℝ) - 1) := by nlinarith only [hnR]
  let gamma : ℝ := 1 / (64 * ((n : ℝ) - 1))
  have hg : 0 < gamma := div_pos (by norm_num) hden
  have hgSmall : gamma ≤ 1 / 64 := by
    dsimp only [gamma]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hnR]
  have hProduct : gamma * ((n : ℝ) - 1) = 1 / 64 := by
    dsimp only [gamma]
    field_simp [show (n : ℝ) - 1 ≠ 0 by linarith only [hnR]]
  have hA : 15 / 64 ≤ 1 / 4 - gamma * ((n : ℝ) - 2) := by
    nlinarith only [hProduct, hg]
  exact ⟨hg, by linarith only [hgSmall], by linarith only [hProduct], hA,
    by linarith only [hA, hgSmall]⟩

private theorem decay_coefficient_threshold (C gamma : ℝ)
    (_hC : 0 < C) (hg : 0 < gamma) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η : ℝ, 0 < η → η ≤ ε →
      3 * C * η ^ (2 * gamma) ≤ 1 / 2 := by
  have hexp : 0 < 2 * gamma := mul_pos (by norm_num) hg
  have hPow : Tendsto (fun η : ℝ => 3 * C * η ^ (2 * gamma)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun η : ℝ => 3 * C * η ^ (2 * gamma)) :=
      continuous_const.mul (Real.continuous_rpow_const hexp.le)
    simpa only [Real.zero_rpow hexp.ne', mul_zero] using hc.tendsto (0 : ℝ)
  obtain ⟨r, hr, hAll⟩ := Metric.eventually_nhds_iff.mp
    (hPow.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro η hη hηsmall
  have hd : dist η 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hη]
    exact hηsmall.trans_lt (half_lt_self hr)
  exact (hAll hd).le

/-- The complete source threshold supplies both source exponent comparisons,
the uniform half-energy coefficient and the actual original-data decay bound. -/
theorem decay_threshold_complete (n : ℕ) (hn : 2 ≤ n)
    (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    ∃ C₂ ε : ℝ, 0 < C₂ ∧ 0 < ε ∧ ε < 1 ∧
    ∀ η : ℝ, 0 < η → η ≤ ε →
    let gamma := 1 / (64 * ((n : ℝ) - 1))
    let tau := η ^ gamma
    0 < tau ∧ tau < 1 / 8 ∧
    η ^ (1 / 4 - gamma * ((n : ℝ) - 2)) ≤ η ^ (2 * gamma) ∧
    η ^ (1 / 8 - gamma * ((n : ℝ) - 1)) ≤ η ^ (2 * gamma) ∧
    3 * C₂ * η ^ (2 * gamma) ≤ 1 / 2 ∧
    ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
      TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
      IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du →
      dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal η →
      tau ^ (2 - (n : ℤ)) * (dirichletEnergy Du (Metric.ball (0 : Domain n) tau)).toReal ≤
        3 * C₂ * η ^ (2 * gamma) *
          (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal ∧
      tau ^ (2 - (n : ℤ)) * (dirichletEnergy Du (Metric.ball (0 : Domain n) tau)).toReal ≤
        (1 / 2 : ℝ) * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
  obtain ⟨C₂, η₀, hC₂, hη₀, hη₀one, hComparison⟩ := decay_energy_comparison n hn q N
  obtain ⟨hg, hgLower, hB, _, hA⟩ := decay_exponents n hn
  obtain ⟨ε₀, hε₀, hCoefficient⟩ := decay_coefficient_threshold C₂ _ hC₂ hg
  let ε : ℝ := min η₀ ε₀
  have hε : 0 < ε := lt_min hη₀ hε₀
  refine ⟨C₂, ε, hC₂, hε, (min_le_left _ _).trans_lt hη₀one, ?_⟩
  intro η hη hηsmall
  let gamma : ℝ := 1 / (64 * ((n : ℝ) - 1))
  let tau : ℝ := η ^ gamma
  have hηgeom : η ≤ η₀ := hηsmall.trans (min_le_left _ _)
  have hηone : η ≤ 1 := (hηgeom.trans_lt hη₀one).le
  have hPowA : η ^ (1 / 4 - gamma * ((n : ℝ) - 2)) ≤ η ^ (2 * gamma) :=
    Real.rpow_le_rpow_of_exponent_ge hη hηone hA
  have hPowB : η ^ (1 / 8 - gamma * ((n : ℝ) - 1)) ≤ η ^ (2 * gamma) :=
    Real.rpow_le_rpow_of_exponent_ge hη hηone (by rw [hB]; exact hgLower)
  have hCoef := hCoefficient η hη (hηsmall.trans (min_le_right _ _))
  obtain ⟨htau, htauSmall, hMaps⟩ := hComparison η hη hηgeom
  refine ⟨htau, htauSmall, hPowA, hPowB, hCoef, ?_⟩
  intro u Du hu hN hmin hsmall
  have hEnergy : 0 ≤ (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal :=
    ENNReal.toReal_nonneg
  have hSum : η ^ (1 / 4 - gamma * ((n : ℝ) - 2)) + η ^ (2 * gamma) +
      η ^ (1 / 8 - gamma * ((n : ℝ) - 1)) ≤ 3 * η ^ (2 * gamma) := by
    linarith only [hPowA, hPowB]
  have hPre := (hMaps u Du hu hN hmin hsmall).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSum hC₂.le) hEnergy)
  have hPre' : tau ^ (2 - (n : ℤ)) *
      (dirichletEnergy Du (Metric.ball (0 : Domain n) tau)).toReal ≤
      3 * C₂ * η ^ (2 * gamma) * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
    have hEq : C₂ * (3 * η ^ (2 * gamma)) = 3 * C₂ * η ^ (2 * gamma) := by ring
    rw [hEq] at hPre
    exact hPre
  exact ⟨hPre', hPre'.trans (mul_le_mul_of_nonneg_right hCoef hEnergy)⟩

end HarmonicMaps
end
