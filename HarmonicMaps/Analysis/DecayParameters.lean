module

public import HarmonicMaps.Frozen.UniformSmoothing
public import HarmonicMaps.Frozen.TubularProjection
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Uniform geometric scales for annular gluing

The source powers of the uniform energy bound satisfy every geometric
smallness inequality below one positive threshold. The threshold depends on
the dimension and the fixed source constants and precedes the map and energy.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace HarmonicMaps

/-- The source geometric scales obey every smallness condition below one
threshold chosen before the energy and the map. -/
theorem decay_geometric_parameters (n : ℕ) (hn : 2 ≤ n)
    (C₀ ρ : ℝ) (_hC₀ : 0 < C₀) (hρ : 0 < ρ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
      let hbar := η ^ (1 / 4 : ℝ)
      let delta := η ^ (1 / 8 : ℝ)
      let gamma := 1 / (64 * ((n : ℝ) - 1))
      let tau := η ^ gamma
      0 < η ∧ η < 1 ∧ 0 < hbar ∧ 0 < delta ∧ 0 < tau ∧
      0 < gamma ∧ gamma < 1 / 8 ∧
      hbar = delta ^ 2 ∧ hbar ≤ delta ∧
      Real.sqrt (C₀ * η) < ρ ∧ hbar ≤ 1 / 4 ∧
      delta ≤ 1 / 8 ∧ 2 * delta ≤ 1 / 4 ∧
      2 * tau < 1 / 4 ∧ 2 ≤ tau / (3 * delta) := by
  let gamma : ℝ := 1 / (64 * ((n : ℝ) - 1))
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < 64 * ((n : ℝ) - 1) := by nlinarith only [hnR]
  have hgamma : 0 < gamma := div_pos (by norm_num) hden
  have hgammaSmall : gamma < 1 / 8 := by
    dsimp only [gamma]
    apply (div_lt_iff₀ hden).mpr
    nlinarith only [hnR]
  have hgap : 0 < (1 / 8 : ℝ) - gamma := sub_pos.mpr hgammaSmall
  have hPow (a : ℝ) (ha : 0 < a) : Tendsto (fun η : ℝ => η ^ a) (𝓝 0) (𝓝 0) := by
    simpa only [Real.zero_rpow ha.ne'] using (Real.continuous_rpow_const ha.le).tendsto 0
  have hRoot : Tendsto (fun η : ℝ => Real.sqrt (C₀ * η)) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun η : ℝ => C₀ * η) := continuous_const.mul continuous_id
    simpa only [mul_zero, Real.sqrt_zero] using
      hcont.sqrt.tendsto (0 : ℝ)
  have hAll : ∀ᶠ η : ℝ in 𝓝 0,
      Real.sqrt (C₀ * η) < ρ ∧
      η ^ (1 / 4 : ℝ) < 1 / 4 ∧
      η ^ (1 / 8 : ℝ) < 1 / 8 ∧
      η ^ gamma < 1 / 8 ∧
      η ^ ((1 / 8 : ℝ) - gamma) < 1 / 6 := by
    filter_upwards [hRoot.eventually (eventually_lt_nhds hρ),
      (hPow (1 / 4) (by norm_num)).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      (hPow (1 / 8) (by norm_num)).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
      (hPow gamma hgamma).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
      (hPow ((1 / 8 : ℝ) - gamma) hgap).eventually
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 6))]
      with η h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ε, hε, hεAll⟩ := Metric.eventually_nhds_iff.mp hAll
  let η₀ : ℝ := min (ε / 2) (1 / 2)
  have hη₀ : 0 < η₀ := lt_min (half_pos hε) (by norm_num)
  have hη₀One : η₀ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨η₀, hη₀, hη₀One, ?_⟩
  intro η hη hηSmall
  have hηε : dist η 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hη]
    exact (hηSmall.trans (min_le_left _ _)).trans_lt (half_lt_self hε)
  obtain ⟨hRootSmall, hhbar, hdelta, htau, hratio⟩ := hεAll hηε
  dsimp only
  have hd : 0 < η ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hη _
  have ht : 0 < η ^ gamma := Real.rpow_pos_of_pos hη _
  have heq : η ^ (1 / 4 : ℝ) = (η ^ (1 / 8 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
    norm_num
  have hhd : η ^ (1 / 4 : ℝ) ≤ η ^ (1 / 8 : ℝ) := by
    rw [heq]
    nlinarith only [hd, hdelta]
  have hRatioEq : η ^ ((1 / 8 : ℝ) - gamma) = η ^ (1 / 8 : ℝ) / η ^ gamma :=
    Real.rpow_sub hη _ _
  rw [hRatioEq, div_lt_iff₀ ht] at hratio
  have hSourceRatio : 2 ≤ η ^ gamma / (3 * η ^ (1 / 8 : ℝ)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hd)).mpr
    linarith only [hratio]
  exact ⟨hη, hηSmall.trans_lt hη₀One, Real.rpow_pos_of_pos hη _, hd, ht,
    hgamma, hgammaSmall, heq, hhd, hRootSmall, hhbar.le, hdelta.le,
    by linarith only [hdelta], by linarith only [htau], hSourceRatio⟩

end HarmonicMaps

end
