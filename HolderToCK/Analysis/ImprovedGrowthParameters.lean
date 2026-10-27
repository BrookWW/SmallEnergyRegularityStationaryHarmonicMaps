module

public import HolderToCK.Analysis.Harmonic.EnergyExcessComparison
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Uniform parameters for improved energy growth

The reference radius and the three regularity exponents have their literal
source values. A vanishing positive power fixes one contraction scale, and a
single positive Holder threshold controls the quadratic comparison coefficient.
-/

@[expose] public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology

namespace HolderToCK

noncomputable section

def growthReferenceRadius : ℝ := 1 / 16

def improvedGrowthBeta (α : ℝ) : ℝ := 1 - α / 4

def improvedEnergyExponent (n : ℕ) (α : ℝ) : ℝ := (n : ℝ) - α / 2

def gradientHolderExponent (α : ℝ) : ℝ := α / 8

def gradientExcessExponent (n : ℕ) (α : ℝ) : ℝ := (n : ℝ) + α / 4

theorem improved_growth_exponents (n : ℕ) (hn : 2 ≤ n) {α : ℝ}
    (hα : 0 < α) (hαOne : α < 1) :
    improvedEnergyExponent n α = (n : ℝ) - 2 + 2 * improvedGrowthBeta α ∧
    0 < improvedEnergyExponent n α ∧
    (n : ℝ) - improvedEnergyExponent n α = α / 2 ∧
    0 < gradientHolderExponent α ∧ gradientHolderExponent α < 1 ∧
    gradientExcessExponent n α = (n : ℝ) + 2 * gradientHolderExponent α ∧
    improvedEnergyExponent n α + α = (n : ℝ) + α / 2 ∧
    gradientExcessExponent n α < (n : ℝ) + α / 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  dsimp only [improvedEnergyExponent, improvedGrowthBeta, gradientHolderExponent,
    gradientExcessExponent]
  refine ⟨by ring, ?_, by ring, ?_, ?_, by ring, by ring, ?_⟩
  · linarith only [hnR, hαOne]
  · linarith only [hα]
  · linarith only [hαOne]
  · linarith only [hα]

theorem small_center_closedBall_subset_threeQuarter {n : ℕ}
    {a : Domain n} (ha : a ∈ Metric.ball (0 : Domain n) (5 / 8 : ℝ))
    {r : ℝ} (hr : r ≤ growthReferenceRadius) :
    Metric.closedBall a r ⊆ Metric.ball (0 : Domain n) (3 / 4 : ℝ) := by
  intro x hx
  have hxa : dist x a ≤ r := hx
  have ha₀ : dist a 0 < (5 / 8 : ℝ) := ha
  change dist x 0 < 3 / 4
  apply lt_of_le_of_lt (dist_triangle x a 0)
  dsimp only [growthReferenceRadius] at hr
  linarith only [hxa, ha₀, hr]

theorem exists_small_rpow_coefficient (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 4 ∧ c * Real.rpow θ δ ≤ 1 / 4 := by
  have hpow : Tendsto (fun t : ℝ => c * Real.rpow t δ) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => c * Real.rpow t δ) :=
      continuous_const.mul (Real.continuous_rpow_const hδ.le)
    simpa only [Real.rpow_eq_pow, Real.zero_rpow hδ.ne', mul_zero] using hc.tendsto (0 : ℝ)
  obtain ⟨ρ, hρ, hAll⟩ := Metric.eventually_nhds_iff.mp
    (hpow.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
  let θ : ℝ := min (ρ / 2) (1 / 4)
  have hθ : 0 < θ := lt_min (half_pos hρ) (by norm_num)
  refine ⟨θ, hθ, min_le_right _ _, ?_⟩
  apply le_of_lt
  apply hAll
  rw [Real.dist_eq, sub_zero, abs_of_pos hθ]
  exact (min_le_left _ _).trans_lt (half_lt_self hρ)

theorem exists_improved_growth_parameters (n : ℕ) (hn : 2 ≤ n)
    {α K c : ℝ} (hα : 0 < α) (hαOne : α < 1) (hK : 0 ≤ K) (hc : 1 ≤ c) :
    ∃ θ H₀ : ℝ, 0 < θ ∧ θ ≤ 1 / 4 ∧ 0 < H₀ ∧ H₀ ≤ 1 ∧
      c * Real.rpow θ (α / 2) ≤ 1 / 4 ∧
      c * (1 + K) * H₀ * Real.rpow growthReferenceRadius α ≤
        (1 / 4 : ℝ) * Real.rpow θ (improvedEnergyExponent n α) ∧
      0 < improvedEnergyExponent n α ∧
      ∀ H : ℝ, 0 ≤ H → H ≤ H₀ → ∀ r : ℝ, 0 < r → r ≤ growthReferenceRadius →
        c * θ ^ n + c * K * H * Real.rpow r α ≤
          (1 / 2 : ℝ) * Real.rpow θ (improvedEnergyExponent n α) := by
  obtain ⟨θ, hθ, hθquarter, hθpower⟩ := exists_small_rpow_coefficient c (half_pos hα)
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hKpos : 0 < 1 + K := by linarith only [hK]
  have hr₀ : 0 < growthReferenceRadius := by norm_num [growthReferenceRadius]
  let D : ℝ := c * (1 + K) * Real.rpow growthReferenceRadius α
  have hD : 0 < D := mul_pos (mul_pos hcpos hKpos) (Real.rpow_pos_of_pos hr₀ _)
  let H₀ : ℝ := min 1 (Real.rpow θ (improvedEnergyExponent n α) / (4 * D))
  have hH₀ : 0 < H₀ := lt_min zero_lt_one
    (div_pos (Real.rpow_pos_of_pos hθ _) (mul_pos (by norm_num) hD))
  have hsmall : c * (1 + K) * H₀ * Real.rpow growthReferenceRadius α ≤
      (1 / 4 : ℝ) * Real.rpow θ (improvedEnergyExponent n α) := by
    have hle : H₀ ≤ Real.rpow θ (improvedEnergyExponent n α) / (4 * D) := min_le_right _ _
    have hmul := (le_div_iff₀ (mul_pos (by norm_num) hD)).mp hle
    dsimp only [D] at hmul
    nlinarith only [hmul]
  have hLambda := (improved_growth_exponents n hn hα hαOne).2.1
  refine ⟨θ, H₀, hθ, hθquarter, hH₀, min_le_left _ _, hθpower, hsmall, hLambda, ?_⟩
  intro H hH hHH r hr hrr₀
  have hfactor : θ ^ n = Real.rpow θ (α / 2) *
      Real.rpow θ (improvedEnergyExponent n α) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hθ]
    have hexp : α / 2 + improvedEnergyExponent n α = (n : ℝ) := by
      dsimp only [improvedEnergyExponent]
      ring
    rw [hexp, Real.rpow_natCast]
  have hfirst : c * θ ^ n ≤ (1 / 4 : ℝ) * Real.rpow θ (improvedEnergyExponent n α) := by
    rw [hfactor, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hθpower (Real.rpow_nonneg hθ.le _)
  have hRpower : Real.rpow r α ≤ Real.rpow growthReferenceRadius α := by
    simpa only [Real.rpow_eq_pow] using Real.rpow_le_rpow hr.le hrr₀ hα.le
  have hsecond : c * K * H * Real.rpow r α ≤
      (1 / 4 : ℝ) * Real.rpow θ (improvedEnergyExponent n α) := by
    apply le_trans _ hsmall
    have hKle : K ≤ 1 + K := by linarith only
    have hKH : K * H ≤ (1 + K) * H₀ :=
      mul_le_mul hKle hHH hH hKpos.le
    have hleft := mul_le_mul_of_nonneg_left hKH hcpos.le
    have hprod := mul_le_mul hleft hRpower (Real.rpow_nonneg hr.le _)
      (mul_nonneg hcpos.le (mul_nonneg hKpos.le hH₀.le))
    simpa only [mul_assoc] using hprod
  linarith only [hfirst, hsecond]

end
end HolderToCK
end
