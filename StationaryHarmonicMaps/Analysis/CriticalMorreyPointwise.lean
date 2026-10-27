module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyDyadicMeans
public import StationaryHarmonicMaps.Analysis.BallMeanEnergyTail

/-!
# Pointwise bounds at Lebesgue points outside ball-average superlevels

The critical Morrey estimate controls the finite number of large dyadic
steps. Actual bounded centered energy averages control the remaining tail.
Their combination is uniform in the target dimension and the map.
-/

public section

open HarmonicMaps MeasureTheory Filter
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

@[expose] def effectivePointwiseConstant (n : ℕ) : ℕ :=
  effectiveDyadicMeanConstant n + 2 ^ (2 * (n + 1)) * (n + 1) + 1

theorem effectivePointwiseConstant_pos (n : ℕ) :
    0 < (effectivePointwiseConstant n : ℝ) := by
  simp only [effectivePointwiseConstant, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  positivity

/-- Outside an actual energy-average superlevel, the original value has a quantitative dyadic bound. -/
theorem effective_pointwise_bound_of_criticalMorrey (n : ℕ) (hn : 2 ≤ n) :
    ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤
        ENNReal.ofReal (η ^ 2) →
      ∀ x ∈ Metric.ball (0 : Domain n) (7 / 8 : ℝ),
      Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, u y)
        (𝓝[>] (0 : ℝ)) (𝓝 (u x)) → ∀ m : ℕ,
      (∀ r : ℝ, 0 < r → r ≤ 1 / 16 →
        (∫ y in Metric.ball x r, hsNormSq (Du y)) ≤
          (16 * η * (2 : ℝ) ^ m) ^ 2 * volume.real (Metric.ball x r)) →
      ‖u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖ ≤ (effectivePointwiseConstant n : ℝ) * η * ((m : ℝ) + 1) := by
  let C₀ : ℝ := effectiveDyadicMeanConstant n
  have hC₀ : 0 < C₀ := effectiveDyadicMeanConstant_pos n
  have hmeans := effective_dyadic_mean_bound_of_criticalMorrey n hn
  let T : ℝ := (2 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ))
  let C : ℝ := effectivePointwiseConstant n
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hTbound : T ≤ (2 : ℝ) ^ (2 * (n + 1)) * ((n : ℝ) + 1) := by
    have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) + 1 := by
      have H := Real.sq_sqrt hnR
      have Hn := Real.sqrt_nonneg (n : ℝ)
      nlinarith only [H, Hn, hnR, sq_nonneg (n : ℝ)]
    have H := mul_le_mul_of_nonneg_left hsqrt
      (show 0 ≤ (2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (n + 1) by positivity)
    have hp : (2 : ℝ) ^ (2 * (n + 1)) = (2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (n + 1) := by
      rw [two_mul, pow_add]
    simpa only [T, hp, mul_assoc] using H
  have hCbound : C₀ + T + 1 ≤ C := by
    dsimp only [C, C₀, effectivePointwiseConstant]
    push_cast
    linarith only [hTbound]
  intro q u Du η hu hη hcritical x hx hLebesgue m henergy
  let r₀ : ℝ := (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ m
  have hr₀ : 0 < r₀ := mul_pos (by norm_num) (pow_pos (by norm_num) m)
  have hcap : r₀ ≤ 1 / 16 := mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ 1 / 16)
    (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have hclosed : Metric.closedBall x r₀ ⊆ (ballDomain (0 : Domain n) 1).val :=
    (Metric.closedBall_subset_closedBall hcap).trans (closedBall_sixteenth_subset_unit hx)
  have htail := ballMean_value_tail_of_energy_average hu.to_memW12Loc x hr₀ hclosed
    hLebesgue (fun r hr hrle => henergy r hr (hrle.trans hcap))
  have hroot : Real.sqrt ((16 * η * (2 : ℝ) ^ m) ^ 2) = 16 * η * (2 : ℝ) ^ m :=
    Real.sqrt_sq (by positivity)
  have hpow : (1 / 2 : ℝ) ^ m * (2 : ℝ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  have hscale : Real.sqrt ((16 * η * (2 : ℝ) ^ m) ^ 2) * r₀ = η := by
    rw [hroot]
    calc
      _ = η * ((1 / 2 : ℝ) ^ m * (2 : ℝ) ^ m) := by dsimp only [r₀]; ring
      _ = _ := by rw [hpow, mul_one]
  have htail' : ‖u x - (⨍ y in Metric.ball x r₀, u y)‖ ≤ T * η := by
    rw [norm_sub_rev]
    have hcoef : T * Real.sqrt ((16 * η * (2 : ℝ) ^ m) ^ 2) * r₀ = T * η := by
      rw [mul_assoc, hscale]
    exact htail.trans_eq hcoef
  have hhead := hmeans q u Du η hu hη hcritical x hx m
  have hscalar : T + C₀ * ((m : ℝ) + 1) ≤ C * ((m : ℝ) + 1) := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hTm := mul_nonneg hT hm
    nlinarith only [hm, hTm, mul_nonneg (sub_nonneg.mpr hCbound) (by linarith : 0 ≤ (m : ℝ) + 1)]
  calc
    _ ≤ ‖u x - (⨍ y in Metric.ball x r₀, u y)‖ +
        ‖(⨍ y in Metric.ball x r₀, u y) - (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ T * η + C₀ * η * ((m : ℝ) + 1) := add_le_add htail' hhead
    _ = (T + C₀ * ((m : ℝ) + 1)) * η := by ring
    _ ≤ (C * ((m : ℝ) + 1)) * η := mul_le_mul_of_nonneg_right hscalar hη
    _ = _ := by ring

/-- Outside an actual energy-average superlevel, the original value has a quantitative dyadic bound. -/
theorem exists_pointwise_bound_of_criticalMorrey (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤
        ENNReal.ofReal (η ^ 2) →
      ∀ x ∈ Metric.ball (0 : Domain n) (7 / 8 : ℝ),
      Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, u y)
        (𝓝[>] (0 : ℝ)) (𝓝 (u x)) → ∀ m : ℕ,
      (∀ r : ℝ, 0 < r → r ≤ 1 / 16 →
        (∫ y in Metric.ball x r, hsNormSq (Du y)) ≤
          (16 * η * (2 : ℝ) ^ m) ^ 2 * volume.real (Metric.ball x r)) →
      ‖u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖ ≤ C * η * ((m : ℝ) + 1) := by
  exact ⟨(effectivePointwiseConstant n : ℝ), effectivePointwiseConstant_pos n,
    effective_pointwise_bound_of_criticalMorrey n hn⟩

end StationaryHarmonicMaps.Analysis

end
