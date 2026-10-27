module

public import StationaryHarmonicMaps.Analysis.NativeMorreyMeanZero
public import StationaryHarmonicMaps.Analysis.EffectiveNeumannBoundary
public import StationaryHarmonicMaps.Analysis.BoundaryLocalizedTest
import HarmonicMaps.Analysis.SobolevPoincare
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Effective arithmetic for Coulomb estimates

The natural-number bounds control the actual native mean-zero norm and
the original Neumann gradient near the boundary.
The rational amplitudes encode conservative arithmetic choices for
absorption and linear inversion. Their arithmetic statements do not
assert the analytic estimates supplying the input bounds.
-/

public section

open HarmonicMaps MeasureTheory Set Metric
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis.EffectiveCoulomb

@[expose] def meanZeroBound (n : ℕ) : ℕ := 1 + 2 ^ (n + 1)

theorem meanZeroBound_pos (n : ℕ) : 0 < meanZeroBound n := by
  exact Nat.add_pos_left (by norm_num) _

theorem native_mean_zero_norm_le (n q : ℕ) (ν : ℝ)
    (hν : ν ≤ (n : ℝ) + 1) (X : MeanZeroNativeMorreySpace n q ν) :
    ‖X‖ ≤ (meanZeroBound n : ℝ) * ‖meanZeroNativeMorreyGradientClass n q ν X‖ := by
  let T : ℝ := 2 ^ (n + 1)
  let C : ℝ := meanZeroBound n
  let P : ℝ := (2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ ν
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hCeq : C = 1 + T := by
    simp only [C, meanZeroBound, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
      Nat.cast_ofNat, T]
  have hCOne : 1 ≤ C := by rw [hCeq]; linarith only [hT]
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hCOne
  have hPow : (2 : ℝ) ^ ν ≤ (2 : ℝ) ^ (n + 1) := by
    have hν' : ν ≤ ((n + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hν
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hν'
  have hPC : P ≤ C ^ 2 := by
    have H : P ≤ T * T := mul_le_mul_of_nonneg_left hPow hT
    rw [hCeq]
    nlinarith only [H, hT]
  obtain ⟨u, Du, hNative, hMean, hMap, hGrad, hGrowth⟩ :=
    exists_raw_native_of_meanZeroNativeMorrey (n := n) (q := q) ν X
  let G := ‖meanZeroNativeMorreyGradientClass n q ν X‖
  have hG : 0 ≤ G := norm_nonneg _
  have hPoincare : (∫ x in ball (0 : Domain n) 1, ‖u x‖ ^ 2) ≤
      (2 : ℝ) ^ (n + 1) * (∫ x in ball (0 : Domain n) 1, hsNormSq (Du x)) := by
    have H := hNative.poincare_ball (by norm_num : (0 : ℝ) < 1)
    rw [hMean] at H
    simpa only [sub_zero, one_pow, mul_one] using H
  have hEnergy : (∫ x in ball (0 : Domain n) 1, hsNormSq (Du x)) ≤ G ^ 2 * (2 : ℝ) ^ ν := by
    simpa only [inter_eq_right.mpr (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)),
      G, meanZeroNativeMorreyGradientClass, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply] using
      hGrowth 0 (mem_ball_self (by norm_num : (0 : ℝ) < 1)) 2 (by norm_num)
  have hMapEnergy : (∫ x in ball (0 : Domain n) 1, ‖u x‖ ^ 2) ≤ P * G ^ 2 :=
    hPoincare.trans ((mul_le_mul_of_nonneg_left hEnergy hT).trans_eq (by dsimp only [P]; ring))
  have hGradSq : G ^ 2 = sSup {e : ℝ | ∃ a ∈ ball (0 : Domain n) 1, ∃ r : ℝ, 0 < r ∧
      e = r ^ (-ν) * (∫ x in ball a r ∩ ball (0 : Domain n) 1, hsNormSq (Du x))} :=
    morreyCoefficient_norm_sq ν Du hNative.2.2
      (nativeMorreyGradientClass (n := n) (q := q) ν X.val) hGrad
  have hTotalSq : ‖X‖ ^ 2 = max (∫ x in ball (0 : Domain n) 1, ‖u x‖ ^ 2) (G ^ 2) :=
    (nativeMorreySobolev_norm_sq ν u Du hNative X.val hMap hGrad).trans
      (congrArg (fun r : ℝ => max (∫ x in ball (0 : Domain n) 1, ‖u x‖ ^ 2) r) hGradSq.symm)
  have hMapBound : (∫ x in ball (0 : Domain n) 1, ‖u x‖ ^ 2) ≤ (C * G) ^ 2 :=
    hMapEnergy.trans ((mul_le_mul_of_nonneg_right hPC (sq_nonneg G)).trans_eq (mul_pow C G 2).symm)
  have hGradBound : G ^ 2 ≤ (C * G) ^ 2 :=
    pow_le_pow_left₀ hG (le_mul_of_one_le_left hG hCOne) 2
  have hSq : ‖X‖ ^ 2 ≤ (C * G) ^ 2 := hTotalSq.trans_le (max_le hMapBound hGradBound)
  have hNorm := norm_nonneg X
  have hCG : 0 ≤ C * G := mul_nonneg hC.le hG
  change ‖X‖ ≤ C * G
  nlinarith only [hSq, hNorm, hCG]

@[expose] def naturalPowerScale (farBound : ℚ) : ℚ :=
  1 / (256 * (1 + 4 * farBound))

theorem naturalPowerScale_pos {farBound : ℚ} (hFar : 0 ≤ farBound) :
    0 < naturalPowerScale farBound := by
  unfold naturalPowerScale
  positivity

theorem naturalPowerScale_le {farBound : ℚ} (hFar : 0 ≤ farBound) :
    naturalPowerScale farBound ≤ 1 / 256 := by
  unfold naturalPowerScale
  apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
  nlinarith only [hFar]

theorem naturalPowerScale_absorbs {farBound : ℚ} (hFar : 0 ≤ farBound) :
    2 * farBound * naturalPowerScale farBound ≤ 1 / 2 := by
  unfold naturalPowerScale
  rw [← mul_div_assoc, mul_one]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hFar]

theorem naturalPowerScale_gap (n : ℕ) (hn : 1 ≤ n) {farBound : ℚ}
    (hFar : 0 ≤ farBound) :
    0 < naturalPowerScale farBound ^ (n - 1) -
      2 * farBound * naturalPowerScale farBound ^ n := by
  let θ := naturalPowerScale farBound
  have hθ : 0 < θ := naturalPowerScale_pos hFar
  have hθPower : 0 < θ ^ (n - 1) := pow_pos hθ _
  have hnEq : n = (n - 1) + 1 := by omega
  have hScale : 2 * farBound * θ ≤ 1 / 2 := naturalPowerScale_absorbs hFar
  have H := mul_le_mul_of_nonneg_right hScale hθPower.le
  have hp : θ ^ n = θ ^ (n - 1) * θ := by
    conv_lhs => rw [hnEq, pow_succ]
  change 0 < θ ^ (n - 1) - 2 * farBound * θ ^ n
  rw [hp]
  nlinarith only [H, hθPower]

@[expose] def naturalPowerBound (n : ℕ) (farBound nearBound energyBound : ℚ) : ℚ :=
  let θ := naturalPowerScale farBound
  let β := energyBound * 8 ^ (n - 1)
  2 ^ (n - 1) * (1 + β +
    (β + nearBound * (2 + 2 * farBound) /
      (θ ^ (n - 1) - 2 * farBound * θ ^ n)) / θ ^ (n - 1))

theorem naturalPowerBound_pos (n : ℕ) (hn : 1 ≤ n)
    {farBound nearBound energyBound : ℚ} (hFar : 0 ≤ farBound)
    (hNear : 0 ≤ nearBound) (hEnergy : 0 ≤ energyBound) :
    0 < naturalPowerBound n farBound nearBound energyBound := by
  have hθ := naturalPowerScale_pos hFar
  have hgap := naturalPowerScale_gap n hn hFar
  unfold naturalPowerBound
  dsimp only
  positivity

@[expose] def alternatingNearBound (n : ℕ) (compensatedBound : ℚ) : ℚ :=
  compensatedBound * (effectiveBoundaryLocalizedTestConstant n : ℚ) *
    (2 ^ (n - 1) * (1 + 2 ^ (2 * n))) * 4 ^ (n - 1)

theorem alternatingNearBound_pos (n : ℕ) {compensatedBound : ℚ}
    (hBound : 0 < compensatedBound) : 0 < alternatingNearBound n compensatedBound := by
  have hCut : (0 : ℚ) < effectiveBoundaryLocalizedTestConstant n := by
    exact_mod_cast effectiveBoundaryLocalizedTestConstant_pos n
  unfold alternatingNearBound
  positivity

theorem alternatingNearBound_controls_exponent (n : ℕ) (hn : 1 ≤ n) (ν : ℝ)
    (hνCap : ν ≤ (n : ℝ) - 1) {compensatedBound : ℚ} (hBound : 0 ≤ compensatedBound) :
    (compensatedBound : ℝ) * (effectiveBoundaryLocalizedTestConstant n : ℝ) *
      ((2 : ℝ) ^ ν * (1 + (2 : ℝ) ^ (2 * n))) * (4 : ℝ) ^ ν ≤
        (alternatingNearBound n compensatedBound : ℝ) := by
  have hν : ν ≤ ((n - 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_sub hn, Nat.cast_one] using hνCap
  have htwo : (2 : ℝ) ^ ν ≤ (2 : ℝ) ^ (n - 1) := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hν
  have hfour : (4 : ℝ) ^ ν ≤ (4 : ℝ) ^ (n - 1) := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hν
  have hBoundR : 0 ≤ (compensatedBound : ℝ) := by exact_mod_cast hBound
  have H := mul_le_mul
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right htwo (show 0 ≤ 1 + (2 : ℝ) ^ (2 * n) by positivity))
      (show 0 ≤ (compensatedBound : ℝ) * (effectiveBoundaryLocalizedTestConstant n : ℝ) by positivity))
    hfour (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
    (show 0 ≤ (compensatedBound : ℝ) * (effectiveBoundaryLocalizedTestConstant n : ℝ) *
      ((2 : ℝ) ^ (n - 1) * (1 + (2 : ℝ) ^ (2 * n))) by positivity)
  simpa only [alternatingNearBound, Rat.cast_mul, Rat.cast_add, Rat.cast_one,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast] using H

@[expose] noncomputable def realPowerGrowthCoefficient (n : ℕ) (ν : ℝ)
    (farBound nearBound energyBound : ℚ) : ℝ :=
  let θ : ℝ := naturalPowerScale farBound
  let β := (energyBound : ℝ) / (1 / 8 : ℝ) ^ ν
  (2 : ℝ) ^ ν * (1 + β +
    (β + (nearBound : ℝ) * (2 + 2 * (farBound : ℝ)) /
      (θ ^ ν - 2 * (farBound : ℝ) * θ ^ n)) / θ ^ ν)

theorem realPowerGrowthCoefficient_le (n : ℕ) (hn : 1 ≤ n) (ν : ℝ)
    (hνCap : ν ≤ (n : ℝ) - 1) {farBound nearBound energyBound : ℚ}
    (hFar : 0 ≤ farBound) (hNear : 0 ≤ nearBound) (hEnergy : 0 ≤ energyBound) :
    realPowerGrowthCoefficient n ν farBound nearBound energyBound ≤
      (naturalPowerBound n farBound nearBound energyBound : ℝ) := by
  let t := naturalPowerScale farBound
  let θ : ℝ := t
  let C : ℝ := farBound
  let D : ℝ := nearBound
  let Ce : ℝ := energyBound
  have hC : 0 ≤ C := by dsimp only [C]; exact_mod_cast hFar
  have hD : 0 ≤ D := by dsimp only [D]; exact_mod_cast hNear
  have hCe : 0 ≤ Ce := by dsimp only [Ce]; exact_mod_cast hEnergy
  have ht : 0 < t := naturalPowerScale_pos hFar
  have hθ : 0 < θ := by change 0 < (t : ℝ); exact_mod_cast ht
  have hθOne : θ ≤ 1 := by
    have H : (t : ℝ) ≤ ((1 / 256 : ℚ) : ℝ) := Rat.cast_le.mpr (naturalPowerScale_le hFar)
    norm_num at H
    exact H.trans (by norm_num)
  have hνNat : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn]; norm_num
  have hPower : θ ^ ((n - 1 : ℕ) : ℝ) ≤ θ ^ ν :=
    Real.rpow_le_rpow_of_exponent_ge hθ hθOne (by simpa only [← hνNat] using hνCap)
  have hGap : 0 < θ ^ ((n - 1 : ℕ) : ℝ) - 2 * C * θ ^ n := by
    have H : (0 : ℝ) < ((t ^ (n - 1) - 2 * farBound * t ^ n : ℚ) : ℝ) :=
      Rat.cast_pos.mpr (naturalPowerScale_gap n hn hFar)
    norm_num only [Rat.cast_sub, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] at H
    rw [Real.rpow_natCast]
    exact H
  have hBeta : Ce / (1 / 8 : ℝ) ^ ν ≤ Ce * (8 : ℝ) ^ (n - 1) := by
    have H := div_le_div_of_nonneg_left hCe
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 8) ((n - 1 : ℕ) : ℝ))
      (Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num)
        (by simpa only [← hνNat] using hνCap))
    simpa only [Real.rpow_natCast, one_div_pow, div_div_eq_mul_div, div_one] using H
  have hGapν : 0 < θ ^ ν - 2 * C * θ ^ n :=
    hGap.trans_le (sub_le_sub_right hPower (2 * C * θ ^ n))
  have hPart := div_le_div_of_nonneg_left (show 0 ≤ D * (2 + 2 * C) by positivity) hGap
    (sub_le_sub_right hPower (2 * C * θ ^ n))
  have hNum := add_le_add hBeta hPart
  have hDiv := div_le_div₀ (show 0 ≤ Ce * (8 : ℝ) ^ (n - 1) +
      D * (2 + 2 * C) / (θ ^ ((n - 1 : ℕ) : ℝ) - 2 * C * θ ^ n) by positivity)
    hNum (Real.rpow_pos_of_pos hθ _) hPower
  have hBetaOne : 1 + Ce / (1 / 8 : ℝ) ^ ν ≤ 1 + Ce * (8 : ℝ) ^ (n - 1) := by
    linarith only [hBeta]
  have hInner := add_le_add hBetaOne hDiv
  have hTwo : (2 : ℝ) ^ ν ≤ (2 : ℝ) ^ ((n - 1 : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by simpa only [← hνNat] using hνCap)
  have hTotal := mul_le_mul hTwo hInner
    (show 0 ≤ 1 + Ce / (1 / 8 : ℝ) ^ ν +
      (Ce / (1 / 8 : ℝ) ^ ν + D * (2 + 2 * C) / (θ ^ ν - 2 * C * θ ^ n)) / θ ^ ν by
      positivity)
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  simpa only [realPowerGrowthCoefficient, naturalPowerBound, Rat.cast_add, Rat.cast_mul,
    Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat,
    Real.rpow_natCast, θ, t, C, D, Ce] using hTotal

@[expose] def inverseAmplitude (operatorBound bilinearBound : ℚ) : ℚ :=
  1 / (2 * operatorBound * (1 + bilinearBound))

theorem inverseAmplitude_pos {operatorBound bilinearBound : ℚ}
    (hOperator : 0 < operatorBound) (hBilinear : 0 ≤ bilinearBound) :
    0 < inverseAmplitude operatorBound bilinearBound := by
  unfold inverseAmplitude
  positivity

theorem inverseAmplitude_controls_product {operatorBound bilinearBound : ℚ}
    (hOperator : 0 < operatorBound) (hBilinear : 0 ≤ bilinearBound)
    {η : ℝ} (hη : 0 ≤ η) (hSmall : η ≤ (inverseAmplitude operatorBound bilinearBound : ℝ)) :
    (operatorBound : ℝ) * (bilinearBound : ℝ) * η ≤ 1 / 2 := by
  have hO : 0 < (operatorBound : ℝ) := by exact_mod_cast hOperator
  have hB : 0 ≤ (bilinearBound : ℝ) := by exact_mod_cast hBilinear
  let D : ℝ := (operatorBound : ℝ) * (1 + (bilinearBound : ℝ))
  have hD : 0 < D := mul_pos hO (by linarith only [hB])
  have hDE : D * (inverseAmplitude operatorBound bilinearBound : ℝ) = 1 / 2 := by
    simp only [inverseAmplitude, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
      Rat.cast_ofNat, Rat.cast_add]
    dsimp only [D]
    field_simp
  have hOB : (operatorBound : ℝ) * (bilinearBound : ℝ) ≤ D := by
    dsimp only [D]
    nlinarith only [hO]
  calc
    _ ≤ D * η := mul_le_mul_of_nonneg_right hOB hη
    _ ≤ D * (inverseAmplitude operatorBound bilinearBound : ℝ) :=
      mul_le_mul_of_nonneg_left hSmall hD.le
    _ = 1 / 2 := hDE

@[expose] def absorptionAmplitude (boundaryBound : ℚ) : ℚ :=
  1 / (8 * (1 + boundaryBound))

theorem absorptionAmplitude_pos {boundaryBound : ℚ} (hBound : 0 ≤ boundaryBound) :
    0 < absorptionAmplitude boundaryBound := by
  unfold absorptionAmplitude
  positivity

theorem absorptionAmplitude_controls_square {boundaryBound : ℚ}
    (hBound : 0 ≤ boundaryBound) :
    4 * (boundaryBound : ℝ) * (absorptionAmplitude boundaryBound : ℝ) ^ 2 ≤ 1 / 2 := by
  have hB : 0 ≤ (boundaryBound : ℝ) := by exact_mod_cast hBound
  have hDen : 0 < 8 * (1 + (boundaryBound : ℝ)) := by positivity
  have hCast : (absorptionAmplitude boundaryBound : ℝ) =
      1 / (8 * (1 + (boundaryBound : ℝ))) := by
    simp only [absorptionAmplitude, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
      Rat.cast_ofNat, Rat.cast_add]
  rw [hCast, div_pow, one_pow, ← mul_div_assoc, mul_one]
  apply (div_le_iff₀ (sq_pos_of_pos hDen)).2
  nlinarith only [hB, sq_nonneg (boundaryBound : ℝ)]

@[expose] def scalarPathAmplitude (absorption inverse bound : ℚ) : ℚ :=
  min (inverse / (1 + bound)) ((absorption / 4) / (1 + bound))

theorem scalarPathAmplitude_pos {absorption inverse bound : ℚ}
    (hAbsorption : 0 < absorption) (hInverse : 0 < inverse) (hBound : 0 ≤ bound) :
    0 < scalarPathAmplitude absorption inverse bound := by
  unfold scalarPathAmplitude
  apply lt_min <;> positivity

theorem scalarPathAmplitude_controls_parameters {absorption inverse bound : ℚ}
    (hAbsorption : 0 < absorption) (hInverse : 0 < inverse) (hBound : 0 < bound)
    {η : ℝ} (hη : 0 ≤ η)
    (hSmall : η ≤ (scalarPathAmplitude absorption inverse bound : ℝ)) :
    0 ≤ (1 + (bound : ℝ)) * η ∧ (1 + (bound : ℝ)) * η ≤ (inverse : ℝ) ∧
      2 * (bound : ℝ) * η ^ 2 + 2 * ((absorption : ℝ) / 4) ^ 2 ≤ (absorption : ℝ) ^ 2 := by
  have hA : 0 < (absorption : ℝ) := by exact_mod_cast hAbsorption
  have hI : 0 < (inverse : ℝ) := by exact_mod_cast hInverse
  have hB : 0 < (bound : ℝ) := by exact_mod_cast hBound
  have hOne : 0 < 1 + (bound : ℝ) := by linarith only [hB]
  have hMin : η ≤ min ((inverse : ℝ) / (1 + (bound : ℝ)))
      (((absorption : ℝ) / 4) / (1 + (bound : ℝ))) := by
    simpa only [scalarPathAmplitude, Rat.cast_min, Rat.cast_div, Rat.cast_add,
      Rat.cast_one, Rat.cast_ofNat] using hSmall
  have hIFT : (1 + (bound : ℝ)) * η ≤ (inverse : ℝ) := by
    have H := (le_div_iff₀ hOne).mp (hMin.trans (min_le_left _ _))
    simpa only [mul_comm] using H
  have hDelta : (1 + (bound : ℝ)) * η ≤ (absorption : ℝ) / 4 := by
    have H := (le_div_iff₀ hOne).mp (hMin.trans (min_le_right _ _))
    simpa only [mul_comm] using H
  have hNonneg : 0 ≤ (1 + (bound : ℝ)) * η := mul_nonneg hOne.le hη
  have hCoefficient : (bound : ℝ) ≤ (1 + (bound : ℝ)) ^ 2 := by
    nlinarith only [hB, sq_nonneg (bound : ℝ)]
  have hScale : (bound : ℝ) * η ^ 2 ≤ ((1 + (bound : ℝ)) * η) ^ 2 :=
    (mul_le_mul_of_nonneg_right hCoefficient (sq_nonneg η)).trans_eq (by ring)
  have hSquare : ((1 + (bound : ℝ)) * η) ^ 2 ≤ ((absorption : ℝ) / 4) ^ 2 :=
    (sq_le_sq₀ hNonneg (by positivity)).mpr hDelta
  refine ⟨hNonneg, hIFT, ?_⟩
  nlinarith only [hScale, hSquare, sq_nonneg (absorption : ℝ)]

theorem scalarPathAmplitude_controls_native_threshold {absorption inverse bound : ℚ}
    (hAbsorption : 0 < absorption) (hInverse : 0 < inverse) (hBound : 0 < bound)
    {η : ℝ} (hη : 0 ≤ η)
    (hSmall : η ≤ (scalarPathAmplitude absorption inverse bound : ℝ)) :
    0 ≤ (1 + (bound : ℝ)) * η ∧ (1 + (bound : ℝ)) * η ≤ (inverse : ℝ) ∧
      2 * (bound : ℝ) * η ^ 2 + 2 * ((absorption : ℝ) / 4) ^ 2 ≤ (absorption : ℝ) ^ 2 ∧
      (bound : ℝ) * η ^ 2 ≤ ((1 + (bound : ℝ)) * η) ^ 2 ∧
      ∀ E : ℝ≥0∞, E ≤ ENNReal.ofReal ((bound : ℝ) * η ^ 2) →
        E ≤ ENNReal.ofReal (((1 + (bound : ℝ)) * η) ^ 2) := by
  obtain ⟨hNonneg, hIFT, hEnergy⟩ :=
    scalarPathAmplitude_controls_parameters hAbsorption hInverse hBound hη hSmall
  have hB : 0 < (bound : ℝ) := by exact_mod_cast hBound
  have hCoeff : (bound : ℝ) ≤ (1 + (bound : ℝ)) ^ 2 := by
    nlinarith only [hB, sq_nonneg (bound : ℝ)]
  have hScale : (bound : ℝ) * η ^ 2 ≤ ((1 + (bound : ℝ)) * η) ^ 2 :=
    (mul_le_mul_of_nonneg_right hCoeff (sq_nonneg η)).trans_eq (by ring)
  refine ⟨hNonneg, hIFT, hEnergy, hScale, ?_⟩
  intro E hE
  exact hE.trans (ENNReal.ofReal_le_ofReal hScale)

@[expose] def criticalAmplitude (n : ℕ) (strongerAmplitude : ℚ) : ℚ :=
  strongerAmplitude / 2 ^ n

theorem criticalAmplitude_pos (n : ℕ) {strongerAmplitude : ℚ}
    (hAmplitude : 0 < strongerAmplitude) :
    0 < criticalAmplitude n strongerAmplitude := by
  unfold criticalAmplitude
  positivity

theorem criticalAmplitude_controls_mollifier (n : ℕ) (strongerAmplitude : ℚ)
    {η : ℝ} (hη : 0 ≤ η) (hSmall : η ≤ (criticalAmplitude n strongerAmplitude : ℝ)) :
    Real.sqrt ((2 : ℝ) ^ (n - 2)) * η ≤ (strongerAmplitude : ℝ) := by
  have hP : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hOne : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hPower : (2 : ℝ) ^ (n - 2) ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have hSquare : (2 : ℝ) ^ n ≤ ((2 : ℝ) ^ n) ^ 2 := by
    nlinarith only [mul_nonneg hP.le (sub_nonneg.mpr hOne)]
  have hRoot : Real.sqrt ((2 : ℝ) ^ (n - 2)) ≤ (2 : ℝ) ^ n := by
    have H := Real.sq_sqrt (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n - 2))
    have Hn := Real.sqrt_nonneg ((2 : ℝ) ^ (n - 2))
    nlinarith only [H, Hn, hP, hPower, hSquare]
  have hRatio : η ≤ (strongerAmplitude : ℝ) / (2 : ℝ) ^ n := by
    simpa only [criticalAmplitude, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hSmall
  calc
    _ ≤ (2 : ℝ) ^ n * η := mul_le_mul_of_nonneg_right hRoot hη
    _ ≤ (strongerAmplitude : ℝ) := by
      simpa only [mul_comm] using (le_div_iff₀ hP).mp hRatio

@[expose] def criticalBound (n : ℕ) (strongerBound : ℚ) : ℚ :=
  2 * strongerBound * 2 ^ (n - 2)

theorem criticalBound_pos (n : ℕ) {strongerBound : ℚ} (hBound : 0 < strongerBound) :
    0 < criticalBound n strongerBound := by
  unfold criticalBound
  positivity

theorem criticalBound_square_identity (n : ℕ) (strongerBound : ℚ) (η : ℝ) :
    (strongerBound : ℝ) * (Real.sqrt ((2 : ℝ) ^ (n - 2)) * η) ^ 2 +
      (strongerBound : ℝ) * (Real.sqrt ((2 : ℝ) ^ (n - 2)) * η) ^ 2 =
        (criticalBound n strongerBound : ℝ) * η ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (n - 2))]
  simp only [criticalBound, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  ring

end StationaryHarmonicMaps.Analysis.EffectiveCoulomb

end
