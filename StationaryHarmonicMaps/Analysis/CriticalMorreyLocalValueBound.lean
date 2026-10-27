module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegerMoments
public import StationaryHarmonicMaps.Analysis.LpPowerComparison
import HolderToCK.Foundation.BallVolume

/-!
# Local value L² growth from genuine critical Morrey gradient control

A sufficiently large integer moment is selected before the Sobolev map.
Forward Hölder comparison and the actual local ball volume give the value
growth with an arbitrary prescribed positive loss in the radius exponent.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- An actual integer moment can be chosen beyond the dimension-dependent loss threshold. -/
theorem exists_integer_exponent_for_local_value (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, 2 < (k : ℝ) ∧ (n : ℝ) / (k : ℝ) < δ := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max (2 : ℝ) ((n : ℝ) / δ))
  have hkTwo : (2 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hn : (n : ℝ) / δ < k := (le_max_right _ _).trans_lt hk
  refine ⟨k, hkTwo, (div_lt_iff₀ (lt_trans (by norm_num) hkTwo)).2 ?_⟩
  have H := (div_lt_iff₀ hδ).1 hn
  nlinarith

/-- The forward moment and volume factors give the desired radius power, including zero amplitude. -/
theorem local_value_moment_volume_scale {n k : ℕ} {δ C V η t : ℝ}
    (hk : 0 < (k : ℝ)) (hfrac : (n : ℝ) / (k : ℝ) ≤ δ)
    (hC : 0 ≤ C) (hV : 0 ≤ V) (hη : 0 ≤ η) (ht : 0 < t) (htOne : t ≤ 1) :
    (V * t ^ n) ^ (1 - 2 / (k : ℝ)) * (C * η ^ k) ^ (2 / (k : ℝ)) ≤
      (V ^ (1 - 2 / (k : ℝ)) * C ^ (2 / (k : ℝ))) * η ^ 2 *
        t ^ ((n : ℝ) - 2 * δ) := by
  have heq : (V * t ^ n) ^ (1 - 2 / (k : ℝ)) * (C * η ^ k) ^ (2 / (k : ℝ)) =
      (V ^ (1 - 2 / (k : ℝ)) * C ^ (2 / (k : ℝ))) * η ^ 2 *
        t ^ ((n : ℝ) - 2 * ((n : ℝ) / (k : ℝ))) := by
    rw [Real.mul_rpow hV (pow_nonneg ht.le n),
      Real.mul_rpow hC (pow_nonneg hη k), ← Real.rpow_natCast t n,
      ← Real.rpow_mul ht.le, ← Real.rpow_natCast η k, ← Real.rpow_mul hη]
    have hkcancel : (k : ℝ) * (2 / (k : ℝ)) = 2 := by field_simp
    have hncancel : (n : ℝ) * (1 - 2 / (k : ℝ)) =
        (n : ℝ) - 2 * ((n : ℝ) / (k : ℝ)) := by ring
    rw [hkcancel, Real.rpow_two, hncancel]
    ring
  rw [heq]
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge ht htOne (by linarith only [hfrac]))
  positivity

/-- Genuine critical Morrey control gives local L² value growth with any prescribed positive loss. -/
theorem exists_local_value_L2_bound_of_criticalMorrey (n : ℕ) (hn : 2 ≤ n)
    {δ : ℝ} (hδ : 0 < δ) (_hδOne : δ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      ∀ (x : Domain n) (t : ℝ), 0 < t → t ≤ 1 →
      MemLp (fun y => u y - (⨍ z in Metric.ball (0 : Domain n) 1, u z)) 2
        (volume.restrict (Metric.ball x t ∩ Metric.ball (0 : Domain n) (7 / 8 : ℝ))) ∧
      IntegrableOn (fun y => ‖u y - (⨍ z in Metric.ball (0 : Domain n) 1, u z)‖ ^ 2)
        (Metric.ball x t ∩ Metric.ball (0 : Domain n) (7 / 8 : ℝ)) volume ∧
      (∫ y in Metric.ball x t ∩ Metric.ball (0 : Domain n) (7 / 8 : ℝ),
        ‖u y - (⨍ z in Metric.ball (0 : Domain n) 1, u z)‖ ^ 2) ≤
        C * η ^ 2 * t ^ ((n : ℝ) - 2 * δ) := by
  obtain ⟨k, hkTwo, hfrac⟩ := exists_integer_exponent_for_local_value n hδ
  have hkpos : 0 < (k : ℝ) := lt_trans (by norm_num) hkTwo
  have hkNatTwo : 2 ≤ k := by exact_mod_cast hkTwo.le
  obtain ⟨D, hD, hmoment⟩ := exists_integer_moment_bound_of_criticalMorrey n hn k
    (by omega : 1 ≤ k)
  let V : ℝ := volume.real (Metric.ball (0 : Domain n) 1)
  have hV : 0 < V := HolderToCK.ball_volume_real_pos (0 : Domain n) (by norm_num)
  have hβ : 0 < 1 - 2 / (k : ℝ) := sub_pos.mpr
    ((div_lt_iff₀ hkpos).2 (by simpa only [one_mul] using hkTwo))
  have hγ : 0 < 2 / (k : ℝ) := div_pos (by norm_num) hkpos
  let C : ℝ := V ^ (1 - 2 / (k : ℝ)) * D ^ (2 / (k : ℝ))
  have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos hV _) (Real.rpow_pos_of_pos hD _)
  refine ⟨C, hC, ?_⟩
  intro q u Du η hu hη hcritical x t ht htOne
  let f (y : Domain n) := u y - (⨍ z in Metric.ball (0 : Domain n) 1, u z)
  let S : Set (Domain n) := Metric.ball x t ∩ Metric.ball (0 : Domain n) (7 / 8 : ℝ)
  let μ : Measure (Domain n) := volume.restrict S
  have hSinner : S ⊆ Metric.ball (0 : Domain n) (7 / 8 : ℝ) := inter_subset_right
  have hSball : S ⊆ Metric.ball x t := inter_subset_left
  have hSfinite : volume S ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hSball) measure_ball_lt_top).ne
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hSfinite
  obtain ⟨hm, hi, hb⟩ := hmoment q u Du η hu hη hcritical
  have hmS : MemLp f (k : ℝ≥0∞) μ :=
    hm.mono_measure (Measure.restrict_mono_set volume hSinner)
  have htwo : MemLp f 2 μ := hmS.mono_exponent (by exact_mod_cast hkNatTwo)
  have hI : (∫ y, ‖f y‖ ^ k ∂μ) ≤ D * η ^ k := by
    exact (setIntegral_mono_set hi
      (Filter.Eventually.of_forall fun y => pow_nonneg (norm_nonneg _) k)
      (Filter.Eventually.of_forall fun y hy => hSinner hy)).trans hb
  have hmass : μ.real univ ≤ V * t ^ n := by
    change (volume.restrict S).real univ ≤ _
    rw [measureReal_restrict_apply_univ]
    calc
      _ ≤ volume.real (Metric.ball x t) := ENNReal.toReal_mono measure_ball_ne_top
        (measure_mono hSball)
      _ = _ := by rw [HolderToCK.ball_volume_real x ht]; ring
  have hmReal : MemLp f (ENNReal.ofReal (k : ℝ)) μ := by
    simpa only [ENNReal.ofReal_natCast] using hmS
  have hforward := integral_norm_rpow_le_of_exponent_le (μ := μ) f
    (by norm_num : (0 : ℝ) < 2) hkTwo.le hmReal
  have hforwardNat : (∫ y, ‖f y‖ ^ 2 ∂μ) ≤
      (μ.real univ) ^ (1 - 2 / (k : ℝ)) * (∫ y, ‖f y‖ ^ k ∂μ) ^ (2 / (k : ℝ)) := by
    simpa only [Real.rpow_two, Real.rpow_natCast] using hforward
  have hIpos : 0 ≤ ∫ y, ‖f y‖ ^ k ∂μ := integral_nonneg fun y => pow_nonneg (norm_nonneg _) k
  have hmasspow := Real.rpow_le_rpow ENNReal.toReal_nonneg hmass hβ.le
  have hIpow := Real.rpow_le_rpow hIpos hI hγ.le
  refine ⟨htwo, htwo.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0), ?_⟩
  calc
    _ ≤ (μ.real univ) ^ (1 - 2 / (k : ℝ)) * (∫ y, ‖f y‖ ^ k ∂μ) ^ (2 / (k : ℝ)) :=
      hforwardNat
    _ ≤ (V * t ^ n) ^ (1 - 2 / (k : ℝ)) * (D * η ^ k) ^ (2 / (k : ℝ)) :=
      mul_le_mul hmasspow hIpow (Real.rpow_nonneg hIpos _)
        (Real.rpow_nonneg (by positivity) _)
    _ ≤ C * η ^ 2 * t ^ ((n : ℝ) - 2 * δ) :=
      local_value_moment_volume_scale hkpos hfrac.le hD.le hV.le hη ht htOne

end StationaryHarmonicMaps.Analysis

end
