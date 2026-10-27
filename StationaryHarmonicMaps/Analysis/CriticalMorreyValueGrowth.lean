module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyLocalValueBound
public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegerMoments
import StationaryHarmonicMaps.Analysis.EffectiveEuclideanVolume

/-!
# All-radius value growth at the critical gradient scale

Small radii use the proved finite-moment local value bound. Large radii use
the actual second moment on the fixed interior ball. Both estimates concern
the original map minus its actual unit-ball mean.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

@[expose] def effectiveLocalValueConstant (n : ℕ) : ℕ :=
  (1 + 2 ^ n) * (1 + effectiveIntegerMomentConstant n (2 * n + 1))

@[expose] def effectiveAllRadiusValueConstant (n : ℕ) : ℕ :=
  effectiveLocalValueConstant n + effectiveIntegerMomentConstant n 2

theorem effectiveLocalValueConstant_pos (n : ℕ) :
    0 < (effectiveLocalValueConstant n : ℝ) := by
  simp only [effectiveLocalValueConstant, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_pow, Nat.cast_ofNat]
  positivity

theorem effectiveAllRadiusValueConstant_pos (n : ℕ) :
    0 < (effectiveAllRadiusValueConstant n : ℝ) := by
  simp only [effectiveAllRadiusValueConstant, Nat.cast_add]
  exact add_pos (effectiveLocalValueConstant_pos n) (effectiveIntegerMomentConstant_pos n 2)

private theorem rpow_le_one_add {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) (hsOne : s ≤ 1) :
    x ^ s ≤ 1 + x := by
  by_cases hOne : x ≤ 1
  · exact (Real.rpow_le_one hx hOne hs).trans (le_add_of_nonneg_right hx)
  · exact (Real.rpow_le_self_of_one_le (not_le.mp hOne).le hsOne).trans
      (le_add_of_nonneg_left zero_le_one)

/-- Genuine critical Morrey control gives local L² value growth with any prescribed positive loss. -/
theorem effective_local_value_L2_bound_of_criticalMorrey (n : ℕ) (hn : 2 ≤ n)
    :
    ∀ (q : ℕ) (u : Domain n → Ambient q)
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
        (effectiveLocalValueConstant n : ℝ) * η ^ 2 * t ^ ((n : ℝ) - 1) := by
  let k : ℕ := 2 * n + 1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hkTwo : (2 : ℝ) < k := by dsimp only [k]; push_cast; linarith
  have hfrac : (n : ℝ) / (k : ℝ) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (show 0 < (k : ℝ) by linarith only [hkTwo])).mpr
    dsimp only [k]
    push_cast
    linarith
  have hkpos : 0 < (k : ℝ) := lt_trans (by norm_num) hkTwo
  have hkNatTwo : 2 ≤ k := by exact_mod_cast hkTwo.le
  let D : ℝ := effectiveIntegerMomentConstant n k
  have hD : 0 < D := effectiveIntegerMomentConstant_pos n k
  have hmoment := effective_integer_moment_bound_of_criticalMorrey n hn k
    (by omega : 1 ≤ k)
  let V : ℝ := volume.real (Metric.ball (0 : Domain n) 1)
  have hV : 0 < V := HolderToCK.ball_volume_real_pos (0 : Domain n) (by norm_num)
  have hβ : 0 < 1 - 2 / (k : ℝ) := sub_pos.mpr
    ((div_lt_iff₀ hkpos).2 (by simpa only [one_mul] using hkTwo))
  have hγ : 0 < 2 / (k : ℝ) := div_pos (by norm_num) hkpos
  let C : ℝ := V ^ (1 - 2 / (k : ℝ)) * D ^ (2 / (k : ℝ))
  have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos hV _) (Real.rpow_pos_of_pos hD _)
  have hCeff : C ≤ (effectiveLocalValueConstant n : ℝ) := by
    have hβOne : 1 - 2 / (k : ℝ) ≤ 1 := by linarith only [hγ]
    have hγOne : 2 / (k : ℝ) ≤ 1 := by linarith only [hβ]
    have hfirst := (rpow_le_one_add hV.le hβ.le hβOne).trans
      (add_le_add_right (euclidean_unit_ball_volume_upper_bound n) 1)
    have hsecond := rpow_le_one_add hD.le hγ.le hγOne
    have H := mul_le_mul hfirst hsecond (Real.rpow_nonneg hD.le _)
      (show 0 ≤ 1 + (2 : ℝ) ^ n by positivity)
    dsimp only [C, D, k, effectiveLocalValueConstant]
    push_cast
    simpa only [D, k, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using H
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
    _ ≤ C * η ^ 2 * t ^ ((n : ℝ) - 2 * (1 / 2)) :=
      local_value_moment_volume_scale hkpos hfrac.le hD.le hV.le hη ht htOne
    _ ≤ (effectiveLocalValueConstant n : ℝ) * η ^ 2 * t ^ ((n : ℝ) - 1) := by
      norm_num only [mul_one_div, div_self (by norm_num : (2 : ℝ) ≠ 0)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCeff (sq_nonneg η)) (Real.rpow_nonneg ht.le _)

/-- The interior value field has actual L² growth at every positive critical radius. -/
theorem effective_all_radius_value_growth_of_criticalMorrey (n : ℕ) (hn : 2 ≤ n) :
    ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      ∀ (x : Domain n) (r : ℝ), 0 < r →
      MemLp (fun y => u y - (⨍ z in Metric.ball (0 : Domain n) 1, u z)) 2
        (volume.restrict (Metric.ball x r ∩ Metric.ball (0 : Domain n) (7 / 8 : ℝ))) ∧
      IntegrableOn (fun y => ‖u y - (⨍ z in Metric.ball (0 : Domain n) 1, u z)‖ ^ 2)
        (Metric.ball x r ∩ Metric.ball (0 : Domain n) (7 / 8 : ℝ)) volume ∧
      (∫ y in Metric.ball x r ∩ Metric.ball (0 : Domain n) (7 / 8 : ℝ),
        ‖u y - (⨍ z in Metric.ball (0 : Domain n) 1, u z)‖ ^ 2) ≤ (effectiveAllRadiusValueConstant n : ℝ) * η ^ 2 * r ^ ((n : ℝ) - 2) := by
  let L : ℝ := effectiveLocalValueConstant n
  have hL : 0 < L := effectiveLocalValueConstant_pos n
  have hlocal := effective_local_value_L2_bound_of_criticalMorrey n hn
  let G : ℝ := effectiveIntegerMomentConstant n 2
  have hG : 0 < G := effectiveIntegerMomentConstant_pos n 2
  have hglobal := effective_integer_moment_bound_of_criticalMorrey n hn 2 (by norm_num)
  let C := L + G
  have hC : 0 < C := add_pos hL hG
  have hLC : L ≤ C := le_add_of_nonneg_right hG.le
  have hGC : G ≤ C := le_add_of_nonneg_left hL.le
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  change ∀ q u Du η, _
  have heff : (effectiveAllRadiusValueConstant n : ℝ) = C := by
    simp only [effectiveAllRadiusValueConstant, Nat.cast_add, C, L, G]
  rw [heff]
  intro q u Du η hu hη hcritical x r hr
  by_cases hsmall : r ≤ 1
  · obtain ⟨hm, hi, hb⟩ := hlocal q u Du η hu hη hcritical x r hr hsmall
    refine ⟨hm, hi, ?_⟩
    calc
      _ ≤ L * η ^ 2 * r ^ ((n : ℝ) - 1) := hb
      _ ≤ L * η ^ 2 * r ^ ((n : ℝ) - 2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hr hsmall (by linarith)) (mul_nonneg hL.le (sq_nonneg η))
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLC (sq_nonneg η)) (Real.rpow_nonneg hr.le _)
  · have hrOne : 1 ≤ r := le_of_lt (lt_of_not_ge hsmall)
    obtain ⟨hm, hi, hb⟩ := hglobal q u Du η hu hη hcritical
    have hmeasure := Measure.restrict_mono_set volume
      (inter_subset_right : Metric.ball x r ∩ Metric.ball (0 : Domain n) (7 / 8 : ℝ) ⊆ _)
    have hmS := hm.mono_measure hmeasure
    have hpow : 1 ≤ r ^ ((n : ℝ) - 2) := Real.one_le_rpow hrOne (sub_nonneg.mpr hnR)
    refine ⟨hmS, hmS.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0), ?_⟩
    calc
      _ ≤ ∫ y in Metric.ball (0 : Domain n) (7 / 8 : ℝ),
          ‖u y - (⨍ z in Metric.ball (0 : Domain n) 1, u z)‖ ^ 2 :=
        setIntegral_mono_set hi (Eventually.of_forall fun y => sq_nonneg _)
          (Eventually.of_forall fun y hy => hy.2)
      _ ≤ G * η ^ 2 := hb
      _ ≤ G * η ^ 2 * r ^ ((n : ℝ) - 2) := le_mul_of_one_le_right
        (mul_nonneg hG.le (sq_nonneg η)) hpow
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hGC (sq_nonneg η)) (Real.rpow_nonneg hr.le _)

/-- The interior value field has actual L² growth at every positive critical radius. -/
theorem exists_all_radius_value_growth_of_criticalMorrey (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      ∀ (x : Domain n) (r : ℝ), 0 < r →
      MemLp (fun y => u y - (⨍ z in Metric.ball (0 : Domain n) 1, u z)) 2
        (volume.restrict (Metric.ball x r ∩ Metric.ball (0 : Domain n) (7 / 8 : ℝ))) ∧
      IntegrableOn (fun y => ‖u y - (⨍ z in Metric.ball (0 : Domain n) 1, u z)‖ ^ 2)
        (Metric.ball x r ∩ Metric.ball (0 : Domain n) (7 / 8 : ℝ)) volume ∧
      (∫ y in Metric.ball x r ∩ Metric.ball (0 : Domain n) (7 / 8 : ℝ),
        ‖u y - (⨍ z in Metric.ball (0 : Domain n) 1, u z)‖ ^ 2) ≤ C * η ^ 2 * r ^ ((n : ℝ) - 2) := by
  exact ⟨(effectiveAllRadiusValueConstant n : ℝ), effectiveAllRadiusValueConstant_pos n,
    effective_all_radius_value_growth_of_criticalMorrey n hn⟩

end StationaryHarmonicMaps.Analysis

end
