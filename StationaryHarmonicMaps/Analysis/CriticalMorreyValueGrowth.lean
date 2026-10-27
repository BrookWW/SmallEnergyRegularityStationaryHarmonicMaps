module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyLocalValueBound

/-!
# All-radius value growth at the critical gradient scale

Small radii use the proved finite-moment local value bound. Large radii use
the actual second moment on the fixed interior ball. Both estimates concern
the original map minus its actual unit-ball mean.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

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
  obtain ⟨L, hL, hlocal⟩ := exists_local_value_L2_bound_of_criticalMorrey n hn
    (δ := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨G, hG, hglobal⟩ := exists_integer_moment_bound_of_criticalMorrey n hn 2 (by norm_num)
  let C := L + G
  have hC : 0 < C := add_pos hL hG
  have hLC : L ≤ C := le_add_of_nonneg_right hG.le
  have hGC : G ≤ C := le_add_of_nonneg_left hL.le
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨C, hC, ?_⟩
  intro q u Du η hu hη hcritical x r hr
  by_cases hsmall : r ≤ 1
  · obtain ⟨hm, hi, hb⟩ := hlocal q u Du η hu hη hcritical x r hr hsmall
    refine ⟨hm, hi, ?_⟩
    calc
      _ ≤ L * η ^ 2 * r ^ ((n : ℝ) - 2 * (1 / 2)) := hb
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

end StationaryHarmonicMaps.Analysis

end
