module

public import StationaryHarmonicMaps.Analysis.CriticalLpMorreyDistribution
public import StationaryHarmonicMaps.Analysis.GeometricTailLp
public import StationaryHarmonicMaps.Analysis.CriticalLpMorreyDyadicMeans

/-!
# Genuine finite moments from lower-power critical gradient growth

The original native map and its displayed critical Lp gradient growth
supply the mean, measurable data and geometric value tails. The zero
amplitude follows from the actual forward Lp Poincare estimate.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual critical Lp gradient growth gives every positive integer
interior value moment, with the same amplitude and target-uniform constant. -/
theorem exists_integer_moment_bound_of_criticalLp_growth (n : ℕ)
    (p : ℝ) (hpOne : 1≤p) (hpTwo : p≤2) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ η →
      (∀a∈Metric.ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫y in Metric.ball a r∩Metric.ball (0 : Domain n) 1,(Real.sqrt (hsNormSq (Du y)))^p)≤
          η^p*r^((n : ℝ)-p)) →
      MemLp (fun x => u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)) (k : ℝ≥0∞)
        (volume.restrict (Metric.ball (0 : Domain n) (7 / 8 : ℝ))) ∧
      IntegrableOn (fun x => ‖u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖ ^ k)
        (Metric.ball (0 : Domain n) (7 / 8 : ℝ)) volume ∧
      (∫ x in Metric.ball (0 : Domain n) (7 / 8 : ℝ),
        ‖u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖ ^ k) ≤ C * η ^ k := by
  have hp : 0<p := zero_lt_one.trans_le hpOne
  let ρ := (1/2 : ℝ)^p
  have hρ : 0<ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρOne : ρ<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  obtain ⟨D,hD,htail⟩ := exists_distribution_tail_of_criticalLp_growth n p hpOne hpTwo
  obtain ⟨K,hK,hmoment⟩ := geometric_tail_integer_moment k hk ρ hρ hρOne
  let V : ℝ := volume.real (Metric.ball (0 : Domain n) (7 / 8 : ℝ))
  let M : ℝ := (5 : ℝ) ^ n
  let C : ℝ := K * D ^ k * (V + M)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hM : 0 < M := by dsimp only [M]; positivity
  have hC : 0 < C := mul_pos (mul_pos hK (pow_pos hD k)) (add_pos_of_nonneg_of_pos hV hM)
  refine ⟨C, hC, ?_⟩
  intro q u Du η hu hη hcritical
  let μ := volume.restrict (Metric.ball (0 : Domain n) (7 / 8 : ℝ))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let f (x : Domain n) := u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)
  have hsub : Metric.ball (0 : Domain n) (7 / 8 : ℝ) ⊆ Metric.ball (0 : Domain n) 1 :=
    Metric.ball_subset_ball (by norm_num)
  have hk0 : k ≠ 0 := (lt_of_lt_of_le Nat.zero_lt_one hk).ne'
  by_cases hη0 : η = 0
  · subst η
    let ν := volume.restrict (Metric.ball (0 : Domain n) 1)
    letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_ball_ne_top
    have hULp : MemLp u 2 ν := hu.2.1
    have hMean := meanOscillation_le_of_criticalLp_growth p hpOne hpTwo u Du 0 hu
      (by norm_num) hcritical (0 : Domain n) 1 (by norm_num) (Subset.refl _)
    have hNormI : Integrable (fun x=>‖u x-(⨍y in Metric.ball (0 : Domain n) 1,u y)‖) ν :=
      ((hULp.integrable (by norm_num)).sub (integrable_const _)).norm
    have hAverageZero : (⨍x in Metric.ball (0 : Domain n) 1,
        ‖u x-(⨍y in Metric.ball (0 : Domain n) 1,u y)‖)=0 := by
      apply le_antisymm
      · simpa only [mul_zero] using hMean
      · exact integral_nonneg fun _=>norm_nonneg _
    rw [setAverage_eq,smul_eq_mul] at hAverageZero
    have hVolume : 0<volume.real (Metric.ball (0 : Domain n) 1) :=
      HolderToCK.ball_volume_real_pos _ (by norm_num)
    have hIntegralZero := (mul_eq_zero.mp hAverageZero).resolve_left (inv_ne_zero hVolume.ne')
    have hAE := (integral_eq_zero_iff_of_nonneg (fun _=>norm_nonneg _) hNormI).mp hIntegralZero
    have hfzero : f=ᵐ[μ](fun _=>0) := by
      filter_upwards [hAE.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub))] with x hx
      exact norm_eq_zero.mp hx
    have hmem : MemLp f (k : ℝ≥0∞) μ := MemLp.ae_eq hfzero.symm MemLp.zero'
    have hnorm : (fun x => ‖f x‖ ^ k) =ᵐ[μ] (fun _ => (0 : ℝ)) := by
      filter_upwards [hfzero] with x hx
      rw [hx, norm_zero, zero_pow hk0]
    have hInt : Integrable (fun x => ‖f x‖ ^ k) μ :=
      (integrable_zero _ _ _).congr hnorm.symm
    refine ⟨hmem, hInt, ?_⟩
    rw [integral_congr_ae hnorm, integral_zero, zero_pow hk0, mul_zero]
  · have hηpos : 0 < η := lt_of_le_of_ne hη (Ne.symm hη0)
    have hum : AEStronglyMeasurable u μ :=
      hu.2.1.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume hsub)
    have hf : AEStronglyMeasurable f μ := hum.sub aestronglyMeasurable_const
    have htailμ (m : ℕ) : μ {x | (D * η) * ((m : ℝ) + 1) < ‖f x‖} ≤
        ENNReal.ofReal (M * ρ ^ m) := by
      change (volume.restrict (Metric.ball (0 : Domain n) (7 / 8 : ℝ)))
        {x | (D * η) * ((m : ℝ) + 1) < ‖f x‖} ≤ _
      rw [Measure.restrict_apply' measurableSet_ball]
      have hset : {x | (D * η) * ((m : ℝ) + 1) < ‖f x‖} ∩
          Metric.ball (0 : Domain n) (7 / 8 : ℝ) =
          {x | x ∈ Metric.ball (0 : Domain n) (7 / 8 : ℝ) ∧
            D * η * ((m : ℝ) + 1) < ‖f x‖} := by
        ext x
        exact and_comm
      rw [hset]
      exact htail q u Du η hu hηpos hcritical m
    obtain ⟨hm, hi, hb⟩ := hmoment μ f hf (mul_pos hD hηpos) hM.le htailμ
    have hmass : μ.real univ = V := by
      rw [measureReal_restrict_apply_univ]
    refine ⟨hm, hi, ?_⟩
    exact hb.trans_eq (by rw [hmass, mul_pow]; dsimp only [C]; ring)

end StationaryHarmonicMaps.Analysis

end
