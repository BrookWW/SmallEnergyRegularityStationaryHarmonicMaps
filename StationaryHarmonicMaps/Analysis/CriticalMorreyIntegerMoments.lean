module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyDistribution
public import StationaryHarmonicMaps.Analysis.EffectiveGeometricMoments
import StationaryHarmonicMaps.Analysis.EffectiveEuclideanVolume
public import StationaryHarmonicMaps.Analysis.ZeroEnergyRepresentative

/-!
# Genuine finite interior moments from critical Morrey gradient control

The actual Sobolev map supplies the mean, measurable data and geometric
distribution tails. Those proved tails give every positive integer moment.
The zero-amplitude case follows from the actual Sobolev Poincaré estimate.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

@[expose] def effectiveIntegerMomentConstant (n k : ℕ) : ℕ :=
  geometricMomentMajorant k * effectivePointwiseConstant n ^ k * (2 ^ n + 5 ^ n)

theorem effectiveIntegerMomentConstant_pos (n k : ℕ) :
    0 < (effectiveIntegerMomentConstant n k : ℝ) := by
  have H := effectivePointwiseConstant_pos n
  simp only [effectiveIntegerMomentConstant, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  have HK : 0 < (geometricMomentMajorant k : ℝ) := by
    simp only [geometricMomentMajorant, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat]
    positivity
  positivity

/-- Critical HS-gradient Morrey control gives every actual integer interior moment uniformly. -/
theorem effective_integer_moment_bound_of_criticalMorrey (n : ℕ) (hn : 2 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      MemLp (fun x => u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)) (k : ℝ≥0∞)
        (volume.restrict (Metric.ball (0 : Domain n) (7 / 8 : ℝ))) ∧
      IntegrableOn (fun x => ‖u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖ ^ k)
        (Metric.ball (0 : Domain n) (7 / 8 : ℝ)) volume ∧
      (∫ x in Metric.ball (0 : Domain n) (7 / 8 : ℝ),
        ‖u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖ ^ k) ≤ (effectiveIntegerMomentConstant n k : ℝ) * η ^ k := by
  let D : ℝ := effectivePointwiseConstant n
  have hD : 0 < D := effectivePointwiseConstant_pos n
  have htail := effective_distribution_tail_of_criticalMorrey n hn
  let K : ℝ := geometricMomentMajorant k
  let V : ℝ := volume.real (Metric.ball (0 : Domain n) (7 / 8 : ℝ))
  let M : ℝ := (5 : ℝ) ^ n
  let C : ℝ := effectiveIntegerMomentConstant n k
  have hM : 0 < M := by dsimp only [M]; positivity
  have hVle : V ≤ (2 : ℝ) ^ n :=
    (ENNReal.toReal_mono measure_ball_ne_top (measure_mono
      (Metric.ball_subset_ball (by norm_num : (7 / 8 : ℝ) ≤ 1)))).trans
      (euclidean_unit_ball_volume_upper_bound n)
  have hCle : K * D ^ k * (V + M) ≤ C := by
    have H := mul_le_mul_of_nonneg_left (add_le_add_right hVle M)
      (show 0 ≤ K * D ^ k by dsimp only [K]; positivity)
    dsimp only [C, K, D, M, effectiveIntegerMomentConstant]
    push_cast
    simpa only [K, D, M, add_comm] using H
  intro q u Du η hu hη hcritical
  let μ := volume.restrict (Metric.ball (0 : Domain n) (7 / 8 : ℝ))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let f (x : Domain n) := u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)
  have hsub : Metric.ball (0 : Domain n) (7 / 8 : ℝ) ⊆ Metric.ball (0 : Domain n) 1 :=
    Metric.ball_subset_ball (by norm_num)
  have hk0 : k ≠ 0 := (lt_of_lt_of_le Nat.zero_lt_one hk).ne'
  by_cases hη0 : η = 0
  · subst η
    have hz : criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤ 0 := by
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero] using hcritical
    have hEq := ae_eq_ballMean_of_zero_criticalMorrey (0 : Domain n)
      (by norm_num : (0 : ℝ) < 1) hu hz
    have hfzero : f =ᵐ[μ] (fun _ => 0) :=
      (ae_restrict_of_ae_restrict_of_subset hsub hEq).mono (fun x hx => sub_eq_zero.mpr hx)
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
        ENNReal.ofReal (M * (1 / 4 : ℝ) ^ m) := by
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
    obtain ⟨hm, hi, hb⟩ := geometric_tail_integer_moment_effective k hk (1 / 4)
      (by norm_num) (by norm_num) μ f hf (mul_pos hD hηpos) hM.le htailμ
    have hmass : μ.real univ = V := by
      rw [measureReal_restrict_apply_univ]
    refine ⟨hm, hi, ?_⟩
    calc
      _ ≤ K * (D * η) ^ k * (V + M) := by simpa only [hmass] using hb
      _ = (K * D ^ k * (V + M)) * η ^ k := by rw [mul_pow]; ring
      _ ≤ C * η ^ k := mul_le_mul_of_nonneg_right hCle (pow_nonneg hη k)

/-- Critical HS-gradient Morrey control gives every actual integer interior moment uniformly. -/
theorem exists_integer_moment_bound_of_criticalMorrey (n : ℕ) (hn : 2 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal (η ^ 2) →
      MemLp (fun x => u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)) (k : ℝ≥0∞)
        (volume.restrict (Metric.ball (0 : Domain n) (7 / 8 : ℝ))) ∧
      IntegrableOn (fun x => ‖u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖ ^ k)
        (Metric.ball (0 : Domain n) (7 / 8 : ℝ)) volume ∧
      (∫ x in Metric.ball (0 : Domain n) (7 / 8 : ℝ),
        ‖u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖ ^ k) ≤ C * η ^ k := by
  exact ⟨(effectiveIntegerMomentConstant n k : ℝ), effectiveIntegerMomentConstant_pos n k,
    effective_integer_moment_bound_of_criticalMorrey n hn k hk⟩

end StationaryHarmonicMaps.Analysis

end
