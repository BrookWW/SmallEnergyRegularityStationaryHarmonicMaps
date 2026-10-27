module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyPointwise
public import StationaryHarmonicMaps.Analysis.InteriorAverageDifferentiation
public import StationaryHarmonicMaps.Analysis.BallSuperlevelMeasure
public import StationaryHarmonicMaps.Analysis.AffineMorreyScaling

/-!
# Geometric distribution tails from the actual critical Morrey energy

Almost-everywhere differentiation supplies the original map values. A tail
point then has an actual ball with large energy average. The centered weak
measure bound controls these balls using the zero-extended energy field.
The indicator field is only an energy field, with no Sobolev extension claim.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem dyadic_energy_level_ratio (n m : ℕ) {η : ℝ} (hη : 0 < η) :
    ((5 : ℝ) ^ n / (16 * η * (2 : ℝ) ^ m) ^ 2) * η ^ 2 ≤
      (5 : ℝ) ^ n * (1 / 4 : ℝ) ^ m := by
  let L : ℝ := (16 * η * (2 : ℝ) ^ m) ^ 2
  have hL : 0 < L := by dsimp only [L]; positivity
  have hpow : (1 / 4 : ℝ) ^ m * ((2 : ℝ) ^ m) ^ 2 = 1 := by
    have htwo : ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
      rw [← pow_mul, Nat.mul_comm m 2, pow_mul]
      norm_num
    rw [htwo, ← mul_pow]
    norm_num
  have hprod : L * (1 / 4 : ℝ) ^ m = 256 * η ^ 2 := by
    calc
      _ = 256 * η ^ 2 * ((1 / 4 : ℝ) ^ m * ((2 : ℝ) ^ m) ^ 2) := by
        dsimp only [L]
        ring
      _ = _ := by rw [hpow, mul_one]
  have hscale : η ^ 2 ≤ L * (1 / 4 : ℝ) ^ m := by
    rw [hprod]
    nlinarith only [sq_nonneg η]
  change ((5 : ℝ) ^ n / L) * η ^ 2 ≤ _
  calc
    _ ≤ ((5 : ℝ) ^ n / L) * (L * (1 / 4 : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = (5 : ℝ) ^ n * (L⁻¹ * L) * (1 / 4 : ℝ) ^ m := by ring
    _ = _ := by rw [inv_mul_cancel₀ hL.ne', mul_one]

/-- The same Sobolev map has a geometric outer-measure tail on the strict interior ball. -/
theorem effective_distribution_tail_of_criticalMorrey (n : ℕ) (hn : 2 ≤ n) :
    ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 < η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤
        ENNReal.ofReal (η ^ 2) → ∀ m : ℕ,
      volume {x | x ∈ Metric.ball (0 : Domain n) (7 / 8 : ℝ) ∧
        (effectivePointwiseConstant n : ℝ) * η * ((m : ℝ) + 1) <
          ‖u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖} ≤
        ENNReal.ofReal ((5 : ℝ) ^ n * (1 / 4 : ℝ) ^ m) := by
  classical
  let C : ℝ := effectivePointwiseConstant n
  have hpoint := effective_pointwise_bound_of_criticalMorrey n hn
  intro q u Du η hu hη hcritical m
  let B : Set (Domain n) := Metric.ball (0 : Domain n) 1
  let F : Domain n → Gradient n q := B.indicator Du
  let f : Domain n → ℝ≥0∞ := fun y => ENNReal.ofReal (hsNormSq (F y))
  let L : ℝ := (16 * η * (2 : ℝ) ^ m) ^ 2
  have hL : 0 < L := by dsimp only [L]; positivity
  let S : Set (Domain n) := {x | ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 16 ∧
    ENNReal.ofReal L * volume (Metric.ball x r) ≤ ∫⁻ y in Metric.ball x r, f y}
  have hSmeasure : volume S ≤ ENNReal.ofReal ((5 : ℝ) ^ n / L) * ∫⁻ y, f y :=
    centered_ball_superlevel_measure_le f S (1 / 16) L hL (fun _ hx => hx)
  have hunit : dirichletEnergy Du B ≤ ENNReal.ofReal (η ^ 2) := by
    have hterm := normalizedEnergy_le_criticalMorrey_of_ball_subset Du
      (x := (0 : Domain n)) (r := 1) (by norm_num) (Subset.refl B)
    have henergy : dirichletEnergy Du B ≤ criticalGradientMorreySquare Du B := by
      simpa only [normalizedEnergy, one_zpow, ENNReal.ofReal_one, one_mul] using hterm
    exact henergy.trans hcritical
  have htotal : (∫⁻ y, f y) ≤ ENNReal.ofReal (η ^ 2) := by
    have hfield := dirichletEnergy_indicator_eq_inter Du (D := B) measurableSet_ball univ
    have heq : dirichletEnergy F univ = dirichletEnergy Du B := by
      simpa only [F, B, univ_inter] using hfield
    simpa only [dirichletEnergy, Measure.restrict_univ] using heq.le.trans hunit
  letI : IsFiniteMeasure (volume.restrict (ballDomain (0 : Domain n) 1).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hLDT := integrableOn_ae_tendsto_ballAverage_interior u (0 : Domain n)
    (s := (7 / 8 : ℝ)) (by norm_num : (0 : ℝ) < 1) (by norm_num)
    (hu.2.1.integrable (by norm_num))
  have htail : volume {x | x ∈ Metric.ball (0 : Domain n) (7 / 8 : ℝ) ∧
      C * η * ((m : ℝ) + 1) <
        ‖u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖} ≤ volume S := by
    apply measure_mono_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hLDT] with x hx
    intro hxtail
    have hLebesgue : Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, u y)
        (𝓝[>] (0 : ℝ)) (𝓝 (u x)) := by
      simpa only [setAverage_eq, measureReal_def] using hx hxtail.1
    have hnot : ¬ (∀ r : ℝ, 0 < r → r ≤ 1 / 16 →
        (∫ y in Metric.ball x r, hsNormSq (Du y)) ≤ L * volume.real (Metric.ball x r)) := by
      intro henergy
      exact (not_le_of_gt hxtail.2)
        (hpoint q u Du η hu hη.le hcritical x hxtail.1 hLebesgue m henergy)
    push Not at hnot
    obtain ⟨r, hr, hrcap, hbad⟩ := hnot
    refine ⟨r, hr, hrcap, ?_⟩
    have hsub : Metric.ball x r ⊆ B := by
      intro y hy
      have hdist := dist_triangle y x (0 : Domain n)
      have hyx : dist y x < r := hy
      have hx0 : dist x 0 < (7 / 8 : ℝ) := hxtail.1
      change dist y 0 < 1
      linarith
    have henergyI : IntegrableOn (fun y => hsNormSq (Du y)) (Metric.ball x r) volume :=
      hu.integrable_hsNormSq.mono_set hsub
    have henergyEq : (∫⁻ y in Metric.ball x r, f y) =
        ENNReal.ofReal (∫ y in Metric.ball x r, hsNormSq (Du y)) := by
      change dirichletEnergy F (Metric.ball x r) = _
      rw [dirichletEnergy_indicator_eq_inter Du measurableSet_ball,
        inter_eq_left.mpr hsub, dirichletEnergy_eq_ofReal_integral henergyI]
    have hprod : ENNReal.ofReal L * volume (Metric.ball x r) =
        ENNReal.ofReal (L * volume.real (Metric.ball x r)) := by
      rw [ENNReal.ofReal_mul hL.le, measureReal_def,
        ENNReal.ofReal_toReal measure_ball_ne_top]
    rw [hprod, henergyEq]
    exact ENNReal.ofReal_le_ofReal hbad.le
  calc
    _ ≤ volume S := htail
    _ ≤ ENNReal.ofReal ((5 : ℝ) ^ n / L) * ∫⁻ y, f y := hSmeasure
    _ ≤ ENNReal.ofReal ((5 : ℝ) ^ n / L) * ENNReal.ofReal (η ^ 2) :=
      mul_le_mul_right htotal _
    _ = ENNReal.ofReal (((5 : ℝ) ^ n / L) * η ^ 2) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (dyadic_energy_level_ratio n m hη)

/-- The same Sobolev map has a geometric outer-measure tail on the strict interior ball. -/
theorem exists_distribution_tail_of_criticalMorrey (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (u : Domain n → Ambient q)
      (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 < η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1) ≤
        ENNReal.ofReal (η ^ 2) → ∀ m : ℕ,
      volume {x | x ∈ Metric.ball (0 : Domain n) (7 / 8 : ℝ) ∧
        C * η * ((m : ℝ) + 1) <
          ‖u x - (⨍ y in Metric.ball (0 : Domain n) 1, u y)‖} ≤
        ENNReal.ofReal ((5 : ℝ) ^ n * (1 / 4 : ℝ) ^ m) := by
  exact ⟨(effectivePointwiseConstant n : ℝ), effectivePointwiseConstant_pos n,
    effective_distribution_tail_of_criticalMorrey n hn⟩

end StationaryHarmonicMaps.Analysis

end
