module

public import HarmonicMaps.Analysis.SobolevPoincare
public import HarmonicMaps.SobolevRestriction
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

/-! # Ball oscillation and comparison of genuine Bochner means -/

public section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace HarmonicMaps

/-- Euclidean positive-radius ball mass, with the exact dimension exponent. -/
theorem morrey_ball_volume {n : ℕ} (x : Domain n) {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.ball x r) = r ^ n * volume.real (Metric.ball (0 : Domain n) 1) := by
  rw [measureReal_def, Measure.addHaar_ball_of_pos volume x hr, ENNReal.toReal_mul]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [ENNReal.toReal_ofReal (pow_nonneg hr.le n)]
  rfl

/-- The balls used in the inner-ball Morrey hypothesis lie in the original unit ball. -/
theorem morrey_ball_subset_unit {n : ℕ} {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2)) {r : ℝ} (hr : r ≤ 1 / 2) :
    Metric.ball x r ⊆ Metric.ball (0 : Domain n) 1 := by
  intro y hy
  have hxy : dist y x < r := hy
  have hx0 : dist x 0 < (1 / 2 : ℝ) := hx
  change dist y 0 < 1
  exact lt_of_le_of_lt (dist_triangle y x 0) (by linarith only [hxy, hx0, hr])

/-- Accepted Poincare and the original HS growth bound give the actual mean oscillation. -/
theorem MemW12.morrey_ball_oscillation {n q : ℕ} {f : Domain n → Ambient q}
    {Df : Domain n → Gradient n q} (hf : MemW12 (ballDomain 0 1) f Df)
    {α M : ℝ} {x : Domain n} (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2))
    {r : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hgrowth : (∫ y in Metric.ball x r, hsNormSq (Df y)) ≤
      M * Real.rpow r ((n : ℝ) - 2 + 2 * α)) :
    (∫ y in Metric.ball x r, ‖f y - ⨍ z in Metric.ball x r, f z‖ ^ 2) ≤
      (2 : ℝ) ^ (n + 1) * M * Real.rpow r ((n : ℝ) + 2 * α) := by
  have hfball : MemW12 (ballDomain x r) f Df :=
    ⟨hf.1.mono (morrey_ball_subset_unit hx hrhalf),
      hf.2.1.mono_measure (Measure.restrict_mono_set volume (morrey_ball_subset_unit hx hrhalf)),
      fun i => (hf.2.2 i).mono_measure
        (Measure.restrict_mono_set volume (morrey_ball_subset_unit hx hrhalf))⟩
  have hp := hfball.poincare_ball hr
  have heq : r ^ 2 * Real.rpow r ((n : ℝ) - 2 + 2 * α) =
      Real.rpow r ((n : ℝ) + 2 * α) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr]
    congr 1
    ring
  calc
    _ ≤ (2 : ℝ) ^ (n + 1) * r ^ 2 *
        (M * Real.rpow r ((n : ℝ) - 2 + 2 * α)) :=
      hp.trans (mul_le_mul_of_nonneg_left hgrowth (by positivity))
    _ = _ := by rw [← mul_assoc, mul_right_comm _ (r ^ 2) M, mul_assoc, heq]

/-- A mean on a contained ball is controlled by the larger ball's quadratic oscillation. -/
theorem ballAverage_sub_sq_le_oscillation {n q : ℕ}
    {f : Domain n → Ambient q} {a b : Domain n} {r R : ℝ}
    (hr : 0 < r) (hsub : Metric.ball a r ⊆ Metric.ball b R)
    (hf : MemLp f 2 (volume.restrict (Metric.ball b R))) :
    ‖(⨍ y in Metric.ball a r, f y) - (⨍ y in Metric.ball b R, f y)‖ ^ 2 ≤
      (volume.real (Metric.ball a r))⁻¹ *
        ∫ y in Metric.ball b R, ‖f y - (⨍ z in Metric.ball b R, f z)‖ ^ 2 := by
  let μ := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hμne : μ ≠ 0 := by
    intro hz
    have hpos := Metric.measure_ball_pos volume a hr
    have hz' : volume (Metric.ball a r) = 0 := by
      simpa only [μ, Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using
        congrArg (fun ν => ν univ) hz
    exact hpos.ne' hz'
  letI : NeZero μ := ⟨hμne⟩
  let m : Ambient q := ⨍ z in Metric.ball b R, f z
  have hfg : MemLp (fun y => f y - m) 2 (volume.restrict (Metric.ball b R)) := by
    letI : IsFiniteMeasure (volume.restrict (Metric.ball b R)) :=
      isFiniteMeasure_restrict.mpr measure_ball_ne_top
    exact hf.sub (memLp_const m)
  have hsmall : MemLp f 2 μ := hf.mono_measure (Measure.restrict_mono_set volume hsub)
  have hsmallg : MemLp (fun y => f y - m) 2 μ := hsmall.sub (memLp_const m)
  have hbigI : IntegrableOn (fun y => ‖f y - m‖ ^ 2) (Metric.ball b R) volume :=
    (memLp_two_iff_integrable_sq_norm hfg.aestronglyMeasurable).mp hfg
  have hsmallI : Integrable (fun y => ‖f y - m‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hsmallg.aestronglyMeasurable).mp hsmallg
  have hc : ConvexOn ℝ Set.univ (fun v : Ambient q => ‖v‖ ^ 2) :=
    (convexOn_univ_norm (E := Ambient q)).pow (fun _ _ => norm_nonneg _) 2
  have hj := hc.map_average_le (continuous_norm.pow 2).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    (hsmallg.integrable (by norm_num)) hsmallI
  have hmean : (⨍ y, f y - m ∂μ) = (⨍ y, f y ∂μ) - m := by
    rw [average_eq, integral_sub (hsmall.integrable (by norm_num)) (integrable_const m),
      smul_sub]
    rw [← average_eq, ← average_eq, average_const]
  rw [hmean] at hj
  change _ ≤ ⨍ y in Metric.ball a r, ‖f y - m‖ ^ 2 at hj
  rw [setAverage_eq volume (fun y => ‖f y - m‖ ^ 2), smul_eq_mul] at hj
  have hmono := setIntegral_mono_set hbigI
    (Filter.Eventually.of_forall fun y => sq_nonneg ‖f y - m‖)
    (Filter.Eventually.of_forall fun y => hsub (a := y))
  exact hj.trans (mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr ENNReal.toReal_nonneg))

/-- Comparable contained-ball means have a dimension-only quantitative bound. -/
theorem MemW12.morrey_ballAverage_compare {n q : ℕ}
    {f : Domain n → Ambient q} {Df : Domain n → Gradient n q}
    (hf : MemW12 (ballDomain 0 1) f Df) {α M c : ℝ} (hM : 0 ≤ M)
    (hc : 0 ≤ c) {a b : Domain n} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hb : b ∈ Metric.ball (0 : Domain n) (1 / 2)) (hRhalf : R ≤ 1 / 2)
    (hsub : Metric.ball a r ⊆ Metric.ball b R) (hratio : R ≤ c * r)
    (hgrowth : (∫ y in Metric.ball b R, hsNormSq (Df y)) ≤
      M * Real.rpow R ((n : ℝ) - 2 + 2 * α)) :
    ‖(⨍ y in Metric.ball a r, f y) - (⨍ y in Metric.ball b R, f y)‖ ≤
      Real.sqrt ((2 : ℝ) ^ (n + 1) * c ^ n /
        volume.real (Metric.ball (0 : Domain n) 1)) * Real.sqrt M * Real.rpow R α := by
  simp only [Real.rpow_eq_pow] at *
  let V := volume.real (Metric.ball (0 : Domain n) 1)
  let P : ℝ := (2 : ℝ) ^ (n + 1)
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume (0 : Domain n) (by norm_num : (0 : ℝ) < 1)).ne'
    measure_ball_ne_top
  have hρ : 0 < r ^ n * V := mul_pos (pow_pos hr _) hV
  have hLf : MemLp f 2 (volume.restrict (Metric.ball b R)) :=
    hf.2.1.mono_measure (Measure.restrict_mono_set volume (morrey_ball_subset_unit hb hRhalf))
  have hdiff := ballAverage_sub_sq_le_oscillation hr hsub hLf
  have hosc := hf.morrey_ball_oscillation hb hR hRhalf hgrowth
  have hsq : r ^ n * V *
      ‖(⨍ y in Metric.ball a r, f y) - (⨍ y in Metric.ball b R, f y)‖ ^ 2 ≤
      P * M * Real.rpow R ((n : ℝ) + 2 * α) := by
    rw [morrey_ball_volume a hr] at hdiff
    have hz := mul_le_mul_of_nonneg_left hdiff hρ.le
    rw [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul] at hz
    exact hz.trans hosc
  simp only [Real.rpow_eq_pow] at hsq
  have hpow : R ^ n ≤ c ^ n * r ^ n := by
    simpa only [mul_pow] using pow_le_pow_left₀ hR.le hratio n
  have hsplit : R ^ ((n : ℝ) + 2 * α) = R ^ n * (R ^ α) ^ 2 := by
    rw [Real.rpow_add hR, Real.rpow_natCast, mul_comm (2 : ℝ) α,
      Real.rpow_mul hR.le, Real.rpow_two]
  have hnon : 0 ≤ P * M * (R ^ α) ^ 2 := by positivity
  have hpow' := mul_le_mul_of_nonneg_right hpow hnon
  let B : ℝ := Real.sqrt (P * c ^ n / V) * Real.sqrt M * R ^ α
  have hB : 0 ≤ B := by positivity
  have hBsq : B ^ 2 = P * c ^ n / V * M * (R ^ α) ^ 2 := by
    dsimp only [B]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hM]
  have heq : r ^ n * V * B ^ 2 = (c ^ n * r ^ n) *
      (P * M * (R ^ α) ^ 2) := by
    rw [hBsq]
    field_simp [hV.ne']
  have hsqB :
      ‖(⨍ y in Metric.ball a r, f y) - (⨍ y in Metric.ball b R, f y)‖ ^ 2 ≤ B ^ 2 := by
    apply (mul_le_mul_iff_right₀ hρ).mp
    rw [heq]
    rw [hsplit] at hsq
    calc
      _ ≤ P * M * (R ^ n * (R ^ α) ^ 2) := hsq
      _ = R ^ n * (P * M * (R ^ α) ^ 2) := by ring
      _ ≤ _ := hpow'
  exact (sq_le_sq₀ (norm_nonneg _) hB).mp hsqB

end HarmonicMaps
