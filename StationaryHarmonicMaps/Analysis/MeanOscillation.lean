module

public import HarmonicMaps.Analysis.MorreyGeometricMeans
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Literal means controlled by mean oscillation

The contained-set and contained-ball estimates use Bochner averages and L¹
mean oscillation. Comparable-radius estimates then feed the existing metric
geometric-limit theorem. No gradient estimate or Sobolev Poincaré inequality is
assumed to have been proved by these results.
-/

public section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps

section GeneralMeasure

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} {s t : Set X}

/-- The difference of contained-set means is bounded by the larger oscillation. -/
theorem norm_setAverage_sub_le_integral_oscillation (f : X → E)
    (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (ht : μ t ≠ ∞)
    (hst : s ⊆ t) (hf : IntegrableOn f t μ) :
    ‖(⨍ y in s, f y ∂μ) - (⨍ y in t, f y ∂μ)‖ ≤
      (μ.real s)⁻¹ * ∫ y in t, ‖f y - (⨍ z in t, f z ∂μ)‖ ∂μ := by
  letI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.mpr hs
  letI : IsFiniteMeasure (μ.restrict t) := isFiniteMeasure_restrict.mpr ht
  let m : E := ⨍ z in t, f z ∂μ
  have hfsmall : IntegrableOn f s μ := hf.mono_set hst
  have hconst : (μ.real s)⁻¹ • (∫ _y in s, m ∂μ) = m := by
    rw [← setAverage_eq, setAverage_const hs₀ hs]
  have hmean : (⨍ y in s, f y - m ∂μ) = (⨍ y in s, f y ∂μ) - m := by
    rw [setAverage_eq, integral_sub hfsmall (integrable_const m), smul_sub, hconst,
      ← setAverage_eq]
  have hnormI : IntegrableOn (fun y => ‖f y - m‖) t μ :=
    (hf.sub (integrable_const m)).norm
  have hmono := setIntegral_mono_set hnormI
    (Filter.Eventually.of_forall fun y => norm_nonneg (f y - m))
    (Filter.Eventually.of_forall fun y => hst (a := y))
  have hmassNonneg : 0 ≤ (μ.real s)⁻¹ :=
    inv_nonneg.mpr (show 0 ≤ μ.real s from ENNReal.toReal_nonneg)
  rw [← hmean, setAverage_eq, norm_smul, Real.norm_of_nonneg hmassNonneg]
  calc
    (μ.real s)⁻¹ * ‖∫ y in s, f y - m ∂μ‖ ≤
        (μ.real s)⁻¹ * ∫ y in s, ‖f y - m‖ ∂μ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
        (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ ≤ (μ.real s)⁻¹ * ∫ y in t, ‖f y - m‖ ∂μ :=
      mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- A bound on the mass ratio converts the integral into genuine mean oscillation. -/
theorem norm_setAverage_sub_le_mul_meanOscillation (f : X → E)
    (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (ht : μ t ≠ ∞)
    (hst : s ⊆ t) (hf : IntegrableOn f t μ) {C : ℝ}
    (hratio : μ.real t ≤ C * μ.real s) :
    ‖(⨍ y in s, f y ∂μ) - (⨍ y in t, f y ∂μ)‖ ≤
      C * (⨍ y in t, ‖f y - (⨍ z in t, f z ∂μ)‖ ∂μ) := by
  let g : X → ℝ := fun y => ‖f y - (⨍ z in t, f z ∂μ)‖
  have hspos : 0 < μ.real s := ENNReal.toReal_pos hs₀ hs
  have hfactor : (μ.real s)⁻¹ * μ.real t ≤ C := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ hspos).mpr hratio
  have havg : 0 ≤ (⨍ y in t, g y ∂μ) := by
    rw [setAverage_eq, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun _y => norm_nonneg _)
  have hmass : μ.real t * (⨍ y in t, g y ∂μ) = ∫ y in t, g y ∂μ := by
    simpa only [smul_eq_mul] using measure_smul_setAverage g ht
  calc
    ‖(⨍ y in s, f y ∂μ) - (⨍ y in t, f y ∂μ)‖ ≤
        (μ.real s)⁻¹ * ∫ y in t, g y ∂μ :=
      norm_setAverage_sub_le_integral_oscillation f hs₀ hs ht hst hf
    _ = ((μ.real s)⁻¹ * μ.real t) * (⨍ y in t, g y ∂μ) := by
      rw [← hmass]
      ring
    _ ≤ C * (⨍ y in t, g y ∂μ) := mul_le_mul_of_nonneg_right hfactor havg

end GeneralMeasure

section RadiusRescaling

/-- The geometric mean-limit theorem at an arbitrary positive reference radius. -/
theorem existsUnique_allRadius_limit_of_comparable_radius
    {E : Type*} [MetricSpace E] [CompleteSpace E] (F : ℝ → E)
    {α K r₀ : ℝ} (hα : 0 < α) (hK : 0 ≤ K) (hr₀ : 0 < r₀)
    (hcompare : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ r₀ → t ≤ 2 * s →
      dist (F s) (F t) ≤ K * t ^ α) :
    ∃! w : E, Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 w) ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        dist (F r) w ≤ K * r ^ α / (1 - (1 / 2 : ℝ) ^ α) := by
  let c : ℝ := 2 * r₀
  let G : ℝ → E := fun s => F (c * s)
  have hc : 0 < c := mul_pos (by norm_num) hr₀
  have hcomp : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ 1 / 2 → t ≤ 2 * s →
      dist (G s) (G t) ≤ (K * c ^ α) * t ^ α := by
    intro s t hs hst ht hratio
    have htpos : 0 < t := hs.trans_le hst
    have hct : c * t ≤ r₀ := by dsimp only [c]; nlinarith only [ht, hr₀]
    have hbound := hcompare (c * s) (c * t) (mul_pos hc hs)
      (mul_le_mul_of_nonneg_left hst hc.le) hct
      (by nlinarith only [mul_le_mul_of_nonneg_left hratio hc.le])
    simpa only [G, Real.mul_rpow hc.le htpos.le, mul_assoc] using hbound
  obtain ⟨w, hw, _⟩ := HarmonicMaps.existsUnique_allRadius_limit_of_comparable G hα
    (mul_nonneg hK (Real.rpow_nonneg hc.le α)) hcomp
  have hcancel (r : ℝ) : c * (r / c) = r := by field_simp [hc.ne']
  have hargZero : Tendsto (fun r : ℝ => r / c) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_div, id_eq] using
      ((tendsto_id.div_const c).mono_left nhdsWithin_le_nhds :
        Tendsto (fun r : ℝ => r / c) (𝓝[>] (0 : ℝ)) (𝓝 (0 / c)))
  have harg : Tendsto (fun r : ℝ => r / c) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hargZero, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_pos hr hc
  have hlimit : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    simpa only [Function.comp_def, G, hcancel] using hw.1.comp harg
  refine ⟨w, ⟨hlimit, ?_⟩, ?_⟩
  · intro r hr hrr₀
    have hrcap : r / c ≤ 1 / 2 := by
      apply (div_le_iff₀ hc).mpr
      dsimp only [c]
      nlinarith only [hrr₀]
    have htail := hw.2 (r / c) (div_pos hr hc) hrcap
    have hpower : c ^ α * (r / c) ^ α = r ^ α := by
      rw [← Real.mul_rpow hc.le (div_pos hr hc).le, hcancel]
    simpa only [G, hcancel, mul_assoc, hpower] using htail
  · intro v hv
    exact tendsto_nhds_unique hv.1 hlimit

end RadiusRescaling

section EuclideanBalls

variable {n : ℕ} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem ball_measureReal_formula (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.ball x r) =
      r ^ n * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [measureReal_def, Measure.addHaar_ball_of_pos volume x hr, ENNReal.toReal_mul]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [ENNReal.toReal_ofReal (pow_nonneg hr.le n)]
  rfl

/-- Euclidean ball masses obey the literal radius-ratio power bound. -/
theorem ball_measureReal_le_of_radius_le_mul
    (a b : EuclideanSpace ℝ (Fin n)) {r R c : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hratio : R ≤ c * r) :
    volume.real (Metric.ball b R) ≤ c ^ n * volume.real (Metric.ball a r) := by
  rw [ball_measureReal_formula a hr, ball_measureReal_formula b hR]
  have hp : R ^ n ≤ c ^ n * r ^ n := by
    simpa only [mul_pow] using pow_le_pow_left₀ hR.le hratio n
  calc
    R ^ n * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≤
        (c ^ n * r ^ n) * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      mul_le_mul_of_nonneg_right hp ENNReal.toReal_nonneg
    _ = c ^ n * (r ^ n * volume.real
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) := by ring

/-- Contained-ball means are controlled by the actual L¹ mean oscillation. -/
theorem norm_ballAverage_sub_le_meanOscillation
    (f : EuclideanSpace ℝ (Fin n) → E)
    {a b : EuclideanSpace ℝ (Fin n)} {r R c : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hsub : Metric.ball a r ⊆ Metric.ball b R) (hratio : R ≤ c * r)
    (hf : IntegrableOn f (Metric.ball b R) volume) :
    ‖(⨍ y in Metric.ball a r, f y) - (⨍ y in Metric.ball b R, f y)‖ ≤
      c ^ n * (⨍ y in Metric.ball b R,
        ‖f y - (⨍ z in Metric.ball b R, f z)‖) := by
  exact norm_setAverage_sub_le_mul_meanOscillation f
    (Metric.measure_ball_pos volume a hr).ne' measure_ball_ne_top measure_ball_ne_top
    hsub hf (ball_measureReal_le_of_radius_le_mul a b hr hR hratio)

/-- Mean oscillation on all small balls gives a unique literal mean limit and tail bound. -/
theorem existsUnique_ballAverage_limit_of_meanOscillation
    (f : EuclideanSpace ℝ (Fin n) → E) (x : EuclideanSpace ℝ (Fin n))
    {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hf : IntegrableOn f (Metric.ball x (1 / 2)) volume)
    (hosc : ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      (⨍ y in Metric.ball x r, ‖f y - (⨍ z in Metric.ball x r, f z)‖) ≤
        K * r ^ α) :
    ∃! w : E,
      Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, f y)
        (𝓝[>] (0 : ℝ)) (𝓝 w) ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
        ‖(⨍ y in Metric.ball x r, f y) - w‖ ≤
          ((2 : ℝ) ^ n * K) * r ^ α / (1 - (1 / 2 : ℝ) ^ α) := by
  let F : ℝ → E := fun r => ⨍ y in Metric.ball x r, f y
  have hcompare : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ 1 / 2 → t ≤ 2 * s →
      dist (F s) (F t) ≤ ((2 : ℝ) ^ n * K) * t ^ α := by
    intro s t hs hst ht hratio
    have htpos : 0 < t := hs.trans_le hst
    have hball := norm_ballAverage_sub_le_meanOscillation f hs htpos
      (Metric.ball_subset_ball hst) hratio (hf.mono_set (Metric.ball_subset_ball ht))
    have hb := hball.trans (mul_le_mul_of_nonneg_left
      (hosc t htpos ht) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))
    simpa only [F, dist_eq_norm, mul_assoc] using hb
  simpa only [F, dist_eq_norm] using
    HarmonicMaps.existsUnique_allRadius_limit_of_comparable F hα
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n) hK) hcompare

/-- The actual ball-mean limit and tail estimate respect any positive radius cap. -/
theorem existsUnique_ballAverage_limit_of_meanOscillation_radius
    (f : EuclideanSpace ℝ (Fin n) → E) (x : EuclideanSpace ℝ (Fin n))
    {α K r₀ : ℝ} (hα : 0 < α) (hK : 0 ≤ K) (hr₀ : 0 < r₀)
    (hf : IntegrableOn f (Metric.ball x r₀) volume)
    (hosc : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (⨍ y in Metric.ball x r, ‖f y - (⨍ z in Metric.ball x r, f z)‖) ≤
        K * r ^ α) :
    ∃! w : E,
      Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, f y)
        (𝓝[>] (0 : ℝ)) (𝓝 w) ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        ‖(⨍ y in Metric.ball x r, f y) - w‖ ≤
          ((2 : ℝ) ^ n * K) * r ^ α / (1 - (1 / 2 : ℝ) ^ α) := by
  let F : ℝ → E := fun r => ⨍ y in Metric.ball x r, f y
  have hcompare : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ r₀ → t ≤ 2 * s →
      dist (F s) (F t) ≤ ((2 : ℝ) ^ n * K) * t ^ α := by
    intro s t hs hst ht hratio
    have htpos : 0 < t := hs.trans_le hst
    have hball := norm_ballAverage_sub_le_meanOscillation f hs htpos
      (Metric.ball_subset_ball hst) hratio (hf.mono_set (Metric.ball_subset_ball ht))
    have hb := hball.trans (mul_le_mul_of_nonneg_left
      (hosc t htpos ht) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))
    simpa only [F, dist_eq_norm, mul_assoc] using hb
  simpa only [F, dist_eq_norm] using
    existsUnique_allRadius_limit_of_comparable_radius F hα
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n) hK) hr₀ hcompare

end EuclideanBalls

end StationaryHarmonicMaps

end
