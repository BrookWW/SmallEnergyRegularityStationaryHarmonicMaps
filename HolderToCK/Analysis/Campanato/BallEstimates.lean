module

public import HolderToCK.Foundation.BallVolume
public import HarmonicMaps.Analysis.MorreyBallEstimates
public import HarmonicMaps.Analysis.MorreyGeometricMeans
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul

/-! # Campanato estimates for actual ball averages of an L2 field

Quadratic oscillation controls the difference of contained-ball means.
Comparable radii give one all-radius limit with an explicit geometric tail.
The field is required only to be square integrable; no weak derivative of
the field enters these estimates.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace HolderToCK

theorem norm_ballAverage_sub_le_oscillation_bound {n q : ℕ}
    {g : Domain n → Ambient q} {a b : Domain n} {r R S γ c : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hS : 0 ≤ S) (hc : 0 ≤ c)
    (hsub : Metric.ball a r ⊆ Metric.ball b R) (hratio : R ≤ c * r)
    (hg : MemLp g 2 (volume.restrict (Metric.ball b R)))
    (hOsc : (∫ y in Metric.ball b R, ‖g y - ⨍ z in Metric.ball b R, g z‖ ^ 2) ≤
      S * Real.rpow R ((n : ℝ) + 2 * γ)) :
    ‖(⨍ y in Metric.ball a r, g y) - (⨍ y in Metric.ball b R, g y)‖ ≤
      Real.sqrt (c ^ n / volume.real (Metric.ball (0 : Domain n) 1)) *
        Real.sqrt S * Real.rpow R γ := by
  simp only [Real.rpow_eq_pow] at *
  let V := volume.real (Metric.ball (0 : Domain n) 1)
  have hV : 0 < V := ball_volume_real_pos (0 : Domain n) (by norm_num)
  have hρ : 0 < r ^ n * V := mul_pos (pow_pos hr _) hV
  have hdiff := ballAverage_sub_sq_le_oscillation hr hsub hg
  have hsq : r ^ n * V *
      ‖(⨍ y in Metric.ball a r, g y) - (⨍ y in Metric.ball b R, g y)‖ ^ 2 ≤
      S * R ^ ((n : ℝ) + 2 * γ) := by
    rw [ball_volume_real a hr] at hdiff
    have hz := mul_le_mul_of_nonneg_left hdiff hρ.le
    rw [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul] at hz
    exact hz.trans hOsc
  have hpow : R ^ n ≤ c ^ n * r ^ n := by
    simpa only [mul_pow] using pow_le_pow_left₀ hR.le hratio n
  have hsplit : R ^ ((n : ℝ) + 2 * γ) = R ^ n * (R ^ γ) ^ 2 := by
    rw [Real.rpow_add hR, Real.rpow_natCast, mul_comm (2 : ℝ) γ,
      Real.rpow_mul hR.le, Real.rpow_two]
  let B : ℝ := Real.sqrt (c ^ n / V) * Real.sqrt S * R ^ γ
  have hB : 0 ≤ B := by positivity
  have hBsq : B ^ 2 = c ^ n / V * S * (R ^ γ) ^ 2 := by
    dsimp only [B]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hS]
  have heq : r ^ n * V * B ^ 2 = (c ^ n * r ^ n) * (S * (R ^ γ) ^ 2) := by
    rw [hBsq]
    field_simp [hV.ne']
  have hsqB :
      ‖(⨍ y in Metric.ball a r, g y) - (⨍ y in Metric.ball b R, g y)‖ ^ 2 ≤ B ^ 2 := by
    apply (mul_le_mul_iff_right₀ hρ).mp
    rw [heq]
    rw [hsplit] at hsq
    calc
      _ ≤ S * (R ^ n * (R ^ γ) ^ 2) := hsq
      _ = R ^ n * (S * (R ^ γ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by positivity)
  exact (sq_le_sq₀ (norm_nonneg _) hB).mp hsqB

theorem norm_ballAverage_le_of_l2_integral_le {n q : ℕ}
    {g : Domain n → Ambient q} (a : Domain n) {r E : ℝ} (hr : 0 < r) (hE : 0 ≤ E)
    (hg : MemLp g 2 (volume.restrict (Metric.ball a r)))
    (hEnergy : (∫ y in Metric.ball a r, ‖g y‖ ^ 2) ≤ E) :
    ‖⨍ y in Metric.ball a r, g y‖ ≤
      (Real.sqrt (volume.real (Metric.ball a r)))⁻¹ * Real.sqrt E := by
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
  have hI : Integrable (fun y => ‖g y‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hc : ConvexOn ℝ Set.univ (fun v : Ambient q => ‖v‖ ^ 2) :=
    (convexOn_univ_norm (E := Ambient q)).pow (fun _ _ => norm_nonneg _) 2
  have hj := hc.map_average_le (continuous_norm.pow 2).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) (hg.integrable (by norm_num)) hI
  change ‖⨍ y in Metric.ball a r, g y‖ ^ 2 ≤ ⨍ y in Metric.ball a r, ‖g y‖ ^ 2 at hj
  rw [setAverage_eq volume (fun y => ‖g y‖ ^ 2), smul_eq_mul] at hj
  have hV : 0 < volume.real (Metric.ball a r) := ball_volume_real_pos a hr
  have hbound : ‖⨍ y in Metric.ball a r, g y‖ ^ 2 ≤
      ((Real.sqrt (volume.real (Metric.ball a r)))⁻¹ * Real.sqrt E) ^ 2 := by
    rw [mul_pow, inv_pow, Real.sq_sqrt hV.le, Real.sq_sqrt hE]
    exact hj.trans (mul_le_mul_of_nonneg_left hEnergy (inv_nonneg.mpr hV.le))
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hbound

theorem existsUnique_allRadius_limit_of_comparable_at_radius
    {E : Type*} [MetricSpace E] [CompleteSpace E] (F : ℝ → E) {γ K r₀ : ℝ}
    (hγ : 0 < γ) (hK : 0 ≤ K) (hr₀ : 0 < r₀)
    (hcompare : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ r₀ → t ≤ 2 * s →
      dist (F s) (F t) ≤ K * t ^ γ) :
    ∃! w : E, Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 w) ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        dist (F r) w ≤ K * r ^ γ / (1 - (1 / 2 : ℝ) ^ γ) := by
  let F' : ℝ → E := fun s => F ((2 * r₀) * s)
  have hscale : 0 < 2 * r₀ := mul_pos (by norm_num) hr₀
  have hK' : 0 ≤ K * (2 * r₀) ^ γ := mul_nonneg hK (Real.rpow_nonneg hscale.le _)
  have hcomp : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ 1 / 2 → t ≤ 2 * s →
      dist (F' s) (F' t) ≤ (K * (2 * r₀) ^ γ) * t ^ γ := by
    intro s t hs hst ht hratio
    have ht0 : 0 < t := hs.trans_le hst
    have h := hcompare ((2 * r₀) * s) ((2 * r₀) * t) (mul_pos hscale hs)
      (mul_le_mul_of_nonneg_left hst hscale.le)
      (by nlinarith only [mul_le_mul_of_nonneg_left ht hscale.le])
      (by nlinarith only [mul_le_mul_of_nonneg_left hratio hscale.le])
    rw [Real.mul_rpow hscale.le ht0.le] at h
    simpa only [F', mul_assoc] using h
  obtain ⟨w, hw, _⟩ := existsUnique_allRadius_limit_of_comparable F' hγ hK' hcomp
  have hdiv : Tendsto (fun r : ℝ => r / (2 * r₀)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [zero_div, id_eq] using
        (((tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).mono_left
          nhdsWithin_le_nhds).div_const (2 * r₀))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact div_pos hr hscale
  have heq (r : ℝ) : (2 * r₀) * (r / (2 * r₀)) = r := by field_simp [hscale.ne']
  have hlim : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    simpa only [F', Function.comp_def, heq] using hw.1.comp hdiv
  refine ⟨w, ⟨hlim, ?_⟩, ?_⟩
  · intro r hr hrr₀
    have hs : 0 < r / (2 * r₀) := div_pos hr hscale
    have hshalf : r / (2 * r₀) ≤ 1 / 2 := by
      apply (div_le_iff₀ hscale).mpr
      nlinarith only [hrr₀]
    have h := hw.2 (r / (2 * r₀)) hs hshalf
    have hpow : (2 * r₀) ^ γ * (r / (2 * r₀)) ^ γ = r ^ γ := by
      rw [← Real.mul_rpow hscale.le hs.le, heq]
    change dist (F ((2 * r₀) * (r / (2 * r₀)))) w ≤
      (K * (2 * r₀) ^ γ) * (r / (2 * r₀)) ^ γ / (1 - (1 / 2 : ℝ) ^ γ) at h
    rw [heq r, mul_assoc K, hpow] at h
    exact h
  · intro v hv
    exact tendsto_nhds_unique hv.1 hlim

end HolderToCK
end
