module

public import HarmonicMaps.Analysis.BallPolarIntegral

/-!
# Polar integration on positive annuli

The exact open-ball difference corresponds to the radius interval [s,r).
Endpoint null sets identify its real integral with the interval integral.
Continuous radial weights are integrable on the compact positive annulus.
-/

public section

open MeasureTheory Set

namespace HarmonicMaps

/-- Polar integration on the literal difference of two open balls. -/
theorem integral_annulus_eq_polar {n : ℕ} (hn : 0 < n) {a : Domain n} {s r : ℝ}
    (hs : 0 < s) (hsr : s ≤ r) {f : Domain n → ℝ}
    (hf : IntegrableOn f (Metric.ball a r \ Metric.ball a s)) :
    (∫ x in Metric.ball a r \ Metric.ball a s, f x) =
      ∫ t in s..r, t ^ (n - 1) *
        ∫ θ : Metric.sphere (0 : Domain n) 1, f (a + t • θ.val)
          ∂(volume : Measure (Domain n)).toSphere := by
  have hset : MeasurableSet (Metric.ball a r \ Metric.ball a s) :=
    measurableSet_ball.diff measurableSet_ball
  have hi := (integrable_indicator_iff hset).mpr hf
  rw [← integral_indicator hset, integral_eq_polar hn hi a]
  have he : (∫ t in Ioi (0 : ℝ), t ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1,
        (Metric.ball a r \ Metric.ball a s).indicator f (a + t • θ.val)
          ∂(volume : Measure (Domain n)).toSphere) =
      ∫ t in Ioi (0 : ℝ), (Ico s r).indicator (fun t => t ^ (n - 1) *
        ∫ θ : Metric.sphere (0 : Domain n) 1, f (a + t • θ.val)
          ∂(volume : Measure (Domain n)).toSphere) t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    have hd (θ : Metric.sphere (0 : Domain n) 1) : dist (a + t • θ.val) a = t := by
      rw [dist_eq_norm_sub, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
      have hθ : ‖θ.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
      rw [hθ, mul_one]
    have hmem (θ : Metric.sphere (0 : Domain n) 1) :
        a + t • θ.val ∈ Metric.ball a r \ Metric.ball a s ↔ t ∈ Ico s r := by
      simp only [mem_sdiff, Metric.mem_ball, hd, mem_Ico, not_lt]
      exact and_comm
    by_cases htr : t ∈ Ico s r
    · rw [indicator_of_mem htr]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun θ => indicator_of_mem ((hmem θ).mpr htr) f
    · rw [indicator_of_notMem htr]
      have hzero : (fun θ : Metric.sphere (0 : Domain n) 1 =>
          (Metric.ball a r \ Metric.ball a s).indicator f (a + t • θ.val)) = fun _ => 0 := by
        funext θ
        exact indicator_of_notMem (fun h => htr ((hmem θ).mp h)) f
      rw [hzero, integral_zero, mul_zero]
  rw [he, setIntegral_indicator measurableSet_Ico]
  have hi : Ioi (0 : ℝ) ∩ Ico s r = Ico s r :=
    inter_eq_right.mpr (fun _ hx => hs.trans_le hx.1)
  rw [hi, intervalIntegral.integral_of_le hsr, integral_Ico_eq_integral_Ioc]

/-- A continuous radial weight is integrable against any L1 density on a
positive annulus, and polar integration retains exactly that weight. -/
theorem integral_weighted_annulus_eq_polar {n : ℕ} (hn : 0 < n)
    {a : Domain n} {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r)
    {f : Domain n → ℝ} (hf : IntegrableOn f (Metric.ball a r \ Metric.ball a s))
    {w : ℝ → ℝ} (hw : ContinuousOn w (Icc s r)) :
    IntegrableOn (fun x => w ‖x - a‖ * f x) (Metric.ball a r \ Metric.ball a s) ∧
    (∫ x in Metric.ball a r \ Metric.ball a s, w ‖x - a‖ * f x) =
      ∫ t in s..r, w t * (t ^ (n - 1) *
        ∫ θ : Metric.sphere (0 : Domain n) 1, f (a + t • θ.val)
          ∂(volume : Measure (Domain n)).toSphere) := by
  have hmaps : MapsTo (fun x : Domain n => ‖x - a‖)
      (Metric.closedBall a r \ Metric.ball a s) (Icc s r) := by
    intro x hx
    simpa only [mem_Icc, Metric.mem_closedBall, Metric.mem_ball,
      dist_eq_norm_sub, not_lt] using And.intro hx.2 hx.1
  have hcont : ContinuousOn (fun x : Domain n => w ‖x - a‖)
      (Metric.closedBall a r \ Metric.ball a s) :=
    hw.comp (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn hmaps
  have hint : IntegrableOn (fun x => w ‖x - a‖ * f x)
      (Metric.ball a r \ Metric.ball a s) :=
    IntegrableOn.continuousOn_mul_of_subset hcont hf
      ((isCompact_closedBall a r).diff Metric.isOpen_ball)
      (measurableSet_ball.diff measurableSet_ball)
      (fun _ hx => ⟨Metric.ball_subset_closedBall hx.1, hx.2⟩)
  refine ⟨hint, (integral_annulus_eq_polar hn hs hsr hint).trans ?_⟩
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc s r := by simpa only [uIcc_of_le hsr] using ht
  have htpos : 0 < t := hs.trans_le ht'.1
  dsimp only
  have heq : (fun θ : Metric.sphere (0 : Domain n) 1 =>
      w ‖a + t • θ.val - a‖ * f (a + t • θ.val)) =
      (fun θ : Metric.sphere (0 : Domain n) 1 => w t * f (a + t • θ.val)) := by
    funext θ
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg htpos.le]
    have hθ : ‖θ.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    rw [hθ, mul_one]
  rw [heq, integral_const_mul]
  ring

end HarmonicMaps
