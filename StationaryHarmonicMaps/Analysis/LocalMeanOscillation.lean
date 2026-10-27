module

public import StationaryHarmonicMaps.Analysis.MeanOscillation
public import HarmonicMaps.Analysis.BallAverageDifferentiation
public import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Local ball geometry, differentiation and Holder chaining

Only the actual outer-ball integrability of the map is used. Indicator
localization in the differentiation proof has proved agreement on every
sufficiently small ball and supplies no global Sobolev extension.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology

namespace StationaryHarmonicMaps

theorem closedBall_quarter_subset_outer {n : ℕ} {a x : Domain n} {R r : ℝ}
    (hx : x ∈ Metric.ball a (3 * R / 4)) (hr : r ≤ R / 4) :
    Metric.closedBall x r ⊆ Metric.ball a R := by
  intro y hy
  have h := dist_triangle y x a
  have hyx : dist y x ≤ r := hy
  have hxa : dist x a < 3 * R / 4 := hx
  change dist y a < R
  linarith

theorem half_ball_subset_threeQuarter {n : ℕ} (a : Domain n) {R : ℝ} (hR : 0 < R) :
    Metric.ball a (R / 2) ⊆ Metric.ball a (3 * R / 4) :=
  Metric.ball_subset_ball (by linarith)

/-- The original outer-ball L1 map is differentiated on the concentric half ball. -/
theorem integrableOn_ae_tendsto_ballAverage_half {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Domain n → E) (a : Domain n) {R : ℝ} (hR : 0 < R)
    (hf : IntegrableOn f (Metric.ball a R) volume) :
    ∀ᵐ x ∂volume.restrict (Metric.ball a (R / 2)),
      Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, f y)
        (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  classical
  let B : Set (Domain n) := Metric.ball a R
  let g : Domain n → E := B.indicator f
  have hg : Integrable g volume := hf.integrable_indicator measurableSet_ball
  have hnative := IsUnifLocDoublingMeasure.ae_tendsto_average volume hg.locallyIntegrable 1
  filter_upwards [hnative.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_ball] with x hx hxhalf
  have hxB : x ∈ B := Metric.ball_subset_ball (by linarith : R / 2 ≤ R) hxhalf
  have hcenter : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), x ∈ Metric.closedBall x (1 * r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [mem_closedBall, dist_self, one_mul] using hr.le
  have hlimit := hx (fun _r : ℝ => x) (fun r : ℝ => r) tendsto_id hcenter
  have heq : (fun r : ℝ => ⨍ y in Metric.ball x r, f y) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r : ℝ => ⨍ y in Metric.closedBall x r, g y) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : (0 : ℝ) < R / 2))]
      with r hr hrsmall
    change r < R / 2 at hrsmall
    have hsub : Metric.ball x r ⊆ B := by
      intro y hy
      have h := dist_triangle y x a
      have hyx : dist y x < r := hy
      have hxa : dist x a < R / 2 := hxhalf
      change dist y a < R
      linarith
    rw [← setAverage_congr (HarmonicMaps.ball_ae_eq_closedBall x hr)]
    apply setAverage_congr_fun measurableSet_ball
    exact Filter.Eventually.of_forall fun y hy => (indicator_of_mem (hsub hy) f).symm
  have hgx : g x = f x := indicator_of_mem hxB f
  rw [hgx] at hlimit
  exact hlimit.congr' heq.symm

/-- Sixteen convex segments turn an R/16 near estimate into a full half-ball bound. -/
theorem holder_allPairs_of_sixteen_segments {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {a : Domain n} {R α D : ℝ}
    (hα : 0 ≤ α) (hD : 0 ≤ D)
    (w : Metric.ball a (R / 2) → E)
    (hnear : ∀ x y : Metric.ball a (R / 2),
      dist (x : Domain n) (y : Domain n) ≤ R / 16 →
      ‖w x - w y‖ ≤ D * (dist (x : Domain n) (y : Domain n)) ^ α) :
    ∀ x y : Metric.ball a (R / 2),
      ‖w x - w y‖ ≤ 16 * D * (dist (x : Domain n) (y : Domain n)) ^ α := by
  intro x y
  let p : ℕ → Domain n := fun k =>
    AffineMap.lineMap (x : Domain n) (y : Domain n) ((k : ℝ) / 16)
  have hp (k : ℕ) (hk : k ≤ 16) : p k ∈ Metric.ball a (R / 2) := by
    apply (convex_ball a (R / 2)).lineMap_mem x.2 y.2
    refine ⟨by positivity, ?_⟩
    have hk' : (k : ℝ) ≤ 16 := by exact_mod_cast hk
    linarith
  let z : ℕ → E := fun k =>
    w ⟨p (min k 16), hp (min k 16) (min_le_right _ _)⟩
  have hdist (k : ℕ) : dist (p k) (p (k + 1)) = dist (x : Domain n) (y : Domain n) / 16 := by
    dsimp only [p]
    rw [dist_lineMap_lineMap, Real.dist_eq, Nat.cast_add, Nat.cast_one]
    have hab : |(k : ℝ) / 16 - ((k : ℝ) + 1) / 16| = 1 / 16 := by
      rw [show (k : ℝ) / 16 - ((k : ℝ) + 1) / 16 = -(1 / 16) by ring, abs_neg]
      norm_num
    rw [hab]
    ring
  have hdiam : dist (x : Domain n) (y : Domain n) < R := by
    have h := dist_triangle (x : Domain n) a (y : Domain n)
    have hx : dist (x : Domain n) a < R / 2 := x.2
    have hy : dist a (y : Domain n) < R / 2 := by
      simpa only [Metric.mem_ball, dist_comm] using y.2
    linarith
  have hpiece (k : ℕ) (hk : k ∈ Finset.range 16) :
      dist (z k) (z (k + 1)) ≤ D * (dist (x : Domain n) (y : Domain n)) ^ α := by
    have hk16 : k < 16 := Finset.mem_range.mp hk
    have hkn : k ≤ 16 := hk16.le
    have hks : k + 1 ≤ 16 := Nat.succ_le_iff.mpr hk16
    have h := hnear ⟨p k, hp k hkn⟩ ⟨p (k + 1), hp (k + 1) hks⟩ (by
      rw [hdist]
      linarith)
    have hpower : (dist (p k) (p (k + 1))) ^ α ≤
        (dist (x : Domain n) (y : Domain n)) ^ α := by
      apply Real.rpow_le_rpow dist_nonneg
      · rw [hdist]; exact div_le_self dist_nonneg (by norm_num)
      · exact hα
    have hb := h.trans (mul_le_mul_of_nonneg_left hpower hD)
    simpa only [z, min_eq_left hkn, min_eq_left hks, dist_eq_norm] using hb
  have hsum := (dist_le_range_sum_dist z 16).trans (Finset.sum_le_sum hpiece)
  have hz0 : z 0 = w x := by
    simp only [z, Nat.zero_min, p, Nat.cast_zero, zero_div, AffineMap.lineMap_apply_zero]
  have hz16 : z 16 = w y := by
    norm_num [z, p, AffineMap.lineMap_apply_one]
  rw [hz0, hz16, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat,
    dist_eq_norm] at hsum
  simpa only [mul_assoc] using hsum

end StationaryHarmonicMaps

end
