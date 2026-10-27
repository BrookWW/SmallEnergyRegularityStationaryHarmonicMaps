module

public import HarmonicMaps.Analysis.MorreyMeans
public import HarmonicMaps.Representative
public import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.Convex

/-! # The full inner-ball Holder estimate from the actual Sobolev means -/

public section

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators NNReal

namespace HarmonicMaps

private theorem meanLimit_holder_near {n q : ℕ} {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    {f : Domain n → Ambient q} {Df : Domain n → Gradient n q}
    (hf : MemW12 (ballDomain 0 1) f Df)
    (hgrowth : ∀ (x : Domain n), x ∈ Metric.ball (0 : Domain n) (1 / 2) →
      ∀ (r : PositiveRadius), r.val ≤ (1 / 2 : ℝ) →
        (∫ y in Metric.ball x r.val, hsNormSq (Df y)) ≤
          M * Real.rpow r.val ((n : ℝ) - 2 + 2 * α))
    (w : Metric.ball (0 : Domain n) (1 / 2) → Ambient q)
    (htail : ∀ (x : Metric.ball (0 : Domain n) (1 / 2)) (r : ℝ), 0 < r → r ≤ 1 / 2 →
      ‖(⨍ y in Metric.ball (x : Domain n) r, f y) - w x‖ ≤
        (Real.sqrt ((2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n /
          volume.real (Metric.ball (0 : Domain n) 1)) /
          (1 - (1 / 2 : ℝ) ^ α)) * Real.sqrt M * Real.rpow r α)
    (x y : Metric.ball (0 : Domain n) (1 / 2))
    (hd : dist (x : Domain n) (y : Domain n) ≤ 1 / 8) :
    ‖w x - w y‖ ≤
      (2 * (Real.sqrt ((2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n /
          volume.real (Metric.ball (0 : Domain n) 1)) /
          (1 - (1 / 2 : ℝ) ^ α)) * (2 : ℝ) ^ α +
        2 * Real.sqrt ((2 : ℝ) ^ (n + 1) * (3 / 2 : ℝ) ^ n /
          volume.real (Metric.ball (0 : Domain n) 1)) * (3 : ℝ) ^ α) *
        Real.sqrt M * Real.rpow (dist (x : Domain n) (y : Domain n)) α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, dist_self,
      Real.rpow_eq_pow, Real.zero_rpow hα.ne', mul_zero, le_refl]
  let d := dist (x : Domain n) (y : Domain n)
  have hd0 : 0 < d := dist_pos.mpr (Subtype.coe_ne_coe.mpr hxy)
  have h2d : 0 < 2 * d := by positivity
  have h3d : 0 < 3 * d := by positivity
  have h2half : 2 * d ≤ 1 / 2 := by dsimp only [d]; linarith only [hd]
  have h3half : 3 * d ≤ 1 / 2 := by dsimp only [d]; linarith only [hd]
  have hxsub : Metric.ball (x : Domain n) (2 * d) ⊆ Metric.ball (x : Domain n) (3 * d) :=
    Metric.ball_subset_ball (by linarith only [hd0])
  have hysub : Metric.ball (y : Domain n) (2 * d) ⊆ Metric.ball (x : Domain n) (3 * d) := by
    apply Metric.ball_subset_ball'
    rw [dist_comm]
    change 2 * d + d ≤ 3 * d
    linarith
  have hxc := hf.morrey_ballAverage_compare hM (by norm_num : (0 : ℝ) ≤ 3 / 2)
    h2d h3d x.2 h3half hxsub (by ring_nf; exact le_refl _)
    (hgrowth x x.2 ⟨3 * d, h3d⟩ h3half)
  have hyc := hf.morrey_ballAverage_compare hM (by norm_num : (0 : ℝ) ≤ 3 / 2)
    h2d h3d x.2 h3half hysub (by ring_nf; exact le_refl _)
    (hgrowth x x.2 ⟨3 * d, h3d⟩ h3half)
  have hxt := htail x (2 * d) h2d h2half
  have hyt := htail y (2 * d) h2d h2half
  let mx := ⨍ z in Metric.ball (x : Domain n) (2 * d), f z
  let my := ⨍ z in Metric.ball (y : Domain n) (2 * d), f z
  let mc := ⨍ z in Metric.ball (x : Domain n) (3 * d), f z
  have hsum : ‖w x - w y‖ ≤ ‖mx - w x‖ + ‖mx - mc‖ + ‖my - mc‖ + ‖my - w y‖ := by
    calc
      _ ≤ ‖w x - mx‖ + ‖mx - w y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖w x - mx‖ + (‖mx - mc‖ + ‖mc - w y‖) :=
        add_le_add_right (norm_sub_le_norm_sub_add_norm_sub _ _ _) _
      _ ≤ ‖w x - mx‖ + (‖mx - mc‖ + (‖mc - my‖ + ‖my - w y‖)) :=
        add_le_add_right (add_le_add_right (norm_sub_le_norm_sub_add_norm_sub _ _ _) _) _
      _ = _ := by rw [norm_sub_rev (w x) mx, norm_sub_rev mc my]; ring
  have hsum' := hsum.trans (add_le_add
    (add_le_add (add_le_add hxt hxc) hyc) hyt)
  simp only [Real.rpow_eq_pow] at hsum' ⊢
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hd0.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hd0.le] at hsum'
  calc
    _ ≤ _ := hsum'
    _ = _ := by ring

private theorem holder_global_of_eightSegments {n q : ℕ} {α D : ℝ} (hα : 0 ≤ α) (hD : 0 ≤ D)
    (w : Metric.ball (0 : Domain n) (1 / 2) → Ambient q)
    (hnear : ∀ x y : Metric.ball (0 : Domain n) (1 / 2),
      dist (x : Domain n) (y : Domain n) ≤ 1 / 8 →
      ‖w x - w y‖ ≤ D * (dist (x : Domain n) (y : Domain n)) ^ α) :
    ∀ x y : Metric.ball (0 : Domain n) (1 / 2),
      ‖w x - w y‖ ≤ 8 * D * (dist (x : Domain n) (y : Domain n)) ^ α := by
  intro x y
  let p : ℕ → Domain n := fun k => AffineMap.lineMap (x : Domain n) (y : Domain n) ((k : ℝ) / 8)
  have hp (k : ℕ) (hk : k ≤ 8) : p k ∈ Metric.ball (0 : Domain n) (1 / 2) := by
    apply (convex_ball (0 : Domain n) (1 / 2)).lineMap_mem x.2 y.2
    refine ⟨by positivity, ?_⟩
    have hk' : (k : ℝ) ≤ 8 := by exact_mod_cast hk
    linarith only [hk']
  let u : ℕ → Ambient q := fun k =>
    w ⟨AffineMap.lineMap (x : Domain n) (y : Domain n) (((min k 8 : ℕ) : ℝ) / 8), hp (min k 8) (min_le_right _ _)⟩
  have hdist (k : ℕ) : dist (p k) (p (k + 1)) = dist (x : Domain n) (y : Domain n) / 8 := by
    dsimp only [p]
    rw [dist_lineMap_lineMap, Real.dist_eq, Nat.cast_add, Nat.cast_one]
    have hab : |(k : ℝ) / 8 - ((k : ℝ) + 1) / 8| = 1 / 8 := by
      rw [show (k : ℝ) / 8 - ((k : ℝ) + 1) / 8 = -(1 / 8) by ring, abs_neg]
      norm_num
    rw [hab]
    ring
  have hdiam : dist (x : Domain n) (y : Domain n) < 1 := by
    have hx : dist (x : Domain n) 0 < (1 / 2 : ℝ) := x.2
    have hy : dist (y : Domain n) 0 < (1 / 2 : ℝ) := y.2
    have ht := dist_triangle (x : Domain n) 0 (y : Domain n)
    rw [dist_comm (0 : Domain n) (y : Domain n)] at ht
    linarith only [hx, hy, ht]
  have hpiece (k : ℕ) (hk : k ∈ Finset.range 8) :
      dist (u k) (u (k + 1)) ≤ D * (dist (x : Domain n) (y : Domain n)) ^ α := by
    have hk8 : k < 8 := Finset.mem_range.mp hk
    have hkn : k ≤ 8 := hk8.le
    have hks : k + 1 ≤ 8 := Nat.succ_le_iff.mpr hk8
    have hn := hnear ⟨p k, hp k hkn⟩ ⟨p (k + 1), hp (k + 1) hks⟩ (by
      rw [hdist]; linarith only [hdiam])
    have hm : (dist (p k) (p (k + 1))) ^ α ≤ (dist (x : Domain n) (y : Domain n)) ^ α := by
      apply Real.rpow_le_rpow dist_nonneg
      · rw [hdist]; exact div_le_self dist_nonneg (by norm_num)
      · exact hα
    have hb := hn.trans (mul_le_mul_of_nonneg_left hm hD)
    simpa only [u, p, min_eq_left hkn, min_eq_left hks, dist_eq_norm] using hb
  have hsum := dist_le_range_sum_dist u 8
  have hsum' := hsum.trans (Finset.sum_le_sum hpiece)
  have hu0 : u 0 = w x := by simp only [u, Nat.zero_min, Nat.cast_zero, zero_div,
    AffineMap.lineMap_apply_zero]
  have hu8 : u 8 = w y := by norm_num [u, AffineMap.lineMap_apply_one]
  rw [hu0, hu8, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat,
    dist_eq_norm] at hsum'
  simpa only [mul_assoc] using hsum'

/-- A power modulus with positive exponent proves actual subtype continuity. -/
theorem continuous_of_norm_sub_le_rpow {X : Type*} [MetricSpace X] {E : Type*}
    [NormedAddCommGroup E] (w : X → E) {α D : ℝ} (hα : 0 < α)
    (hbound : ∀ x y, ‖w x - w y‖ ≤ D * (dist x y) ^ α) : Continuous w := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc : Continuous (fun y : X => D * (dist y x) ^ α) :=
    continuous_const.mul ((Real.continuous_rpow_const hα.le).comp (continuous_id.dist continuous_const))
  have hz : Tendsto (fun y : X => D * (dist y x) ^ α) (𝓝 x) (𝓝 0) := by
    simpa only [dist_self, Real.zero_rpow hα.ne', mul_zero] using hc.tendsto x
  filter_upwards [(tendsto_order.mp hz).2 ε hε] with y hy
  exact lt_of_le_of_lt (by simpa only [dist_eq_norm] using hbound y x) hy

/-- One dimension/exponent constant controls the continuous representative of every source map. -/
theorem morrey_holder (n : ℕ) (_hn : 2 ≤ n) (α : ℝ) (hα : 0 < α) (_hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ (q : ℕ) (f : Domain n → Ambient q) (Df : Domain n → Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) f Df → ∀ (M : ℝ), 0 ≤ M →
      (∀ (x : Domain n), x ∈ Metric.ball (0 : Domain n) (1 / 2) →
        ∀ (r : PositiveRadius), r.val ≤ (1 / 2 : ℝ) →
          (∫ y in Metric.ball x r.val, hsNormSq (Df y)) ≤
            M * Real.rpow r.val ((n : ℝ) - 2 + 2 * α)) →
      ∃ w : Metric.ball (0 : Domain n) (1 / 2) → Ambient q,
        IsContinuousRepresentative (ballDomain (0 : Domain n) (1 / 2)) f w ∧
        (∀ (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2)),
          Tendsto (fun r : ℝ => (volume (Metric.ball x r)).toReal⁻¹ •
            (∫ y in Metric.ball x r, f y)) (𝓝[>] (0 : ℝ)) (𝓝 (w ⟨x, hx⟩))) ∧
        (∀ x y : Metric.ball (0 : Domain n) (1 / 2),
          ‖w x - w y‖ ≤ (C : ℝ) * Real.sqrt M *
            Real.rpow (dist (x : Domain n) (y : Domain n)) α) := by
  let H : ℝ := Real.sqrt ((2 : ℝ) ^ (n + 1) * (2 : ℝ) ^ n /
    volume.real (Metric.ball (0 : Domain n) 1)) / (1 - (1 / 2 : ℝ) ^ α)
  let J : ℝ := Real.sqrt ((2 : ℝ) ^ (n + 1) * (3 / 2 : ℝ) ^ n /
    volume.real (Metric.ball (0 : Domain n) 1))
  let D : ℝ := 2 * H * (2 : ℝ) ^ α + 2 * J * (3 : ℝ) ^ α
  have hden : 0 < 1 - (1 / 2 : ℝ) ^ α := sub_pos.mpr
    (Real.rpow_lt_one (by norm_num) (by norm_num) hα)
  have hD : 0 ≤ D := by dsimp only [D, H, J]; positivity
  refine ⟨⟨8 * D, by positivity⟩, ?_⟩
  intro q f Df hf M hM hgrowth
  obtain ⟨w, hwlimit, hwtail, hwae⟩ := hf.morrey_means hα hM hgrowth
  have hnear : ∀ x y : Metric.ball (0 : Domain n) (1 / 2),
      dist (x : Domain n) (y : Domain n) ≤ 1 / 8 →
      ‖w x - w y‖ ≤ (D * Real.sqrt M) * (dist (x : Domain n) (y : Domain n)) ^ α := by
    intro x y hd
    simpa only [D, H, J, Real.rpow_eq_pow] using
      meanLimit_holder_near hα hM hf hgrowth w hwtail x y hd
  have hglobal := holder_global_of_eightSegments hα.le (mul_nonneg hD (Real.sqrt_nonneg M)) w hnear
  have hcontinuity : Continuous w := continuous_of_norm_sub_le_rpow w hα (by
    intro x y
    simpa only [Subtype.dist_eq] using hglobal x y)
  refine ⟨w, ⟨hcontinuity, hwae⟩, hwlimit, ?_⟩
  intro x y
  change ‖w x - w y‖ ≤ (8 * D) * Real.sqrt M *
    Real.rpow (dist (x : Domain n) (y : Domain n)) α
  simpa only [Real.rpow_eq_pow, mul_assoc] using hglobal x y

end HarmonicMaps
