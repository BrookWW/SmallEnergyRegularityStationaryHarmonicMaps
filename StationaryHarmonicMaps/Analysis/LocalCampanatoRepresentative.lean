module

public import StationaryHarmonicMaps.Analysis.LocalMeanOscillation
public import StationaryHarmonicMaps.Analysis.CampanatoRepresentative
public import HarmonicMaps.Analysis.ContinuousRepresentativeLocality

/-! # Continuous half-ball representatives from local mean oscillation -/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology

namespace StationaryHarmonicMaps

/-- Local mean limits have a Holder bound for distances at most R/16. -/
theorem local_ballAverage_limit_holder_near {n q : ℕ}
    (f : Domain n → Ambient q) {a : Domain n} {R α K : ℝ}
    (w : Metric.ball a (R / 2) → Ambient q)
    (hf : IntegrableOn f (Metric.ball a R) volume) (hα : 0 < α) (hR : 0 < R)
    (hosc : ∀ (x : Domain n), x ∈ Metric.ball a (3 * R / 4) →
      ∀ r : ℝ, 0 < r → r ≤ R / 4 →
        (⨍ y in Metric.ball x r, ‖f y - (⨍ z in Metric.ball x r, f z)‖) ≤ K * r ^ α)
    (htail : ∀ (x : Metric.ball a (R / 2)) (r : ℝ), 0 < r → r ≤ R / 4 →
      ‖(⨍ y in Metric.ball (x : Domain n) r, f y) - w x‖ ≤
        ((2 : ℝ) ^ n * K) * r ^ α / (1 - (1 / 2 : ℝ) ^ α))
    (x y : Metric.ball a (R / 2))
    (hd : dist (x : Domain n) (y : Domain n) ≤ R / 16) :
    ‖w x - w y‖ ≤
      (2 * (2 : ℝ) ^ n * ((2 : ℝ) ^ α / (1 - (1 / 2 : ℝ) ^ α) + (4 : ℝ) ^ α)) *
        K * (dist (x : Domain n) (y : Domain n)) ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, dist_self, Real.zero_rpow hα.ne', mul_zero, le_refl]
  let d : ℝ := dist (x : Domain n) (y : Domain n)
  have hdpos : 0 < d := dist_pos.mpr (Subtype.coe_ne_coe.mpr hxy)
  have h2d : 0 < 2 * d := mul_pos (by norm_num) hdpos
  have h4d : 0 < 4 * d := mul_pos (by norm_num) hdpos
  have h2cap : 2 * d ≤ R / 4 := by dsimp only [d]; linarith
  have h4cap : 4 * d ≤ R / 4 := by dsimp only [d]; linarith
  have hxinner := half_ball_subset_threeQuarter a hR x.2
  have hxsub : Metric.ball (x : Domain n) (2 * d) ⊆ Metric.ball (x : Domain n) (4 * d) :=
    Metric.ball_subset_ball (by linarith)
  have hysub : Metric.ball (y : Domain n) (2 * d) ⊆ Metric.ball (x : Domain n) (4 * d) := by
    apply Metric.ball_subset_ball'
    rw [dist_comm]
    change 2 * d + d ≤ 4 * d
    linarith
  have hfi : IntegrableOn f (Metric.ball (x : Domain n) (4 * d)) volume :=
    hf.mono_set (Metric.ball_subset_closedBall.trans
      (closedBall_quarter_subset_outer hxinner h4cap))
  have hxc := norm_ballAverage_sub_le_meanOscillation f h2d h4d hxsub
    (show 4 * d ≤ 2 * (2 * d) by ring_nf; exact le_rfl) hfi
  have hyc := norm_ballAverage_sub_le_meanOscillation f h2d h4d hysub
    (show 4 * d ≤ 2 * (2 * d) by ring_nf; exact le_rfl) hfi
  have hosc4 := mul_le_mul_of_nonneg_left (hosc x hxinner (4 * d) h4d h4cap)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
  have hxc' := hxc.trans hosc4
  have hyc' := hyc.trans hosc4
  have hxt := htail x (2 * d) h2d h2cap
  have hyt := htail y (2 * d) h2d h2cap
  let mx := ⨍ z in Metric.ball (x : Domain n) (2 * d), f z
  let my := ⨍ z in Metric.ball (y : Domain n) (2 * d), f z
  let mc := ⨍ z in Metric.ball (x : Domain n) (4 * d), f z
  have hsum : ‖w x - w y‖ ≤
      ‖mx - w x‖ + ‖mx - mc‖ + ‖my - mc‖ + ‖my - w y‖ := by
    calc
      _ ≤ ‖w x - mx‖ + ‖mx - w y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ‖w x - mx‖ + (‖mx - mc‖ + ‖mc - w y‖) :=
        add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _ _ _)
      _ ≤ ‖w x - mx‖ + (‖mx - mc‖ + (‖mc - my‖ + ‖my - w y‖)) :=
        add_le_add le_rfl (add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _ _ _))
      _ = _ := by rw [norm_sub_rev (w x) mx, norm_sub_rev mc my]; ring
  have hbound := hsum.trans (add_le_add
    (add_le_add (add_le_add hxt hxc') hyc') hyt)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hdpos.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hdpos.le] at hbound
  calc
    _ ≤ _ := hbound
    _ = _ := by dsimp only [d]; ring

/-- Explicit coefficient for the local mean-oscillation representative estimate. -/
@[expose] noncomputable def localCampanatoConstant (n : ℕ) (α : ℝ) : ℝ :=
  1 + |(2 : ℝ)^n / (1 - (1/2 : ℝ)^α)| +
    16 * (2 * (2 : ℝ)^n * ((2 : ℝ)^α / (1 - (1/2 : ℝ)^α) + (4 : ℝ)^α))

/-- Local all-center mean oscillation supplies the unique actual half-ball
representative with the displayed coefficient. -/
theorem existsUnique_local_representative_of_meanOscillation_explicit (n : ℕ) (α : ℝ)
    (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ C = localCampanatoConstant n α ∧ ∀ (q : ℕ) (f : Domain n → Ambient q)
      (a : Domain n) (R K : ℝ), 0 < R → 0 ≤ K →
      IntegrableOn f (Metric.ball a R) volume →
      (∀ (x : Domain n), x ∈ Metric.ball a (3 * R / 4) →
        ∀ r : ℝ, 0 < r → r ≤ R / 4 →
          (⨍ y in Metric.ball x r, ‖f y - (⨍ z in Metric.ball x r, f z)‖) ≤ K * r ^ α) →
      ∃! w : Metric.ball a (R / 2) → Ambient q,
        IsContinuousRepresentative (ballDomain a (R / 2)) f w ∧
        (∀ x : Metric.ball a (R / 2),
          Tendsto (fun r : ℝ => ⨍ y in Metric.ball (x : Domain n) r, f y)
          (𝓝[>] (0 : ℝ)) (𝓝 (w x))) ∧
        (∀ (x : Metric.ball a (R / 2)) (r : ℝ), 0 < r → r ≤ R / 4 →
          ‖(⨍ y in Metric.ball (x : Domain n) r, f y) - w x‖ ≤ C * K * r ^ α) ∧
        (∀ x y : Metric.ball a (R / 2),
          ‖w x - w y‖ ≤ C * K * (dist (x : Domain n) (y : Domain n)) ^ α) := by
  let T : ℝ := (2 : ℝ) ^ n / (1 - (1 / 2 : ℝ) ^ α)
  let H : ℝ := 2 * (2 : ℝ) ^ n *
    ((2 : ℝ) ^ α / (1 - (1 / 2 : ℝ) ^ α) + (4 : ℝ) ^ α)
  let C : ℝ := 1 + |T| + 16 * H
  have hden : 0 < 1 - (1 / 2 : ℝ) ^ α := sub_pos.mpr
    (Real.rpow_lt_one (by norm_num) (by norm_num) hα)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hTC : T ≤ C := by dsimp only [C]; linarith [le_abs_self T]
  have hHC : 16 * H ≤ C := by dsimp only [C]; linarith [abs_nonneg T]
  refine ⟨C, hC, rfl, ?_⟩
  intro q f a R K hR hK hf hosc
  classical
  have hex (x : Metric.ball a (R / 2)) :=
    existsUnique_ballAverage_limit_of_meanOscillation_radius f (x : Domain n) hα hK
      (by linarith : 0 < R / 4)
      (hf.mono_set (Metric.ball_subset_closedBall.trans
        (closedBall_quarter_subset_outer (half_ball_subset_threeQuarter a hR x.2) le_rfl)))
      (hosc x (half_ball_subset_threeQuarter a hR x.2))
  let w : Metric.ball a (R / 2) → Ambient q := fun x => (hex x).exists.choose
  have hw (x : Metric.ball a (R / 2)) := (hex x).exists.choose_spec
  have hnear : ∀ x y : Metric.ball a (R / 2),
      dist (x : Domain n) (y : Domain n) ≤ R / 16 →
      ‖w x - w y‖ ≤ (H * K) * (dist (x : Domain n) (y : Domain n)) ^ α := by
    intro x y hd
    exact local_ballAverage_limit_holder_near f w hf hα hR hosc (fun z => (hw z).2) x y hd
  have hcont : Continuous w := continuous_of_norm_sub_le_rpow_near w hα
    (by linarith : 0 < R / 16) (fun x y hd => hnear x y hd)
  have hrep : IsContinuousRepresentative (ballDomain a (R / 2)) f w := by
    refine ⟨hcont, ?_⟩
    filter_upwards [integrableOn_ae_tendsto_ballAverage_half f a hR hf] with x hx
    intro hxball
    exact tendsto_nhds_unique (hw ⟨x, hxball⟩).1 hx
  have hfull := holder_allPairs_of_sixteen_segments hα.le (mul_nonneg hH hK) w hnear
  refine ⟨w, ⟨hrep, (fun x => (hw x).1), ?_, ?_⟩, ?_⟩
  · intro x r hr hcap
    calc
      _ ≤ ((2 : ℝ) ^ n * K) * r ^ α / (1 - (1 / 2 : ℝ) ^ α) := (hw x).2 r hr hcap
      _ = T * K * r ^ α := by dsimp only [T]; ring
      _ ≤ C * K * r ^ α := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hTC hK) (Real.rpow_nonneg hr.le _)
  · intro x y
    calc
      _ ≤ 16 * (H * K) * (dist (x : Domain n) (y : Domain n)) ^ α := hfull x y
      _ = (16 * H) * K * (dist (x : Domain n) (y : Domain n)) ^ α := by ring
      _ ≤ C * K * (dist (x : Domain n) (y : Domain n)) ^ α := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hHC hK) (Real.rpow_nonneg dist_nonneg _)
  · intro v hv
    exact hv.1.unique hrep

theorem existsUnique_local_representative_of_meanOscillation (n : ℕ) (α : ℝ)
    (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (f : Domain n → Ambient q)
      (a : Domain n) (R K : ℝ), 0 < R → 0 ≤ K →
      IntegrableOn f (Metric.ball a R) volume →
      (∀ (x : Domain n), x ∈ Metric.ball a (3 * R / 4) →
        ∀ r : ℝ, 0 < r → r ≤ R / 4 →
          (⨍ y in Metric.ball x r, ‖f y - (⨍ z in Metric.ball x r, f z)‖) ≤ K * r ^ α) →
      ∃! w : Metric.ball a (R / 2) → Ambient q,
        IsContinuousRepresentative (ballDomain a (R / 2)) f w ∧
        (∀ x : Metric.ball a (R / 2),
          Tendsto (fun r : ℝ => ⨍ y in Metric.ball (x : Domain n) r, f y)
          (𝓝[>] (0 : ℝ)) (𝓝 (w x))) ∧
        (∀ (x : Metric.ball a (R / 2)) (r : ℝ), 0 < r → r ≤ R / 4 →
          ‖(⨍ y in Metric.ball (x : Domain n) r, f y) - w x‖ ≤ C * K * r ^ α) ∧
        (∀ x y : Metric.ball a (R / 2),
          ‖w x - w y‖ ≤ C * K * (dist (x : Domain n) (y : Domain n)) ^ α) := by
  obtain ⟨C, hC, _hFormula, H⟩ := existsUnique_local_representative_of_meanOscillation_explicit n α hα
  exact ⟨C, hC, H⟩

namespace Analysis

theorem localCampanatoConstant_le_of_half_le (n : ℕ) (α : ℝ)
    (hαHalf : (1 / 2 : ℝ) ≤ α) (hαOne : α ≤ 1) :
    localCampanatoConstant n α ≤ (512 : ℝ) * 2 ^ n := by
  let A : ℝ := 2 ^ n
  let v : ℝ := (1 / 2 : ℝ) ^ α
  let u : ℝ := (2 : ℝ) ^ α
  let T : ℝ := A / (1 - v)
  let H : ℝ := 2 * A * (u / (1 - v) + (4 : ℝ) ^ α)
  have hA : 1 ≤ A := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hroot : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) ≤ (3 / 4 : ℝ) := by
    have hsq : ((1 / 2 : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hnonneg := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (1 / 2 : ℝ)
    nlinarith only [hsq, hnonneg]
  have hv : v ≤ (3 / 4 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) hαHalf).trans hroot
  have hu : u ≤ 2 := by
    simpa only [u, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hαOne
  have hfour : (4 : ℝ)^α ≤ 4 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hαOne
  have hd : 0 < 1 - v := by linarith only [hv]
  have hfrac : u / (1 - v) ≤ 8 :=
    (div_le_iff₀ hd).mpr (by linarith only [hu, hv])
  have hT : T ≤ 4 * A := by
    apply (div_le_iff₀ hd).mpr
    have Hmul := mul_le_mul_of_nonneg_left (show (1 / 4 : ℝ) ≤ 1 - v by linarith only [hv]) hAp
    nlinarith only [Hmul]
  have hH : H ≤ 24 * A := by
    dsimp only [H]
    have Hmul := mul_le_mul_of_nonneg_left
      (show u / (1 - v) + (4 : ℝ)^α ≤ 12 by linarith only [hfrac, hfour])
      (show 0 ≤ 2 * A by positivity)
    nlinarith only [Hmul]
  have hT0 : 0 ≤ T := div_nonneg hAp hd.le
  change 1 + |T| + 16 * H ≤ 512 * A
  rw [abs_of_nonneg hT0]
  nlinarith only [hT, hH, hA]

theorem localCampanatoConstant_half_le (n : ℕ) :
    localCampanatoConstant n (1 / 2) ≤ (512 : ℝ) * 2 ^ n := by
  let A : ℝ := 2 ^ n
  let v : ℝ := (1 / 2 : ℝ) ^ (1 / 2 : ℝ)
  let u : ℝ := (2 : ℝ) ^ (1 / 2 : ℝ)
  let T : ℝ := A / (1 - v)
  let H : ℝ := 2 * A * (u / (1 - v) + (4 : ℝ) ^ (1 / 2 : ℝ))
  have hA : 1 ≤ A := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hvSq : v ^ 2 = (1 / 2 : ℝ) := by
    dsimp only [v]
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hv : v ≤ (3 / 4 : ℝ) := by
    have hv0 : 0 ≤ v := Real.rpow_nonneg (by norm_num) _
    nlinarith only [hvSq, hv0]
  have huSq : u ^ 2 = (2 : ℝ) := by
    dsimp only [u]
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hu : u ≤ (3 / 2 : ℝ) := by
    have hu0 : 0 ≤ u := Real.rpow_nonneg (by norm_num) _
    nlinarith only [huSq, hu0]
  have hfour : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow]
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hd : 0 < 1 - v := by linarith only [hv]
  have hfrac : u / (1 - v) ≤ 6 :=
    (div_le_iff₀ hd).mpr (by linarith only [hu, hv])
  have hT : T ≤ 4 * A := by
    apply (div_le_iff₀ hd).mpr
    have Hmul := mul_le_mul_of_nonneg_left (show (1 / 4 : ℝ) ≤ 1 - v by linarith only [hv]) hAp
    nlinarith only [Hmul]
  have hH : H ≤ 16 * A := by
    dsimp only [H]
    rw [hfour]
    have Hmul := mul_le_mul_of_nonneg_left
      (show u / (1 - v) + 2 ≤ 8 by linarith only [hfrac]) (show 0 ≤ 2 * A by positivity)
    nlinarith only [Hmul]
  have hT0 : 0 ≤ T := div_nonneg hAp hd.le
  change 1 + |T| + 16 * H ≤ 512 * A
  rw [abs_of_nonneg hT0]
  nlinarith only [hT, hH, hA]

end Analysis

end StationaryHarmonicMaps

end
