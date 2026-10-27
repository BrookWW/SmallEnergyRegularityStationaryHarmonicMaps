module

public import StationaryHarmonicMaps.Analysis.MeanOscillation
public import HarmonicMaps.Analysis.BallAverageDifferentiation
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Representatives from all-center mean oscillation

Local L¹ integrability and a power bound for the literal mean oscillation give
one continuous representative. The representative is the limit of all positive
ball radii, agrees almost everywhere with the original function, and satisfies
a quantitative Hölder estimate for distances below the reference scale.

These results do not prove the Sobolev Poincaré estimate that can supply the
mean-oscillation bound from gradient growth.
-/

public section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace StationaryHarmonicMaps

section EuclideanMeans

variable {n : ℕ} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Local L¹ integrability differentiates the actual open-ball Bochner means. -/
theorem locallyIntegrable_ae_tendsto_ballAverage
    (f : EuclideanSpace ℝ (Fin n) → E) (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume,
      Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, f y)
        (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have hnative := IsUnifLocDoublingMeasure.ae_tendsto_average volume hf 1
  filter_upwards [hnative] with x hx
  have hcenter : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      x ∈ Metric.closedBall x (1 * r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [mem_closedBall, dist_self, one_mul] using hr.le
  have hlimit := hx (fun _r : ℝ => x) (fun r : ℝ => r) tendsto_id hcenter
  have heq : (fun r : ℝ => ⨍ y in Metric.ball x r, f y) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun r : ℝ => ⨍ y in Metric.closedBall x r, f y) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact setAverage_congr (HarmonicMaps.ball_ae_eq_closedBall x hr)
  exact hlimit.congr' heq.symm

/-- All literal means converge to a single function which agrees almost everywhere. -/
theorem exists_ballAverage_representative_of_meanOscillation
    (f : EuclideanSpace ℝ (Fin n) → E) (hf : LocallyIntegrable f volume)
    {α K r₀ : ℝ} (hα : 0 < α) (hK : 0 ≤ K) (hr₀ : 0 < r₀)
    (hosc : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → r ≤ r₀ →
      (⨍ y in Metric.ball x r, ‖f y - (⨍ z in Metric.ball x r, f z)‖) ≤
        K * r ^ α) :
    ∃ w : EuclideanSpace ℝ (Fin n) → E,
      (∀ x, Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, f y)
        (𝓝[>] (0 : ℝ)) (𝓝 (w x))) ∧
      (∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → r ≤ r₀ →
        ‖(⨍ y in Metric.ball x r, f y) - w x‖ ≤
          ((2 : ℝ) ^ n * K) * r ^ α / (1 - (1 / 2 : ℝ) ^ α)) ∧
      w =ᵐ[volume] f := by
  classical
  have hex (x : EuclideanSpace ℝ (Fin n)) :=
    existsUnique_ballAverage_limit_of_meanOscillation_radius f x hα hK hr₀
      ((hf.integrableOn_isCompact (isCompact_closedBall x r₀)).mono_set
        Metric.ball_subset_closedBall) (hosc x)
  let w : EuclideanSpace ℝ (Fin n) → E := fun x => (hex x).exists.choose
  have hw (x : EuclideanSpace ℝ (Fin n)) := (hex x).exists.choose_spec
  refine ⟨w, (fun x => (hw x).1), (fun x => (hw x).2), ?_⟩
  filter_upwards [locallyIntegrable_ae_tendsto_ballAverage f hf] with x hx
  exact tendsto_nhds_unique (hw x).1 hx

/-- The dimension and exponent constant in the near-point Campanato estimate. -/
noncomputable def meanOscillationHolderConstant (n : ℕ) (α : ℝ) : ℝ :=
  2 * (2 : ℝ) ^ n *
    ((2 : ℝ) ^ α / (1 - (1 / 2 : ℝ) ^ α) + (4 : ℝ) ^ α)

/-- The limit tails and actual mean oscillation give a quantitative near-point estimate. -/
theorem ballAverage_limit_holder_near
    (f w : EuclideanSpace ℝ (Fin n) → E) (hf : LocallyIntegrable f volume)
    {α K r₀ : ℝ} (hα : 0 < α) (hr₀ : 0 < r₀)
    (hosc : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → r ≤ r₀ →
      (⨍ y in Metric.ball x r, ‖f y - (⨍ z in Metric.ball x r, f z)‖) ≤
        K * r ^ α)
    (htail : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → r ≤ r₀ →
      ‖(⨍ y in Metric.ball x r, f y) - w x‖ ≤
        ((2 : ℝ) ^ n * K) * r ^ α / (1 - (1 / 2 : ℝ) ^ α))
    (x y : EuclideanSpace ℝ (Fin n)) (hd : dist x y ≤ r₀ / 4) :
    ‖w x - w y‖ ≤ meanOscillationHolderConstant n α * K * (dist x y) ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, dist_self, Real.zero_rpow hα.ne', mul_zero, le_refl]
  let d : ℝ := dist x y
  have hdpos : 0 < d := dist_pos.mpr hxy
  have h2d : 0 < 2 * d := mul_pos (by norm_num) hdpos
  have h4d : 0 < 4 * d := mul_pos (by norm_num) hdpos
  have h2cap : 2 * d ≤ r₀ := by dsimp only [d]; linarith only [hd, hr₀]
  have h4cap : 4 * d ≤ r₀ := by dsimp only [d]; linarith only [hd]
  have hxsub : Metric.ball x (2 * d) ⊆ Metric.ball x (4 * d) :=
    Metric.ball_subset_ball (by linarith only [hdpos])
  have hysub : Metric.ball y (2 * d) ⊆ Metric.ball x (4 * d) := by
    apply Metric.ball_subset_ball'
    rw [dist_comm]
    change 2 * d + d ≤ 4 * d
    linarith only [hdpos]
  have hfi : IntegrableOn f (Metric.ball x (4 * d)) volume :=
    (hf.integrableOn_isCompact (isCompact_closedBall x (4 * d))).mono_set
      Metric.ball_subset_closedBall
  have hxc := norm_ballAverage_sub_le_meanOscillation f h2d h4d hxsub
    (show 4 * d ≤ 2 * (2 * d) by ring_nf; exact le_rfl) hfi
  have hyc := norm_ballAverage_sub_le_meanOscillation f h2d h4d hysub
    (show 4 * d ≤ 2 * (2 * d) by ring_nf; exact le_rfl) hfi
  have hosc4 := mul_le_mul_of_nonneg_left (hosc x (4 * d) h4d h4cap)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
  have hxc' := hxc.trans hosc4
  have hyc' := hyc.trans hosc4
  have hxt := htail x (2 * d) h2d h2cap
  have hyt := htail y (2 * d) h2d h2cap
  let mx : E := ⨍ z in Metric.ball x (2 * d), f z
  let my : E := ⨍ z in Metric.ball y (2 * d), f z
  let mc : E := ⨍ z in Metric.ball x (4 * d), f z
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
    ‖w x - w y‖ ≤ _ := hbound
    _ = meanOscillationHolderConstant n α * K * (dist x y) ^ α := by
      dsimp only [meanOscillationHolderConstant, d]
      ring

end EuclideanMeans

section Continuity

/-- A power estimate for all sufficiently close pairs gives continuity. -/
theorem continuous_of_norm_sub_le_rpow_near
    {X E : Type*} [MetricSpace X] [NormedAddCommGroup E]
    (w : X → E) {α D R : ℝ} (hα : 0 < α) (hR : 0 < R)
    (hnear : ∀ x y : X, dist x y ≤ R → ‖w x - w y‖ ≤ D * (dist x y) ^ α) :
    Continuous w := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc : Continuous (fun y : X => D * (dist y x) ^ α) :=
    continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
      (continuous_id.dist continuous_const))
  have hz : Tendsto (fun y : X => D * (dist y x) ^ α) (𝓝 x) (𝓝 0) := by
    simpa only [dist_self, Real.zero_rpow hα.ne', mul_zero] using hc.tendsto x
  filter_upwards [Metric.ball_mem_nhds x hR, (tendsto_order.mp hz).2 ε hε]
    with y hy hbound
  exact lt_of_le_of_lt
    (by simpa only [dist_eq_norm] using hnear y x (le_of_lt hy)) hbound

end Continuity

/-- All-center mean oscillation gives the unique continuous representative and near Hölder bound. -/
theorem existsUnique_continuous_representative_of_meanOscillation
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : EuclideanSpace ℝ (Fin n) → E) (hf : LocallyIntegrable f volume)
    {α K r₀ : ℝ} (hα : 0 < α) (hK : 0 ≤ K) (hr₀ : 0 < r₀)
    (hosc : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → r ≤ r₀ →
      (⨍ y in Metric.ball x r, ‖f y - (⨍ z in Metric.ball x r, f z)‖) ≤
        K * r ^ α) :
    ∃! w : EuclideanSpace ℝ (Fin n) → E,
      Continuous w ∧ w =ᵐ[volume] f ∧
      (∀ x, Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, f y)
        (𝓝[>] (0 : ℝ)) (𝓝 (w x))) ∧
      (∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → r ≤ r₀ →
        ‖(⨍ y in Metric.ball x r, f y) - w x‖ ≤
          ((2 : ℝ) ^ n * K) * r ^ α / (1 - (1 / 2 : ℝ) ^ α)) ∧
      (∀ x y : EuclideanSpace ℝ (Fin n), dist x y ≤ r₀ / 4 →
        ‖w x - w y‖ ≤ meanOscillationHolderConstant n α * K * (dist x y) ^ α) := by
  obtain ⟨w, hlimit, htail, hae⟩ :=
    exists_ballAverage_representative_of_meanOscillation f hf hα hK hr₀ hosc
  have hnear := ballAverage_limit_holder_near f w hf hα hr₀ hosc htail
  have hcont : Continuous w := continuous_of_norm_sub_le_rpow_near w hα
    (div_pos hr₀ (by norm_num : (0 : ℝ) < 4)) hnear
  refine ⟨w, ⟨hcont, hae, hlimit, htail, hnear⟩, ?_⟩
  intro v hv
  exact MeasureTheory.Measure.eq_of_ae_eq (hv.2.1.trans hae.symm) hv.1 hcont

end StationaryHarmonicMaps

end
