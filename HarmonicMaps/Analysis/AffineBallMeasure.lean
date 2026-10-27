module

public import HarmonicMaps.Analysis.AffineSobolevTransform
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Exact measure transport between two balls

Positive affine maps transfer restricted volume, arbitrary L2 data and their
literal integral expressions. Centers are independent of the dilation center.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

namespace HarmonicMaps

theorem affineBall_contDiff {n : ℕ} (a b : Domain n) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => a + t • (x - b)) :=
  contDiff_const.add ((contDiff_id.sub contDiff_const).const_smul t)

theorem affineBall_inverse {n : ℕ} (a b : Domain n) {t : ℝ} (ht : t ≠ 0)
    (x : Domain n) : b + t⁻¹ • ((a + t • (x - b)) - a) = x := by
  simp [smul_smul, ht]

theorem affineBall_mem_ball_iff {n : ℕ} (a b : Domain n) {t : ℝ}
    (ht : 0 < t) (r : ℝ) (x : Domain n) :
    a + t • (x - b) ∈ Metric.ball a r ↔ x ∈ Metric.ball b (r / t) := by
  simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht]
  rw [lt_div_iff₀ ht, mul_comm]

theorem affineBall_mem_closedBall_iff {n : ℕ} (a b : Domain n) {t : ℝ}
    (ht : 0 < t) (r : ℝ) (x : Domain n) :
    a + t • (x - b) ∈ Metric.closedBall a r ↔ x ∈ Metric.closedBall b (r / t) := by
  simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht]
  rw [le_div_iff₀ ht, mul_comm]

theorem affineBall_measurableEmbedding {n : ℕ} (a b : Domain n) {t : ℝ}
    (ht : t ≠ 0) : MeasurableEmbedding (fun x => a + t • (x - b)) := by
  let e := (Homeomorph.addRight (-b)).trans
    ((Homeomorph.smul (Units.mk0 t ht)).trans (Homeomorph.addLeft a))
  convert e.isClosedEmbedding.measurableEmbedding using 1
  funext x
  simp [e, sub_eq_add_neg]

theorem affineBall_map_volume {n : ℕ} (a b : Domain n) {t : ℝ}
    (ht : 0 < t) :
    Measure.map (fun x => a + t • (x - b)) volume =
      ENNReal.ofReal ((t ^ n)⁻¹) • volume := by
  change Measure.map ((fun x : Domain n => a + x) ∘
    ((fun x : Domain n => t • x) ∘ (fun x => x - b))) volume = _
  rw [← Measure.map_map (by fun_prop : Measurable (fun x : Domain n => a + x))
      (by fun_prop : Measurable ((fun x : Domain n => t • x) ∘ (fun x => x - b))),
    ← Measure.map_map (by fun_prop : Measurable (fun x : Domain n => t • x))
      (by fun_prop : Measurable (fun x : Domain n => x - b)),
    (measurePreserving_sub_right volume b).map_eq,
    Measure.map_addHaar_smul volume ht.ne', Measure.map_smul,
    (measurePreserving_add_left volume a).map_eq]
  simp only [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos ht n))]

theorem affineBall_map_restrict {n : ℕ} (a b : Domain n) {t : ℝ}
    (ht : 0 < t) (r : ℝ) :
    Measure.map (fun x => a + t • (x - b))
      (volume.restrict (Metric.ball b (r / t))) =
      ENNReal.ofReal ((t ^ n)⁻¹) • volume.restrict (Metric.ball a r) := by
  have he := affineBall_measurableEmbedding a b ht.ne'
  have hs : (fun x => a + t • (x - b)) ⁻¹' Metric.ball a r =
      Metric.ball b (r / t) := by
    ext x
    exact affineBall_mem_ball_iff a b ht r x
  rw [← hs, ← he.restrict_map, affineBall_map_volume a b ht, Measure.restrict_smul]

theorem memLp_affineBall {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (a b : Domain n) {t : ℝ} (ht : 0 < t) (r : ℝ)
    {f : Domain n → E} (hf : MemLp f 2 (volume.restrict (Metric.ball a r))) :
    MemLp (fun x => f (a + t • (x - b))) 2
      (volume.restrict (Metric.ball b (r / t))) := by
  have hh := hf.smul_measure (c := ENNReal.ofReal ((t ^ n)⁻¹)) ENNReal.ofReal_ne_top
  rw [← affineBall_map_restrict a b ht r] at hh
  exact hh.comp_of_map (affineBall_measurableEmbedding a b ht.ne').measurable.aemeasurable

theorem eLpNorm_affineBall {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (a b : Domain n) {t : ℝ} (ht : 0 < t) (r : ℝ) (f : Domain n → E) :
    eLpNorm (fun x => f (a + t • (x - b))) 2
      (volume.restrict (Metric.ball b (r / t))) =
      ENNReal.ofReal ((t ^ n)⁻¹) ^ (1 / 2 : ℝ) *
        eLpNorm f 2 (volume.restrict (Metric.ball a r)) := by
  change eLpNorm (f ∘ (fun x => a + t • (x - b))) 2 _ = _
  rw [← (affineBall_measurableEmbedding a b ht.ne').eLpNorm_map_measure,
    affineBall_map_restrict a b ht r,
    eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))]
  norm_num

theorem integral_affineBall {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a b : Domain n) {t : ℝ} (ht : 0 < t)
    (r : ℝ) (f : Domain n → E) :
    (∫ x in Metric.ball b (r / t), f (a + t • (x - b))) =
      (t ^ n)⁻¹ • ∫ x in Metric.ball a r, f x := by
  rw [← (affineBall_measurableEmbedding a b ht.ne').integral_map,
    affineBall_map_restrict a b ht r, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg ht.le n))]

theorem lintegral_affineBall {n : ℕ} (a b : Domain n) {t : ℝ} (ht : 0 < t)
    (r : ℝ) (f : Domain n → ℝ≥0∞) :
    (∫⁻ x in Metric.ball b (r / t), f (a + t • (x - b))) =
      ENNReal.ofReal ((t ^ n)⁻¹) * ∫⁻ x in Metric.ball a r, f x := by
  rw [← (affineBall_measurableEmbedding a b ht.ne').lintegral_map,
    affineBall_map_restrict a b ht r, lintegral_smul_measure]
  rfl

theorem ae_affineBall {n : ℕ} (a b : Domain n) {t : ℝ} (ht : 0 < t)
    (r : ℝ) {p : Domain n → Prop}
    (hp : ∀ᵐ x ∂volume.restrict (Metric.ball a r), p x) :
    ∀ᵐ x ∂volume.restrict (Metric.ball b (r / t)), p (a + t • (x - b)) := by
  have hpc : ∀ᵐ x ∂(ENNReal.ofReal ((t ^ n)⁻¹) •
      volume.restrict (Metric.ball a r)), p x :=
    Measure.ae_smul_measure hp _
  rw [← affineBall_map_restrict a b ht r] at hpc
  exact ae_of_ae_map (affineBall_measurableEmbedding a b ht.ne').measurable.aemeasurable hpc

theorem affineBallTest_hasCompactSupport {n : ℕ} {E : Type*} [Zero E]
    {f : Domain n → E} (hf : HasCompactSupport f) (a b : Domain n)
    {t : ℝ} (ht : t ≠ 0) :
    HasCompactSupport (fun x => f (a + t • (x - b))) := by
  let e := (Homeomorph.addRight (-b)).trans
    ((Homeomorph.smul (Units.mk0 t ht)).trans (Homeomorph.addLeft a))
  convert hf.comp_homeomorph e using 1
  funext x
  simp [e, sub_eq_add_neg]

theorem affineBallTest_tsupport_subset {n : ℕ} {E : Type*} [Zero E]
    {f : Domain n → E} (a b : Domain n) {t : ℝ} (ht : 0 < t) (r : ℝ)
    (hs : tsupport f ⊆ Metric.ball a r) :
    tsupport (fun x => f (a + t • (x - b))) ⊆ Metric.ball b (r / t) := by
  let e := (Homeomorph.addRight (-b)).trans
    ((Homeomorph.smul (Units.mk0 t ht.ne')).trans (Homeomorph.addLeft a))
  have heq : (fun x => f (a + t • (x - b))) = f ∘ e := by
    funext x
    simp [e, sub_eq_add_neg]
  rw [heq, tsupport_comp_eq_preimage]
  intro x hx
  apply (affineBall_mem_ball_iff a b ht r x).mp
  apply hs
  simpa [e, sub_eq_add_neg] using hx

theorem affineBallTest_coordinateDerivative {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Domain n → E}
    (hf : ContDiff ℝ ∞ f) (a b : Domain n) (t : ℝ) (i : Fin n) (x : Domain n) :
    coordinateDerivative (fun x => f (a + t • (x - b)))
      (hf.comp (affineBall_contDiff a b t)) i x =
      t • coordinateDerivative f hf i (a + t • (x - b)) := by
  have hA := (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const b).const_smul t).const_add a
  have hcomp := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x hA
  change HasFDerivAt (fun z => f (a + t • (z - b)))
    ((fderiv ℝ f (a + t • (x - b))).comp
      (t • ContinuousLinearMap.id ℝ (Domain n))) x at hcomp
  unfold coordinateDerivative
  rw [hcomp.fderiv]
  simp

end HarmonicMaps
