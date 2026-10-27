module

public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Affine averages of an integrable density on a ball

The two halves of the segment parameter admit a change of variables with
Jacobian bounded by `2 ^ n`. Tonelli's theorem supplies joint integrability
before the real iterated integral is estimated.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace HarmonicMaps

private theorem affine_integrable {n : ℕ} {f : Domain n → ℝ}
    (hf : Integrable f) {c : ℝ} (hc : c ≠ 0) (b : Domain n) :
    Integrable (fun x => f (c • x + b)) :=
  (hf.comp_add_right b).comp_smul hc

private theorem affine_integral {n : ℕ} (f : Domain n → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (b : Domain n) :
    (∫ x, f (c • x + b)) = (c ^ n)⁻¹ * ∫ x, f x := by
  rw [Measure.integral_comp_smul_of_nonneg volume (fun x => f (x + b)) c
    (hR := hc)]
  simp only [Domain, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
    integral_add_right_eq_self]

private theorem affine_setIntegral_le {n : ℕ} {f : Domain n → ℝ}
    (hf : Integrable f) (hfn : ∀ x, 0 ≤ f x) (s : Set (Domain n))
    {c : ℝ} (hc : (1 : ℝ) / 2 ≤ c) (b : Domain n) :
    (∫ x in s, f (c • x + b)) ≤ (2 : ℝ) ^ n * ∫ x, f x := by
  have hcpos : 0 < c := by linarith
  have hcinv : c⁻¹ ≤ (2 : ℝ) := by
    apply (inv_le_comm₀ hcpos (by norm_num : (0 : ℝ) < 2)).mpr
    norm_num
    exact hc
  calc
    (∫ x in s, f (c • x + b)) ≤ ∫ x, f (c • x + b) :=
      setIntegral_le_integral (affine_integrable hf hcpos.ne' b)
        (Eventually.of_forall fun x => hfn _)
    _ = (c⁻¹) ^ n * ∫ x, f x := by
      rw [affine_integral f hcpos.le b, inv_pow]
    _ ≤ (2 : ℝ) ^ n * ∫ x, f x :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.mpr hcpos.le) hcinv n)
        (integral_nonneg hfn)

private theorem affine_setLIntegral_le {n : ℕ} {f : Domain n → ℝ}
    (hf : Integrable f) (hfn : ∀ x, 0 ≤ f x) (s : Set (Domain n))
    {c : ℝ} (hc : (1 : ℝ) / 2 ≤ c) (b : Domain n) :
    (∫⁻ x in s, ENNReal.ofReal (f (c • x + b))) ≤
      ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ x, ENNReal.ofReal (f x) := by
  have hci : Integrable (fun x => f (c • x + b)) :=
    affine_integrable hf (by linarith) b
  rw [← ofReal_integral_eq_lintegral_ofReal hci.integrableOn
    (Eventually.of_forall fun x => hfn _),
    ← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hfn),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ n)]
  exact ENNReal.ofReal_le_ofReal (affine_setIntegral_le hf hfn s hc b)

private theorem affine_double_lintegral_le {n : ℕ} {f : Domain n → ℝ}
    (hfm : Measurable f) (hf : Integrable f) (hfn : ∀ x, 0 ≤ f x)
    (a : Domain n) (r : ℝ) {t : ℝ} (_ht : t ∈ Icc (0 : ℝ) 1) :
    (∫⁻ x in Metric.ball a r, ∫⁻ y in Metric.ball a r,
      ENNReal.ofReal (f ((1 - t) • x + t • y))) ≤
      ENNReal.ofReal ((2 : ℝ) ^ n) * volume (Metric.ball a r) *
        ∫⁻ z, ENNReal.ofReal (f z) := by
  by_cases hthalf : t ≤ (1 : ℝ) / 2
  · rw [lintegral_lintegral_swap
      ((hfm.comp (by fun_prop : Measurable (fun p : Domain n × Domain n =>
        (1 - t) • p.1 + t • p.2))).ennreal_ofReal.aemeasurable)]
    calc
      _ ≤ ∫⁻ y in Metric.ball a r,
          ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z, ENNReal.ofReal (f z) := by
        apply lintegral_mono
        intro y
        exact affine_setLIntegral_le hf hfn (Metric.ball a r) (by linarith) (t • y)
      _ = _ := by simp [lintegral_const, mul_assoc, mul_comm, mul_left_comm]
  · calc
      _ ≤ ∫⁻ x in Metric.ball a r,
          ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z, ENNReal.ofReal (f z) := by
        apply lintegral_mono
        intro x
        simpa only [add_comm] using
          affine_setLIntegral_le hf hfn (Metric.ball a r) (c := t) (by linarith)
            ((1 - t) • x)
      _ = _ := by simp [lintegral_const, mul_assoc, mul_comm, mul_left_comm]

private theorem affine_triple_lintegral_le {n : ℕ} {f : Domain n → ℝ}
    (hfm : Measurable f) (hf : Integrable f) (hfn : ∀ x, 0 ≤ f x)
    (a : Domain n) (r : ℝ) :
    (∫⁻ p : Domain n × (Domain n × ℝ),
      ENNReal.ofReal (f ((1 - p.2.2) • p.1 + p.2.2 • p.2.1))
      ∂(volume.restrict (Metric.ball a r)).prod
        ((volume.restrict (Metric.ball a r)).prod (volume.restrict (Icc (0 : ℝ) 1)))) ≤
      ENNReal.ofReal ((2 : ℝ) ^ n) * volume (Metric.ball a r) *
        ∫⁻ z, ENNReal.ofReal (f z) := by
  let B := Metric.ball a r
  let F := fun x y (t : ℝ) => ENNReal.ofReal (f ((1 - t) • x + t • y))
  have hF : Measurable (fun p : Domain n × (Domain n × ℝ) => F p.1 p.2.1 p.2.2) :=
    (hfm.comp (by fun_prop)).ennreal_ofReal
  have hFy (x : Domain n) : Measurable (fun p : Domain n × ℝ => F x p.1 p.2) :=
    (hfm.comp (by fun_prop)).ennreal_ofReal
  have hFxy : Measurable (fun p : Domain n × ℝ => ∫⁻ y in B, F p.1 y p.2) := by
    exact ((hfm.comp (by fun_prop : Measurable (fun p : (Domain n × ℝ) × Domain n =>
      (1 - p.1.2) • p.1.1 + p.1.2 • p.2))).ennreal_ofReal).lintegral_prod_right'
  change (∫⁻ p : Domain n × (Domain n × ℝ), F p.1 p.2.1 p.2.2
    ∂(volume.restrict B).prod ((volume.restrict B).prod (volume.restrict (Icc (0 : ℝ) 1)))) ≤ _
  rw [lintegral_prod _ hF.aemeasurable]
  simp_rw [lintegral_prod _ (hFy _).aemeasurable]
  have hswap (x : Domain n) :
      (∫⁻ y in B, ∫⁻ t in Icc (0 : ℝ) 1, F x y t) =
        ∫⁻ t in Icc (0 : ℝ) 1, ∫⁻ y in B, F x y t :=
    lintegral_lintegral_swap (hFy x).aemeasurable
  simp_rw [hswap]
  rw [lintegral_lintegral_swap hFxy.aemeasurable]
  calc
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
        ENNReal.ofReal ((2 : ℝ) ^ n) * volume B *
          ∫⁻ z, ENNReal.ofReal (f z) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact affine_double_lintegral_le hfm hf hfn a r ht
    _ = _ := by simp [lintegral_const, Real.volume_Icc, B]

/-- Zero extension on a ball does not change its affine pullback almost
everywhere on the ball product and the segment parameter. -/
theorem ball_affine_indicator_ae {n : ℕ} (a : Domain n) (r : ℝ)
    (g : Domain n → ℝ) :
    (fun p : Domain n × (Domain n × ℝ) =>
      (Metric.ball a r).indicator g ((1 - p.2.2) • p.1 + p.2.2 • p.2.1)) =ᵐ[
      (volume.restrict (Metric.ball a r)).prod
        ((volume.restrict (Metric.ball a r)).prod (volume.restrict (Icc (0 : ℝ) 1)))]
      (fun p : Domain n × (Domain n × ℝ) =>
        g ((1 - p.2.2) • p.1 + p.2.2 • p.2.1)) := by
  rw [Measure.prod_restrict, Measure.prod_restrict]
  filter_upwards [ae_restrict_mem
    (measurableSet_ball.prod (measurableSet_ball.prod measurableSet_Icc))] with p hp
  have hz : (1 - p.2.2) • p.1 + p.2.2 • p.2.1 ∈ Metric.ball a r :=
    convex_ball a r hp.1 hp.2.1 (by linarith [hp.2.2.2]) hp.2.2.1 (by ring)
  exact indicator_of_mem hz g

/-- Zero extension preserves a ball's set integral. -/
theorem ball_setIntegral_indicator {n : ℕ} (a : Domain n) (r : ℝ)
    (g : Domain n → ℝ) :
    (∫ z in Metric.ball a r, (Metric.ball a r).indicator g z) =
      ∫ z in Metric.ball a r, g z := by
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  exact indicator_of_mem hz g

/-- Zero extension preserves the segment integral between two points of a ball. -/
theorem ball_affine_segmentIntegral_indicator {n : ℕ} {a x y : Domain n} {r : ℝ}
    (hx : x ∈ Metric.ball a r) (hy : y ∈ Metric.ball a r) (g : Domain n → ℝ) :
    (∫ t in Icc (0 : ℝ) 1,
      (Metric.ball a r).indicator g ((1 - t) • x + t • y)) =
      ∫ t in Icc (0 : ℝ) 1, g ((1 - t) • x + t • y) := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  exact indicator_of_mem (convex_ball a r hx hy (by linarith [ht.2]) ht.1 (by ring)) g

/-- The endpoint function defined by a segment integral is unchanged almost
everywhere when its density is extended by zero from the ball. -/
theorem ball_affine_segmentIntegral_indicator_ae {n : ℕ} (a : Domain n) (r : ℝ)
    (g : Domain n → ℝ) :
    (fun p : Domain n × Domain n => ∫ t in Icc (0 : ℝ) 1,
      (Metric.ball a r).indicator g ((1 - t) • p.1 + t • p.2)) =ᵐ[
        (volume.restrict (Metric.ball a r)).prod (volume.restrict (Metric.ball a r))]
      (fun p : Domain n × Domain n =>
        ∫ t in Icc (0 : ℝ) 1, g ((1 - t) • p.1 + t • p.2)) := by
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_ball.prod measurableSet_ball)] with p hp
  exact ball_affine_segmentIntegral_indicator hp.1 hp.2 g

/-- Zero extension preserves the three iterated affine integrals on a ball. -/
theorem ball_affine_iteratedIntegral_indicator {n : ℕ} (a : Domain n) (r : ℝ)
    (g : Domain n → ℝ) :
    (∫ x in Metric.ball a r, ∫ y in Metric.ball a r, ∫ t in Icc (0 : ℝ) 1,
      (Metric.ball a r).indicator g ((1 - t) • x + t • y)) =
      ∫ x in Metric.ball a r, ∫ y in Metric.ball a r, ∫ t in Icc (0 : ℝ) 1,
        g ((1 - t) • x + t • y) := by
  apply setIntegral_congr_fun measurableSet_ball
  intro x hx
  apply setIntegral_congr_fun measurableSet_ball
  intro y hy
  exact ball_affine_segmentIntegral_indicator hx hy g

/-- A nonnegative measurable density integrable on a ball has an integrable
affine pullback on the two ball variables and the segment parameter. Its
iterated integral is bounded using the two parameter halves. -/
theorem ball_affine_integrable_and_integral_le {n : ℕ}
    {a : Domain n} {r : ℝ} {g : Domain n → ℝ}
    (hg : Measurable g) (hgn : ∀ x ∈ Metric.ball a r, 0 ≤ g x)
    (hgi : IntegrableOn g (Metric.ball a r)) :
    Integrable (fun p : Domain n × (Domain n × ℝ) =>
      g ((1 - p.2.2) • p.1 + p.2.2 • p.2.1))
      ((volume.restrict (Metric.ball a r)).prod
        ((volume.restrict (Metric.ball a r)).prod (volume.restrict (Icc (0 : ℝ) 1)))) ∧
    (∫ x in Metric.ball a r, ∫ y in Metric.ball a r, ∫ t in Icc (0 : ℝ) 1,
      g ((1 - t) • x + t • y)) ≤
      (2 : ℝ) ^ n * volume.real (Metric.ball a r) * ∫ z in Metric.ball a r, g z := by
  let B := Metric.ball a r
  let f := B.indicator g
  let μ := (volume.restrict B).prod
    ((volume.restrict B).prod (volume.restrict (Icc (0 : ℝ) 1)))
  let H := fun p : Domain n × (Domain n × ℝ) =>
    f ((1 - p.2.2) • p.1 + p.2.2 • p.2.1)
  have hfm : Measurable f := hg.indicator measurableSet_ball
  have hfi : Integrable f := hgi.integrable_indicator measurableSet_ball
  have hfn : ∀ x, 0 ≤ f x := by
    intro x
    by_cases hx : x ∈ B
    · simpa [f, indicator_of_mem hx] using hgn x hx
    · simp [f, indicator_of_notMem hx]
  have hHm : Measurable H := hfm.comp (by fun_prop)
  have hHn : ∀ p, 0 ≤ H p := fun p => hfn _
  have hL := affine_triple_lintegral_le hfm hfi hfn a r
  have hfL : (∫⁻ z, ENNReal.ofReal (f z)) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hfm.stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall hfn)).mpr hfi
  have hR : ENNReal.ofReal ((2 : ℝ) ^ n) * volume B *
      (∫⁻ z, ENNReal.ofReal (f z)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_ne_top) hfL
  have hHL : (∫⁻ p, ENNReal.ofReal (H p) ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top hR hL
  have hHi : Integrable H μ :=
    (lintegral_ofReal_ne_top_iff_integrable hHm.stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall hHn)).mp hHL
  have hEq : H =ᵐ[μ] (fun p : Domain n × (Domain n × ℝ) =>
      g ((1 - p.2.2) • p.1 + p.2.2 • p.2.1)) :=
    ball_affine_indicator_ae a r g
  have hJ : Integrable (fun p : Domain n × (Domain n × ℝ) =>
      g ((1 - p.2.2) • p.1 + p.2.2 • p.2.1)) μ := hHi.congr hEq
  refine ⟨hJ, ?_⟩
  have hFub : (∫ p : Domain n × (Domain n × ℝ),
      g ((1 - p.2.2) • p.1 + p.2.2 • p.2.1) ∂μ) =
      ∫ x in B, ∫ y in B, ∫ t in Icc (0 : ℝ) 1, g ((1 - t) • x + t • y) := by
    rw [integral_prod _ hJ]
    apply integral_congr_ae
    filter_upwards [hJ.prod_right_ae] with x hx
    exact integral_prod _ hx
  rw [← hFub, ← integral_congr_ae hEq]
  calc
    (∫ p, H p ∂μ) = (∫⁻ p, ENNReal.ofReal (H p) ∂μ).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hHn)
        hHi.aestronglyMeasurable
    _ ≤ (ENNReal.ofReal ((2 : ℝ) ^ n) * volume B *
        ∫⁻ z, ENNReal.ofReal (f z)).toReal := ENNReal.toReal_mono hR hL
    _ = (2 : ℝ) ^ n * volume.real B * ∫ z in B, g z := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 : ℝ) ^ n),
        ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hfn)
          hfi.aestronglyMeasurable]
      rw [show f = B.indicator g from rfl,
        integral_indicator (show MeasurableSet B from measurableSet_ball)]
      rfl

/-- The segment integral is integrable jointly in its two endpoints. -/
theorem ball_affine_segmentIntegral_integrable {n : ℕ}
    {a : Domain n} {r : ℝ} {g : Domain n → ℝ}
    (hg : Measurable g) (hgn : ∀ x ∈ Metric.ball a r, 0 ≤ g x)
    (hgi : IntegrableOn g (Metric.ball a r)) :
    Integrable (fun p : Domain n × Domain n =>
      ∫ t in Icc (0 : ℝ) 1, g ((1 - t) • p.1 + t • p.2))
      ((volume.restrict (Metric.ball a r)).prod (volume.restrict (Metric.ball a r))) := by
  have hJ := (ball_affine_integrable_and_integral_le hg hgn hgi).1
  have hAssoc := (measurePreserving_prodAssoc
    (volume.restrict (Metric.ball a r)) (volume.restrict (Metric.ball a r))
      (volume.restrict (Icc (0 : ℝ) 1))).integrable_comp hJ.aestronglyMeasurable |>.mpr hJ
  exact hAssoc.integral_prod_left

/-- The segment density is integrable in the parameter for almost every
pair of endpoints in the ball. -/
theorem ball_affine_parameter_integrable_ae {n : ℕ}
    {a : Domain n} {r : ℝ} {g : Domain n → ℝ}
    (hg : Measurable g) (hgn : ∀ x ∈ Metric.ball a r, 0 ≤ g x)
    (hgi : IntegrableOn g (Metric.ball a r)) :
    ∀ᵐ p : Domain n × Domain n
      ∂(volume.restrict (Metric.ball a r)).prod (volume.restrict (Metric.ball a r)),
      IntegrableOn (fun t : ℝ => g ((1 - t) • p.1 + t • p.2)) (Icc (0 : ℝ) 1) := by
  have hJ := (ball_affine_integrable_and_integral_le hg hgn hgi).1
  have hAssoc := (measurePreserving_prodAssoc
    (volume.restrict (Metric.ball a r)) (volume.restrict (Metric.ball a r))
      (volume.restrict (Icc (0 : ℝ) 1))).integrable_comp hJ.aestronglyMeasurable |>.mpr hJ
  exact hAssoc.prod_right_ae

/-- The inner endpoint integral exists for almost every outer endpoint. -/
theorem ball_affine_inner_integrable_ae {n : ℕ}
    {a : Domain n} {r : ℝ} {g : Domain n → ℝ}
    (hg : Measurable g) (hgn : ∀ x ∈ Metric.ball a r, 0 ≤ g x)
    (hgi : IntegrableOn g (Metric.ball a r)) :
    ∀ᵐ x ∂volume.restrict (Metric.ball a r),
      IntegrableOn (fun y => ∫ t in Icc (0 : ℝ) 1, g ((1 - t) • x + t • y))
        (Metric.ball a r) :=
  (ball_affine_segmentIntegral_integrable hg hgn hgi).prod_right_ae

/-- The iterated inner integrals are integrable in the outer endpoint. -/
theorem ball_affine_outer_integrable {n : ℕ}
    {a : Domain n} {r : ℝ} {g : Domain n → ℝ}
    (hg : Measurable g) (hgn : ∀ x ∈ Metric.ball a r, 0 ≤ g x)
    (hgi : IntegrableOn g (Metric.ball a r)) :
    IntegrableOn (fun x => ∫ y in Metric.ball a r, ∫ t in Icc (0 : ℝ) 1,
      g ((1 - t) • x + t • y)) (Metric.ball a r) :=
  (ball_affine_segmentIntegral_integrable hg hgn hgi).integral_prod_left

end HarmonicMaps
