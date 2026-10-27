module

public import HarmonicMaps.Analysis.QuantitativeCutoffProfile
public import HarmonicMaps.Analysis.RadialVectorField
public import Mathlib.Analysis.Calculus.FDeriv.Norm

/-!
# The quantitative radial cutoff

The literal integral profile is constant on the inner ball. This gives
smoothness and zero differential at the origin, while the ordinary norm
chain rule gives the actual differential and its uniform bound elsewhere.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace HarmonicMaps

/-- Every admissible density yields the literal smooth radial cutoff. -/
theorem quantitativeRadialCutoff_properties (b : ℝ → ℝ)
    (hb : ContDiff ℝ ∞ b) (hcompact : HasCompactSupport b)
    (hsupport : tsupport b ⊆ Ioo 0 1)
    (hvalues : ∀ t, 0 ≤ b t ∧ b t ≤ 2) (hmass : (∫ t, b t) = 1)
    (n : ℕ) (theta delta hbar : ℝ)
    (hdelta : 0 < delta) (htheta : delta < theta)
    (_hhalf : theta + 2 * delta < 1 / 2) (hhbar : 0 ≤ hbar) (_hscale : hbar ≤ delta) :
    let beta : ℝ → ℝ := fun t => 1 - ∫ y in Iic t, b y
    let s : Domain n → ℝ := fun x => hbar * beta ((‖x‖ - theta) / delta)
    ContDiff ℝ ∞ s ∧
    HasCompactSupport s ∧
    tsupport s ⊆ Metric.closedBall 0 (theta + delta) ∧
    (∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z) ∧
    (∀ x, 0 ≤ s x ∧ s x ≤ hbar) ∧
    (∀ x ∈ Metric.ball (0 : Domain n) theta, s x = hbar) ∧
    (∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0) ∧
    HasFDerivAt s (0 : Domain n →L[ℝ] ℝ) (0 : Domain n) ∧
    (∀ x : Domain n, x ≠ 0 →
      HasFDerivAt s
        ((-hbar * b ((‖x‖ - theta) / delta) / delta) •
          (‖x‖⁻¹ • innerSL ℝ x)) x) ∧
    (∀ x, ‖fderiv ℝ s x‖ ≤ 2 * hbar / delta) := by
  obtain ⟨hetaSmooth, hetaDeriv, hetaActual, hetaBound, hetaValues, hetaOne, hetaZero⟩ :=
    quantitativeCutoffProfile_scaled b hb hcompact hsupport hvalues hmass
      theta delta hbar hdelta hhbar
  let beta : ℝ → ℝ := fun t => 1 - ∫ y in Iic t, b y
  let eta : ℝ → ℝ := fun r => hbar * beta ((r - theta) / delta)
  let s : Domain n → ℝ := fun x => eta ‖x‖
  have hthetaPos : 0 < theta := hdelta.trans htheta
  have hplateau : ∀ x ∈ Metric.ball (0 : Domain n) theta, s x = hbar := by
    intro x hx
    have hnorm : ‖x‖ < theta := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact hetaOne ‖x‖ hnorm.le
  have hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0 := by
    intro x hx
    apply hetaZero
    exact le_of_not_gt (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
  have hEvent : s =ᶠ[𝓝 (0 : Domain n)] (fun _ => hbar) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Domain n) hthetaPos] with x hx
    exact hplateau x hx
  have hSmooth : ContDiff ℝ ∞ s := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      exact contDiffAt_const.congr_of_eventuallyEq hEvent
    · exact hetaSmooth.contDiffAt.comp x (contDiffAt_norm (𝕜 := ℝ) hx)
  have hTSupport : tsupport s ⊆ Metric.closedBall 0 (theta + delta) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    apply Metric.ball_subset_closedBall
    by_contra hout
    exact hx (hoff x hout)
  have hOrigin : HasFDerivAt s (0 : Domain n →L[ℝ] ℝ) (0 : Domain n) :=
    (hasFDerivAt_const hbar (0 : Domain n)).congr_of_eventuallyEq hEvent
  have hAway : ∀ x : Domain n, x ≠ 0 →
      HasFDerivAt s ((-hbar * b ((‖x‖ - theta) / delta) / delta) •
        (‖x‖⁻¹ • innerSL ℝ x)) x := by
    intro x hx
    exact (hetaDeriv ‖x‖).comp_hasFDerivAt x (radialNorm_hasFDerivAt hx)
  refine ⟨hSmooth, (isCompact_closedBall (0 : Domain n) (theta + delta)).of_isClosed_subset
    (isClosed_tsupport s) hTSupport, hTSupport,
    (fun x z hxz => congrArg eta hxz), (fun x => hetaValues ‖x‖),
    hplateau, hoff, hOrigin, hAway, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    rw [hOrigin.fderiv, norm_zero]
    exact div_nonneg (mul_nonneg (by norm_num) hhbar) hdelta.le
  · have hNorm : ‖‖x‖⁻¹ • innerSL ℝ x‖ ≤ 1 := by
      rw [← (radialNorm_hasFDerivAt hx).fderiv]
      exact norm_fderiv_le_of_lipschitz (f := fun y : Domain n => ‖y‖)
        (x₀ := x) ℝ lipschitzWith_one_norm
    rw [(hAway x hx).fderiv, norm_smul, Real.norm_eq_abs]
    have hScalar : |-hbar * b ((‖x‖ - theta) / delta) / delta| ≤ 2 * hbar / delta := by
      rw [← hetaActual ‖x‖]
      exact hetaBound ‖x‖
    calc
      _ ≤ |-hbar * b ((‖x‖ - theta) / delta) / delta| * 1 :=
        mul_le_mul_of_nonneg_left hNorm (abs_nonneg _)
      _ ≤ 2 * hbar / delta := by simpa only [mul_one] using hScalar

/-- One density works before the dimension and all cutoff scales are chosen. -/
theorem quantitativeRadialCutoff_exists :
    ∃ b : ℝ → ℝ,
      ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ tsupport b ⊆ Ioo 0 1 ∧
      (∀ t, 0 ≤ b t ∧ b t ≤ 2) ∧ (∫ t, b t) = 1 ∧
      (let beta : ℝ → ℝ := fun t => 1 - ∫ y in Iic t, b y
       ContDiff ℝ ∞ beta ∧
       (∀ t, 0 ≤ beta t ∧ beta t ≤ 1) ∧
       (∀ t, t ≤ 0 → beta t = 1) ∧
       (∀ t, 1 ≤ t → beta t = 0) ∧
       (∀ t, HasDerivAt beta (-b t) t) ∧
       (∀ t, deriv beta t = -b t) ∧
       ∀ (n : ℕ) (theta delta hbar : ℝ),
         0 < delta → delta < theta → theta + 2 * delta < 1 / 2 →
         0 ≤ hbar → hbar ≤ delta →
         let s : Domain n → ℝ := fun x => hbar * beta ((‖x‖ - theta) / delta)
         ContDiff ℝ ∞ s ∧
         HasCompactSupport s ∧
         tsupport s ⊆ Metric.closedBall 0 (theta + delta) ∧
         (∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z) ∧
         (∀ x, 0 ≤ s x ∧ s x ≤ hbar) ∧
         (∀ x ∈ Metric.ball (0 : Domain n) theta, s x = hbar) ∧
         (∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0) ∧
         HasFDerivAt s (0 : Domain n →L[ℝ] ℝ) (0 : Domain n) ∧
         (∀ x : Domain n, x ≠ 0 →
           HasFDerivAt s
             ((-hbar * b ((‖x‖ - theta) / delta) / delta) •
               (‖x‖⁻¹ • innerSL ℝ x)) x) ∧
         (∀ x, ‖fderiv ℝ s x‖ ≤ 2 * hbar / delta)) := by
  obtain ⟨b, hb, hcompact, hsupport, hvalues, hmass⟩ := quantitativeCutoffDensity_exists
  obtain ⟨hSmooth, hRange, hOne, hZero, hDeriv, hActual⟩ :=
    quantitativeCutoffProfile_properties b hb hcompact hsupport (fun t => (hvalues t).1) hmass
  exact ⟨b, hb, hcompact, hsupport, hvalues, hmass, hSmooth, hRange, hOne, hZero,
    hDeriv, hActual, quantitativeRadialCutoff_properties b hb hcompact hsupport hvalues hmass⟩

end HarmonicMaps
