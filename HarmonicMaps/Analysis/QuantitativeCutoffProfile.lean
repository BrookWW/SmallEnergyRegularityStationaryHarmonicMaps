module

public import HarmonicMaps.Analysis.QuantitativeCutoffDensity
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The integral profile of a quantitative cutoff density

The literal lower-tail integral defines a smooth decreasing profile. Its
actual derivative is minus the supplied density, and its endpoint plateaux
follow from the compact support inside the open interval.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace HarmonicMaps

/-- The literal cumulative-integral profile has its full source properties. -/
theorem quantitativeCutoffProfile_properties (b : ℝ → ℝ)
    (hb : ContDiff ℝ ∞ b) (hcompact : HasCompactSupport b)
    (hsupport : tsupport b ⊆ Ioo 0 1) (hnonneg : ∀ t, 0 ≤ b t)
    (hmass : (∫ t, b t) = 1) :
    let beta : ℝ → ℝ := fun t => 1 - ∫ y in Iic t, b y
    ContDiff ℝ ∞ beta ∧
    (∀ t, 0 ≤ beta t ∧ beta t ≤ 1) ∧
    (∀ t, t ≤ 0 → beta t = 1) ∧
    (∀ t, 1 ≤ t → beta t = 0) ∧
    (∀ t, HasDerivAt beta (-b t) t) ∧
    (∀ t, deriv beta t = -b t) := by
  dsimp only
  let beta : ℝ → ℝ := fun t => 1 - ∫ y in Iic t, b y
  have hInt : Integrable b volume := hb.continuous.integrable_of_hasCompactSupport hcompact
  have hzero : ∀ t, t ≤ 0 → b t = 0 := by
    intro t ht
    by_contra h
    have hpos := (hsupport (subset_tsupport b h)).1
    exact (not_lt_of_ge ht) hpos
  have hone : ∀ t, 1 ≤ t → b t = 0 := by
    intro t ht
    by_contra h
    have hlt := (hsupport (subset_tsupport b h)).2
    exact (not_lt_of_ge ht) hlt
  have hIicZero : (∫ y in Iic (0 : ℝ), b y) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun y hy => hzero y hy)
  have hprimitive : beta = fun t => 1 - ∫ y in (0 : ℝ)..t, b y := by
    funext t
    have hsplit := intervalIntegral.integral_Iic_sub_Iic
      (hInt.integrableOn (s := Iic 0)) (hInt.integrableOn (s := Iic t))
    rw [hIicZero, sub_zero] at hsplit
    exact congrArg (fun a : ℝ => 1 - a) hsplit
  have hDeriv : ∀ t, HasDerivAt beta (-b t) t := by
    intro t
    rw [hprimitive]
    simpa only [Pi.sub_def, zero_sub] using (hasDerivAt_const t (1 : ℝ)).sub
      (hb.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hActual : deriv beta = fun t => -b t := funext (fun t => (hDeriv t).deriv)
  have hSmooth : ContDiff ℝ ∞ beta := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun t => (hDeriv t).differentiableAt, ?_⟩
    rw [hActual]
    exact hb.neg
  refine ⟨hSmooth, ?_, ?_, ?_, hDeriv, fun t => (hDeriv t).deriv⟩
  · intro t
    have h0 := setIntegral_nonneg (μ := volume) measurableSet_Iic (fun y _ => hnonneg y)
      (s := Iic t)
    have h1 := setIntegral_le_integral (s := Iic t) hInt (ae_of_all _ hnonneg)
    rw [hmass] at h1
    constructor <;> linarith only [h0, h1]
  · intro t ht
    have hi : (∫ y in Iic t, b y) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero (fun y hy => hzero y (hy.trans ht))
    rw [hi, sub_zero]
  · intro t ht
    have hi : (∫ y in Iic t, b y) = ∫ y, b y :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
        apply hone
        have hty : t < y := lt_of_not_ge hy
        exact ht.trans hty.le)
    rw [hi, hmass, sub_self]

/-- Rescaling the literal profile gives its actual scalar derivative and sharp bound. -/
theorem quantitativeCutoffProfile_scaled (b : ℝ → ℝ)
    (hb : ContDiff ℝ ∞ b) (hcompact : HasCompactSupport b)
    (hsupport : tsupport b ⊆ Ioo 0 1)
    (hvalues : ∀ t, 0 ≤ b t ∧ b t ≤ 2) (hmass : (∫ t, b t) = 1)
    (theta delta hbar : ℝ) (hdelta : 0 < delta) (hhbar : 0 ≤ hbar) :
    let beta : ℝ → ℝ := fun t => 1 - ∫ y in Iic t, b y
    let eta : ℝ → ℝ := fun r => hbar * beta ((r - theta) / delta)
    ContDiff ℝ ∞ eta ∧
    (∀ r, HasDerivAt eta (-hbar * b ((r - theta) / delta) / delta) r) ∧
    (∀ r, deriv eta r = -hbar * b ((r - theta) / delta) / delta) ∧
    (∀ r, |deriv eta r| ≤ 2 * hbar / delta) ∧
    (∀ r, 0 ≤ eta r ∧ eta r ≤ hbar) ∧
    (∀ r, r ≤ theta → eta r = hbar) ∧
    (∀ r, theta + delta ≤ r → eta r = 0) := by
  obtain ⟨hSmooth, hRange, hOne, hZero, hDeriv, _⟩ :=
    quantitativeCutoffProfile_properties b hb hcompact hsupport (fun t => (hvalues t).1) hmass
  let beta : ℝ → ℝ := fun t => 1 - ∫ y in Iic t, b y
  let eta : ℝ → ℝ := fun r => hbar * beta ((r - theta) / delta)
  have hetaDeriv : ∀ r, HasDerivAt eta (-hbar * b ((r - theta) / delta) / delta) r := by
    intro r
    have ha : HasDerivAt (fun r : ℝ => (r - theta) / delta) (1 / delta) r :=
      ((hasDerivAt_id r).sub_const theta).div_const delta
    have hc := (hDeriv ((r - theta) / delta)).comp r ha
    have heq : -hbar * b ((r - theta) / delta) / delta =
        hbar * (-b ((r - theta) / delta) * (1 / delta)) := by ring
    rw [heq]
    exact hc.const_mul hbar
  refine ⟨contDiff_const.mul (hSmooth.comp ((contDiff_id.sub contDiff_const).div_const delta)),
    hetaDeriv, fun r => (hetaDeriv r).deriv, ?_, ?_, ?_, ?_⟩
  · intro r
    rw [(hetaDeriv r).deriv, abs_div, abs_mul, abs_neg,
      abs_of_nonneg hhbar, abs_of_nonneg (hvalues _).1, abs_of_pos hdelta]
    apply div_le_div_of_nonneg_right _ hdelta.le
    exact (mul_le_mul_of_nonneg_left (hvalues _).2 hhbar).trans_eq (mul_comm hbar 2)
  · intro r
    exact ⟨mul_nonneg hhbar (hRange _).1,
      (mul_le_mul_of_nonneg_left (hRange _).2 hhbar).trans_eq (mul_one hbar)⟩
  · intro r hr
    change hbar * (1 - ∫ y in Iic ((r - theta) / delta), b y) = hbar
    simpa only [mul_one] using congrArg (fun z : ℝ => hbar * z)
      (hOne _ (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) hdelta.le))
  · intro r hr
    change hbar * (1 - ∫ y in Iic ((r - theta) / delta), b y) = 0
    simpa only [mul_zero] using congrArg (fun z : ℝ => hbar * z)
      (hZero _ ((le_div_iff₀ hdelta).mpr (by linarith only [hr])))

end HarmonicMaps
