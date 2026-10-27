module

public import HarmonicMaps.SobolevLemmas
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Centered affine changes of variables

Positive dilations about a ball center transfer compact smooth tests and
Lebesgue integrals. The derivative and Jacobian factors are explicit.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff

namespace HarmonicMaps

noncomputable section

/-- The literal centered dilation used to move a ball strictly into itself. -/
def ballAffine {n : ℕ} (a : Domain n) (t : ℝ) (x : Domain n) : Domain n :=
  a + t • (x - a)

theorem ballAffine_contDiff {n : ℕ} (a : Domain n) (t : ℝ) :
    ContDiff ℝ ∞ (ballAffine a t) :=
  contDiff_const.add ((contDiff_id.sub contDiff_const).const_smul t)

theorem ballAffine_inverse {n : ℕ} (a : Domain n) {t : ℝ} (ht : t ≠ 0)
    (x : Domain n) : ballAffine a t⁻¹ (ballAffine a t x) = x := by
  simp [ballAffine, smul_smul, ht]

theorem ballAffine_mem_ball_iff {n : ℕ} (a : Domain n) {t : ℝ} (ht : 0 < t)
    (R : ℝ) (x : Domain n) :
    ballAffine a t x ∈ Metric.ball a R ↔ x ∈ Metric.ball a (R / t) := by
  simp only [Metric.mem_ball, dist_eq_norm, ballAffine, add_sub_cancel_left,
    norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  rw [lt_div_iff₀ ht, mul_comm]

theorem integral_ballAffine {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a : Domain n) {t : ℝ} (ht : 0 < t) (f : Domain n → E) :
    (∫ x, f (ballAffine a t x)) = (t ^ n)⁻¹ • ∫ x, f x := by
  calc
    (∫ x, f (ballAffine a t x)) = ∫ x, f (a + t • x) :=
      integral_sub_right_eq_self (fun x => f (a + t • x)) a
    _ = (t ^ n)⁻¹ • ∫ x, f (a + x) := by
      simpa only [finrank_euclideanSpace_fin] using
        Measure.integral_comp_smul_of_nonneg volume (fun x => f (a + x)) t
          (hR := ht.le)
    _ = (t ^ n)⁻¹ • ∫ x, f x := by rw [integral_add_left_eq_self]

theorem Integrable.comp_ballAffine {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : Domain n → E} (hf : Integrable f volume) (a : Domain n)
    {t : ℝ} (ht : t ≠ 0) : Integrable (fun x => f (ballAffine a t x)) volume :=
  ((hf.comp_add_left a).comp_smul ht).comp_sub_right a

theorem ballAffineTest_hasCompactSupport {n : ℕ} {φ : Domain n → ℝ}
    (hc : HasCompactSupport φ) (a : Domain n) {t : ℝ} (ht : t ≠ 0) :
    HasCompactSupport (fun x => φ (ballAffine a t x)) := by
  let e := (Homeomorph.addRight (-a)).trans
    ((Homeomorph.smul (Units.mk0 t ht)).trans (Homeomorph.addLeft a))
  change HasCompactSupport (φ ∘ e)
  exact hc.comp_homeomorph e

theorem ballAffineTest_coordinateDerivative {n : ℕ} {φ : Domain n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (a : Domain n) (t : ℝ) (i : Fin n) (x : Domain n) :
    coordinateDerivative (fun x => φ (ballAffine a t x))
      (hφ.comp (ballAffine_contDiff a t)) i x =
      t * coordinateDerivative φ hφ i (ballAffine a t x) := by
  have hA := (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const a).const_smul t).const_add a
  have hcomp := (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x hA
  change HasFDerivAt (fun z => φ (ballAffine a t z))
    ((fderiv ℝ φ (ballAffine a t x)).comp
      (t • ContinuousLinearMap.id ℝ (Domain n))) x at hcomp
  unfold coordinateDerivative
  rw [hcomp.fderiv]
  simp

theorem ballAffineTest_tsupport_subset {n : ℕ} {φ : Domain n → ℝ}
    (a : Domain n) {t : ℝ} (ht : 0 < t) (R : ℝ)
    (hs : tsupport φ ⊆ Metric.ball a (R / t)) :
    tsupport (fun x => φ (ballAffine a t⁻¹ x)) ⊆ Metric.ball a R := by
  let e := (Homeomorph.addRight (-a)).trans
    ((Homeomorph.smul (Units.mk0 t⁻¹ (inv_ne_zero ht.ne'))).trans
      (Homeomorph.addLeft a))
  have heq : (fun x => φ (ballAffine a t⁻¹ x)) = φ ∘ e := by
    funext x
    simp [e, ballAffine, sub_eq_add_neg]
  rw [heq, tsupport_comp_eq_preimage]
  intro x hx
  have hx' : ballAffine a t⁻¹ x ∈ Metric.ball a (R / t) := by
    apply hs
    simpa [e, ballAffine, sub_eq_add_neg] using hx
  have h := (ballAffine_mem_ball_iff a ht R (ballAffine a t⁻¹ x)).mpr hx'
  simpa [ballAffine, smul_smul, ht.ne'] using h

end
end HarmonicMaps
