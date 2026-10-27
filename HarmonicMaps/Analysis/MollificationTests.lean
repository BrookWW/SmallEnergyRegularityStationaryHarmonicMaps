module

public import HarmonicMaps.Analysis.MollificationConvolution
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Smooth tests for local convolution

Reflection and translation of a compactly supported smooth kernel give the
scalar test used in the weak-gradient identity. The derivative of this test
has the sign imposed by the reflection.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff

namespace HarmonicMaps

noncomputable section

/-- The scalar weak test obtained by reflection and translation of a kernel. -/
def translatedKernelTest {n : ℕ} (χ : Domain n → ℝ) (x z : Domain n) : ℝ :=
  χ (x - z)

theorem translatedKernelTest_contDiff {n : ℕ} {χ : Domain n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (x : Domain n) :
    ContDiff ℝ ∞ (translatedKernelTest χ x) :=
  hχ.comp (contDiff_const.sub contDiff_id)

theorem translatedKernelTest_hasCompactSupport {n : ℕ} {χ : Domain n → ℝ}
    (hχ : HasCompactSupport χ) (x : Domain n) :
    HasCompactSupport (translatedKernelTest χ x) :=
  hχ.comp_homeomorph (Homeomorph.subLeft x)

theorem translatedKernelTest_tsupport_subset {n : ℕ} {χ : Domain n → ℝ}
    (Ω : OpenDomain n) (x : Domain n)
    (hSample : ∀ y ∈ tsupport χ, x - y ∈ Ω.val) :
    tsupport (translatedKernelTest χ x) ⊆ Ω.val := by
  change tsupport (χ ∘ (Homeomorph.subLeft x)) ⊆ Ω.val
  rw [tsupport_comp_eq_preimage]
  intro z hz
  simpa only [Homeomorph.subLeft_apply, sub_sub_cancel] using hSample (x - z) hz

theorem translatedKernelTest_coordinateDerivative {n : ℕ} {χ : Domain n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (x z : Domain n) (i : Fin n) :
    coordinateDerivative (translatedKernelTest χ x)
      (translatedKernelTest_contDiff hχ x) i z =
      -(fderiv ℝ χ (x - z) (EuclideanSpace.single i 1)) := by
  have hcomp := (hχ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_sub x)
  simp only [Function.comp_def, id_eq] at hcomp
  change fderiv ℝ (fun z => χ (x - z)) z (EuclideanSpace.single i 1) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

theorem scaledMollifierKernel_sampling_unitBall {n : ℕ} (h : PositiveRadius)
    (hh : h.val ≤ 1 / 4) {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    ∀ y ∈ tsupport (scaledMollifierKernel n h),
      x - y ∈ Metric.ball (0 : Domain n) 1 := by
  intro y hy
  have hy' := scaledMollifierKernel_tsupport_subset_halfBall n h hy
  rw [Metric.mem_closedBall, dist_zero_right] at hy'
  rw [Metric.mem_ball, dist_zero_right] at hx ⊢
  calc
    ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
    _ < 3 / 4 + h.val / 2 := add_lt_add_of_lt_of_le hx hy'
    _ ≤ 1 := by linarith only [hh]

theorem scaledMollifierKernel_test_tsupport_unitBall {n : ℕ} (h : PositiveRadius)
    (hh : h.val ≤ 1 / 4) {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    tsupport (translatedKernelTest (scaledMollifierKernel n h) x) ⊆
      Metric.ball (0 : Domain n) 1 :=
  translatedKernelTest_tsupport_subset (ballDomain (0 : Domain n) 1) x
    (scaledMollifierKernel_sampling_unitBall h hh hx)

/-- A strict ball margin contains every point sampled by the scaled kernel. -/
theorem scaledMollifierKernel_sampling_ball {n : ℕ} (h : PositiveRadius)
    (a x : Domain n) (R : ℝ) (hMargin : dist x a + h.val / 2 < R) :
    ∀ y ∈ tsupport (scaledMollifierKernel n h), x - y ∈ Metric.ball a R := by
  intro y hy
  have hy' := scaledMollifierKernel_tsupport_subset_halfBall n h hy
  rw [Metric.mem_closedBall, dist_zero_right] at hy'
  rw [Metric.mem_ball]
  calc
    dist (x - y) a = ‖(x - a) - y‖ := by
      rw [dist_eq_norm]
      congr 1
      abel
    _ ≤ ‖x - a‖ + ‖y‖ := norm_sub_le _ _
    _ ≤ dist x a + h.val / 2 := by
      rw [dist_eq_norm]
      exact add_le_add_right hy' _
    _ < R := hMargin

end
end HarmonicMaps

end
