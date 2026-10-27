module

public import HarmonicMaps.Analysis.SobolevCutoffBoundary
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Zero boundary values from interior support

An interior cutoff leaves a supported Sobolev map unchanged. Uniqueness of
weak gradients identifies the cutoff product gradient with the original
columns, so the compact approximation converges to the displayed gradient.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace HarmonicMaps

/-- Zero boundary membership depends on the a.e. weak gradient, with the map
and its actual Sobolev membership held fixed. -/
theorem HasZeroBoundaryValues.congr_gradient {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (h : HasZeroBoundaryValues Ω u Du) (hu : MemW12 Ω u Dv) :
    HasZeroBoundaryValues Ω u Dv := by
  obtain ⟨hw, m, hm, hmc, hlim, hDlim⟩ := h
  have heq := hw.1.ae_eq hu.1
  refine ⟨hu, m, hm, hmc, hlim, ?_⟩
  intro i
  have hnorm (k : ℕ) :
      eLpNorm (fun x => coordinateDerivative (m k) (hm k) i x - Dv x i)
        2 (volume.restrict Ω.val) =
      eLpNorm (fun x => coordinateDerivative (m k) (hm k) i x - Du x i)
        2 (volume.restrict Ω.val) := by
    apply eLpNorm_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  simp_rw [hnorm]
  exact hDlim i

/-- A finite Sobolev map supported in a strictly smaller concentric closed
ball has zero boundary values on the larger ball, for the same weak gradient. -/
theorem MemW12.zeroBoundary_of_support_subset_closedBall {n q : ℕ}
    {a : Domain n} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du)
    (hs : Function.support u ⊆ Metric.closedBall a r) :
    HasZeroBoundaryValues (ballDomain a R) u Du := by
  let χ : ContDiffBump a := ⟨r, (r + R) / 2, hr, by linarith only [hrR]⟩
  have hχ : ContDiff ℝ ∞ (χ : Domain n → ℝ) := χ.contDiff
  have hsχ : tsupport (χ : Domain n → ℝ) ⊆ Metric.ball a R := by
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [χ]; linarith only [hrR])
  have heq : (fun x => χ x • u x) = u := by
    funext x
    by_cases hx : x ∈ Function.support u
    · rw [χ.one_of_mem_closedBall (hs hx), one_smul]
    · rw [Function.notMem_support.mp hx, smul_zero]
  have hz := hu.smoothCutoff_zeroBoundary_ball (hr.trans hrR) hχ χ.hasCompactSupport hsχ
  rw [heq] at hz
  exact hz.congr_gradient hu

/-- A compactly supported Sobolev map with support inside the ball has zero
boundary values, without any vanishing assumption on its weak gradient. -/
theorem MemW12.zeroBoundary_of_compactSupport_ball {n q : ℕ}
    {a : Domain n} {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ Metric.ball a R) :
    HasZeroBoundaryValues (ballDomain a R) u Du := by
  have hK := hc.insert a
  have hne : (insert a (tsupport u)).Nonempty := ⟨a, mem_insert a _⟩
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne (continuous_id.dist continuous_const).continuousOn
  have hzR : dist z a < R := by
    rcases hz with rfl | hz
    · simpa only [dist_self] using hR
    · exact hs hz
  have hr : 0 < (dist z a + R) / 2 := by
    linarith only [dist_nonneg (x := z) (y := a), hR]
  apply hu.zeroBoundary_of_support_subset_closedBall hr (by linarith only [hzR])
  intro x hx
  have hle : dist x a ≤ dist z a := hmax (mem_insert_of_mem a (subset_tsupport u hx))
  exact show dist x a ≤ (dist z a + R) / 2 by linarith only [hle, hzR]

end HarmonicMaps
