module

public import StationaryHarmonicMaps.Geometry.UnitInversion
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Smooth exterior representatives for even inversion

A cutoff near the origin regularizes the exterior inversion formula. On and
outside the unit sphere the same smooth representative is the original map
composed with inversion, with its actual chain derivative.
-/

public section

open HarmonicMaps EuclideanGeometry Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Every smooth map has an actual smooth representative of its even inversion on and outside the unit sphere. -/
theorem exists_smooth_even_inversion_extension {n q : ℕ}
    (u : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u) :
    ∃ v : Domain n → Ambient q, ContDiff ℝ ∞ v ∧
      (∀ x : Domain n, ‖x‖ = 1 → v x = u x) ∧
      (∀ x : Domain n, 1 < ‖x‖ → v x = u (inversion (0 : Domain n) 1 x)) ∧
      ∀ (x z : Domain n), 1 < ‖x‖ →
        fderiv ℝ v x z = fderiv ℝ u (inversion (0 : Domain n) 1 x)
          (fderiv ℝ (inversion (0 : Domain n) 1) x z) := by
  let χ : ContDiffBump (0 : Domain n) := ⟨1/2, 3/4, by norm_num, by norm_num⟩
  let I := inversion (0 : Domain n) 1
  let v := fun x => (1 - χ x) • u (I x)
  have hAway (x : Domain n) (hx : x ≠ 0) : ContDiffAt ℝ ∞ v x := by
    have hI : ContDiffAt ℝ ∞ I x :=
      contDiffAt_const.inversion contDiffAt_const contDiffAt_id hx
    exact (contDiff_const.sub χ.contDiff).contDiffAt.smul (hu.contDiffAt.comp x hI)
  have hZero : v =ᶠ[𝓝 (0 : Domain n)] (fun _ => (0 : Ambient q)) := by
    filter_upwards [ball_mem_nhds (0 : Domain n) (by norm_num : (0 : ℝ) < 1/2)] with x hx
    have hχ : χ x = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hx)
    simp only [v, hχ, sub_self, zero_smul]
  have hv : ContDiff ℝ ∞ v := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      exact contDiffAt_const.congr_of_eventuallyEq hZero
    · exact hAway x hx
  have hExterior (x : Domain n) (hx : 3/4 < ‖x‖) : v x = u (I x) := by
    have hNot : x ∉ closedBall (0 : Domain n) (3/4 : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hx
    have hχ : χ x = 0 := image_eq_zero_of_notMem_tsupport (by
      rw [χ.tsupport_eq]
      exact hNot)
    simp only [v, hχ, sub_zero, one_smul]
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · intro x hx
    rw [hExterior x (by rw [hx]; norm_num)]
    have hIx : I x = x := inversion_of_mem_sphere (by
      simpa only [mem_sphere, dist_zero_right] using hx)
    rw [hIx]
  · intro x hx
    exact hExterior x (by linarith)
  · intro x z hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hx)
    have hNear : v =ᶠ[𝓝 x] (fun y => u (I y)) := by
      filter_upwards [continuous_norm.continuousAt.eventually_const_lt
        (show (3/4 : ℝ) < ‖x‖ by linarith)] with y hy
      exact hExterior y hy
    have hDI : HasFDerivAt I (fderiv ℝ I x) x :=
      (hasFDerivAt_unit_inversion x hx0).differentiableAt.hasFDerivAt
    have hComp := (hu.differentiable (by simp) (I x)).hasFDerivAt.comp x hDI
    rw [hNear.fderiv_eq]
    change (fderiv ℝ (u ∘ I) x) z = _
    rw [hComp.fderiv]
    rfl

end StationaryHarmonicMaps.Analysis

end
