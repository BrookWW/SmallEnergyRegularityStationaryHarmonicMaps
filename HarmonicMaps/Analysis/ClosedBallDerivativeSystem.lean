module

public import HarmonicMaps.Sobolev
public import HarmonicMaps.Analysis.ClosedBallSmoothBootstrap
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Closed-ball smoothness for a finite differential system

A family continuous on a closed ball and smooth in its interior is smooth up
to the boundary if every Cartesian derivative is a finite linear combination
of family members with coefficients smooth away from the origin. The interior
smoothness supplies the derivative field near the origin.
-/

public section

open Set Filter Metric
open scoped Topology ContDiff BigOperators

namespace HarmonicMaps

/-- A finite differential system with coefficients smooth away from the origin
propagates every finite regularity order to the closed ball. -/
theorem contDiffOn_closedBall_family_of_finite_derivative_system {n q : ℕ}
    {I J : Type*} [Fintype J] {R : ℝ} (hR : 0 < R)
    (f : I → Domain n → Ambient q)
    (σ : I → Fin n → J → I)
    (c : I → Fin n → J → Domain n → ℝ)
    (hf : ∀ i, ContinuousOn (f i) (closedBall 0 R))
    (hsmooth : ∀ i, ContDiffOn ℝ ∞ (f i) (ball 0 R))
    (hc : ∀ i k j, ContDiffOn ℝ ∞ (c i k j) ({0}ᶜ : Set (Domain n)))
    (hsystem : ∀ i k x, x ∈ ball 0 R → x ≠ 0 →
      fderiv ℝ (f i) x (EuclideanSpace.single k 1) =
        ∑ j : J, c i k j x • f (σ i k j) x) :
    ∀ i, ContDiffOn ℝ ∞ (f i) (closedBall 0 R) := by
  classical
  let B : I → Domain n → Domain n →L[ℝ] Ambient q := fun i x =>
    ∑ k : Fin n, (EuclideanSpace.proj k).smulRight
      (∑ j : J, c i k j x • f (σ i k j) x)
  have hB (i : I) (x : Domain n) (hx : x ∈ ball 0 R) (hx0 : x ≠ 0) :
      fderiv ℝ (f i) x = B i x := by
    apply ContinuousLinearMap.ext
    intro v
    have hv : (∑ k : Fin n, v k • EuclideanSpace.single k 1) = v := by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
    calc
      fderiv ℝ (f i) x v =
          fderiv ℝ (f i) x (∑ k : Fin n, v k • EuclideanSpace.single k 1) := by rw [hv]
      _ = ∑ k : Fin n, v k • (∑ j : J, c i k j x • f (σ i k j) x) := by
        simp only [map_sum, map_smul, hsystem i _ x hx hx0]
      _ = B i x v := by
        simp only [B, sum_apply, ContinuousLinearMap.smulRight_apply,
          EuclideanSpace.coe_proj]
  let g : I → Domain n → Domain n →L[ℝ] Ambient q := fun i x =>
    if x ∈ ball 0 R then fderiv ℝ (f i) x else B i x
  have hg_in (i : I) {x : Domain n} (hx : x ∈ ball 0 R) :
      g i x = fderiv ℝ (f i) x := if_pos hx
  have hg_out (i : I) {x : Domain n} (hx0 : x ≠ 0) : g i x = B i x := by
    by_cases hx : x ∈ ball 0 R
    · exact (hg_in i hx).trans (hB i x hx hx0)
    · exact if_neg hx
  apply contDiffOn_closedBall_family_of_derivative_stability hR f g hf
  · intro i x hx
    rw [hg_in i hx]
    exact ((hsmooth i).contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt
      (by simp) |>.hasFDerivAt
  · intro m ih i x hx
    by_cases hxin : x ∈ ball 0 R
    · have hd : ContDiffOn ℝ m (fderiv ℝ (f i)) (ball 0 R) :=
        ((hsmooth i).fderiv_of_isOpen isOpen_ball (m := ∞) (by simp)).of_le
          (WithTop.coe_le_coe.mpr le_top)
      apply (hd.contDiffAt (isOpen_ball.mem_nhds hxin)).contDiffWithinAt.congr_of_eventuallyEq
      · filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hxin)] with y hy
        exact hg_in i hy
      · exact hg_in i hxin
    · have hx0 : x ≠ 0 := by
        intro heq
        exact hxin (heq ▸ mem_ball_self hR)
      have hBreg : ContDiffWithinAt ℝ m (B i) (closedBall 0 R) x := by
        apply ContDiffWithinAt.sum
        intro k _
        apply contDiffWithinAt_const.smulRight
        apply ContDiffWithinAt.sum
        intro j _
        exact ((hc i k j).contDiffAt
          (isClosed_singleton.isOpen_compl.mem_nhds hx0)).contDiffWithinAt.of_le
          (WithTop.coe_le_coe.mpr le_top) |>.smul (ih (σ i k j) x hx)
      apply hBreg.congr_of_eventuallyEq
      · filter_upwards [mem_nhdsWithin_of_mem_nhds
          (isClosed_singleton.isOpen_compl.mem_nhds hx0)] with y hy
        exact hg_out i hy
      · exact hg_out i hx0

end HarmonicMaps
end
