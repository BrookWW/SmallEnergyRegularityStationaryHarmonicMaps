module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Smoothness on a closed ball from interior derivatives

A continuous derivative field on a closed ball gives the actual derivative
within the closed ball, including its boundary. For an indexed family, a
finite-order regularity step for the derivative fields then implies smoothness
of every family member. The regularity step is explicit helper data.
-/

public section

open Set Filter Metric
open scoped Topology ContDiff

namespace HarmonicMaps

variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuous extension of the interior derivative is the derivative within
the closed ball at every point of that ball. -/
theorem hasFDerivWithinAt_closedBall_of_continuousOn {R : ℝ} (hR : 0 < R)
    {f : E → F} {g : E → E →L[ℝ] F}
    (hf : ContinuousOn f (closedBall 0 R))
    (hg : ContinuousOn g (closedBall 0 R))
    (hderiv : ∀ x ∈ ball 0 R, HasFDerivAt f (g x) x)
    {x : E} (hx : x ∈ closedBall 0 R) :
    HasFDerivWithinAt f (g x) (closedBall 0 R) x := by
  have hclosure : closure (ball (0 : E) R) = closedBall 0 R := closure_ball 0 hR.ne'
  rw [← hclosure]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hderiv y hy).differentiableAt.differentiableWithinAt)
    (convex_ball 0 R) isOpen_ball
  · intro y hy
    exact (hf y (hclosure ▸ hy)).mono ball_subset_closedBall
  · apply ((hg x hx).mono ball_subset_closedBall).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hderiv y hy).fderiv.symm

/-- A continuous family on a closed ball is smooth if every finite regularity
level of the family implies the same regularity level of its actual interior
derivative fields on the closed ball. -/
theorem contDiffOn_closedBall_family_of_derivative_stability {R : ℝ} (hR : 0 < R)
    (f : I → E → F) (g : I → E → E →L[ℝ] F)
    (hf : ∀ i, ContinuousOn (f i) (closedBall 0 R))
    (hderiv : ∀ i x, x ∈ ball 0 R → HasFDerivAt (f i) (g i x) x)
    (hstep : ∀ k : ℕ, (∀ i, ContDiffOn ℝ k (f i) (closedBall 0 R)) →
      ∀ i, ContDiffOn ℝ k (g i) (closedBall 0 R)) :
    ∀ i, ContDiffOn ℝ ∞ (f i) (closedBall 0 R) := by
  have huniq : UniqueDiffOn ℝ (closedBall (0 : E) R) :=
    uniqueDiffOn_convex (convex_closedBall 0 R)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self hR)⟩
  have hfinite : ∀ k : ℕ, ∀ i, ContDiffOn ℝ k (f i) (closedBall 0 R) := by
    intro k
    induction k with
    | zero =>
        intro i
        exact contDiffOn_zero.mpr (hf i)
    | succ k ih =>
        intro i
        rw [Nat.cast_add, Nat.cast_one]
        apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn huniq).mpr
        refine ⟨fun hk => ?_, g i, hstep k ih i, ?_⟩
        · exact (WithTop.coe_ne_top hk).elim
        · intro x hx
          exact hasFDerivWithinAt_closedBall_of_continuousOn hR (hf i)
            (hstep k ih i).continuousOn (hderiv i) hx
  intro i
  exact contDiffOn_infty.mpr (fun k => hfinite k i)

end HarmonicMaps
end
