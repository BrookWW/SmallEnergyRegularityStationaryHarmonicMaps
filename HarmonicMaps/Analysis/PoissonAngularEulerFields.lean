module

public import HarmonicMaps.Analysis.PoissonEulerBoundary
import Mathlib.Tactic.Module

/-!
# Euler fields of continuous harmonic angular families

The actual angular recurrence and harmonic equation supply a continuous
closed-ball Euler field for each word. The same fields satisfy the radial and
angular first-order equations needed for simultaneous boundary regularity.
-/

public section

open Set Filter
open scoped ContDiff BigOperators Topology

namespace HarmonicMaps

/-- Harmonic angular families produce their continuous Euler fields and the
complete first-order radial/angular system, without prescribed boundary jets. -/
theorem poisson_angular_family_euler_fields {n q : ℕ}
    (R : PositiveRadius)
    (A : Fin n → Fin n → (Domain n →L[ℝ] Domain n))
    (hA : ∀ i j (x : Domain n), A i j x =
      x i • EuclideanSpace.single j 1 - x j • EuclideanSpace.single i 1)
    (F : List (Fin n × Fin n) → Domain n → Ambient q)
    (hFc : ∀ w, ContinuousOn (F w) (Metric.closedBall (0 : Domain n) R.val))
    (hFs : ∀ w, ContDiffOn ℝ ∞ (F w) (Metric.ball (0 : Domain n) R.val))
    (hFh : ∀ w x, x ∈ Metric.ball (0 : Domain n) R.val → Laplacian.laplacian (F w) x = 0)
    (hFa : ∀ w i j x, x ∈ Metric.ball (0 : Domain n) R.val →
      fderiv ℝ (F w) x (A i j x) = F ((i, j) :: w) x) :
    ∃ E : List (Fin n × Fin n) → Domain n → Ambient q,
      (∀ w, ContinuousOn (E w) (Metric.closedBall (0 : Domain n) R.val)) ∧
      (∀ w, ContDiffOn ℝ ∞ (E w) (Metric.ball (0 : Domain n) R.val)) ∧
      (∀ w x, x ∈ Metric.ball (0 : Domain n) R.val →
        fderiv ℝ (F w) x x = E w x) ∧
      (∀ w i j x, x ∈ Metric.ball (0 : Domain n) R.val →
        fderiv ℝ (E w) x (A i j x) = E ((i, j) :: w) x) ∧
      ∀ w x, x ∈ Metric.ball (0 : Domain n) R.val →
        fderiv ℝ (E w) x x = -((n : ℝ) - 2) • E w x -
          (1 / 2 : ℝ) • (∑ i : Fin n, ∑ j : Fin n, F ((i, j) :: (i, j) :: w) x) := by
  classical
  let B : Set (Domain n) := Metric.ball 0 R.val
  let E₀ : List (Fin n × Fin n) → Domain n → Ambient q := fun w x =>
    fderiv ℝ (F w) x x
  have hE₀ (w : List (Fin n × Fin n)) : ContDiffOn ℝ ∞ (E₀ w) B :=
    ((hFs w).fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply contDiffOn_id
  have hAngularLocal (w : List (Fin n × Fin n)) (i j : Fin n)
      (x : Domain n) (hx : x ∈ B) :
      (fun y => fderiv ℝ (F w) y (A i j y)) =ᶠ[nhds x] F ((i, j) :: w) := by
    filter_upwards [Metric.isOpen_ball.eventually_mem hx] with y hy
    exact hFa w i j y hy
  have hAngularSecond (w : List (Fin n × Fin n)) (i j : Fin n)
      (x : Domain n) (hx : x ∈ B) :
      fderiv ℝ (fun y => fderiv ℝ (F w) y (A i j y)) x (A i j x) =
        F ((i, j) :: (i, j) :: w) x := by
    rw [(hAngularLocal w i j x hx).fderiv_eq]
    exact hFa ((i, j) :: w) i j x hx
  have hExists (w : List (Fin n × Fin n)) :
      ∃ e : Domain n → Ambient q,
        ContinuousOn e (Metric.closedBall (0 : Domain n) R.val) ∧ EqOn e (E₀ w) B := by
    let W : Metric.closedBall (0 : Domain n) R.val → Ambient q := fun x =>
      ∑ i : Fin n, ∑ j : Fin n, F ((i, j) :: (i, j) :: w) x.val
    have hW : Continuous W := by
      apply continuous_finsetSum
      intro i _
      apply continuous_finsetSum
      intro j _
      exact (hFc ((i, j) :: (i, j) :: w)).restrict
    apply poisson_euler_continuousOn_closedBall_of_angularSum A hA R (F w)
      (hFs w) (hFh w) W hW
    intro x hx
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (hAngularSecond w i j x hx).symm
  choose E hE using hExists
  have hELocal (w : List (Fin n × Fin n)) (x : Domain n) (hx : x ∈ B) :
      E w =ᶠ[nhds x] E₀ w := by
    filter_upwards [Metric.isOpen_ball.eventually_mem hx] with y hy
    exact (hE w).2 hy
  obtain ⟨A', hA', hPolar⟩ := poisson_coordinate_polar_calculus n
  have hAA : A' = A := by
    funext i j
    apply ContinuousLinearMap.ext
    intro x
    exact ((hA' i j).2 x).trans (hA i j x).symm
  subst A'
  refine ⟨E, fun w => (hE w).1, ?_, ?_, ?_, ?_⟩
  · intro w
    exact (hE₀ w).congr (hE w).2
  · intro w x hx
    exact ((hE w).2 hx).symm
  · intro w i j x hx
    rw [(hELocal w x hx).fderiv_eq]
    have hCommute := (hPolar q B Metric.isOpen_ball (F w) (hFs w) x hx).2 i j
    change fderiv ℝ (E₀ w) x (A i j x) =
      fderiv ℝ (fun y => fderiv ℝ (F w) y (A i j y)) x x at hCommute
    rw [hCommute, (hAngularLocal w i j x hx).fderiv_eq]
    exact ((hE ((i, j) :: w)).2 hx).symm
  · intro w x hx
    rw [(hELocal w x hx).fderiv_eq, (hE w).2 hx]
    have hPolarX := (hPolar q B Metric.isOpen_ball (F w) (hFs w) x hx).1
    change (∑ i : Fin n, ∑ j : Fin n,
      fderiv ℝ (fun y => fderiv ℝ (F w) y (A i j y)) x (A i j x)) =
      (2 : ℝ) • (‖x‖ ^ 2 • Laplacian.laplacian (F w) x -
        fderiv ℝ (E₀ w) x x - ((n : ℝ) - 2) • E₀ w x) at hPolarX
    simp_rw [hAngularSecond w _ _ x hx] at hPolarX
    rw [hFh w x hx, smul_zero, zero_sub] at hPolarX
    rw [hPolarX]
    module

end HarmonicMaps
end
