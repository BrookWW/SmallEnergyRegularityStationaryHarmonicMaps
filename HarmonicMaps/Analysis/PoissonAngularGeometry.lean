module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Coordinate rotations and recovery of Cartesian derivatives

Actual skew-adjoint coordinate generators have their literal Euclidean action.
Every Cartesian derivative is recovered from the radial derivative and these
angular derivatives away from the origin.
-/

public section

open scoped BigOperators

namespace HarmonicMaps

/-- The coordinate rotation fields are produced by actual skew-adjoint
continuous linear maps with their full literal action. -/
theorem poisson_coordinateSkewGenerators (n : ℕ) :
    ∃ A : Fin n → Fin n → (Domain n →L[ℝ] Domain n),
      ∀ i j, star (A i j) = -A i j ∧
        ∀ x : Domain n, A i j x =
          x i • EuclideanSpace.single j 1 - x j • EuclideanSpace.single i 1 := by
  let e : Fin n → Domain n := fun i => EuclideanSpace.single i 1
  let A : Fin n → Fin n → (Domain n →L[ℝ] Domain n) := fun i j =>
    InnerProductSpace.rankOne ℝ (e j) (e i) - InnerProductSpace.rankOne ℝ (e i) (e j)
  refine ⟨A, ?_⟩
  intro i j
  constructor
  · change star (InnerProductSpace.rankOne ℝ (e j) (e i) -
      InnerProductSpace.rankOne ℝ (e i) (e j)) = _
    rw [star_sub]
    change ContinuousLinearMap.adjoint (InnerProductSpace.rankOne ℝ (e j) (e i)) -
      ContinuousLinearMap.adjoint (InnerProductSpace.rankOne ℝ (e i) (e j)) = _
    rw [InnerProductSpace.adjoint_rankOne, InnerProductSpace.adjoint_rankOne]
    dsimp only [A]
    abel
  · intro x
    dsimp only [A, e]
    simp only [sub_apply, InnerProductSpace.rankOne_apply,
      EuclideanSpace.inner_single_left, map_one, one_mul]

/-- The radial and coordinate-angular evaluations determine every Cartesian
column, with the exact squared-radius coefficient. -/
theorem poisson_cartesian_column_from_radial_angular {n q : ℕ}
    (B : Domain n →L[ℝ] Ambient q) (x : Domain n) (k : Fin n) :
    ‖x‖ ^ 2 • B (EuclideanSpace.single k 1) =
      x k • B x + ∑ j : Fin n, x j •
        B (x j • EuclideanSpace.single k 1 - x k • EuclideanSpace.single j 1) := by
  have hrepr : (∑ j : Fin n, x j • EuclideanSpace.single j 1) = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
  have hBsum : (∑ j : Fin n, x j • B (EuclideanSpace.single j 1)) = B x := by
    calc
      _ = ∑ j : Fin n, B (x j • EuclideanSpace.single j 1) :=
        Finset.sum_congr rfl (fun j _ => (B.map_smul (x j) _).symm)
      _ = B (∑ j : Fin n, x j • EuclideanSpace.single j 1) := (map_sum B _ _).symm
      _ = B x := congrArg B hrepr
  have hsum : (∑ j : Fin n, x j •
      B (x j • EuclideanSpace.single k 1 - x k • EuclideanSpace.single j 1)) =
      ‖x‖ ^ 2 • B (EuclideanSpace.single k 1) - x k • B x := by
    simp only [map_sub, map_smul, smul_sub, smul_smul]
    rw [Finset.sum_sub_distrib]
    have hSquare : (∑ j : Fin n, (x j * x j) • B (EuclideanSpace.single k 1)) =
        ‖x‖ ^ 2 • B (EuclideanSpace.single k 1) := by
      rw [← Finset.sum_smul]
      exact congrArg (fun a : ℝ => a • B (EuclideanSpace.single k 1))
        (by simpa only [pow_two] using (EuclideanSpace.real_norm_sq_eq x).symm)
    have hCross : (∑ j : Fin n, (x j * x k) • B (EuclideanSpace.single j 1)) =
        x k • B x := by
      rw [← hBsum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul, mul_comm]
    rw [hSquare, hCross]
  rw [hsum]
  abel

end HarmonicMaps
end
