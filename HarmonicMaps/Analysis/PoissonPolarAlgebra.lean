module

public import HarmonicMaps.Analysis.PoissonAngularGeometry
import Mathlib.Tactic.Module

/-!
# Euler and coordinate-rotation second derivative algebra

The sum over all ordered coordinate rotation pairs has its exact factor two.
The identity uses the true Euclidean squared radius and curried second
Fréchet derivative, including the linear derivative of each rotation field.
-/

public section

open scoped BigOperators

namespace HarmonicMaps

/-- Exact ordered-pair rotation contraction for an arbitrary first and
curried second derivative. No Hessian symmetry premise is needed. -/
theorem poisson_orderedRotation_secondDerivative_algebra {n q : ℕ}
    (x : Domain n) (B : Domain n →L[ℝ] Ambient q)
    (H : Domain n →L[ℝ] (Domain n →L[ℝ] Ambient q)) :
    let e : Fin n → Domain n := fun i => EuclideanSpace.single i 1
    let V : Fin n → Fin n → Domain n := fun i j => x i • e j - x j • e i
    (∑ i : Fin n, ∑ j : Fin n,
      (H (V i j) (V i j) + B ((V i j) i • e j - (V i j) j • e i))) =
      (2 : ℝ) • (‖x‖ ^ 2 • (∑ i : Fin n, H (e i) (e i)) - H x x -
        ((n : ℝ) - 1) • B x) := by
  let e : Fin n → Domain n := fun i => EuclideanSpace.single i 1
  let V : Fin n → Fin n → Domain n := fun i j => x i • e j - x j • e i
  have hrepr : (∑ i : Fin n, x i • e i) = x := by
    simpa only [e, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
  have hHxx : H x x = ∑ i : Fin n, ∑ j : Fin n, (x i * x j) • H (e i) (e j) := by
    calc
      _ = H (∑ i : Fin n, x i • e i) (∑ j : Fin n, x j • e j) := by rw [hrepr]
      _ = _ := by
        simp only [map_sum, map_smul, sum_apply, smul_apply,
          Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_comm]
  have hBsum : (∑ i : Fin n, x i • B (e i)) = B x := by
    calc
      _ = ∑ i : Fin n, B (x i • e i) :=
        Finset.sum_congr rfl (fun i _ => (B.map_smul (x i) _).symm)
      _ = B (∑ i : Fin n, x i • e i) := (map_sum B _ _).symm
      _ = B x := congrArg B hrepr
  have hExpand (i j : Fin n) : H (V i j) (V i j) =
      (x i ^ 2 • H (e j) (e j) + x j ^ 2 • H (e i) (e i)) -
        ((x i * x j) • H (e j) (e i) + (x i * x j) • H (e i) (e j)) := by
    simp only [V, map_sub, map_smul, sub_apply, smul_apply, smul_sub, smul_smul]
    module
  have hDiag : (∑ i : Fin n, ∑ j : Fin n, x i ^ 2 • H (e j) (e j)) =
      ‖x‖ ^ 2 • (∑ j : Fin n, H (e j) (e j)) := by
    simp_rw [← Finset.smul_sum]
    rw [← Finset.sum_smul]
    exact congrArg (fun a : ℝ => a • (∑ j : Fin n, H (e j) (e j)))
      (EuclideanSpace.real_norm_sq_eq x).symm
  have hDiag' : (∑ i : Fin n, ∑ j : Fin n, x j ^ 2 • H (e i) (e i)) =
      ‖x‖ ^ 2 • (∑ j : Fin n, H (e j) (e j)) := by
    rw [Finset.sum_comm]
    exact hDiag
  have hCross : (∑ i : Fin n, ∑ j : Fin n, (x i * x j) • H (e j) (e i)) = H x x := by
    rw [hHxx, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  have hHsum : (∑ i : Fin n, ∑ j : Fin n, H (V i j) (V i j)) =
      (2 : ℝ) • (‖x‖ ^ 2 • (∑ i : Fin n, H (e i) (e i)) - H x x) := by
    simp_rw [hExpand, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hDiag, hDiag', hCross, ← hHxx]
    module
  have hBExpand (i j : Fin n) : B ((V i j) i • e j - (V i j) j • e i) =
      (if i = j then (2 : ℝ) • (x i • B (e i)) else 0) -
        x i • B (e i) - x j • B (e j) := by
    by_cases hij : i = j
    · subst j
      simp only [V, sub_self, PiLp.zero_apply, zero_smul, map_zero, ite_true]
      module
    · have hji : j ≠ i := Ne.symm hij
      simp only [V, e, PiLp.sub_apply, PiLp.smul_apply, EuclideanSpace.single,
        PiLp.single_apply, hij, hji, ite_false, ite_true, smul_eq_mul,
        mul_zero, mul_one, zero_sub, map_sub, map_smul]
      module
  have hBdiag : (∑ i : Fin n, ∑ j : Fin n,
      if i = j then (2 : ℝ) • (x i • B (e i)) else 0) = (2 : ℝ) • B x := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← Finset.smul_sum, hBsum]
  have hBrow : (∑ i : Fin n, ∑ _j : Fin n, x i • B (e i)) = (n : ℝ) • B x := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ]
    rw [← Finset.smul_sum, hBsum]
  have hBcol : (∑ i : Fin n, ∑ j : Fin n, x j • B (e j)) = (n : ℝ) • B x := by
    rw [Finset.sum_comm]
    exact hBrow
  have hBtotal : (∑ i : Fin n, ∑ j : Fin n,
      B ((V i j) i • e j - (V i j) j • e i)) =
      -(2 : ℝ) • (((n : ℝ) - 1) • B x) := by
    simp_rw [hBExpand, Finset.sum_sub_distrib]
    rw [hBdiag, hBrow, hBcol]
    module
  change (∑ i : Fin n, ∑ j : Fin n,
    (H (V i j) (V i j) + B ((V i j) i • e j - (V i j) j • e i))) = _
  simp_rw [Finset.sum_add_distrib]
  rw [hHsum, hBtotal]
  module

end HarmonicMaps
end
