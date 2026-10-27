module

public import HolderToCK.Analysis.Bootstrap.CoordinateWords
public import HolderToCK.Foundation.HolderBounds
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-! # Native derivative norms from actual coordinate words

Expanding each Euclidean argument in its coordinate basis expresses a native
multilinear operator as a finite sum of its coordinate evaluations. Their
norms control the operator norm with the dimension factor `n^k`. Applying the
same estimate to an operator difference transfers the full Holder exponent
from the coordinate words of the original map to its native derivative.
-/

public section

open HarmonicMaps Set
open scoped ContDiff

namespace HolderToCK

/-- Finite coordinate expansion of an actual Euclidean multilinear operator. -/
theorem euclidean_multilinear_coordinate_expansion {n k : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Domain n) E)
    (v : Fin k → Domain n) :
    T v = ∑ I : Fin k → Fin n,
      (∏ j : Fin k, v j (I j)) •
        T (fun j => EuclideanSpace.single (I j) 1) := by
  have hrepr (j : Fin k) :
      (∑ i : Fin n, v j i • EuclideanSpace.single i 1) = v j := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (v j)
  calc
    T v = T (fun j => ∑ i : Fin n, v j i • EuclideanSpace.single i 1) :=
      congrArg T (funext hrepr).symm
    _ = ∑ I : Fin k → Fin n,
        T (fun j => v j (I j) • EuclideanSpace.single (I j) 1) :=
      T.map_sum (fun j i => v j i • EuclideanSpace.single i 1)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I _
      exact T.map_smul_univ (fun j => v j (I j))
        (fun j => EuclideanSpace.single (I j) 1)

/-- Coordinate values bounded by M give an operator-norm bound with a constant
depending only on the dimension and arity. -/
theorem norm_euclidean_multilinear_le_of_coordinate_bounds {n k : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Domain n) E)
    {M : ℝ} (hM : 0 ≤ M)
    (hcoordinates : ∀ I : Fin k → Fin n,
      ‖T (fun j => EuclideanSpace.single (I j) 1)‖ ≤ M) :
    ‖T‖ ≤ (n : ℝ) ^ k * M := by
  apply ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) k) hM)
  intro v
  rw [euclidean_multilinear_coordinate_expansion T v]
  have hproduct (I : Fin k → Fin n) :
      ‖∏ j : Fin k, v j (I j)‖ ≤ ∏ j : Fin k, ‖v j‖ := by
    rw [norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun j _ => PiLp.norm_apply_le (v j) (I j))
  calc
    _ ≤ ∑ I : Fin k → Fin n,
        ‖(∏ j : Fin k, v j (I j)) •
          T (fun j => EuclideanSpace.single (I j) 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _I : Fin k → Fin n, (∏ j : Fin k, ‖v j‖) * M := by
      apply Finset.sum_le_sum
      intro I _
      rw [norm_smul]
      exact mul_le_mul (hproduct I) (hcoordinates I) (norm_nonneg _)
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    _ = ((n : ℝ) ^ k * M) * ∏ j : Fin k, ‖v j‖ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      ring

/-- Actual coordinate-word bounds control the native iterated derivative
at the same point of the open domain. -/
theorem norm_iteratedFDeriv_le_of_coordinate_words {n q : ℕ}
    (Ω : OpenDomain n) {u : Domain n → Ambient q} (k : ℕ)
    (hu : ContDiffOn ℝ k u Ω.val) {M : ℝ} (hM : 0 ≤ M)
    (x : Domain n) (hx : x ∈ Ω.val)
    (hwords : ∀ w : List (Fin n), w.length = k → ‖coordinateWord u w x‖ ≤ M) :
    ‖iteratedFDeriv ℝ k u x‖ ≤ (n : ℝ) ^ k * M := by
  apply norm_euclidean_multilinear_le_of_coordinate_bounds _ hM
  intro I
  rw [← coordinateWord_ofFn_eq_iteratedFDeriv Ω I hu x hx]
  exact hwords (List.ofFn I) (List.length_ofFn (f := I))

/-- Differences of the same actual coordinate words control differences of
the same native iterated derivative. -/
theorem norm_iteratedFDeriv_sub_le_of_coordinate_words {n q : ℕ}
    (Ω : OpenDomain n) {u : Domain n → Ambient q} (k : ℕ)
    (hu : ContDiffOn ℝ k u Ω.val) {M : ℝ} (hM : 0 ≤ M)
    (x y : Domain n) (hx : x ∈ Ω.val) (hy : y ∈ Ω.val)
    (hwords : ∀ w : List (Fin n), w.length = k →
      ‖coordinateWord u w x - coordinateWord u w y‖ ≤ M) :
    ‖iteratedFDeriv ℝ k u x - iteratedFDeriv ℝ k u y‖ ≤ (n : ℝ) ^ k * M := by
  apply norm_euclidean_multilinear_le_of_coordinate_bounds _ hM
  intro I
  rw [sub_apply,
    ← coordinateWord_ofFn_eq_iteratedFDeriv Ω I hu x hx,
    ← coordinateWord_ofFn_eq_iteratedFDeriv Ω I hu y hy]
  exact hwords (List.ofFn I) (List.length_ofFn (f := I))

/-- Finite coordinate combination preserves the complete Holder exponent. -/
theorem iteratedFDeriv_holderBoundOn_of_coordinate_words {n q : ℕ}
    (Ω : OpenDomain n) {u : Domain n → Ambient q} (k : ℕ)
    (hu : ContDiffOn ℝ k u Ω.val) {α H : ℝ} (hH : 0 ≤ H)
    (hwords : ∀ w : List (Fin n), w.length = k →
      HolderBoundOn Ω.val (coordinateWord u w) α H) :
    HolderBoundOn Ω.val (iteratedFDeriv ℝ k u) α ((n : ℝ) ^ k * H) := by
  intro x hx y hy
  have hM : 0 ≤ H * Real.rpow (dist x y) α :=
    mul_nonneg hH (Real.rpow_nonneg dist_nonneg _)
  simpa only [mul_assoc] using norm_iteratedFDeriv_sub_le_of_coordinate_words Ω k hu hM
    x y hx hy (fun w hw => hwords w hw x hx y hy)

end HolderToCK
end
