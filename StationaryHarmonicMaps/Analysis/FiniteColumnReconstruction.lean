module

public import StationaryHarmonicMaps.Analysis.FiniteWeightedSum

/-!
# Actual finite-column cancellation of the correction reconstruction

At the original point only finitely many high weights are nonzero.
Each original compensation column has finite support in the low index.
The union of those actual finite supports makes the complete correction
sum finite before changing its order. Ordinary finite sums then give
zero from the original column sums.
-/

public section

open HarmonicMaps Set

namespace StationaryHarmonicMaps.Analysis

/-- The original finite high weights and genuinely finite zero-sum compensation columns produce a finite low correction family with actual total sum zero. -/
theorem finite_column_correction_tsum_zero {I J : Type*} (w : J → ℝ)
    (hW : Function.HasFiniteSupport w) (d : I → J → ℝ)
    (hColumns : ∀ j,Function.HasFiniteSupport (fun i=>d i j)) (hZero : ∀ j,(∑' i,d i j)=0) :
    Function.HasFiniteSupport (fun i=>∑' j,d i j*w j) ∧ (∑' i,∑' j,d i j*w j)=0 := by
  classical
  let V := hW.toFinset
  have hWZero (j : J) (hj : j∉V) : w j=0 := by
    by_contra hn
    exact hj (hW.mem_toFinset.mpr hn)
  have hFin : (⋃ j∈(V : Set J),Function.support (fun i=>d i j)).Finite :=
    V.finite_toSet.biUnion (fun j _=>hColumns j)
  let U := hFin.toFinset
  have hDZero (j : J) (hj : j∈V) (i : I) (hi : i∉U) : d i j=0 := by
    by_contra hn
    exact hi (hFin.mem_toFinset.mpr (mem_iUnion_of_mem j (mem_iUnion_of_mem hj hn)))
  have hRowEq (i : I) : (∑' j,d i j*w j)=∑ j∈V,d i j*w j :=
    tsum_eq_sum (fun j hj=>by rw [hWZero j hj,mul_zero])
  have hRowZero (i : I) (hi : i∉U) : (∑' j,d i j*w j)=0 := by
    rw [hRowEq]
    exact Finset.sum_eq_zero (fun j hj=>by rw [hDZero j hj i hi,zero_mul])
  have hFiniteRow : Function.HasFiniteSupport (fun i=>∑' j,d i j*w j) := U.finite_toSet.subset (by
    intro i hi
    by_contra hn
    exact hi (hRowZero i hn))
  have hColumnZero (j : J) (hj : j∈V) : (∑ i∈U,d i j)=0 :=
    (tsum_eq_sum (fun i hi=>hDZero j hj i hi)).symm.trans (hZero j)
  refine ⟨hFiniteRow,?_⟩
  rw [tsum_eq_sum hRowZero]
  simp_rw [hRowEq]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  rw [← Finset.sum_mul,hColumnZero j hj,zero_mul]

end StationaryHarmonicMaps.Analysis

end
