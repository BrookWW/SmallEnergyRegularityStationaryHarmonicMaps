module

public import StationaryHarmonicMaps.Analysis.OperatorHSCoefficientBounds
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Euclidean encoding of all operator coefficients

The standard product equivalence indexes the input and output coordinates.
The encoding is continuous linear and its Euclidean norm is the genuine
matrix Hilbert--Schmidt norm. No operator-norm isometry is asserted.
-/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps.Analysis

/-- A genuine continuous linear coefficient map realizes the full HS square as a Euclidean norm. -/
theorem exists_operator_coefficient_encoding (q : ℕ) :
    ∃ E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q),
      (∀ (T : Ambient q →L[ℝ] Ambient q) (k : Fin (q * q)),
        E T k = T (EuclideanSpace.single
          ((finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm k).1 1)
          ((finProdFinEquiv : Fin q × Fin q ≃ Fin (q * q)).symm k).2) ∧
      ∀ T : Ambient q →L[ℝ] Ambient q,
        ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2 := by
  let e : Fin q × Fin q ≃ Fin (q * q) := finProdFinEquiv
  let L : (Ambient q →L[ℝ] Ambient q) →ₗ[ℝ] (Fin (q * q) → ℝ) :=
    { toFun := fun T k => T (EuclideanSpace.single (e.symm k).1 1) (e.symm k).2
      map_add' := by intro T S; rfl
      map_smul' := by intro c T; rfl }
  let E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (q * q) => ℝ)).symm.toContinuousLinearMap.comp
      L.toContinuousLinearMap
  have hE (T : Ambient q →L[ℝ] Ambient q) (k : Fin (q * q)) :
      E T k = T (EuclideanSpace.single (e.symm k).1 1) (e.symm k).2 := rfl
  refine ⟨E, hE, ?_⟩
  intro T
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [hE]
  rw [operator_column_sq_sum_eq_entries_sq_sum]
  have hsum := Fintype.sum_equiv e
    (fun z : Fin q × Fin q => (T (EuclideanSpace.single z.1 1) z.2) ^ 2)
    (fun k : Fin (q * q) =>
      (T (EuclideanSpace.single (e.symm k).1 1) (e.symm k).2) ^ 2)
    (fun z => by rw [e.symm_apply_apply])
  simpa only [Fintype.sum_prod_type] using hsum.symm

end StationaryHarmonicMaps.Analysis

end
