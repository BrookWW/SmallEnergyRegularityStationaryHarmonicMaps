module

public import StationaryHarmonicMaps.Analysis.OperatorCoefficientEncoding

/-!
# Genuine Euclidean coordinates for operator-valued Sobolev fields

The coefficient encoder and a continuous linear decoder are inverse on their
whole carriers. The Euclidean norm retains the full Hilbert--Schmidt square;
no equality with the operator norm is asserted.
-/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps.Analysis

/-- Full coefficient coordinates admit an actual continuous linear inverse. -/
theorem exists_operator_coefficient_coordinates (q : ℕ) :
    ∃ (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q))
      (R : Ambient (q * q) →L[ℝ] (Ambient q →L[ℝ] Ambient q)),
      (∀ (T : Ambient q →L[ℝ] Ambient q) (j k : Fin q),
        E T (finProdFinEquiv (j, k)) = T (EuclideanSpace.single j 1) k) ∧
      (∀ (z : Ambient (q * q)) (j k : Fin q),
        R z (EuclideanSpace.single j 1) k = z (finProdFinEquiv (j, k))) ∧
      (∀ T, R (E T) = T) ∧ (∀ z, E (R z) = z) ∧
      ∀ T : Ambient q →L[ℝ] Ambient q,
        ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2 := by
  classical
  obtain ⟨E, hE, hnorm⟩ := exists_operator_coefficient_encoding q
  let C : Ambient (q * q) →ₗ[ℝ] (Fin q → Ambient q) :=
    { toFun := fun z j => WithLp.toLp 2 (fun k => z (finProdFinEquiv (j, k)))
      map_add' := by intro z w; ext j k; rfl
      map_smul' := by intro c z; ext j k; rfl }
  let B := (EuclideanSpace.basisFun (Fin q) ℝ).toBasis
  let L : Ambient (q * q) →ₗ[ℝ] (Ambient q →L[ℝ] Ambient q) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp ((B.constr ℝ).toLinearMap.comp C)
  let R : Ambient (q * q) →L[ℝ] (Ambient q →L[ℝ] Ambient q) := L.toContinuousLinearMap
  have hE' (T : Ambient q →L[ℝ] Ambient q) (j k : Fin q) :
      E T (finProdFinEquiv (j, k)) = T (EuclideanSpace.single j 1) k := by
    rw [hE]
    simp only [Equiv.symm_apply_apply]
  have hb (j : Fin q) : B j = EuclideanSpace.single j 1 := by
    simp only [B, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  have hR (z : Ambient (q * q)) (j k : Fin q) :
      R z (EuclideanSpace.single j 1) k = z (finProdFinEquiv (j, k)) := by
    change ((B.constr ℝ) (C z)) (EuclideanSpace.single j 1) k = _
    rw [← hb j, B.constr_basis]
    rfl
  refine ⟨E, R, hE', hR, ?_, ?_, hnorm⟩
  · intro T
    apply ContinuousLinearMap.coe_injective
    apply B.ext
    intro j
    apply PiLp.ext
    intro k
    simp only [hb, ContinuousLinearMap.coe_coe]
    change R (E T) (EuclideanSpace.single j 1) k = T (EuclideanSpace.single j 1) k
    rw [hR, hE']
  · intro z
    apply PiLp.ext
    intro k
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    rw [hE', hR]

end StationaryHarmonicMaps.Analysis

end
