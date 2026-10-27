module

public import HarmonicMaps.Analysis.PoissonPolarAlgebra
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module

/-!
# Native Euler and angular derivative identities

The actual coordinate rotations give the full polar Laplacian identity with
its ordered-pair coefficient two. Euler differentiation commutes with each
coordinate rotation for the same smooth map and native Fréchet derivatives.
-/

public section

open Set
open scoped BigOperators ContDiff

namespace HarmonicMaps

/-- Actual coordinate generators produce the polar Laplacian and Euler
commutation identities from genuine open-domain smoothness. -/
theorem poisson_coordinate_polar_calculus (n : ℕ) :
    ∃ A : Fin n → Fin n → (Domain n →L[ℝ] Domain n),
      (∀ i j, star (A i j) = -A i j ∧
        ∀ x : Domain n, A i j x =
          x i • EuclideanSpace.single j 1 - x j • EuclideanSpace.single i 1) ∧
      ∀ (q : ℕ) (W : Set (Domain n)), IsOpen W →
      ∀ (f : Domain n → Ambient q), ContDiffOn ℝ ∞ f W →
      ∀ x ∈ W,
      let E : Domain n → Ambient q := fun y => fderiv ℝ f y y
      let L : Fin n → Fin n → Domain n → Ambient q :=
        fun i j y => fderiv ℝ f y (A i j y)
      (∑ i : Fin n, ∑ j : Fin n, fderiv ℝ (L i j) x (A i j x)) =
        (2 : ℝ) • (‖x‖ ^ 2 • Laplacian.laplacian f x -
          fderiv ℝ E x x - ((n : ℝ) - 2) • E x) ∧
      ∀ i j, fderiv ℝ E x (A i j x) = fderiv ℝ (L i j) x x := by
  obtain ⟨A, hA⟩ := poisson_coordinateSkewGenerators n
  refine ⟨A, hA, ?_⟩
  intro q W hW f hf x hx
  let B := fderiv ℝ f x
  let H := fderiv ℝ (fderiv ℝ f) x
  let e : Fin n → Domain n := fun i => EuclideanSpace.single i 1
  let E : Domain n → Ambient q := fun y => fderiv ℝ f y y
  let L : Fin n → Fin n → Domain n → Ambient q :=
    fun i j y => fderiv ℝ f y (A i j y)
  have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hW.mem_nhds hx)
  have hDfSmooth : ContDiffOn ℝ ∞ (fderiv ℝ f) W := hf.fderiv_of_isOpen hW (by simp)
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hDfSmooth.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have hRotation (i j : Fin n) (v : Domain n) :
      fderiv ℝ (L i j) x v = B (A i j v) + H v (A i j x) := by
    rw [fderiv_clm_apply hDf (A i j).differentiableAt]
    simp only [B, H, (A i j).fderiv, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
  have hEuler (v : Domain n) : fderiv ℝ E x v = B v + H v x := by
    change fderiv ℝ (fun y : Domain n => fderiv ℝ f y y) x v = _
    rw [fderiv_clm_apply (u := fun y : Domain n => y) hDf differentiableAt_id]
    simp only [B, H, fderiv_fun_id, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply]
  have hLap : Laplacian.laplacian f x = ∑ i : Fin n, H (e i) (e i) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
      (EuclideanSpace.basisFun (Fin n) ℝ)]
    simp only [e, H, EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · have hAlgebra := poisson_orderedRotation_secondDerivative_algebra x B H
    dsimp only at hAlgebra
    have hsum : (∑ i : Fin n, ∑ j : Fin n, fderiv ℝ (L i j) x (A i j x)) =
        ∑ i : Fin n, ∑ j : Fin n,
          (H (x i • e j - x j • e i) (x i • e j - x j • e i) +
            B ((x i • e j - x j • e i) i • e j -
              (x i • e j - x j • e i) j • e i)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hRotation]
      rw [(hA i j).2 (A i j x), (hA i j).2 x]
      exact add_comm _ _
    rw [hsum, hAlgebra, hLap, hEuler]
    change (2 : ℝ) • (‖x‖ ^ 2 • (∑ i : Fin n, H (e i) (e i)) - H x x -
      ((n : ℝ) - 1) • B x) =
      (2 : ℝ) • (‖x‖ ^ 2 • (∑ i : Fin n, H (e i) (e i)) -
        (B x + H x x) - ((n : ℝ) - 2) • B x)
    module
  · intro i j
    rw [hEuler, hRotation]
    have hSymm : H (A i j x) x = H x (A i j x) :=
      (hfx.isSymmSndFDerivAt
        (by simp only [minSmoothness_of_isRCLikeNormedField]
            exact WithTop.coe_le_coe.mpr le_top)).eq _ _
    rw [hSymm]

end HarmonicMaps
end
