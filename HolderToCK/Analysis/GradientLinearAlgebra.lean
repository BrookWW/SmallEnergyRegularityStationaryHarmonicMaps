module

public import HarmonicMaps.Analysis.BallSegmentEnergy
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! # Coordinate columns and the actual linear derivative

The finite sum of coordinate projections with vector columns is characterized
on the whole Euclidean carrier. Its norm uses the actual Hilbert--Schmidt
column density rather than the native Pi norm of the column array.
-/

public section

open HarmonicMaps Set

namespace HolderToCK

theorem columnLinearMap_apply {n q : ℕ} (G : Gradient n q) (v : Domain n) :
    (∑ i : Fin n, (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).smulRight (G i)) v =
      ∑ i : Fin n, v i • G i := by
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply]

theorem columnLinearMap_single {n q : ℕ} (G : Gradient n q) (j : Fin n) :
    (∑ i : Fin n, (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).smulRight (G i))
      (EuclideanSpace.single j 1) = G j := by
  rw [columnLinearMap_apply]
  simp only [EuclideanSpace.single, PiLp.single_apply, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem linearMap_eq_columnSum {n q : ℕ} (L : Domain n →L[ℝ] Ambient q) :
    L = ∑ i : Fin n, (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).smulRight
      (L (EuclideanSpace.single i 1)) := by
  apply ContinuousLinearMap.ext
  intro v
  have hrepr : (∑ i : Fin n, v i • EuclideanSpace.single i 1) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  rw [columnLinearMap_apply]
  calc
    L v = L (∑ i : Fin n, v i • EuclideanSpace.single i 1) := congrArg L hrepr.symm
    _ = _ := by simp only [map_sum, map_smul]

theorem norm_linearMap_le_sqrt_hsNormSq {n q : ℕ} (L : Domain n →L[ℝ] Ambient q) :
    ‖L‖ ≤ Real.sqrt (hsNormSq (fun i => L (EuclideanSpace.single i 1))) := by
  let M := Real.sqrt (hsNormSq (fun i => L (EuclideanSpace.single i 1)))
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hMsq : M ^ 2 = hsNormSq (fun i => L (EuclideanSpace.single i 1)) :=
    Real.sq_sqrt (hsNormSq_nonneg _)
  apply L.opNorm_le_bound hM
  intro v
  have hsq : ‖L v‖ ^ 2 ≤ (M * ‖v‖) ^ 2 := by
    rw [mul_pow, hMsq, mul_comm]
    exact norm_apply_sq_le_hsNormSq L v
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp hsq

theorem norm_linearMap_le_of_columns_bound {n q : ℕ}
    (L : Domain n →L[ℝ] Ambient q) {M : ℝ} (hM : 0 ≤ M)
    (hcolumns : ∀ i : Fin n, ‖L (EuclideanSpace.single i 1)‖ ≤ M) :
    ‖L‖ ≤ Real.sqrt (n : ℝ) * M := by
  have hHS : hsNormSq (fun i => L (EuclideanSpace.single i 1)) ≤ (n : ℝ) * M ^ 2 := by
    unfold hsNormSq
    calc
      _ ≤ ∑ _i : Fin n, M ^ 2 :=
        Finset.sum_le_sum (fun i _ => (sq_le_sq₀ (norm_nonneg _) hM).mpr (hcolumns i))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    ‖L‖ ≤ Real.sqrt (hsNormSq (fun i => L (EuclideanSpace.single i 1))) :=
      norm_linearMap_le_sqrt_hsNormSq L
    _ ≤ Real.sqrt ((n : ℝ) * M ^ 2) := Real.sqrt_le_sqrt hHS
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hM]

theorem columnLinearMap_continuousOn {n q : ℕ} {s : Set (Domain n)}
    {G : Domain n → Gradient n q} (hG : ∀ i : Fin n, ContinuousOn (fun x => G x i) s) :
    ContinuousOn (fun x => ∑ i : Fin n,
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).smulRight (G x i)) s := by
  apply continuousOn_finsetSum Finset.univ
  intro i _
  exact ((ContinuousLinearMap.smulRightL ℝ (Domain n) (Ambient q))
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i)).continuous.comp_continuousOn (hG i)

end HolderToCK
end
