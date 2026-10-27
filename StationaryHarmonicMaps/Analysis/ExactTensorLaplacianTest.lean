module

public import StationaryHarmonicMaps.Analysis.ClosedNormalExactTests
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Actual exact tensor tests for coefficient harmonicity

The single-component exterior derivative is an actual smooth closed normal
test. Its true divergence is the coefficient Laplacian minus a gradient,
with all second derivatives supplied by the original smooth vector test.
-/

public section

open HarmonicMaps Set Metric
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The actual vector Laplacian is the complete coordinate second-derivative sum. -/
theorem smooth_vector_laplacian_eq_coordinate_sum {n q : ℕ}
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ) (x : Domain n) :
    Laplacian.laplacian ψ x=∑ i : Fin n,fderiv ℝ
      (fun y=>fderiv ℝ ψ y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    (hψ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis ψ (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply,iteratedFDeriv_two_apply,
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,fderiv_const_apply,
    ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]

/-- The original supported smooth vector test produces a genuine closed normal exact tensor with its literal Laplacian-gradient divergence formula. -/
theorem single_component_exact_twoTensor_test {n q : ℕ}
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
    (hSupport : tsupport ψ ⊆ ball (0 : Domain n) 1) (l : Fin n) :
    let φ := fun (a : Fin n) (x : Domain n)=>if a=l then ψ x else 0
    let C := fun i j (x : Domain n)=>fderiv ℝ (φ j) x (EuclideanSpace.single i 1)-
      fderiv ℝ (φ i) x (EuclideanSpace.single j 1)
    (∀ i j,ContDiff ℝ ∞ (C i j)) ∧
      (∀ i j x,C i j x = -C j i x) ∧
      (∀ i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0) ∧
      (∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • C i j x)=0) ∧
      ∀ a (x : Domain n),(∑ i : Fin n,fderiv ℝ (C i a) x (EuclideanSpace.single i 1)) =
        (if a=l then Laplacian.laplacian ψ x else 0)-
          fderiv ℝ (fun y=>fderiv ℝ ψ y (EuclideanSpace.single l 1)) x (EuclideanSpace.single a 1) := by
  intro φ C
  have hφ (a : Fin n) : ContDiff ℝ ∞ (φ a) := by
    by_cases ha : a=l
    · simpa only [φ,if_pos ha] using hψ
    · simp only [φ,if_neg ha];exact contDiff_const
  have hsφ (a : Fin n) : tsupport (φ a) ⊆ ball (0 : Domain n) 1 := by
    by_cases ha : a=l
    · simpa only [φ,if_pos ha] using hSupport
    · simp only [φ,if_neg ha,tsupport_fun_zero,Set.empty_subset]
  obtain ⟨hC,hCS,hCD,hCN⟩ := supported_smooth_exact_twoTensor_core φ hφ hsφ
  refine ⟨hC,hCS,hCD,hCN,?_⟩
  intro a x
  let D := fun (i j : Fin n) (y : Domain n)=>fderiv ℝ (φ j) y (EuclideanSpace.single i 1)
  have hD (i j : Fin n) : ContDiff ℝ ∞ (D i j) :=
    ((hφ j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hDC (i j : Fin n) : fderiv ℝ (C i j) x=fderiv ℝ (D i j) x-fderiv ℝ (D j i) x := by
    have heq : C i j=D i j-D j i := rfl
    rw [heq]
    exact fderiv_sub ((hD i j).differentiable (by simp) x) ((hD j i).differentiable (by simp) x)
  have hDD (j i k : Fin n) : fderiv ℝ (D i j) x (EuclideanSpace.single k 1)=
      if j=l then fderiv ℝ (fun y=>fderiv ℝ ψ y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single k 1) else 0 := by
    by_cases hj : j=l
    · simp only [D,φ,if_pos hj]
    · simp [D,φ,hj]
  have hFirst : (∑ i : Fin n,fderiv ℝ (D i a) x (EuclideanSpace.single i 1)) =
      if a=l then Laplacian.laplacian ψ x else 0 := by
    simp_rw [hDD]
    by_cases ha : a=l
    · simp only [if_pos ha]
      exact (smooth_vector_laplacian_eq_coordinate_sum ψ hψ x).symm
    · simp only [if_neg ha,Finset.sum_const_zero]
  have hSecond : (∑ i : Fin n,fderiv ℝ (D a i) x (EuclideanSpace.single i 1)) =
      fderiv ℝ (fun y=>fderiv ℝ ψ y (EuclideanSpace.single l 1)) x (EuclideanSpace.single a 1) := by
    simp_rw [hDD]
    rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ l)]
    exact smooth_vector_mixed_fderiv ψ hψ x a l
  simp only [hDC,sub_apply,Finset.sum_sub_distrib,hFirst,hSecond]

end StationaryHarmonicMaps.Analysis

end
