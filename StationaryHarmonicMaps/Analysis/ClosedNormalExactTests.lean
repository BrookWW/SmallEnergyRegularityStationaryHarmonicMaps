module

public import StationaryHarmonicMaps.Geometry.OneFormGaffneyIdentity
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-! # Actual compact exact test tensors in the closed normal core -/

public section

open HarmonicMaps Set Metric
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Exterior derivatives of the actual supported smooth one-form tests belong to the genuine closed antisymmetric normal core. -/
theorem supported_smooth_exact_twoTensor_core {n q : ℕ}
    (φ : Fin n → Domain n → Ambient q) (hφ : ∀ i,ContDiff ℝ ∞ (φ i))
    (hSupport : ∀ i,tsupport (φ i) ⊆ ball (0 : Domain n) 1) :
    let C := fun i j (x : Domain n)=>fderiv ℝ (φ j) x (EuclideanSpace.single i 1)-
      fderiv ℝ (φ i) x (EuclideanSpace.single j 1)
    (∀ i j,ContDiff ℝ ∞ (C i j)) ∧
      (∀ i j x,C i j x = -C j i x) ∧
      (∀ i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0) ∧
      ∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • C i j x)=0 := by
  intro C
  let D := fun (i j : Fin n) (x : Domain n)=>fderiv ℝ (φ j) x (EuclideanSpace.single i 1)
  have hD (i j : Fin n) : ContDiff ℝ ∞ (D i j) :=
    ((hφ j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hDC (i j : Fin n) (x : Domain n) : fderiv ℝ (C i j) x =
      fderiv ℝ (D i j) x-fderiv ℝ (D j i) x := by
    have heq : C i j=D i j-D j i := rfl
    rw [heq]
    exact fderiv_sub ((hD i j).differentiable (by simp) x) ((hD j i).differentiable (by simp) x)
  refine ⟨fun i j=>(hD i j).sub (hD j i),?_,?_,?_⟩
  · intro i j x
    dsimp only [C]
    abel
  · intro i j k x
    simp only [hDC,sub_apply]
    have h1 := smooth_vector_mixed_fderiv (φ j) (hφ j) x i k
    have h2 := smooth_vector_mixed_fderiv (φ i) (hφ i) x j k
    have h3 := smooth_vector_mixed_fderiv (φ k) (hφ k) x j i
    change fderiv ℝ (D i j) x (EuclideanSpace.single k 1)=
      fderiv ℝ (D k j) x (EuclideanSpace.single i 1) at h1
    change fderiv ℝ (D j i) x (EuclideanSpace.single k 1)=
      fderiv ℝ (D k i) x (EuclideanSpace.single j 1) at h2
    change fderiv ℝ (D j k) x (EuclideanSpace.single i 1)=
      fderiv ℝ (D i k) x (EuclideanSpace.single j 1) at h3
    rw [h1,h2,h3]
    abel
  · intro j x hx
    have hxBall : x∉ball (0 : Domain n) 1 := by
      simp only [mem_ball,dist_zero_right,hx,lt_self_iff_false,not_false_eq_true]
    have hDz (i a : Fin n) : D i a x=0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun hmem=>hxBall (hSupport a ((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)) hmem))
    apply Finset.sum_eq_zero
    intro i _
    change x i • (D i j x-D j i x)=0
    rw [hDz,hDz,sub_self,smul_zero]

end StationaryHarmonicMaps.Analysis

end
