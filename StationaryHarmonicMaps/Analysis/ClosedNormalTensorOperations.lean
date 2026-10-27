module

public import StationaryHarmonicMaps.Analysis.ClosedTwoTensorCoercivity

/-! # Actual linear operations on the smooth closed normal tensor core -/

public section

open HarmonicMaps Set Metric
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Differences preserve the actual smoothness, antisymmetry, differential closedness and normal contraction of the original tensor fields. -/
theorem smooth_closed_normal_twoTensor_sub {n q : ℕ}
    (B C : Fin n → Fin n → Domain n → Ambient q)
    (hB : ∀ i j,ContDiff ℝ ∞ (B i j)) (hC : ∀ i j,ContDiff ℝ ∞ (C i j))
    (hBS : ∀ i j x,B i j x = -B j i x) (hCS : ∀ i j x,C i j x = -C j i x)
    (hBD : ∀ i j k x,fderiv ℝ (B i j) x (EuclideanSpace.single k 1)+
      fderiv ℝ (B j k) x (EuclideanSpace.single i 1)+fderiv ℝ (B k i) x (EuclideanSpace.single j 1)=0)
    (hCD : ∀ i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
      fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0)
    (hBN : ∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • B i j x)=0)
    (hCN : ∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • C i j x)=0) :
    let D := fun i j x=>B i j x-C i j x
    (∀ i j,ContDiff ℝ ∞ (D i j)) ∧
      (∀ i j x,D i j x = -D j i x) ∧
      (∀ i j k x,fderiv ℝ (D i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (D j k) x (EuclideanSpace.single i 1)+fderiv ℝ (D k i) x (EuclideanSpace.single j 1)=0) ∧
      ∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • D i j x)=0 := by
  intro D
  have hDF (i j : Fin n) (x : Domain n) : fderiv ℝ (D i j) x =
      fderiv ℝ (B i j) x-fderiv ℝ (C i j) x := by
    have H := (((hB i j).differentiable (by simp) x).hasFDerivAt.sub
      ((hC i j).differentiable (by simp) x).hasFDerivAt).fderiv
    have heq : (B i j-C i j) = D i j := rfl
    rw [heq] at H
    exact H
  refine ⟨fun i j=>(hB i j).sub (hC i j),?_,?_,?_⟩
  · intro i j x
    change B i j x-C i j x = -(B j i x-C j i x)
    rw [hBS,hCS]
    abel
  · intro i j k x
    simp only [hDF,sub_apply]
    calc
      _ = (fderiv ℝ (B i j) x (EuclideanSpace.single k 1)+
          fderiv ℝ (B j k) x (EuclideanSpace.single i 1)+fderiv ℝ (B k i) x (EuclideanSpace.single j 1))-
          (fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
          fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)) := by abel
      _ = 0 := by rw [hBD,hCD,sub_self]
  · intro j x hx
    simp only [D,smul_sub,Finset.sum_sub_distrib,hBN j x hx,hCN j x hx,sub_self]

/-- A scalar multiple preserves the actual closed normal smooth tensor core. -/
theorem smooth_closed_normal_twoTensor_smul {n q : ℕ}
    (c : ℝ) (B : Fin n → Fin n → Domain n → Ambient q)
    (hB : ∀ i j,ContDiff ℝ ∞ (B i j))
    (hBS : ∀ i j x,B i j x = -B j i x)
    (hBD : ∀ i j k x,fderiv ℝ (B i j) x (EuclideanSpace.single k 1)+
      fderiv ℝ (B j k) x (EuclideanSpace.single i 1)+fderiv ℝ (B k i) x (EuclideanSpace.single j 1)=0)
    (hBN : ∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • B i j x)=0) :
    let D := fun i j x=>c • B i j x
    (∀ i j,ContDiff ℝ ∞ (D i j)) ∧
      (∀ i j x,D i j x = -D j i x) ∧
      (∀ i j k x,fderiv ℝ (D i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (D j k) x (EuclideanSpace.single i 1)+fderiv ℝ (D k i) x (EuclideanSpace.single j 1)=0) ∧
      ∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • D i j x)=0 := by
  intro D
  have hDF (i j : Fin n) (x : Domain n) : fderiv ℝ (D i j) x = c • fderiv ℝ (B i j) x := by
    have H := (((hB i j).differentiable (by simp) x).hasFDerivAt.const_smul c).fderiv
    have heq : (c • B i j) = D i j := rfl
    rw [heq] at H
    exact H
  refine ⟨fun i j=>(contDiff_const (c := c)).smul (hB i j),?_,?_,?_⟩
  · intro i j x
    change c • B i j x = -(c • B j i x)
    rw [hBS,smul_neg]
  · intro i j k x
    simp only [hDF,smul_apply,← smul_add,hBD,smul_zero]
  · intro j x hx
    simp only [D,smul_comm (x _),← Finset.smul_sum,hBN j x hx,smul_zero]

end StationaryHarmonicMaps.Analysis

end
