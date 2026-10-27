/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Geometry.OneFormGaffneyIdentity

/-!
# A closed normal tensor from an Euler primitive

The literal radial correction of two smooth one-forms has zero normal
contraction on the unit sphere when the second one is an Euler primitive
of the first. The derivative of its radial contraction and actual Hessian
symmetry supply the cancellation; no boundary identity is assumed.
-/

public section

open HarmonicMaps Set Metric
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem clm_coordinate_sum {n q : ℕ}
    (L : Domain n →L[ℝ] Ambient q) (x : Domain n) :
    (∑ i : Fin n,x i • L (EuclideanSpace.single i 1))=L x := by
  nth_rw 2 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x]
  simp only [map_sum,map_smul,EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply]

private theorem radial_corrected_coefficient_smooth {n q : ℕ}
    (H K S : Domain n → Ambient q) (j : Fin n)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (fun x : Domain n=>(1-‖x‖^2) • H x+(2:ℝ) • K x+
      ‖x‖^2 • fderiv ℝ S x (EuclideanSpace.single j 1)) := by
  have hD : ContDiff ℝ ∞ (fun x : Domain n=>fderiv ℝ S x (EuclideanSpace.single j 1)) :=
    (hS.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hr : ContDiff ℝ ∞ (fun x : Domain n=>‖x‖^2) := contDiff_norm_sq ℝ
  have hOne : ContDiff ℝ ∞ (fun x : Domain n=>(1:ℝ)-‖x‖^2) := contDiff_const.sub hr
  have hTwo : ContDiff ℝ ∞ (fun _x : Domain n=>(2:ℝ)) := contDiff_const
  exact ((hOne.smul hH).add (hTwo.smul hK)).add (hr.smul hD)

private theorem radial_corrected_coefficient_sphere_derivative {n q : ℕ}
    (H K S : Domain n → Ambient q) (j i : Fin n)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (hS : ContDiff ℝ ∞ S)
    (x : Domain n) (hx : ‖x‖=1) :
    fderiv ℝ (fun y : Domain n=>(1-‖y‖^2) • H y+(2:ℝ) • K y+
      ‖y‖^2 • fderiv ℝ S y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)=
      (-2*x i) • H x+(2:ℝ) • fderiv ℝ K x (EuclideanSpace.single i 1)+
      (2*x i) • fderiv ℝ S x (EuclideanSpace.single j 1)+
      fderiv ℝ (fun y=>fderiv ℝ S y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) := by
  let DS := fun y : Domain n=>fderiv ℝ S y (EuclideanSpace.single j 1)
  have hDS : ContDiff ℝ ∞ DS :=
    (hS.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hr := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hd := ((((hasFDerivAt_const (1:ℝ) x).sub hr).smul
    (hH.differentiable (by simp) x).hasFDerivAt).add
    ((hasFDerivAt_const (2:ℝ) x).smul (hK.differentiable (by simp) x).hasFDerivAt)).add
    (hr.smul (hDS.differentiable (by simp) x).hasFDerivAt)
  have hfun : (((fun _ : Domain n=>(1:ℝ))-fun y=>‖y‖^2) • H+
      (fun _ : Domain n=>(2:ℝ)) • K+(fun y : Domain n=>‖y‖^2) • DS)=
      (fun y : Domain n=>(1-‖y‖^2) • H y+(2:ℝ) • K y+
        ‖y‖^2 • fderiv ℝ S y (EuclideanSpace.single j 1)) := by
    funext y
    rfl
  rw [hfun] at hd
  rw [hd.fderiv]
  simp only [Pi.sub_apply,add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,sub_apply,
    zero_apply,zero_smul,zero_add,add_zero,hx,one_pow,sub_self,one_smul,
    innerSL_apply_apply,EuclideanSpace.inner_single_right,conj_trivial,one_mul,DS]
  module

private theorem exact_smooth_twoTensor_properties {n q : ℕ}
    (φ : Fin n → Domain n → Ambient q) (hφ : ∀ j,ContDiff ℝ ∞ (φ j)) :
    let C := fun i j (x : Domain n)=>fderiv ℝ (φ j) x (EuclideanSpace.single i 1)-
      fderiv ℝ (φ i) x (EuclideanSpace.single j 1)
    (∀ i j,ContDiff ℝ ∞ (C i j)) ∧
      (∀ i j x,C i j x = -C j i x) ∧
      ∀ i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0 := by
  intro C
  let D := fun (i j : Fin n) (x : Domain n)=>fderiv ℝ (φ j) x (EuclideanSpace.single i 1)
  have hD (i j : Fin n) : ContDiff ℝ ∞ (D i j) :=
    ((hφ j).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hDC (i j : Fin n) (x : Domain n) : fderiv ℝ (C i j) x =
      fderiv ℝ (D i j) x-fderiv ℝ (D j i) x := by
    have heq : C i j=D i j-D j i := rfl
    rw [heq]
    exact fderiv_sub ((hD i j).differentiable (by simp) x) ((hD j i).differentiable (by simp) x)
  refine ⟨fun i j=>(hD i j).sub (hD j i),?_,?_⟩
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

private theorem euler_primitive_normal_twoTensor {n q : ℕ}
    (H K : Fin n → Domain n → Ambient q)
    (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hK : ∀ i,ContDiff ℝ ∞ (K i))
    (hEuler : ∀ j (x : Domain n),fderiv ℝ (K j) x x+K j x=H j x) :
    let S := fun x : Domain n=>∑ i : Fin n,x i • K i x
    let φ := fun j (x : Domain n)=>(1-‖x‖^2) • H j x+(2:ℝ) • K j x+
      ‖x‖^2 • fderiv ℝ S x (EuclideanSpace.single j 1)
    let C := fun i j (x : Domain n)=>fderiv ℝ (φ j) x (EuclideanSpace.single i 1)-
      fderiv ℝ (φ i) x (EuclideanSpace.single j 1)
    ∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • C i j x)=0 := by
  intro S φ C
  have hS : ContDiff ℝ ∞ S := ContDiff.sum fun i _=>
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin n=>ℝ) i).contDiff.smul (hK i)
  let DS := fun j (x : Domain n)=>fderiv ℝ S x (EuclideanSpace.single j 1)
  intro j x hx
  have hSder (v : Domain n) : fderiv ℝ S x v=
      ∑ i : Fin n,(x i • fderiv ℝ (K i) x v+v i • K i x) := by
    have hd := normal_contraction_hasFDerivAt K x (fun i=>(hK i).differentiable (by simp) x)
    have he := congrArg (fun L : Domain n →L[ℝ] Ambient q=>L v) hd.fderiv
    simpa only [S,sum_apply,add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply] using he
  have hSrad : fderiv ℝ S x x=∑ i : Fin n,x i • H i x := by
    rw [hSder]
    apply Finset.sum_congr rfl
    intro i _
    rw [← smul_add,hEuler]
  have hSj : DS j x=(∑ i : Fin n,x i • fderiv ℝ (K i) x (EuclideanSpace.single j 1))+K j x := by
    rw [show DS j x=fderiv ℝ S x (EuclideanSpace.single j 1) from rfl,hSder,Finset.sum_add_distrib]
    congr 1
    simp only [PiLp.single_apply,ite_smul,zero_smul,one_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hφder (a i : Fin n) := radial_corrected_coefficient_sphere_derivative
    (H a) (K a) S a i (hH a) (hK a) hS x hx
  have hCurl (i : Fin n) : C i j x=
      (-2*x i) • H j x-(-2*x j) • H i x+
      (2:ℝ) • (fderiv ℝ (K j) x (EuclideanSpace.single i 1)-
        fderiv ℝ (K i) x (EuclideanSpace.single j 1))+
      (2*x i) • DS j x-(2*x j) • DS i x := by
    have hSym := smooth_vector_mixed_fderiv S hS x j i
    change fderiv ℝ (DS j) x (EuclideanSpace.single i 1)=
      fderiv ℝ (DS i) x (EuclideanSpace.single j 1) at hSym
    dsimp only [C]
    rw [hφder,hφder,hSym,smul_sub]
    abel
  have hSq : (∑ i : Fin n,x i^2)=1 := by rw [← EuclideanSpace.real_norm_sq_eq,hx,one_pow]
  have hSum : (∑ i : Fin n,x i • C i j x)=
      (-2:ℝ) • H j x+(2*x j) • (∑ i : Fin n,x i • H i x)+
      (2:ℝ) • (fderiv ℝ (K j) x x-
        ∑ i : Fin n,x i • fderiv ℝ (K i) x (EuclideanSpace.single j 1))+
      (2:ℝ) • DS j x-(2*x j) • fderiv ℝ S x x := by
    simp only [hCurl,smul_sub,smul_add,smul_smul]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have h1 : (∑ i : Fin n,(x i*(-2*x i)) • H j x)=(-2:ℝ) • H j x := by
      rw [← Finset.sum_smul]
      congr 1
      calc
        _=(-2:ℝ)*(∑ i : Fin n,x i^2) := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;ring
        _= -2 := by rw [hSq,mul_one]
    have h2 (A : Fin n → Ambient q) :
        (∑ i : Fin n,(x i*(2*x j)) • A i)=(2*x j) • (∑ i : Fin n,x i • A i) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul]
      congr 1
      ring
    have h3 (A : Fin n → Ambient q) :
        (∑ i : Fin n,(x i*2) • A i)=(2:ℝ) • (∑ i : Fin n,x i • A i) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul]
      congr 1
      ring
    have h4 : (∑ i : Fin n,(x i*(2*x i)) • DS j x)=(2:ℝ) • DS j x := by
      rw [← Finset.sum_smul]
      congr 1
      calc
        _=(2:ℝ)*(∑ i : Fin n,x i^2) := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;ring
        _= 2 := by rw [hSq,mul_one]
    have h2neg : (∑ i : Fin n,(x i*(-2*x j)) • H i x)=
        -(2*x j) • (∑ i : Fin n,x i • H i x) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul]
      congr 1
      ring
    rw [h1,h2neg,h3,h3,h4,h2,clm_coordinate_sum,clm_coordinate_sum]
    simp only [neg_smul,sub_neg_eq_add]
  rw [hSum,hSrad,hSj,← hEuler j x]
  module

/-- An actual smooth Euler primitive produces the full smooth closed normal
tensor core through its displayed radial correction. -/
theorem euler_primitive_closed_normal_twoTensor {n q : ℕ}
    (H K : Fin n → Domain n → Ambient q)
    (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hK : ∀ i,ContDiff ℝ ∞ (K i))
    (hEuler : ∀ j (x : Domain n),fderiv ℝ (K j) x x+K j x=H j x) :
    let S := fun x : Domain n=>∑ i : Fin n,x i • K i x
    let φ := fun j (x : Domain n)=>(1-‖x‖^2) • H j x+(2:ℝ) • K j x+
      ‖x‖^2 • fderiv ℝ S x (EuclideanSpace.single j 1)
    let C := fun i j (x : Domain n)=>fderiv ℝ (φ j) x (EuclideanSpace.single i 1)-
      fderiv ℝ (φ i) x (EuclideanSpace.single j 1)
    (∀ i j,ContDiff ℝ ∞ (C i j)) ∧
      (∀ i j x,C i j x = -C j i x) ∧
      (∀ i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0) ∧
      ∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • C i j x)=0 := by
  intro S φ C
  have hS : ContDiff ℝ ∞ S := ContDiff.sum fun i _=>
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin n=>ℝ) i).contDiff.smul (hK i)
  have hφ (j : Fin n) : ContDiff ℝ ∞ (φ j) :=
    radial_corrected_coefficient_smooth (H j) (K j) S j (hH j) (hK j) hS
  obtain ⟨hC,hCS,hCD⟩ := exact_smooth_twoTensor_properties φ hφ
  exact ⟨hC,hCS,hCD,euler_primitive_normal_twoTensor H K hH hK hEuler⟩

end StationaryHarmonicMaps.Analysis

end
