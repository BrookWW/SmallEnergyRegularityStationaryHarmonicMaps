/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.CoexactDualNormalPotential
public import StationaryHarmonicMaps.Analysis.CoexactDualRadialLaplacian
public import HarmonicMaps.Analysis.HarmonicDerivative

/-!
# The actual equation of the relative radial tensor potential

The radial correction of harmonic solenoidal Euler primitives is itself
solenoidal. Its actual closed normal tensor has divergence equal to the
original Euler forcing plus a genuine gradient, with the harmonic
identities required only on the specified open carrier.
-/

public section

open HarmonicMaps Set Metric Filter
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

private theorem two_le_infty : (2 : ℕ∞ω) ≤ ∞ :=
  le_of_lt (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top (2 : ℕ)))

private theorem clm_coordinate_sum {n q : ℕ}
    (L : Domain n →L[ℝ] Ambient q) (x : Domain n) :
    (∑ i : Fin n,x i • L (EuclideanSpace.single i 1))=L x := by
  nth_rw 2 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x]
  simp only [map_sum,map_smul,EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply]

private theorem smooth_radial_derivative_fderiv {n q : ℕ}
    (f : Domain n → Ambient q) (hf : ContDiff ℝ ∞ f) (j : Fin n) (x : Domain n) :
    fderiv ℝ (fun y=>fderiv ℝ f y y) x (EuclideanSpace.single j 1)=
      fderiv ℝ f x (EuclideanSpace.single j 1)+
        fderiv ℝ (fun y=>fderiv ℝ f y (EuclideanSpace.single j 1)) x x := by
  let D := fun i (y : Domain n)=>fderiv ℝ f y (EuclideanSpace.single i 1)
  have hD (i : Fin n) : ContDiff ℝ ∞ (D i) :=
    (hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hRep : (fun y=>fderiv ℝ f y y)=(fun y=>∑ i : Fin n,y i • D i y) := by
    funext y
    exact (clm_coordinate_sum (fderiv ℝ f y) y).symm
  rw [hRep]
  have hd := normal_contraction_hasFDerivAt D x (fun i=>(hD i).differentiable (by simp) x)
  rw [hd.fderiv]
  simp only [sum_apply,add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,
    Finset.sum_add_distrib,PiLp.single_apply,ite_smul,one_smul,zero_smul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hSwap : (∑ i : Fin n,x i • fderiv ℝ (D i) x (EuclideanSpace.single j 1))=
      fderiv ℝ (D j) x x := by
    rw [← clm_coordinate_sum]
    exact Finset.sum_congr rfl (fun i _=>congrArg (fun v : Ambient q=>x i • v)
      (smooth_vector_mixed_fderiv f hf x i j))
  rw [hSwap]
  exact add_comm _ _

private theorem exact_tensor_divergence {n q : ℕ}
    (φ : Fin n → Domain n → Ambient q) (hφ : ∀ j,ContDiff ℝ ∞ (φ j))
    (j : Fin n) (x : Domain n) :
    (∑ i : Fin n,fderiv ℝ (fun y=>fderiv ℝ (φ j) y (EuclideanSpace.single i 1)-
      fderiv ℝ (φ i) y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1))=
      Laplacian.laplacian (φ j) x-
        fderiv ℝ (fun y=>∑ i : Fin n,fderiv ℝ (φ i) y (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) := by
  have hD (i a : Fin n) : ContDiff ℝ ∞ (fun y=>fderiv ℝ (φ a) y (EuclideanSpace.single i 1)) :=
    ((hφ a).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hCurl (i : Fin n) : fderiv ℝ (fun y=>fderiv ℝ (φ j) y (EuclideanSpace.single i 1)-
      fderiv ℝ (φ i) y (EuclideanSpace.single j 1)) x=
      fderiv ℝ (fun y=>fderiv ℝ (φ j) y (EuclideanSpace.single i 1)) x-
        fderiv ℝ (fun y=>fderiv ℝ (φ i) y (EuclideanSpace.single j 1)) x :=
    fderiv_fun_sub ((hD i j).differentiable (by simp) x) ((hD j i).differentiable (by simp) x)
  simp_rw [hCurl,sub_apply]
  rw [Finset.sum_sub_distrib,← smooth_vector_laplacian_eq_coordinate_sum _ (hφ j) x,
    fderiv_fun_sum (fun i _=>(hD i i).differentiable (by simp) x),sum_apply]
  congr 1
  exact Finset.sum_congr rfl (fun i _=>smooth_vector_mixed_fderiv (φ i) (hφ i) x j i)

private theorem corrected_coefficient_smooth {n q : ℕ}
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

private theorem corrected_coefficient_derivative {n q : ℕ}
    (H K S : Domain n → Ambient q) (j i : Fin n)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (hS : ContDiff ℝ ∞ S) (x : Domain n) :
    fderiv ℝ (fun y : Domain n=>(1-‖y‖^2) • H y+(2:ℝ) • K y+
      ‖y‖^2 • fderiv ℝ S y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)=
      (1-‖x‖^2) • fderiv ℝ H x (EuclideanSpace.single i 1)+(-2*x i) • H x+
        (2:ℝ) • fderiv ℝ K x (EuclideanSpace.single i 1)+
        ‖x‖^2 • fderiv ℝ (fun y=>fderiv ℝ S y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)+
        (2*x i) • fderiv ℝ S x (EuclideanSpace.single j 1) := by
  let DS := fun y : Domain n=>fderiv ℝ S y (EuclideanSpace.single j 1)
  have hDS : ContDiff ℝ ∞ DS := (hS.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hr := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hd := ((((hasFDerivAt_const (1:ℝ) x).sub hr).smul (hH.differentiable (by simp) x).hasFDerivAt).add
    ((hasFDerivAt_const (2:ℝ) x).smul (hK.differentiable (by simp) x).hasFDerivAt)).add
    (hr.smul (hDS.differentiable (by simp) x).hasFDerivAt)
  have hfun : (((fun _ : Domain n=>(1:ℝ))-fun y=>‖y‖^2) • H+
      (fun _ : Domain n=>(2:ℝ)) • K+(fun y : Domain n=>‖y‖^2) • DS)=
      (fun y : Domain n=>(1-‖y‖^2) • H y+(2:ℝ) • K y+
        ‖y‖^2 • fderiv ℝ S y (EuclideanSpace.single j 1)) := by funext y;rfl
  rw [hfun] at hd
  rw [hd.fderiv]
  simp only [Pi.sub_apply,add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,sub_apply,
    zero_apply,zero_smul,add_zero,innerSL_apply_apply,EuclideanSpace.inner_single_right,
    conj_trivial,one_mul,DS]
  module

private theorem corrected_coefficient_laplacian {n q : ℕ}
    (H K S : Domain n → Ambient q) (j : Fin n)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (hS : ContDiff ℝ ∞ S)
    (x : Domain n) (hLH : Laplacian.laplacian H x=0) (hLK : Laplacian.laplacian K x=0)
    (hLS : Laplacian.laplacian (fun y=>fderiv ℝ S y (EuclideanSpace.single j 1)) x=0) :
    Laplacian.laplacian (fun y : Domain n=>(1-‖y‖^2) • H y+(2:ℝ) • K y+
      ‖y‖^2 • fderiv ℝ S y (EuclideanSpace.single j 1)) x=
      -(2*(n:ℝ)) • H x-(4:ℝ) • fderiv ℝ H x x+
        (2*(n:ℝ)) • fderiv ℝ S x (EuclideanSpace.single j 1)+
        (4:ℝ) • fderiv ℝ (fun y=>fderiv ℝ S y (EuclideanSpace.single j 1)) x x := by
  let DS := fun y : Domain n=>fderiv ℝ S y (EuclideanSpace.single j 1)
  let RH := fun y : Domain n=>‖y‖^2 • H y
  let RS := fun y : Domain n=>‖y‖^2 • DS y
  have hDS : ContDiff ℝ ∞ DS := (hS.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hRH : ContDiff ℝ ∞ RH := (contDiff_norm_sq ℝ).smul hH
  have hRS : ContDiff ℝ ∞ RS := (contDiff_norm_sq ℝ).smul hDS
  have hRep : (fun y : Domain n=>(1-‖y‖^2) • H y+(2:ℝ) • K y+
      ‖y‖^2 • fderiv ℝ S y (EuclideanSpace.single j 1))=H-RH+(2:ℝ) • K+RS := by
    funext y
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,RH,RS,DS,sub_smul,one_smul]
  have hSub : ContDiff ℝ ∞ (H-RH) := hH.sub hRH
  have hScaled : ContDiff ℝ ∞ ((2:ℝ) • K) := hK.const_smul (2:ℝ)
  have hAdd : ContDiff ℝ ∞ (H-RH+(2:ℝ) • K) := hSub.add hScaled
  rw [hRep,(hAdd.contDiffAt.of_le two_le_infty).laplacian_add (hRS.contDiffAt.of_le two_le_infty),
    (hSub.contDiffAt.of_le two_le_infty).laplacian_add (hScaled.contDiffAt.of_le two_le_infty),
    (hH.contDiffAt.of_le two_le_infty).laplacian_sub (hRH.contDiffAt.of_le two_le_infty),
    InnerProductSpace.laplacian_smul (2:ℝ) (hK.contDiffAt.of_le two_le_infty)]
  rw [show Laplacian.laplacian RH x=‖x‖^2 • Laplacian.laplacian H x+
      (4:ℝ) • fderiv ℝ H x x+(2*(n:ℝ)) • H x from normSq_smul_laplacian H hH x,
    show Laplacian.laplacian RS x=‖x‖^2 • Laplacian.laplacian DS x+
      (4:ℝ) • fderiv ℝ DS x x+(2*(n:ℝ)) • DS x from normSq_smul_laplacian DS hDS x]
  change Laplacian.laplacian DS x=0 at hLS
  rw [hLH,hLK,hLS,smul_zero,smul_zero,zero_add,zero_add]
  dsimp only [DS]
  module

/-- The displayed Euler correction is solenoidal and its actual tensor
divergence is the Euler forcing plus a genuine gradient on the original open carrier. -/
theorem euler_primitive_relative_tensor_equation {n q : ℕ}
    (U : Set (Domain n)) (hU : IsOpen U)
    (H K : Fin n → Domain n → Ambient q)
    (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hK : ∀ i,ContDiff ℝ ∞ (K i))
    (hEuler : ∀ j (x : Domain n),fderiv ℝ (K j) x x+K j x=H j x)
    (hLH : ∀ j x,x∈U → Laplacian.laplacian (H j) x=0)
    (hLK : ∀ j x,x∈U → Laplacian.laplacian (K j) x=0)
    (hDivH : ∀ x,x∈U → (∑ j : Fin n,fderiv ℝ (H j) x (EuclideanSpace.single j 1))=0)
    (hDivK : ∀ x,x∈U → (∑ j : Fin n,fderiv ℝ (K j) x (EuclideanSpace.single j 1))=0) :
    let S := fun x : Domain n=>∑ i : Fin n,x i • K i x
    let φ := fun j (x : Domain n)=>(1-‖x‖^2) • H j x+(2:ℝ) • K j x+
      ‖x‖^2 • fderiv ℝ S x (EuclideanSpace.single j 1)
    let C := fun i j (x : Domain n)=>fderiv ℝ (φ j) x (EuclideanSpace.single i 1)-
      fderiv ℝ (φ i) x (EuclideanSpace.single j 1)
    let g := fun x : Domain n=>(2*((n:ℝ)-2)) • S x+(4:ℝ) • fderiv ℝ S x x
    ContDiff ℝ ∞ g ∧
      (∀ x,x∈U → (∑ j : Fin n,fderiv ℝ (φ j) x (EuclideanSpace.single j 1))=0) ∧
      ∀ j x,x∈U → (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1))=
        -(2:ℝ) • ((n:ℝ) • H j x+(2:ℝ) • fderiv ℝ (H j) x x)+
          fderiv ℝ g x (EuclideanSpace.single j 1) := by
  intro S φ C g
  have hS : ContDiff ℝ ∞ S := ContDiff.sum fun i _=>
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin n=>ℝ) i).contDiff.smul (hK i)
  have hES : ContDiff ℝ ∞ (fun x : Domain n=>fderiv ℝ S x x) :=
    (hS.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_id
  have hg : ContDiff ℝ ∞ g :=
    (hS.const_smul (2*((n:ℝ)-2))).add (hES.const_smul (4:ℝ))
  let DS := fun j (x : Domain n)=>fderiv ℝ S x (EuclideanSpace.single j 1)
  have hφ (j : Fin n) : ContDiff ℝ ∞ (φ j) :=
    corrected_coefficient_smooth (H j) (K j) S j (hH j) (hK j) hS
  have hSrad (x : Domain n) : fderiv ℝ S x x=∑ i : Fin n,x i • H i x := by
    have hd := normal_contraction_hasFDerivAt K x (fun i=>(hK i).differentiable (by simp) x)
    rw [hd.fderiv]
    simp only [sum_apply,add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply]
    exact Finset.sum_congr rfl (fun i _=>by rw [← smul_add,hEuler])
  have hLS (x : Domain n) (hx : x∈U) : Laplacian.laplacian S x=0 := by
    rw [radial_contraction_laplacian K hK x,hDivK x hx]
    simp only [hLK _ x hx,smul_zero,Finset.sum_const_zero,add_zero]
  have hLDS (j : Fin n) (x : Domain n) (hx : x∈U) : Laplacian.laplacian (DS j) x=0 :=
    (harmonic_fderiv_column U hU S hS.contDiffOn hLS j).2 x hx
  have hDiv (x : Domain n) (hx : x∈U) :
      (∑ j : Fin n,fderiv ℝ (φ j) x (EuclideanSpace.single j 1))=0 := by
    have hD (j : Fin n) := corrected_coefficient_derivative (H j) (K j) S j j (hH j) (hK j) hS x
    have hSum : (∑ j : Fin n,fderiv ℝ (φ j) x (EuclideanSpace.single j 1))=
        (1-‖x‖^2) • (∑ j : Fin n,fderiv ℝ (H j) x (EuclideanSpace.single j 1))+
        (-2:ℝ) • (∑ j : Fin n,x j • H j x)+
        (2:ℝ) • (∑ j : Fin n,fderiv ℝ (K j) x (EuclideanSpace.single j 1))+
        ‖x‖^2 • Laplacian.laplacian S x+(2:ℝ) • fderiv ℝ S x x := by
      dsimp only [φ]
      simp_rw [hD]
      simp only [Finset.sum_add_distrib]
      rw [← Finset.smul_sum,← Finset.smul_sum]
      have hA : (∑ j : Fin n,(-2*x j) • H j x)=(-2:ℝ) • (∑ j : Fin n,x j • H j x) := by
        simp only [Finset.smul_sum,smul_smul]
      have hB : (∑ j : Fin n,(2*x j) • fderiv ℝ S x (EuclideanSpace.single j 1))=
          (2:ℝ) • fderiv ℝ S x x := by
        rw [← clm_coordinate_sum]
        simp only [Finset.smul_sum,smul_smul]
      rw [hA,hB,← Finset.smul_sum,← smooth_vector_laplacian_eq_coordinate_sum S hS x]
    rw [hSum,hDivH x hx,hDivK x hx,hLS x hx,hSrad,smul_zero,smul_zero,smul_zero]
    module
  refine ⟨hg,hDiv,?_⟩
  intro j x hx
  have hDivZero : (fun y=>∑ i : Fin n,fderiv ℝ (φ i) y (EuclideanSpace.single i 1)) =ᶠ[𝓝 x]
      (fun _=>(0:Ambient q)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hDiv y hy
  have hGradDiv : fderiv ℝ (fun y=>∑ i : Fin n,fderiv ℝ (φ i) y (EuclideanSpace.single i 1)) x=0 := by
    rw [hDivZero.fderiv_eq]
    exact fderiv_const_apply _
  rw [exact_tensor_divergence φ hφ j x,hGradDiv,zero_apply,sub_zero]
  rw [corrected_coefficient_laplacian (H j) (K j) S j (hH j) (hK j) hS x
    (hLH j x hx) (hLK j x hx) (hLDS j x hx)]
  have hG : fderiv ℝ g x (EuclideanSpace.single j 1)=
      (2*((n:ℝ)-2)) • fderiv ℝ S x (EuclideanSpace.single j 1)+
      (4:ℝ) • (fderiv ℝ S x (EuclideanSpace.single j 1)+
        fderiv ℝ (DS j) x x) := by
    dsimp only [g]
    rw [fderiv_fun_add ((hS.const_smul (2*((n:ℝ)-2))).differentiable (by simp) x)
        ((hES.const_smul (4:ℝ)).differentiable (by simp) x),add_apply,
      fderiv_fun_const_smul (hS.differentiable (by simp) x),
      fderiv_fun_const_smul (hES.differentiable (by simp) x),smul_apply,smul_apply,
      smooth_radial_derivative_fderiv S hS j x]
  rw [hG]
  dsimp only [DS]
  module

end StationaryHarmonicMaps.Analysis

end
