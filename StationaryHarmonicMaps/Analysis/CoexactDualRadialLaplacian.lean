/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.ExactTensorLaplacianTest

/-!
# Radial polynomial products in the relative tensor potential

The full coordinate Laplacian of a norm-square weighted coefficient keeps
the dimension and Euler terms. Coordinate-weighted coefficients supply
the Laplacian of the radial contraction used in the normal potential.
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

/-- The actual first derivative of the norm-square coefficient product. -/
theorem normSq_smul_fderiv_apply {n q : ℕ} (f : Domain n → Ambient q)
    (hf : ContDiff ℝ ∞ f) (x v : Domain n) :
    fderiv ℝ (fun y=>‖y‖^2 • f y) x v=
      ‖x‖^2 • fderiv ℝ f x v+(2*inner ℝ x v) • f x := by
  have hd := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.smul
    (hf.differentiable (by simp) x).hasFDerivAt
  have hfun : ((fun y : Domain n=>‖y‖^2) • f)=(fun y=>‖y‖^2 • f y) := by funext y;rfl
  rw [hfun] at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
    ]
  module

/-- The actual first derivative of one coordinate times the coefficient. -/
theorem coordinate_smul_fderiv_apply {n q : ℕ} (f : Domain n → Ambient q)
    (hf : ContDiff ℝ ∞ f) (j : Fin n) (x v : Domain n) :
    fderiv ℝ (fun y=>y j • f y) x v=x j • fderiv ℝ f x v+v j • f x := by
  let π := PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin n=>ℝ) j
  have hd := π.hasFDerivAt.smul (hf.differentiable (by simp) x).hasFDerivAt
  have hfun : ((fun y : Domain n=>π y) • f)=(fun y=>y j • f y) := by funext y;rfl
  rw [hfun] at hd
  rw [hd.fderiv]
  rfl

/-- The norm-square weighted coefficient has the full dimension and Euler Laplacian terms. -/
theorem normSq_smul_laplacian {n q : ℕ} (f : Domain n → Ambient q)
    (hf : ContDiff ℝ ∞ f) (x : Domain n) :
    Laplacian.laplacian (fun y=>‖y‖^2 • f y) x=
      ‖x‖^2 • Laplacian.laplacian f x+(4:ℝ) • fderiv ℝ f x x+(2*(n:ℝ)) • f x := by
  let D := fun i (y : Domain n)=>fderiv ℝ f y (EuclideanSpace.single i 1)
  have hD (i : Fin n) : ContDiff ℝ ∞ (D i) :=
    (hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hw : ContDiff ℝ ∞ (fun y : Domain n=>‖y‖^2 • f y) := (contDiff_norm_sq ℝ).smul hf
  have hFirst (i : Fin n) : (fun y=>fderiv ℝ (fun z=>‖z‖^2 • f z) y (EuclideanSpace.single i 1))=
      (fun y=>‖y‖^2 • D i y+(2:ℝ) • (y i • f y)) := by
    funext y
    rw [normSq_smul_fderiv_apply f hf]
    simp only [EuclideanSpace.inner_single_right,conj_trivial,one_mul,smul_smul,D]
  have hSecond (i : Fin n) : fderiv ℝ
      (fun y=>fderiv ℝ (fun z=>‖z‖^2 • f z) y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)=
      ‖x‖^2 • fderiv ℝ (D i) x (EuclideanSpace.single i 1)+
        (4:ℝ) • (x i • D i x)+(2:ℝ) • f x := by
    rw [hFirst]
    have hLeft : DifferentiableAt ℝ (fun y : Domain n=>‖y‖^2 • D i y) x :=
      ((contDiff_norm_sq ℝ).smul (hD i)).differentiable (by simp) x
    have hRight : DifferentiableAt ℝ (fun y : Domain n=>(2:ℝ) • (y i • f y)) x :=
      (((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin n=>ℝ) i).contDiff.smul hf).const_smul (2:ℝ)).differentiable (by simp) x
    have hCoord : DifferentiableAt ℝ (fun y : Domain n=>y i • f y) x :=
      (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin n=>ℝ) i).differentiableAt.smul (hf.differentiable (by simp) x)
    rw [fderiv_fun_add hLeft hRight,add_apply,fderiv_fun_const_smul hCoord,smul_apply,
      normSq_smul_fderiv_apply (D i) (hD i),coordinate_smul_fderiv_apply f hf]
    simp only [EuclideanSpace.inner_single_right,conj_trivial,one_mul,PiLp.single_apply,ite_true,one_smul]
    change ‖x‖^2 • fderiv ℝ (D i) x (EuclideanSpace.single i 1)+
      (2*x i) • D i x+(2:ℝ) • (x i • D i x+f x)=_
    module
  rw [smooth_vector_laplacian_eq_coordinate_sum _ hw]
  simp_rw [hSecond]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.smul_sum,← Finset.smul_sum]
  rw [← smooth_vector_laplacian_eq_coordinate_sum f hf x,clm_coordinate_sum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  congr 2
  ring

/-- The coordinate-weighted coefficient has the actual first-derivative cross term. -/
theorem coordinate_smul_laplacian {n q : ℕ} (f : Domain n → Ambient q)
    (hf : ContDiff ℝ ∞ f) (j : Fin n) (x : Domain n) :
    Laplacian.laplacian (fun y=>y j • f y) x=
      x j • Laplacian.laplacian f x+(2:ℝ) • fderiv ℝ f x (EuclideanSpace.single j 1) := by
  let D := fun i (y : Domain n)=>fderiv ℝ f y (EuclideanSpace.single i 1)
  have hD (i : Fin n) : ContDiff ℝ ∞ (D i) :=
    (hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hw : ContDiff ℝ ∞ (fun y : Domain n=>y j • f y) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin n=>ℝ) j).contDiff.smul hf
  have hFirst (i : Fin n) : (fun y=>fderiv ℝ (fun z=>z j • f z) y (EuclideanSpace.single i 1))=
      (fun y=>y j • D i y+(if i=j then (1:ℝ) else 0) • f y) := by
    funext y
    rw [coordinate_smul_fderiv_apply f hf]
    simp only [PiLp.single_apply,eq_comm,D]
  have hSecond (i : Fin n) : fderiv ℝ
      (fun y=>fderiv ℝ (fun z=>z j • f z) y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)=
      x j • fderiv ℝ (D i) x (EuclideanSpace.single i 1)+
        (if i=j then (2:ℝ) • D i x else 0) := by
    rw [hFirst]
    have hLeft : DifferentiableAt ℝ (fun y : Domain n=>y j • D i y) x :=
      ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin n=>ℝ) j).contDiff.smul (hD i)).differentiable (by simp) x
    rw [fderiv_fun_add hLeft ((hf.const_smul (if i=j then (1:ℝ) else 0)).differentiable (by simp) x),
      add_apply,fderiv_fun_const_smul (hf.differentiable (by simp) x),smul_apply,
      coordinate_smul_fderiv_apply (D i) (hD i)]
    by_cases hij : i=j
    · subst i
      simp only [PiLp.single_apply,ite_true,one_smul,D]
      module
    · simp only [PiLp.single_apply,if_neg hij,if_neg (Ne.symm hij),zero_smul,add_zero]
  rw [smooth_vector_laplacian_eq_coordinate_sum _ hw]
  simp_rw [hSecond]
  rw [Finset.sum_add_distrib,← Finset.smul_sum,
    ← smooth_vector_laplacian_eq_coordinate_sum f hf x]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,D]

private theorem laplacian_finite_sum {n q : ℕ} (A : Fin n → Domain n → Ambient q)
    (hA : ∀ i,ContDiff ℝ ∞ (A i)) (x : Domain n) :
    Laplacian.laplacian (fun y=>∑ i : Fin n,A i y) x=∑ i : Fin n,Laplacian.laplacian (A i) x := by
  have hSum : ContDiff ℝ ∞ (fun y=>∑ i : Fin n,A i y) := ContDiff.sum (fun i _=>hA i)
  have hD (i j : Fin n) : ContDiff ℝ ∞ (fun y=>fderiv ℝ (A i) y (EuclideanSpace.single j 1)) :=
    ((hA i).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hFirst (j : Fin n) :
      (fun y=>fderiv ℝ (fun z=>∑ i : Fin n,A i z) y (EuclideanSpace.single j 1))=
        (fun y=>∑ i : Fin n,fderiv ℝ (A i) y (EuclideanSpace.single j 1)) := by
    funext y
    rw [fderiv_fun_sum (fun i _=>(hA i).differentiable (by simp) y)]
    exact sum_apply _ _ _
  rw [smooth_vector_laplacian_eq_coordinate_sum _ hSum]
  simp_rw [hFirst]
  have hSecond (j : Fin n) : fderiv ℝ
      (fun y=>∑ i : Fin n,fderiv ℝ (A i) y (EuclideanSpace.single j 1)) x (EuclideanSpace.single j 1)=
        ∑ i : Fin n,fderiv ℝ (fun y=>fderiv ℝ (A i) y (EuclideanSpace.single j 1)) x (EuclideanSpace.single j 1) := by
    rw [fderiv_fun_sum (fun i _=>(hD i j).differentiable (by simp) x)]
    exact sum_apply _ _ _
  simp_rw [hSecond]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _=>(smooth_vector_laplacian_eq_coordinate_sum (A i) (hA i) x).symm)

/-- The radial contraction of the original one-form has its full Laplacian formula. -/
theorem radial_contraction_laplacian {n q : ℕ} (K : Fin n → Domain n → Ambient q)
    (hK : ∀ i,ContDiff ℝ ∞ (K i)) (x : Domain n) :
    Laplacian.laplacian (fun y=>∑ i : Fin n,y i • K i y) x=
      (∑ i : Fin n,x i • Laplacian.laplacian (K i) x)+
        (2:ℝ) • (∑ i : Fin n,fderiv ℝ (K i) x (EuclideanSpace.single i 1)) := by
  rw [laplacian_finite_sum (fun i y=>y i • K i y)
    (fun i=>(PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin n=>ℝ) i).contDiff.smul (hK i))]
  simp_rw [coordinate_smul_laplacian _ (hK _)]
  rw [Finset.sum_add_distrib,Finset.smul_sum]

end StationaryHarmonicMaps.Analysis

end
