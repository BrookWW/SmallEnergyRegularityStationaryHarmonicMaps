module

public import StationaryHarmonicMaps.Analysis.KelvinGradientPairing
public import HarmonicMaps.Analysis.BallAverageDifferentiation

/-!
# Genuine conformal compact-test pairing for native odd Kelvin reflection

The original native W0 graph supplies the actual radial correction
identity. The true Jacobian transports the complete reflected gradient
pairing, including that correction. Actual integrability is established
before the change of variables and integral identities are used.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open StationaryHarmonicMaps.Geometry
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

private theorem apply_eq_sum_original_columns {n q : ℕ} (F : Domain n →L[ℝ] Ambient q) (v : Domain n) :
    F v=∑i : Fin n,v i • F (EuclideanSpace.single i 1) := by
  have hV : (∑i : Fin n,v i • EuclideanSpace.single i 1)=v := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  calc
    _=F (∑i : Fin n,v i • EuclideanSpace.single i 1) := congrArg F hV.symm
    _=_ := by rw [map_sum];simp only [map_smul]

private theorem kelvin_transformed_pairing_of_weighted_derivative {n q : ℕ}
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (ψ φ : Domain n → Ambient q)
    (hφ : ∀(x v : Domain n),x≠0 →
      fderiv ℝ φ x v=fderiv ℝ ψ x v-
        ‖x‖^(2-(n:ℝ)) • fderiv ℝ ψ (inversion (0:Domain n) 1 x)
          (fderiv ℝ (inversion (0:Domain n) 1) x v)-
        ((2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x v) • ψ (inversion (0:Domain n) 1 x))
    (y : Domain n) (hy : y≠0) :
    let I := inversion (0:Domain n) 1
    let C := fun x i=>∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • Du (I x) j
    let W := fun (x : Domain n) (i : Fin n)=>
      -‖x‖^(2-(n:ℝ)) • C x i-
        ((2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x (EuclideanSpace.single i 1)) • u (I x)
    let Pψ := fun x : Domain n=>∑i : Fin n,inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))
    let Pφ := fun x : Domain n=>∑i : Fin n,inner ℝ (Du x i) (fderiv ℝ φ x (EuclideanSpace.single i 1))
    let L := fun x : Domain n=>∑i : Fin n,inner ℝ
      ((‖x‖^(-(n:ℝ))*x i) • ψ (I x)) (Du x i)
    let H := fun x : Domain n=>inner ℝ (‖x‖^(-(n:ℝ)) • (∑i : Fin n,x i •
      fderiv ℝ ψ (I x) (fderiv ℝ I x (EuclideanSpace.single i 1)))) (u x)
    |(fderiv ℝ I y).det| * (∑i : Fin n,inner ℝ (W (I y) i)
      (fderiv ℝ ψ (I y) (EuclideanSpace.single i 1)))=
      Pφ y-Pψ y+(2-(n:ℝ))*(L y+H y) := by
  intro I C W Pψ Pφ L H
  let F : Domain n →L[ℝ] Ambient q :=
    ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constr ℝ (Du y)).toContinuousLinearMap
  let B := fderiv ℝ ψ (I y)
  let N := ∑i : Fin n,inner ℝ (Du y i) (‖y‖^(2-(n:ℝ)) • B (fderiv ℝ I y (EuclideanSpace.single i 1)))
  have hFCol (i : Fin n) : F (EuclideanSpace.single i 1)=Du y i := by
    change ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constr ℝ (Du y)) (EuclideanSpace.single i 1)=Du y i
    simpa only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.constr_basis ℝ (Du y) i
  have hFApply (z : Domain n) : F z=∑i : Fin n,z i • Du y i := by
    rw [apply_eq_sum_original_columns F z]
    exact Finset.sum_congr rfl (fun i _=>by rw [hFCol])
  have hH : H y=inner ℝ (‖y‖^(-(n:ℝ)) • B (fderiv ℝ I y y)) (u y) := by
    have H0 := apply_eq_sum_original_columns (B.comp (fderiv ℝ I y)) y
    change B (fderiv ℝ I y y)=(∑i : Fin n,y i • B (fderiv ℝ I y (EuclideanSpace.single i 1))) at H0
    exact congrArg (fun z : Ambient q=>inner ℝ (‖y‖^(-(n:ℝ)) • z) (u y)) H0.symm
  have hRad : (∑i : Fin n,inner ℝ (Du y i)
      (((2-(n:ℝ))*‖y‖^(-(n:ℝ))*inner ℝ y (EuclideanSpace.single i 1)) • ψ (I y)))=
      (2-(n:ℝ))*L y := by
    change (∑i : Fin n,inner ℝ (Du y i)
      (((2-(n:ℝ))*‖y‖^(-(n:ℝ))*inner ℝ y (EuclideanSpace.single i 1)) • ψ (I y)))=
      (2-(n:ℝ))*(∑i : Fin n,inner ℝ ((‖y‖^(-(n:ℝ))*y i) • ψ (I y)) (Du y i))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [inner_smul_right,real_inner_smul_left,EuclideanSpace.inner_single_right,conj_trivial,one_mul]
    rw [real_inner_comm (ψ (I y)) (Du y i)]
    ring
  have hPhi : Pφ y=Pψ y-N-(2-(n:ℝ))*L y := by
    change (∑i : Fin n,inner ℝ (Du y i) (fderiv ℝ φ y (EuclideanSpace.single i 1)))=Pψ y-N-(2-(n:ℝ))*L y
    simp_rw [hφ y _ hy,inner_sub_right]
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,hRad]
  have hPoint := unit_inversion_weighted_gradient_pairing y hy F B (u y)
  simp only [hFCol] at hPoint
  rw [← hH] at hPoint
  have hLeft : (∑i : Fin n,inner ℝ (W (I y) i) (fderiv ℝ ψ (I y) (EuclideanSpace.single i 1)))=
      ∑i : Fin n,inner ℝ
        (-‖I y‖^(2-(n:ℝ)) • F (fderiv ℝ I (I y) (EuclideanSpace.single i 1))-
          ((2-(n:ℝ))*‖I y‖^(-(n:ℝ))*inner ℝ (I y) (EuclideanSpace.single i 1)) • u y)
        (B (EuclideanSpace.single i 1)) := by
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [W,C,hFApply,I,inversion_inversion _ (by norm_num : (1:ℝ)≠0),B]
  rw [hLeft]
  change |(fderiv ℝ I y).det| * (∑i : Fin n,inner ℝ
        (-‖I y‖^(2-(n:ℝ)) • F (fderiv ℝ I (I y) (EuclideanSpace.single i 1))-
          ((2-(n:ℝ))*‖I y‖^(-(n:ℝ))*inner ℝ (I y) (EuclideanSpace.single i 1)) • u y)
        (B (EuclideanSpace.single i 1)))=Pφ y-Pψ y+(2-(n:ℝ))*(L y+H y)
  rw [hPoint,hPhi]
  change -N+(2-(n:ℝ))*H y=(Pψ y-N-(2-(n:ℝ))*L y)-Pψ y+(2-(n:ℝ))*(L y+H y)
  ring

/-- The literal reflected gradient of an original native W0 graph has the genuine full conformal compact-test pairing, with the true weighted native test produced. -/
theorem exists_weighted_kelvin_conformal_pairing {n q : ℕ} (hn : 2≤n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : HasZeroBoundaryValues (ballDomain (0:Domain n) 1) u Du)
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    let I := inversion (0:Domain n) 1
    let C := fun x i=>∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • Du (I x) j
    let W := fun (x : Domain n) (i : Fin n)=>
      -‖x‖^(2-(n:ℝ)) • C x i-
        ((2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x (EuclideanSpace.single i 1)) • u (I x)
    let Dext := fun (x : Domain n) (i : Fin n)=>if ‖x‖≤1 then Du x i else W x i
    ∃φ : Domain n → Ambient q,ContDiff ℝ ∞ φ ∧
      HasZeroBoundaryValues (ballDomain (0:Domain n) 1) φ
        (fun x i=>fderiv ℝ φ x (EuclideanSpace.single i 1)) ∧
      (∀x : Domain n,x≠0 → φ x=ψ x-‖x‖^(2-(n:ℝ)) • ψ (I x)) ∧
      (∀x v : Domain n,x≠0 → fderiv ℝ φ x v=fderiv ℝ ψ x v-
        ‖x‖^(2-(n:ℝ)) • fderiv ℝ ψ (I x) (fderiv ℝ I x v)-
        ((2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x v) • ψ (I x)) ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (W x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))
        {x : Domain n | 1<‖x‖} volume ∧
      Integrable (fun x=>∑i : Fin n,inner ℝ (Dext x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) volume ∧
      (∫x,∑i : Fin n,inner ℝ (Dext x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=
        ∫x in Metric.ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Du x i) (fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
  classical
  intro I C W Dext
  letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  let B := Metric.ball (0:Domain n) 1
  let D := B\{0}
  let O := {x : Domain n | 1<‖x‖}
  let μ := volume.restrict B
  obtain ⟨φ,hφ,hφW,hφVal,hφD⟩ := exists_weighted_kelvin_test_zeroBoundary hn ψ hψ hcψ
  let Pψ := fun x : Domain n=>∑i : Fin n,inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))
  let Pφ := fun x : Domain n=>∑i : Fin n,inner ℝ (Du x i) (fderiv ℝ φ x (EuclideanSpace.single i 1))
  let L := fun x : Domain n=>∑i : Fin n,inner ℝ ((‖x‖^(-(n:ℝ))*x i) • ψ (I x)) (Du x i)
  let H := fun x : Domain n=>inner ℝ (‖x‖^(-(n:ℝ)) • (∑i : Fin n,x i •
    fderiv ℝ ψ (I x) (fderiv ℝ I x (EuclideanSpace.single i 1)))) (u x)
  let E := fun x : Domain n=>∑i : Fin n,inner ℝ (W x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))
  have hPψ : Integrable Pψ μ := integrable_finsetSum _ (fun i _=>
    HolderToCK.integrable_inner_of_memLp_two (hu.1.2.2 i)
      (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hcψ.fderiv_apply ℝ (EuclideanSpace.single i 1))))
  have hPφ : Integrable Pφ μ := integrable_finsetSum _ (fun i _=>
    HolderToCK.integrable_inner_of_memLp_two (hu.1.2.2 i) (hφW.1.2.2 i))
  obtain ⟨_hL,_hH,hCorr,hCorrZero⟩ := zeroBoundary_kelvin_radial_correction (by omega : 1≤n) u Du hu ψ hψ hcψ
  have hAE0 : ∀ᵐx : Domain n∂volume,x≠0 := by simp [ae_iff]
  have hDB : D=ᵐ[volume] B := by
    filter_upwards [hAE0] with x hx
    change (x∈B\{0})=(x∈B)
    apply propext
    simp only [Set.mem_sdiff,mem_singleton_iff,hx,not_false_eq_true,and_true]
  have hMeasure := Measure.restrict_congr_set hDB
  have hD : MeasurableSet D := measurableSet_ball.diff (measurableSet_singleton _)
  have hD0 (x : Domain n) (hx : x∈D) : x≠0 := by simpa only [mem_singleton_iff] using hx.2
  have hID : I '' D=O := unit_inversion_image_punctured_ball
  have hDeriv (x : Domain n) (hx : x∈D) : HasFDerivWithinAt I (fderiv ℝ I x) D x :=
    (hasFDerivAt_unit_inversion x (hD0 x hx)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hInj : InjOn I D := (inversion_injective (0:Domain n) (by norm_num : (1:ℝ)≠0)).injOn
  have hPoint : (fun x=>|(fderiv ℝ I x).det| * E (I x)) =ᵐ[volume.restrict D]
      (fun x=>Pφ x-Pψ x+(2-(n:ℝ))*(L x+H x)) := by
    filter_upwards [ae_restrict_mem hD] with x hx
    exact kelvin_transformed_pairing_of_weighted_derivative u Du ψ φ hφD x (hD0 x hx)
  have hPφD : Integrable Pφ (volume.restrict D) := by rw [hMeasure];exact hPφ
  have hPψD : Integrable Pψ (volume.restrict D) := by rw [hMeasure];exact hPψ
  have hCorrD : Integrable (fun x=>L x+H x) (volume.restrict D) := by rw [hMeasure];exact hCorr
  have hRHS : Integrable (fun x=>Pφ x-Pψ x+(2-(n:ℝ))*(L x+H x)) (volume.restrict D) :=
    (hPφD.sub hPψD).add (hCorrD.const_mul _)
  have hTransformed : IntegrableOn (fun x=>|(fderiv ℝ I x).det| * E (I x)) D volume := hRHS.congr hPoint.symm
  have hEI : IntegrableOn E O volume := by
    have H0 := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hD hDeriv hInj E).mpr hTransformed
    simpa only [hID] using H0
  have hChange := integral_image_eq_integral_abs_det_fderiv_smul volume hD hDeriv hInj E
  rw [hID] at hChange
  simp only [smul_eq_mul] at hChange
  rw [integral_congr_ae hPoint] at hChange
  have hDiff : (∫x,Pφ x-Pψ x ∂volume.restrict D)=(∫x,Pφ x ∂volume.restrict D)-(∫x,Pψ x ∂volume.restrict D) := by
    simpa only [Pi.sub_apply] using integral_sub hPφD hPψD
  have hSum : (∫x,Pφ x-Pψ x+(2-(n:ℝ))*(L x+H x) ∂volume.restrict D)=
      (∫x,Pφ x-Pψ x ∂volume.restrict D)+(∫x,(2-(n:ℝ))*(L x+H x) ∂volume.restrict D) := by
    simpa only [Pi.add_apply,Pi.sub_apply] using integral_add (hPφD.sub hPψD) (hCorrD.const_mul _)
  have hExterior : (∫x in O,E x)=(∫x,Pφ x ∂μ)-(∫x,Pψ x ∂μ) := by
    rw [hChange,hSum,hDiff,integral_const_mul,hMeasure]
    change (∫x,Pφ x ∂μ)-(∫x,Pψ x ∂μ)+(2-(n:ℝ))*(∫x,L x+H x ∂μ)=_
    rw [hCorrZero,mul_zero,add_zero]
  let S := Metric.closedBall (0:Domain n) 1
  have hClosedMeasure : volume.restrict S=μ :=
    (Measure.restrict_congr_set (HarmonicMaps.ball_ae_eq_closedBall (0:Domain n) (by norm_num : (0:ℝ)<1))).symm
  have hClosed : IntegrableOn Pψ S volume := by
    change Integrable Pψ (volume.restrict S)
    rw [hClosedMeasure]
    exact hPψ
  have hOSet : Sᶜ=O := by ext x;simp only [S,O,mem_compl_iff,mem_setOf_eq,Metric.mem_closedBall,dist_zero_right,not_le]
  have hOuter : IntegrableOn E Sᶜ volume := by rw [hOSet];exact hEI
  have hPiece : (fun x=>∑i : Fin n,inner ℝ (Dext x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=
      S.piecewise Pψ E := by
    funext x
    by_cases hx : ‖x‖≤1 <;> simp only [Dext,piecewise,S,
      Metric.mem_closedBall,dist_zero_right,Pψ,E,hx,ite_true,ite_false]
  have hGlobal : Integrable (fun x=>∑i : Fin n,inner ℝ (Dext x i)
      (fderiv ℝ ψ x (EuclideanSpace.single i 1))) volume := by
    rw [hPiece]
    exact Integrable.piecewise measurableSet_closedBall hClosed hOuter
  refine ⟨φ,hφ,hφW,hφVal,hφD,hEI,hGlobal,?_⟩
  rw [hPiece,integral_piecewise measurableSet_closedBall hClosed hOuter,hClosedMeasure,hOSet,hExterior]
  ring

end StationaryHarmonicMaps.Analysis

end
