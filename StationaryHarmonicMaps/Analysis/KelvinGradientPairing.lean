module

public import StationaryHarmonicMaps.Analysis.KelvinRadialCorrection
public import StationaryHarmonicMaps.Analysis.KelvinPiolaPairing

/-!
# Actual conformal first-derivative pairings for Kelvin reflection

The genuine inversion derivative is symmetric. Its Jacobian and radial
weights transfer the gradient part exactly. The remaining radial part is
the original first-derivative correction supplied by zero-boundary
integration by parts. All norm powers use the actual Euclidean norm.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open StationaryHarmonicMaps.Geometry
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

private theorem apply_eq_sum_columns {n q : ℕ} (F : Domain n →L[ℝ] Ambient q) (v : Domain n) :
    F v=∑i : Fin n,v i • F (EuclideanSpace.single i 1) := by
  have hV : (∑i : Fin n,v i • EuclideanSpace.single i 1)=v := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  calc
    _=F (∑i : Fin n,v i • EuclideanSpace.single i 1) := congrArg F hV.symm
    _=_ := by rw [map_sum];simp only [map_smul]

private theorem symmetric_right_composition_pairing {n q : ℕ}
    (F B : Domain n →L[ℝ] Ambient q) (D : Domain n →L[ℝ] Domain n)
    (hSym : ∀v z : Domain n,inner ℝ (D v) z=inner ℝ v (D z)) :
    (∑i : Fin n,inner ℝ (F (D (EuclideanSpace.single i 1))) (B (EuclideanSpace.single i 1)))=
      ∑i : Fin n,inner ℝ (F (EuclideanSpace.single i 1)) (B (D (EuclideanSpace.single i 1))) := by
  have hEntry (i j : Fin n) : (D (EuclideanSpace.single i 1)) j=(D (EuclideanSpace.single j 1)) i := by
    simpa only [EuclideanSpace.inner_single_right,EuclideanSpace.inner_single_left,
      conj_trivial,one_mul] using hSym (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have hF (i : Fin n) : F (D (EuclideanSpace.single i 1))=
      ∑j : Fin n,(D (EuclideanSpace.single i 1)) j • F (EuclideanSpace.single j 1) :=
    apply_eq_sum_columns F _
  have hB (i : Fin n) : B (D (EuclideanSpace.single i 1))=
      ∑j : Fin n,(D (EuclideanSpace.single i 1)) j • B (EuclideanSpace.single j 1) :=
    apply_eq_sum_columns B _
  simp_rw [hF,hB]
  simp only [sum_inner,inner_sum,real_inner_smul_left,inner_smul_right]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _=>Finset.sum_congr rfl (fun j _=>by rw [hEntry j i]))

private theorem inversion_derivative_inner_symmetric {n : ℕ} (x : Domain n) (hx : x≠0) :
    ∀v z : Domain n,inner ℝ (fderiv ℝ (inversion (0:Domain n) 1) x v) z=
      inner ℝ v (fderiv ℝ (inversion (0:Domain n) 1) x z) := by
  intro v z
  let S := (ℝ ∙ x)ᗮ.reflection
  have hS : inner ℝ (S v) z=inner ℝ v (S z) := by
    calc
      _=inner ℝ (S v) (S (S z)) := by rw [(ℝ ∙ x)ᗮ.reflection_reflection]
      _=_ := S.inner_map_map v (S z)
  rw [(hasFDerivAt_unit_inversion x hx).fderiv]
  simp only [smul_apply,real_inner_smul_left,inner_smul_right]
  exact congrArg (fun t : ℝ=>(‖x‖^2)⁻¹*t) hS

private theorem inversion_rpow {n : ℕ} (x : Domain n) (p : ℝ) :
    ‖inversion (0:Domain n) 1 x‖^p=‖x‖^(-p) := by
  rw [norm_unit_inversion,Real.inv_rpow (norm_nonneg x),← Real.rpow_neg (norm_nonneg x)]

private theorem inversion_jacobian_real_power {n : ℕ} (x : Domain n) (hx : x≠0) :
    |(fderiv ℝ (inversion (0:Domain n) 1) x).det|=‖x‖^(-2*(n:ℝ)) := by
  rw [abs_det_fderiv_unit_inversion x hx]
  calc
    _=(‖x‖^((2*n:ℕ):ℝ))⁻¹ := by rw [Real.rpow_natCast]
    _=‖x‖^(-((2*n:ℕ):ℝ)) := (Real.rpow_neg (norm_nonneg x) _).symm
    _=_ := by congr 1;push_cast;ring

private theorem inversion_weighted_derivative_covariance {n : ℕ} (x v : Domain n) (hx : x≠0) :
    let I := inversion (0:Domain n) 1
    (|(fderiv ℝ I x).det| *‖I x‖^(2-(n:ℝ))) • fderiv ℝ I (I x) v=
      ‖x‖^(2-(n:ℝ)) • fderiv ℝ I x v := by
  intro I
  have hPos : 0<‖x‖ := norm_pos_iff.mpr hx
  have hI0 : I x≠0 := norm_pos_iff.mp (by rw [show ‖I x‖=‖x‖⁻¹ from norm_unit_inversion x];positivity)
  have hScalar : (|(fderiv ℝ I x).det| *‖I x‖^(2-(n:ℝ)))*(‖I x‖^2)⁻¹=
      ‖x‖^(2-(n:ℝ))*(‖x‖^2)⁻¹ := by
    rw [inversion_jacobian_real_power x hx,inversion_rpow x (2-(n:ℝ)),norm_unit_inversion,inv_pow,inv_inv]
    have hRight : ‖x‖^(2-(n:ℝ))*(‖x‖^2)⁻¹=‖x‖^(-(n:ℝ)) := by
      rw [← Real.rpow_two,← Real.rpow_neg hPos.le,← Real.rpow_add hPos]
      congr 1
      ring
    rw [hRight,← Real.rpow_two,← Real.rpow_add hPos,← Real.rpow_add hPos]
    congr 1
    ring
  have hD1 : fderiv ℝ I (I x) v=(‖I x‖^2)⁻¹ • (ℝ ∙ I x)ᗮ.reflection v :=
    congrArg (fun L : Domain n →L[ℝ] Domain n=>L v) (hasFDerivAt_unit_inversion (I x) hI0).fderiv
  have hD2 : fderiv ℝ I x v=(‖x‖^2)⁻¹ • (ℝ ∙ x)ᗮ.reflection v :=
    congrArg (fun L : Domain n →L[ℝ] Domain n=>L v) (hasFDerivAt_unit_inversion x hx).fderiv
  rw [hD1,hD2,unit_inversion_radial_reflection_eq x hx,smul_smul,smul_smul,hScalar]

private theorem inversion_radial_coefficient_covariance {n : ℕ} (x : Domain n) (i : Fin n) (hx : x≠0) :
    let I := inversion (0:Domain n) 1
    |(fderiv ℝ I x).det| *‖I x‖^(-(n:ℝ))*inner ℝ (I x) (EuclideanSpace.single i 1)=
      ‖x‖^(-(n:ℝ)-2)*x i := by
  intro I
  have hPos : 0<‖x‖ := norm_pos_iff.mpr hx
  have hI : I x=(‖x‖^2)⁻¹ • x := by
    simp only [I,inversion,dist_zero_right,vsub_eq_sub,sub_zero,vadd_eq_add,add_zero,one_div,inv_pow]
  rw [inversion_jacobian_real_power x hx,inversion_rpow x (-(n:ℝ)),hI]
  simp only [EuclideanSpace.inner_single_right,conj_trivial,one_mul,PiLp.smul_apply,smul_eq_mul]
  rw [show -(-(n:ℝ))=(n:ℝ) by ring,← Real.rpow_two,← Real.rpow_neg hPos.le]
  calc
    _=(‖x‖^(-2*(n:ℝ))*‖x‖^(n:ℝ)*‖x‖^(-(2:ℝ)))*x i := by ring
    _=‖x‖^(-(n:ℝ)-2)*x i := by
      rw [← Real.rpow_add hPos,← Real.rpow_add hPos]
      congr 2
      ring

/-- The actual weighted Kelvin gradient has the exact Jacobian-transferred point pairing, including the radial correction, for arbitrary true derivative maps. -/
theorem unit_inversion_weighted_gradient_pairing {n q : ℕ}
    (x : Domain n) (hx : x≠0) (F B : Domain n →L[ℝ] Ambient q) (b : Ambient q) :
    let I := inversion (0:Domain n) 1
    |(fderiv ℝ I x).det| *(∑i : Fin n,inner ℝ
      (-‖I x‖^(2-(n:ℝ)) • F (fderiv ℝ I (I x) (EuclideanSpace.single i 1))-
        ((2-(n:ℝ))*‖I x‖^(-(n:ℝ))*inner ℝ (I x) (EuclideanSpace.single i 1)) • b)
      (B (EuclideanSpace.single i 1)))=
      -(∑i : Fin n,inner ℝ (F (EuclideanSpace.single i 1))
        (‖x‖^(2-(n:ℝ)) • B (fderiv ℝ I x (EuclideanSpace.single i 1))))+
      (2-(n:ℝ))*inner ℝ (‖x‖^(-(n:ℝ)) • B (fderiv ℝ I x x)) b := by
  intro I
  let J := |(fderiv ℝ I x).det|
  have hPos : 0<‖x‖ := norm_pos_iff.mpr hx
  have hTransfer := symmetric_right_composition_pairing F B (fderiv ℝ I x)
    (inversion_derivative_inner_symmetric x hx)
  have hFirst : J*(∑i : Fin n,inner ℝ
      (‖I x‖^(2-(n:ℝ)) • F (fderiv ℝ I (I x) (EuclideanSpace.single i 1)))
      (B (EuclideanSpace.single i 1)))=
      ∑i : Fin n,inner ℝ (F (EuclideanSpace.single i 1))
        (‖x‖^(2-(n:ℝ)) • B (fderiv ℝ I x (EuclideanSpace.single i 1))) := by
    calc
      _=∑i : Fin n,inner ℝ
          (F ((J*‖I x‖^(2-(n:ℝ))) • fderiv ℝ I (I x) (EuclideanSpace.single i 1)))
          (B (EuclideanSpace.single i 1)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _=>by simp only [map_smul,real_inner_smul_left];ring)
      _=∑i : Fin n,inner ℝ
          (F (‖x‖^(2-(n:ℝ)) • fderiv ℝ I x (EuclideanSpace.single i 1)))
          (B (EuclideanSpace.single i 1)) := by
        exact Finset.sum_congr rfl (fun i _=>by rw [inversion_weighted_derivative_covariance x _ hx])
      _=‖x‖^(2-(n:ℝ))*(∑i : Fin n,inner ℝ
          (F (fderiv ℝ I x (EuclideanSpace.single i 1))) (B (EuclideanSpace.single i 1))) := by
        simp only [map_smul,real_inner_smul_left,Finset.mul_sum]
      _=‖x‖^(2-(n:ℝ))*(∑i : Fin n,inner ℝ (F (EuclideanSpace.single i 1))
          (B (fderiv ℝ I x (EuclideanSpace.single i 1)))) := by rw [hTransfer]
      _=_ := by simp only [inner_smul_right,Finset.mul_sum]
  have hDX : fderiv ℝ I x x= -((‖x‖^2)⁻¹) • x := by
    rw [(hasFDerivAt_unit_inversion x hx).fderiv]
    change (‖x‖^2)⁻¹ • (ℝ ∙ x)ᗮ.reflection x= -((‖x‖^2)⁻¹) • x
    rw [Submodule.reflection_orthogonalComplement_singleton_eq_neg]
    simp only [smul_neg,neg_smul]
  have hPower : ‖x‖^(-(n:ℝ))*(‖x‖^2)⁻¹=‖x‖^(-(n:ℝ)-2) := by
    rw [← Real.rpow_two,← Real.rpow_neg hPos.le,← Real.rpow_add hPos]
    congr 1
  have hSecond : J*(∑i : Fin n,inner ℝ
      (((2-(n:ℝ))*‖I x‖^(-(n:ℝ))*inner ℝ (I x) (EuclideanSpace.single i 1)) • b)
      (B (EuclideanSpace.single i 1)))=
      -(2-(n:ℝ))*inner ℝ (‖x‖^(-(n:ℝ)) • B (fderiv ℝ I x x)) b := by
    have hScalarPair : J*(∑i : Fin n,inner ℝ
        (((2-(n:ℝ))*‖I x‖^(-(n:ℝ))*inner ℝ (I x) (EuclideanSpace.single i 1)) • b)
        (B (EuclideanSpace.single i 1)))=
        (2-(n:ℝ))*‖x‖^(-(n:ℝ)-2)*inner ℝ b (B x) := by
      simp only [real_inner_smul_left]
      calc
        _=(2-(n:ℝ))*‖x‖^(-(n:ℝ)-2)*(∑i : Fin n,x i*inner ℝ b (B (EuclideanSpace.single i 1))) := by
          rw [Finset.mul_sum,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          have H := inversion_radial_coefficient_covariance x i hx
          change J*‖I x‖^(-(n:ℝ))*inner ℝ (I x) (EuclideanSpace.single i 1)=_ at H
          calc
            _=(2-(n:ℝ))*(J*‖I x‖^(-(n:ℝ))*inner ℝ (I x) (EuclideanSpace.single i 1))*
                inner ℝ b (B (EuclideanSpace.single i 1)) := by ring
            _=_ := by rw [H];ring
        _=_ := by
          rw [apply_eq_sum_columns B x,inner_sum]
          simp only [inner_smul_right]
    rw [hScalarPair,hDX,map_smul,smul_smul,real_inner_smul_left]
    have hFactor : ‖x‖^(-(n:ℝ))*(-((‖x‖^2)⁻¹))= -‖x‖^(-(n:ℝ)-2) := by rw [mul_neg,hPower]
    rw [hFactor,real_inner_comm (B x) b]
    ring
  change J*(∑i : Fin n,inner ℝ
      (-‖I x‖^(2-(n:ℝ)) • F (fderiv ℝ I (I x) (EuclideanSpace.single i 1))-
        ((2-(n:ℝ))*‖I x‖^(-(n:ℝ))*inner ℝ (I x) (EuclideanSpace.single i 1)) • b)
      (B (EuclideanSpace.single i 1)))=_
  simp only [neg_smul,inner_sub_left,inner_neg_left,Finset.sum_sub_distrib,
    Finset.sum_neg_distrib,mul_sub,mul_neg]
  rw [hFirst,hSecond]
  ring

end StationaryHarmonicMaps.Analysis

end
