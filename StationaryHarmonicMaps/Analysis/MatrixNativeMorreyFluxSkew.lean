module

public import StationaryHarmonicMaps.Analysis.MatrixNativeMorreyInverseExponential
public import StationaryHarmonicMaps.Analysis.SobolevOrthogonalFrame
public import StationaryHarmonicMaps.Analysis.OrthogonalOperatorBounds

/-!
# Actual skewness of the original exponential flux

The original positive exponential weak gradient differentiates its actual
orthogonality. The same negative exponential raw map is its adjoint. These
facts produce the original flux's skew constraint in arbitrary genuine
matrix coordinates.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace StationaryHarmonicMaps.Analysis

private theorem conjugated_operator_skew {q : ℕ}
    (Q Z : Ambient q→L[ℝ]Ambient q) (hZ : star Z=-Z) :
    star (star Q*Z*Q)=-(star Q*Z*Q) := by
  rw [star_mul (star Q*Z) Q,star_mul (star Q) Z,star_star Q,hZ]
  apply ContinuousLinearMap.ext
  intro w
  change star Q ((-Z) (Q w))=-(star Q (Z (Q w)))
  rw [neg_apply,map_neg]

/-- The actual raw exponential flux is skew and belongs to the literal
coordinate kernel. Neither a differentiated constraint nor an inverse
exponential identity is assumed. -/
theorem skew_nativeMorrey_exp_raw_flux_skew
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (X : SkewMeanZeroNativeMorreySpace n q ((n : ℝ)-2+γ) e) :
    let ν := (n : ℝ)-2+γ
    let E := e.symm.toContinuousLinearMap
    let R := e.toContinuousLinearMap
    let hRE : ∀T,R (E T)=T := e.apply_symm_apply
    let hER : ∀z,E (R z)=z := e.symm_apply_apply
    let Zp := matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER X.val.val
    let Zm := matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER (-X.val.val)
    ∀(v : Domain n→Ambient (q*q)) (Dv : Domain n→Gradient n (q*q))
      (hv : MemW12 (ballDomain (0 : Domain n) 1) v Dv),
      nativeMorreyMapClass (n:=n) (q:=q*q) ν Zp=hv.2.1.toLp v →
      ∀(r : Domain n→Ambient (q*q))
        (hr : MemLp r 2 (volume.restrict (ball (0 : Domain n) 1))),
        nativeMorreyMapClass (n:=n) (q:=q*q) ν Zm=hr.toLp r →
        ∀Zt : Domain n→Gradient n (q*q),
          (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
            star (e (Zt x i))=-(e (Zt x i))) →
          let F := fun x i=>e.symm (e (r x)*e (Dv x i)+e (r x)*e (Zt x i)*e (v x))
          (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
            star (e (F x i))=-(e (F x i))) ∧
          (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
            skewMorreyCoordinateConstraint q e (F x i)=0) := by
  intro ν E R hRE hER Zp Zm v Dv hv hVMap r hr hRMap Zt hZt F
  have hVSO := skew_nativeMorrey_exp_raw_specialOrthogonal n hn γ hγ hγTwo q e X v Dv hv hVMap
  have hVorth : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (v x))*R (v x)=1 :=
    hVSO.mono fun _ hx=>hx.1
  have hVBound : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖v x‖≤‖E‖ := by
    filter_upwards [hVSO] with x hx
    calc
      ‖v x‖=‖E (e (v x))‖ := (congrArg (fun z : Ambient (q*q)=>‖z‖) (e.symm_apply_apply (v x))).symm
      _≤‖E‖*‖e (v x)‖ := E.le_opNorm _
      _≤‖E‖*1 := mul_le_mul_of_nonneg_left (orthogonal_opNorm_le_one (e (v x)) hx.1) (norm_nonneg E)
      _=‖E‖ := mul_one _
  have hDerivative := ae_orthogonal_frame_derivative hv.to_memW12Loc R ‖E‖ hVBound hVorth
  have hInverse := skew_nativeMorrey_exp_neg_ae_eq_star n hn γ hγ hγTwo q e X
  have hRawInverse : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),e (r x)=star (e (v x)) := by
    filter_upwards [hInverse,hv.2.1.coeFn_toLp,hr.coeFn_toLp] with x hx hvx hrx
    have hV : (nativeMorreyMapClass (n:=n) (q:=q*q) ν Zp).val x=v x :=
      (congrArg (fun U : MapUnitBallL2 n (q*q)=>U.val x) hVMap).trans hvx
    have hR : (nativeMorreyMapClass (n:=n) (q:=q*q) ν Zm).val x=r x :=
      (congrArg (fun U : MapUnitBallL2 n (q*q)=>U.val x) hRMap).trans hrx
    exact (congrArg e hR).symm.trans (hx.trans (congrArg (fun z : Ambient (q*q)=>star (e z)) hV))
  have hPhysical : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
      star (e (r x)*e (Dv x i)+e (r x)*e (Zt x i)*e (v x))=
        -(e (r x)*e (Dv x i)+e (r x)*e (Zt x i)*e (v x)) := by
    filter_upwards [hDerivative,hRawInverse,hZt] with x hxD hxInv hxZ
    intro i
    have hFirst : star (star (e (v x))*e (Dv x i))=-(star (e (v x))*e (Dv x i)) := by
      rw [star_mul (star (e (v x))) (e (Dv x i)),star_star]
      exact eq_neg_of_add_eq_zero_left (hxD i)
    have hSecond := conjugated_operator_skew (e (v x)) (e (Zt x i)) (hxZ i)
    rw [hxInv]
    change ContinuousLinearMap.adjoint
      (star (e (v x))*e (Dv x i)+star (e (v x))*e (Zt x i)*e (v x))=_
    rw [map_add]
    change star (star (e (v x))*e (Dv x i))+star (star (e (v x))*e (Zt x i)*e (v x))=_
    rw [hFirst,hSecond]
    abel
  have hSkew : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
      star (e (F x i))=-(e (F x i)) := by
    filter_upwards [hPhysical] with x hx
    intro i
    exact (congrArg (fun T : Ambient q→L[ℝ]Ambient q=>star T=-T)
      (e.apply_symm_apply (e (r x)*e (Dv x i)+e (r x)*e (Zt x i)*e (v x)))).mpr (hx i)
  refine ⟨hSkew,?_⟩
  filter_upwards [hSkew] with x hx
  intro i
  exact (skewMorreyCoordinateConstraint_eq_zero_iff q e (F x i)).mpr (hx i)

end StationaryHarmonicMaps.Analysis

end
