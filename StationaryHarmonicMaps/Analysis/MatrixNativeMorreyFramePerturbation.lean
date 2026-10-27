module

public import StationaryHarmonicMaps.Analysis.MatrixNativeMorreyInverseExponential
import Mathlib.Tactic.NoncommRing

/-!
# Actual right exponential perturbations of native frames

The same original frame and exponential native graphs give the literal
right product and its two-term weak gradient. Its transformed original
connection is the actual exponential flux with the original matrix order.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace StationaryHarmonicMaps.Analysis

/-- The original transformed connection under a right frame product. -/
theorem matrix_right_frame_gauged_connection_identity {q : ℕ}
    (P DP Q DQ A : Ambient q→L[ℝ]Ambient q) (hP : star P*P=1) :
    star (P*Q)*(DP*Q+P*DQ)+star (P*Q)*A*(P*Q)=
      star Q*DQ+star Q*(star P*DP+star P*A*P)*Q := by
  calc
    _=star Q*(star P*DP)*Q+star Q*(star P*P)*DQ+star Q*(star P*A*P)*Q := by
      rw [star_mul P Q]
      noncomm_ring
    _=star Q*(star P*DP)*Q+star Q*DQ+star Q*(star P*A*P)*Q := by rw [hP,mul_one]
    _=_ := by noncomm_ring

private theorem product_specialOrthogonal {q : ℕ}
    (P Q : Ambient q→L[ℝ]Ambient q)
    (hP : star P*P=1) (hQ : star Q*Q=1) (hPD : P.det=1) (hQD : Q.det=1) :
    star (P*Q)*(P*Q)=1 ∧ (P*Q).det=1 := by
  constructor
  · calc
      _=star Q*(star P*P)*Q := by rw [star_mul P Q];noncomm_ring
      _=1 := by rw [hP,mul_one,hQ]
  · change LinearMap.det (P.toLinearMap*Q.toLinearMap)=1
    rw [map_mul]
    change P.det*Q.det=1
    rw [hPD,hQD,mul_one]

/-- The actual right exponential product is a native SO frame, with its
original two-term weak gradient and its original transformed connection. -/
theorem nativeMorrey_right_exp_frame_perturbation
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q))
    (hp : MemW12 (ballDomain (0 : Domain n) 1) p Dp)
    (P : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ))
    (hPMap : nativeMorreyMapClass (n:=n) (q:=q*q) ((n : ℝ)-2+γ) P=hp.2.1.toLp p)
    (hPSO : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (e (p x))*e (p x)=1 ∧ (e (p x)).det=1)
    (X : SkewMeanZeroNativeMorreySpace n q ((n : ℝ)-2+γ) e)
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q)) (t : ℝ) :
    let ν := (n : ℝ)-2+γ
    let E := e.symm.toContinuousLinearMap
    let R := e.toContinuousLinearMap
    let hRE : ∀T,R (E T)=T := e.apply_symm_apply
    let hER : ∀z,E (R z)=z := e.symm_apply_apply
    let Zp := matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER X.val.val
    let Zm := matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER (-X.val.val)
    ∃(v : Domain n→Ambient (q*q)) (Dv : Domain n→Gradient n (q*q))
      (hv : MemW12 (ballDomain (0 : Domain n) 1) v Dv)
      (r : Domain n→Ambient (q*q)) (Dr : Domain n→Gradient n (q*q))
      (hr : MemW12 (ballDomain (0 : Domain n) 1) r Dr),
      nativeMorreyMapClass (n:=n) (q:=q*q) ν Zp=hv.2.1.toLp v ∧
      nativeMorreyHSClass (n:=n) (q:=q*q) ν Zp=hsUnitBallL2Class Dv hv.2.2 ∧
      nativeMorreyMapClass (n:=n) (q:=q*q) ν Zm=hr.2.1.toLp r ∧
      nativeMorreyHSClass (n:=n) (q:=q*q) ν Zm=hsUnitBallL2Class Dr hr.2.2 ∧
      let B := matrixMorreyCoefficientProduct E R
      let W := fun x=>B (p x) (v x)
      let DW := fun x i=>B (Dp x i) (v x)+B (p x) (Dv x i)
      let Y := matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R P Zp
      ∃hW : MemW12 (ballDomain (0 : Domain n) 1) W DW,
        nativeMorreyMapClass (n:=n) (q:=q*q) ν Y=hW.2.1.toLp W ∧
        nativeMorreyHSClass (n:=n) (q:=q*q) ν Y=hsUnitBallL2Class DW hW.2.2 ∧
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (e (W x))*e (W x)=1 ∧ (e (W x)).det=1) ∧
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
          star (e (W x))*e (DW x i)+star (e (W x))*(t • A x i)*e (W x)=
            e (r x)*e (Dv x i)+e (r x)*(star (e (p x))*e (Dp x i)+
              star (e (p x))*(t • A x i)*e (p x))*e (v x)) := by
  intro ν E R hRE hER Zp Zm
  have hPos : ∃(v : Domain n→Ambient (q*q)) (Dv : Domain n→Gradient n (q*q))
      (hv : MemW12 (ballDomain (0 : Domain n) 1) v Dv),
      nativeMorreyMapClass (n:=n) (q:=q*q) ν Zp=hv.2.1.toLp v ∧
      nativeMorreyHSClass (n:=n) (q:=q*q) ν Zp=hsUnitBallL2Class Dv hv.2.2 ∧
      ∀a∈ball (0 : Domain n) 1,∀s : ℝ,0<s →
        (∫x in ball a s∩ball (0 : Domain n) 1,hsNormSq (Dv x))≤
          ‖nativeMorreyGradientClass (n:=n) (q:=q*q) ν Zp‖^2*s^ν :=
    exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=q*q) ν Zp
  obtain ⟨v,Dv,hv,hVMap,hVGrad,_hVGrowth⟩ := hPos
  have hNeg : ∃(r : Domain n→Ambient (q*q)) (Dr : Domain n→Gradient n (q*q))
      (hr : MemW12 (ballDomain (0 : Domain n) 1) r Dr),
      nativeMorreyMapClass (n:=n) (q:=q*q) ν Zm=hr.2.1.toLp r ∧
      nativeMorreyHSClass (n:=n) (q:=q*q) ν Zm=hsUnitBallL2Class Dr hr.2.2 ∧
      ∀a∈ball (0 : Domain n) 1,∀s : ℝ,0<s →
        (∫x in ball a s∩ball (0 : Domain n) 1,hsNormSq (Dr x))≤
          ‖nativeMorreyGradientClass (n:=n) (q:=q*q) ν Zm‖^2*s^ν :=
    exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=q*q) ν Zm
  obtain ⟨r,Dr,hr,hRMap,hRGrad,_hRGrowth⟩ := hNeg
  refine ⟨v,Dv,hv,r,Dr,hr,hVMap,hVGrad,hRMap,hRGrad,?_⟩
  let B := matrixMorreyCoefficientProduct E R
  let W := fun x=>B (p x) (v x)
  let DW := fun x i=>B (Dp x i) (v x)+B (p x) (Dv x i)
  let Y := matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R P Zp
  have hProduct : ∃hW : MemW12 (ballDomain (0 : Domain n) 1) W DW,
      nativeMorreyMapClass (n:=n) (q:=q*q) ν Y=hW.2.1.toLp W ∧
      nativeMorreyHSClass (n:=n) (q:=q*q) ν Y=hsUnitBallL2Class DW hW.2.2 :=
    nativeMorreyBilinearProduct_raw_leibniz (m:=q*q) (k:=q*q) (q:=q*q)
      n hn γ hγ hγTwo B p Dp hp P hPMap v Dv hv Zp hVMap
  obtain ⟨hW,hWMap,hWGrad⟩ := hProduct
  have hValue (x : Domain n) : e (W x)=e (p x)*e (v x) := e.apply_symm_apply _
  have hGradient (x : Domain n) (i : Fin n) : e (DW x i)=e (Dp x i)*e (v x)+e (p x)*e (Dv x i) :=
    (e.map_add _ _).trans (congrArg₂ (fun T U : Ambient q→L[ℝ]Ambient q=>T+U)
      (e.apply_symm_apply _) (e.apply_symm_apply _))
  have hVSO := skew_nativeMorrey_exp_raw_specialOrthogonal n hn γ hγ hγTwo q e X v Dv hv hVMap
  have hInv := skew_nativeMorrey_exp_neg_raw_eq_star n hn γ hγ hγTwo q e X v Dv hv hVMap r Dr hr hRMap
  refine ⟨hW,hWMap,hWGrad,?_,?_⟩
  · filter_upwards [hPSO,hVSO] with x hxP hxV
    have H := product_specialOrthogonal (e (p x)) (e (v x)) hxP.1 hxV.1 hxP.2 hxV.2
    exact (congrArg (fun T : Ambient q→L[ℝ]Ambient q=>star T*T=1 ∧ T.det=1) (hValue x)).mpr H
  · filter_upwards [hPSO,hInv] with x hxP hxInv
    intro i
    rw [hValue,hGradient,hxInv]
    exact matrix_right_frame_gauged_connection_identity (e (p x)) (e (Dp x i))
      (e (v x)) (e (Dv x i)) (t • A x i) hxP.1

end StationaryHarmonicMaps.Analysis

end
