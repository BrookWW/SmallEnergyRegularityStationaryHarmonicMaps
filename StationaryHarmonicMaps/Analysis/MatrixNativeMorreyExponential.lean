module

public import StationaryHarmonicMaps.Analysis.MatrixNativeMorreyAlgebra
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Analytic.Composition
import HarmonicMaps.Analysis.SobolevAECongruence

/-!
# Actual matrix exponential in the intrinsic native Banach space

Left multiplication acts on the original complete native carrier. Its
Banach operator exponential applied to the literal matrix unit is the
pointwise matrix exponential, and has strict derivative the identity at0.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped ENNReal Topology Nat

noncomputable section

namespace StationaryHarmonicMaps.Analysis

private theorem operator_pow_succ_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V→L[ℝ]V) (k : ℕ) (e : V) : (L^(k+1)) e=L ((L^k) e) := by
  rw [pow_succ']
  rfl

private theorem operator_exp_zero_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (e : V) : (NormedSpace.exp (0 : V→L[ℝ]V)) e=e := by
  rw [NormedSpace.exp_zero]
  rfl

private theorem operator_exp_linear_hasStrictFDerivAt_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (M : V→L[ℝ](V→L[ℝ]V)) (e : V) :
    HasStrictFDerivAt (fun U : V=>(NormedSpace.exp (M U)) e)
      ((ContinuousLinearMap.apply ℝ V e).comp M) 0 := by
  have hExpAt : HasStrictFDerivAt NormedSpace.exp
      (1 : (V→L[ℝ]V)→L[ℝ](V→L[ℝ]V)) (M 0) := by
    rw [map_zero]
    exact hasStrictFDerivAt_exp_zero (𝕂:=ℝ) (𝔸:=V→L[ℝ]V)
  have hExp := hExpAt.comp (0 : V) (M.hasStrictFDerivAt (x:=0))
  have h := (ContinuousLinearMap.apply ℝ V e).hasStrictFDerivAt.comp (0 : V) hExp
  have hD : (ContinuousLinearMap.apply ℝ V e).comp
      ((1 : (V→L[ℝ]V)→L[ℝ](V→L[ℝ]V)).comp M)=
      (ContinuousLinearMap.apply ℝ V e).comp M := by
    apply ContinuousLinearMap.ext
    intro U
    rfl
  rw [hD] at h
  exact h

private theorem operator_exp_evaluation_of_pow
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedRing W] [NormedAlgebra ℝ W] [CompleteSpace W]
    (L : V→L[ℝ]V) (e : V) (ev : V→L[ℝ]W) (a : W)
    (hPow : ∀k : ℕ,ev ((L^k) e)=a^k) :
    ev ((NormedSpace.exp L) e)=NormedSpace.exp a := by
  let A : (V→L[ℝ]V)→L[ℝ]V := ContinuousLinearMap.apply ℝ V e
  have hOperator : HasSum (fun k : ℕ=>(k !⁻¹ : ℝ) • L^k) (NormedSpace.exp L) :=
    NormedSpace.exp_series_hasSum_exp' L
  have hRaw : HasSum (fun k : ℕ=>ev (A ((k !⁻¹ : ℝ) • L^k)))
      (ev (A (NormedSpace.exp L))) := (hOperator.mapL A).mapL ev
  have hTerm (k : ℕ) : ev (A ((k !⁻¹ : ℝ) • L^k))=(k !⁻¹ : ℝ) • a^k := by
    calc
      _=ev ((k !⁻¹ : ℝ) • A (L^k)) := congrArg ev (A.map_smul (k !⁻¹ : ℝ) (L^k))
      _=(k !⁻¹ : ℝ) • ev (A (L^k)) := ev.map_smul (k !⁻¹ : ℝ) (A (L^k))
      _=_ := congrArg (fun z : W=>(k !⁻¹ : ℝ) • z) (hPow k)
  have hFn : (fun k : ℕ=>ev (A ((k !⁻¹ : ℝ) • L^k)))=
      (fun k : ℕ=>(k !⁻¹ : ℝ) • a^k) := funext hTerm
  rw [hFn] at hRaw
  exact hRaw.unique (NormedSpace.exp_series_hasSum_exp' (𝕂:=ℝ) a)

theorem matrixNativeMorreyEvaluation_leftMul_pow
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T)
    (X : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ))
    (x : closedBall (0 : Domain n) 1) (k : ℕ) :
    matrixNativeMorreyEvaluation n hn γ hγ hγTwo q R x
      (((matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R X)^k)
        (matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E))=
      (matrixNativeMorreyEvaluation n hn γ hγ hγTwo q R x X)^k := by
  let S := NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)
  let L : S→L[ℝ]S := matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R X
  let ev : S→L[ℝ](Ambient q→L[ℝ]Ambient q) := matrixNativeMorreyEvaluation n hn γ hγ hγTwo q R x
  let e : S := matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E
  let a : Ambient q→L[ℝ]Ambient q := ev X
  have he : ev e=1 := matrixNativeMorreyEvaluation_unit n hn γ hγ hγTwo q E R hRE x
  have hL (U : S) : ev (L U)=a*ev U :=
    matrixNativeMorreyEvaluation_mul n hn γ hγ hγTwo q E R hRE X U x
  change ev ((L^k) e)=a^k
  clear_value L ev e a
  induction k with
  | zero =>
      simpa only [pow_zero,one_apply_eq_self] using he
  | succ k hk =>
      calc
        ev ((L^(k+1)) e)=ev (L ((L^k) e)) := congrArg ev (operator_pow_succ_apply L k e)
        _=a*ev ((L^k) e) := hL _
        _=a*a^k := congrArg (fun z : Ambient q→L[ℝ]Ambient q=>a*z) hk
        _=a^(k+1) := (pow_succ' a k).symm

/-- The actual matrix exponential, using the native Banach operator algebra.
The encoder and decoder are required to be genuine two-sided inverses. -/
@[expose] def matrixNativeMorreyExp
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (_hRE : ∀T,R (E T)=T) (_hER : ∀z,E (R z)=z)
    (X : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)) :
    NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ) :=
  (NormedSpace.exp (matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R X))
    (matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E)

/-- Evaluation of the native exponential is the original matrix exponential. -/
theorem matrixNativeMorreyExp_evaluation
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (X : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ))
    (x : closedBall (0 : Domain n) 1) :
    matrixNativeMorreyEvaluation n hn γ hγ hγTwo q R x
      (matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER X)=
      NormedSpace.exp (matrixNativeMorreyEvaluation n hn γ hγ hγTwo q R x X) := by
  exact operator_exp_evaluation_of_pow
    (matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R X)
    (matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E)
    (matrixNativeMorreyEvaluation n hn γ hγ hγTwo q R x)
    (matrixNativeMorreyEvaluation n hn γ hγ hγTwo q R x X)
    (matrixNativeMorreyEvaluation_leftMul_pow n hn γ hγ hγTwo q E R hRE X x)

/-- The full coefficient value is the encoded original matrix exponential
at every closed-ball point. -/
theorem matrixNativeMorreyExp_point
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (X : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ))
    (x : closedBall (0 : Domain n) 1) :
    nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo
      (matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER X) x=
      E (NormedSpace.exp (R (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo X x))) := by
  have h := congrArg E (matrixNativeMorreyExp_evaluation n hn γ hγ hγTwo q E R hRE hER X x)
  simpa only [matrixNativeMorreyEvaluation,nativeMorreyEvaluation_apply,
    ContinuousLinearMap.comp_apply,hER] using h

/-- The original AE map class is the literal encoded matrix exponential. -/
theorem matrixNativeMorreyExp_ae
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (X : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)) :
    ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q*q) ((n : ℝ)-2+γ)
        (matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER X)).val x=
        E (NormedSpace.exp (R ((nativeMorreyMapClass (n:=n) (q:=q*q) ((n : ℝ)-2+γ) X).val x))) := by
  filter_upwards [nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo X,
    nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo
      (matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER X),
    ae_restrict_mem measurableSet_ball] with x hx hExp hxBall
  calc
    _=nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo
        (matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER X) ⟨x,ball_subset_closedBall hxBall⟩ :=
      (hExp hxBall).symm
    _=E (NormedSpace.exp (R (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo X
        ⟨x,ball_subset_closedBall hxBall⟩))) :=
      matrixNativeMorreyExp_point n hn γ hγ hγTwo q E R hRE hER X _
    _=_ := congrArg (fun z : Ambient (q*q)=>E (NormedSpace.exp (R z))) (hx hxBall)

/-- The full original AE matrix exponential uniquely determines its native
class, including the weak gradient. -/
theorem matrixNativeMorreyExp_eq_iff
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (X Z : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)) :
    Z=matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER X ↔
      ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
        (nativeMorreyMapClass (n:=n) (q:=q*q) ((n : ℝ)-2+γ) Z).val x=
          E (NormedSpace.exp (R ((nativeMorreyMapClass (n:=n) (q:=q*q) ((n : ℝ)-2+γ) X).val x))) := by
  constructor
  · intro hZ
    rw [hZ]
    exact matrixNativeMorreyExp_ae n hn γ hγ hγTwo q E R hRE hER X
  · intro hZ
    apply nativeMorreyMapClass_injective (n:=n) (q:=q*q) ((n : ℝ)-2+γ)
    apply Lp.ext
    filter_upwards [hZ,matrixNativeMorreyExp_ae n hn γ hγ hγTwo q E R hRE hER X] with x hz hx
    exact hz.trans hx.symm

theorem matrixNativeMorreyExp_zero
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z) :
    matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER 0=
      matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E := by
  let S := NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)
  let M : S→L[ℝ](S→L[ℝ]S) := matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R
  let e : S := matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E
  have hM0 : M 0=(0 : S→L[ℝ]S) := M.map_zero
  change (NormedSpace.exp (M 0)) e=e
  calc
    _=(NormedSpace.exp (0 : S→L[ℝ]S)) e :=
      congrArg (fun T : S→L[ℝ]S=>(NormedSpace.exp T) e) hM0
    _=e := operator_exp_zero_apply e

/-- Analyticity is with respect to the original complete native norm. -/
theorem matrixNativeMorreyExp_analytic
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (X : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)) :
    AnalyticAt ℝ (matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER) X := by
  let S := NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)
  let M : S→L[ℝ](S→L[ℝ]S) := matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R
  let A : (S→L[ℝ]S)→L[ℝ]S :=
    ContinuousLinearMap.apply ℝ S (matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E)
  have hInner : AnalyticAt ℝ (fun U : S=>NormedSpace.exp (M U)) X :=
    (NormedSpace.exp_analytic (𝕂:=ℝ) (M X)).comp (f:=fun U : S=>M U) (M.analyticAt X)
  exact (A.analyticAt (NormedSpace.exp (M X))).comp
    (f:=fun U : S=>NormedSpace.exp (M U)) hInner

/-- The native exponential has actual strict Fréchet derivative the identity
at zero, since left multiplication sends the actual unit to the original class. -/
theorem matrixNativeMorreyExp_hasStrictFDerivAt_zero
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z) :
    HasStrictFDerivAt (matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER)
      (1 : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)→L[ℝ]
        NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)) 0 := by
  let S := NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)
  let M : S→L[ℝ](S→L[ℝ]S) := matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R
  let A : (S→L[ℝ]S)→L[ℝ]S :=
    ContinuousLinearMap.apply ℝ S (matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E)
  have hA := operator_exp_linear_hasStrictFDerivAt_zero M
    (matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E)
  have hDerivative : A.comp M=(1 : S→L[ℝ]S) := by
    apply ContinuousLinearMap.ext
    intro U
    exact matrixNativeMorreyMultiplication_unit_right n hn γ hγ hγTwo q E R hRE hER U
  rw [hDerivative] at hA
  exact hA

/-- The literal original pointwise matrix exponential has the native weak
graph selected by the Banach construction, with its full original growth. -/
theorem matrixNativeMorreyExp_raw_native
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (u : Domain n→Ambient (q*q)) (Du : Domain n→Gradient n (q*q))
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (X : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ))
    (hX : nativeMorreyMapClass (n:=n) (q:=q*q) ((n : ℝ)-2+γ) X=hu.2.1.toLp u) :
    let ν := (n : ℝ)-2+γ
    let Z := matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER X
    let W := fun x=>E (NormedSpace.exp (R (u x)))
    ∃(DW : Domain n→Gradient n (q*q)) (hW : MemW12 (ballDomain (0 : Domain n) 1) W DW),
      nativeMorreyMapClass (n:=n) (q:=q*q) ν Z=hW.2.1.toLp W ∧
      nativeMorreyHSClass (n:=n) (q:=q*q) ν Z=hsUnitBallL2Class DW hW.2.2 ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (DW x))≤
          ‖nativeMorreyGradientClass (n:=n) (q:=q*q) ν Z‖^2*r^ν := by
  intro ν Z W
  have hData : ∃(v : Domain n→Ambient (q*q)) (Dv : Domain n→Gradient n (q*q))
      (hv : MemW12 (ballDomain (0 : Domain n) 1) v Dv),
      nativeMorreyMapClass (n:=n) (q:=q*q) ν Z=hv.2.1.toLp v ∧
      nativeMorreyHSClass (n:=n) (q:=q*q) ν Z=hsUnitBallL2Class Dv hv.2.2 ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dv x))≤
          ‖nativeMorreyGradientClass (n:=n) (q:=q*q) ν Z‖^2*r^ν :=
    exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=q*q) ν Z
  obtain ⟨v,Dv,hv,hVMap,hVGrad,hGrowth⟩ := hData
  have hRepU : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀hx : x∈ball (0 : Domain n) 1,
      nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo X ⟨x,ball_subset_closedBall hx⟩=u x := by
    filter_upwards [nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo X,
      hu.2.1.coeFn_toLp] with x hx hux
    intro hxBall
    exact (hx hxBall).trans ((congrArg (fun U : MapUnitBallL2 n (q*q)=>U.val x) hX).trans hux)
  have hRepV : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀hx : x∈ball (0 : Domain n) 1,
      nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo Z ⟨x,ball_subset_closedBall hx⟩=v x := by
    filter_upwards [nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo Z,
      hv.2.1.coeFn_toLp] with x hx hvx
    intro hxBall
    exact (hx hxBall).trans ((congrArg (fun U : MapUnitBallL2 n (q*q)=>U.val x) hVMap).trans hvx)
  have hAE : v=ᵐ[volume.restrict (ball (0 : Domain n) 1)]W := by
    filter_upwards [hRepU,hRepV,ae_restrict_mem measurableSet_ball] with x hxU hxV hxBall
    calc
      v x=nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo Z ⟨x,ball_subset_closedBall hxBall⟩ :=
        (hxV hxBall).symm
      _=E (NormedSpace.exp (R (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo X
          ⟨x,ball_subset_closedBall hxBall⟩))) :=
        matrixNativeMorreyExp_point n hn γ hγ hγTwo q E R hRE hER X _
      _=W x := congrArg (fun z : Ambient (q*q)=>E (NormedSpace.exp (R z))) (hxU hxBall)
  have hW : MemW12 (ballDomain (0 : Domain n) 1) W Dv := hv.congr_ae hAE (EventuallyEq.refl _ _)
  have hMap : nativeMorreyMapClass (n:=n) (q:=q*q) ν Z=hW.2.1.toLp W :=
    hVMap.trans ((MemLp.toLp_eq_toLp_iff hv.2.1 hW.2.1).mpr hAE)
  exact ⟨Dv,hW,hMap,hVGrad,hGrowth⟩

end StationaryHarmonicMaps.Analysis

end
