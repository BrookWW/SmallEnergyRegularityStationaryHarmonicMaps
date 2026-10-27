module

public import StationaryHarmonicMaps.Analysis.NativeMorreyCoefficientActionExistence
public import StationaryHarmonicMaps.Analysis.MatrixNativeMorreyExponential
import StationaryHarmonicMaps.Analysis.HilbertSchmidtDecoding
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The actual native matrix Coulomb flux

The coefficient actions use their complete original-representative
characteristic. The matrix exponential is the actual native exponential,
and the gradient is the original native graph projection.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

noncomputable section

namespace StationaryHarmonicMaps.Analysis

private def selectedAction
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ : ℝ) {k m q : ℕ} (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient q)) :
    NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)→L[ℝ]
      MorreyCoefficientSpace n m σ→L[ℝ]MorreyCoefficientSpace n q σ :=
  ((exists_uniform_unique_native_morrey_coefficient_action n hn γ hγ hγTwo).choose_spec.2 σ k m q B).choose

private theorem selectedAction_raw
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ : ℝ) {k m q : ℕ} (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) (F : MorreyCoefficientSpace n m σ)
    (u : Domain n→Ambient k) (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hU : nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X=hu.toLp u)
    (Fr : Domain n→Gradient n m)
    (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hF : morreyCoefficientRecover (n:=n) (q:=m) σ F=hsUnitBallL2Class Fr hFr) :
    ∃hP : ∀i,MemLp (fun x=>B (u x) (Fr x i)) 2 (volume.restrict (ball (0 : Domain n) 1)),
      morreyCoefficientRecover (n:=n) (q:=q) σ (selectedAction n hn γ hγ hγTwo σ B X F)=
        hsUnitBallL2Class (fun x i=>B (u x) (Fr x i)) hP :=
  ((exists_uniform_unique_native_morrey_coefficient_action n hn γ hγ hγTwo).choose_spec.2 σ k m q B).choose_spec.1.2 X F u hu hU Fr hFr hF

private theorem coefficient_class_eq_of_raw_constant {n k m : ℕ} (σ : ℝ)
    (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient m)) (u : Domain n→Ambient k)
    (c : Ambient k) (hUnit : ∀(z : Ambient m),B c z=z)
    (hConstant : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),u x=c)
    (Fr : Domain n→Gradient n m)
    (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (F : MorreyCoefficientSpace n m σ)
    (hF : morreyCoefficientRecover (n:=n) (q:=m) σ F=hsUnitBallL2Class Fr hFr)
    (G : MorreyCoefficientSpace n m σ)
    (hProduct : ∃hP : ∀i,MemLp (fun x=>B (u x) (Fr x i)) 2 (volume.restrict (ball (0 : Domain n) 1)),
      morreyCoefficientRecover (n:=n) (q:=m) σ G=hsUnitBallL2Class (fun x i=>B (u x) (Fr x i)) hP) : G=F := by
  obtain ⟨hP,hClass⟩ := hProduct
  apply morreyCoefficientRecover_injective (n:=n) (q:=m) σ
  apply hClass.trans
  apply Eq.trans _ hF.symm
  apply (hsUnitBallL2Class_eq_iff_ae _ _ _ _).mpr
  intro i
  filter_upwards [hConstant] with x hx
  exact (congrArg (fun v : Ambient k=>B v (Fr x i)) hx).trans (hUnit (Fr x i))

private theorem selectedAction_constant_unit_apply
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ : ℝ) {k m : ℕ} (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient m))
    (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ))
    (c : Ambient k) (hUnit : ∀(z : Ambient m),B c z=z)
    (hConstant : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X).val x=c)
    (F : MorreyCoefficientSpace n m σ) :
    selectedAction (k:=k) (m:=m) (q:=m) n hn γ hγ hγTwo σ B X F=F := by
  let hFData := exists_raw_field_of_morreyCoefficient (n:=n) (q:=m) σ F
  let Fr : Domain n→Gradient n m := hFData.choose
  let hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)) := hFData.choose_spec.choose
  have hF : morreyCoefficientRecover (n:=n) (q:=m) σ F=hsUnitBallL2Class Fr hFr :=
    hFData.choose_spec.choose_spec.1
  let U := nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X
  have hu : MemLp (U : Domain n→Ambient k) 2 (volume.restrict (ball (0 : Domain n) 1)) := Lp.memLp U
  have hU : nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X=hu.toLp (U : Domain n→Ambient k) :=
    (Lp.toLp_coeFn U hu).symm
  exact coefficient_class_eq_of_raw_constant σ B U c hUnit hConstant Fr hFr F hF
    (selectedAction (k:=k) (m:=m) (q:=m) n hn γ hγ hγTwo σ B X F)
    (selectedAction_raw (k:=k) (m:=m) (q:=m) n hn γ hγ hγTwo σ B X F U hu hU Fr hFr hF)

private theorem selectedAction_constant_unit
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ : ℝ) {k m : ℕ} (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient m))
    (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ))
    (c : Ambient k) (hUnit : ∀(z : Ambient m),B c z=z)
    (hConstant : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X).val x=c) :
    selectedAction (k:=k) (m:=m) (q:=m) n hn γ hγ hγTwo σ B X=
      ContinuousLinearMap.id ℝ (MorreyCoefficientSpace n m σ) := by
  apply ContinuousLinearMap.ext
  intro F
  exact selectedAction_constant_unit_apply n hn γ hγ hγTwo σ B X c hUnit hConstant F

private abbrev mapValue {n q : ℕ} (ν : ℝ) (X : NativeMorreySobolevSpace n q ν) : Domain n→Ambient q :=
  nativeMorreyMapClass (n:=n) (q:=q) ν X

private abbrev coefficientValue {n q : ℕ} (ν : ℝ) (F : MorreyCoefficientSpace n q ν) : Domain n→Gradient n q :=
  fun x i=>WithLp.toLp 2 (fun j : Fin q=>morreyCoefficientRecover (n:=n) (q:=q) ν F x (finProdFinEquiv (i,j)))

private theorem coefficientValue_memLp {n q : ℕ} (ν : ℝ) (F : MorreyCoefficientSpace n q ν) (i : Fin n) :
    MemLp (fun x=>coefficientValue ν F x i) 2 (volume.restrict (ball (0 : Domain n) 1)) :=
  memLp_hs_unflatten (morreyCoefficientRecover (n:=n) (q:=q) ν F)
    (Lp.memLp (morreyCoefficientRecover (n:=n) (q:=q) ν F)) i

private theorem coefficientValue_class {n q : ℕ} (ν : ℝ) (F : MorreyCoefficientSpace n q ν) :
    morreyCoefficientRecover (n:=n) (q:=q) ν F=
      hsUnitBallL2Class (coefficientValue ν F) (coefficientValue_memLp ν F) := by
  symm
  apply Lp.ext
  exact (hsUnitBallL2Class_ae (coefficientValue ν F) (coefficientValue_memLp ν F)).trans
    (Eventually.of_forall fun x=>hs_flatten_unflatten (morreyCoefficientRecover (n:=n) (q:=q) ν F x))

private theorem coefficientValue_of_raw {n q : ℕ} (ν : ℝ) (Fr : Domain n→Gradient n q)
    (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (F : MorreyCoefficientSpace n q ν)
    (hF : morreyCoefficientRecover (n:=n) (q:=q) ν F=hsUnitBallL2Class Fr hFr) :
    coefficientValue ν F=ᵐ[volume.restrict (ball (0 : Domain n) 1)]Fr := by
  have hAE : (morreyCoefficientRecover (n:=n) (q:=q) ν F : Domain n→Ambient (n*q))=ᵐ[
      volume.restrict (ball (0 : Domain n) 1)]hsFlatten Fr := by
    rw [hF]
    exact hsUnitBallL2Class_ae Fr hFr
  filter_upwards [hAE] with x hx
  have hDecode := congrArg (fun v : Ambient (n*q)=>fun i : Fin n=>
    WithLp.toLp 2 (fun j : Fin q=>v (finProdFinEquiv (i,j)))) hx
  exact hDecode.trans (hs_unflatten_flatten (Fr x))

private theorem coefficientValue_add {n q : ℕ} (ν : ℝ) (F G : MorreyCoefficientSpace n q ν) :
    coefficientValue ν (F+G)=ᵐ[volume.restrict (ball (0 : Domain n) 1)]
      (fun x i=>coefficientValue ν F x i+coefficientValue ν G x i) :=
  coefficientValue_of_raw ν _ (fun i=>(coefficientValue_memLp ν F i).add (coefficientValue_memLp ν G i))
    (F+G) (morreyCoefficientRecover_add_raw ν (coefficientValue ν F) (coefficientValue ν G)
      (coefficientValue_memLp ν F) (coefficientValue_memLp ν G) F G (coefficientValue_class ν F) (coefficientValue_class ν G))

private theorem coefficientValue_smul {n q : ℕ} (ν c : ℝ) (F : MorreyCoefficientSpace n q ν) :
    coefficientValue ν (c • F)=ᵐ[volume.restrict (ball (0 : Domain n) 1)]
      (fun x i=>c • coefficientValue ν F x i) :=
  coefficientValue_of_raw ν _ (fun i=>(coefficientValue_memLp ν F i).const_smul c) (c • F)
    (morreyCoefficientRecover_smul_raw ν c (coefficientValue ν F) (coefficientValue_memLp ν F) F (coefficientValue_class ν F))

private theorem coefficientValue_sub {n q : ℕ} (ν : ℝ) (F G : MorreyCoefficientSpace n q ν) :
    coefficientValue ν (F-G)=ᵐ[volume.restrict (ball (0 : Domain n) 1)]
      (fun x i=>coefficientValue ν F x i-coefficientValue ν G x i) := by
  have hAdd := coefficientValue_add ν F ((-1 : ℝ) • G)
  have hScale := coefficientValue_smul ν (-1) G
  have hExpr : F-G=F+(-1 : ℝ) • G := by rw [neg_one_smul,sub_eq_add_neg]
  rw [hExpr]
  filter_upwards [hAdd,hScale] with x hx hy
  funext i
  rw [congrFun hx i,congrFun hy i,neg_one_smul,sub_eq_add_neg]

private theorem coefficient_recover_of_ae {n q : ℕ} (ν : ℝ) (F : MorreyCoefficientSpace n q ν)
    (Fr : Domain n→Gradient n q)
    (hAE : coefficientValue ν F=ᵐ[volume.restrict (ball (0 : Domain n) 1)]Fr) :
    ∃hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)),
      morreyCoefficientRecover (n:=n) (q:=q) ν F=hsUnitBallL2Class Fr hFr := by
  have hFr (i : Fin n) : MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)) :=
    (coefficientValue_memLp ν F i).ae_eq (hAE.mono fun x hx=>congrFun hx i)
  exact ⟨hFr,(coefficientValue_class ν F).trans
    ((hsUnitBallL2Class_eq_iff_ae _ _ _ _).mpr fun i=>hAE.mono fun x hx=>congrFun hx i)⟩

private theorem coefficientValue_injective_ae {n q : ℕ} (ν : ℝ) (F G : MorreyCoefficientSpace n q ν)
    (hAE : coefficientValue ν F=ᵐ[volume.restrict (ball (0 : Domain n) 1)]coefficientValue ν G) : F=G := by
  apply morreyCoefficientRecover_injective (n:=n) (q:=q) ν
  exact (coefficientValue_class ν F).trans (((hsUnitBallL2Class_eq_iff_ae _ _ _ _).mpr
    (fun i=>hAE.mono fun x hx=>congrFun hx i)).trans (coefficientValue_class ν G).symm)

private theorem selectedAction_value_ae
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ : ℝ) {k m q : ℕ} (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) (F : MorreyCoefficientSpace n m σ) :
    coefficientValue σ (selectedAction (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X F)=ᵐ[
      volume.restrict (ball (0 : Domain n) 1)]
      (fun x i=>B (mapValue ((n : ℝ)-2+γ) X x) (coefficientValue σ F x i)) := by
  let U := nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X
  have hu : MemLp (U : Domain n→Ambient k) 2 (volume.restrict (ball (0 : Domain n) 1)) := Lp.memLp U
  have hU : nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X=hu.toLp (U : Domain n→Ambient k) :=
    (Lp.toLp_coeFn U hu).symm
  exact (selectedAction_raw n hn γ hγ hγTwo σ B X F U hu hU
    (coefficientValue σ F) (coefficientValue_memLp σ F) (coefficientValue_class σ F)).elim
      (fun hP hProduct=>coefficientValue_of_raw σ _ hP _ hProduct)

private theorem affine_coefficient_raw {n q : ℕ} (ν t : ℝ)
    (Z Y : MorreyCoefficientSpace n q ν) (Zr Yr : Domain n→Gradient n q)
    (hZr : ∀i,MemLp (fun x=>Zr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hYr : ∀i,MemLp (fun x=>Yr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hZ : morreyCoefficientRecover (n:=n) (q:=q) ν Z=hsUnitBallL2Class Zr hZr)
    (hY : morreyCoefficientRecover (n:=n) (q:=q) ν Y=hsUnitBallL2Class Yr hYr) :
    morreyCoefficientRecover (n:=n) (q:=q) ν (Z+t • Y)=
      hsUnitBallL2Class (fun x i=>Zr x i+t • Yr x i) (fun i=>(hZr i).add ((hYr i).const_smul t)) :=
  morreyCoefficientRecover_add_raw ν Zr (fun x i=>t • Yr x i) hZr
    (fun i=>(hYr i).const_smul t) Z (t • Y) hZ (morreyCoefficientRecover_smul_raw ν t Yr hYr Y hY)


private theorem coefficientValue_affine {n q : ℕ} (ν t : ℝ) (Z Y : MorreyCoefficientSpace n q ν) :
    coefficientValue ν (Z+t • Y)=ᵐ[volume.restrict (ball (0 : Domain n) 1)]
      (fun x i=>coefficientValue ν Z x i+t • coefficientValue ν Y x i) :=
  coefficientValue_of_raw ν _ (fun i=>(coefficientValue_memLp ν Z i).add ((coefficientValue_memLp ν Y i).const_smul t))
    (Z+t • Y) (affine_coefficient_raw ν t Z Y (coefficientValue ν Z) (coefficientValue ν Y)
      (coefficientValue_memLp ν Z) (coefficientValue_memLp ν Y) (coefficientValue_class ν Z) (coefficientValue_class ν Y))

private theorem action_flux_ae
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (B : Ambient q→L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    let ν := (n : ℝ)-2+γ
    let L : NativeMorreySobolevSpace n q ν→L[ℝ]MorreyCoefficientSpace n q ν→L[ℝ]MorreyCoefficientSpace n q ν :=
      selectedAction (k:=q) (m:=q) (q:=q) n hn γ hγ hγTwo ν B
    let R : NativeMorreySobolevSpace n q ν→L[ℝ]MorreyCoefficientSpace n q ν→L[ℝ]MorreyCoefficientSpace n q ν :=
      selectedAction (k:=q) (m:=q) (q:=q) n hn γ hγ hγTwo ν B.flip
    ∀(U V : NativeMorreySobolevSpace n q ν) (A Z Y : MorreyCoefficientSpace n q ν) (t : ℝ),
      coefficientValue ν (L U A+L U (R V (Z+t • Y)))=ᵐ[volume.restrict (ball (0 : Domain n) 1)]
        (fun x i=>B (mapValue ν U x) (coefficientValue ν A x i)+
          B (mapValue ν U x) (B (coefficientValue ν Z x i+t • coefficientValue ν Y x i) (mapValue ν V x))) := by
  intro ν L R U V A Z Y t
  have hFirst := selectedAction_value_ae n hn γ hγ hγTwo ν B U A
  have hRight := selectedAction_value_ae n hn γ hγ hγTwo ν B.flip V (Z+t • Y)
  have hOuter := selectedAction_value_ae n hn γ hγ hγTwo ν B U (R V (Z+t • Y))
  have hSum := coefficientValue_add ν (L U A) (L U (R V (Z+t • Y)))
  have hAffine := coefficientValue_affine ν t Z Y
  filter_upwards [hFirst,hRight,hOuter,hSum,hAffine] with x hFirstX hRightX hOuterX hSumX hAffineX
  funext i
  calc
    _=coefficientValue ν (L U A) x i+coefficientValue ν (L U (R V (Z+t • Y))) x i := congrFun hSumX i
    _=B (mapValue ν U x) (coefficientValue ν A x i)+
        B (mapValue ν U x) (coefficientValue ν (R V (Z+t • Y)) x i) := congrArg₂ (fun a b : Ambient q=>a+b)
      (congrFun hFirstX i) (congrFun hOuterX i)
    _=_ := by rw [congrFun hRightX i,congrFun hAffineX i];rfl

private def bilinearFlux {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Exp : V→V) (D : V→L[ℝ]W) (L R : V→L[ℝ]W→L[ℝ]W) (Z Y : W) (p : V×ℝ) : W :=
  L (Exp (-p.1)) (D (Exp p.1))+L (Exp (-p.1)) (R (Exp p.1) (Z+p.2 • Y))

private theorem analytic_bilinear_apply {U V W A : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    (B : V→L[ℝ]W→L[ℝ]A) (f : U→V) (g : U→W) (p : U)
    (hf : AnalyticAt ℝ f p) (hg : AnalyticAt ℝ g p) :
    AnalyticAt ℝ (fun u=>B (f u) (g u)) p :=
  (B.analyticAt_bilinear (f p,g p)).comp (f:=fun u=>(f u,g u)) (hf.prod hg)

private theorem bilinearFlux_analytic {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Exp : V→V) (D : V→L[ℝ]W) (L R : V→L[ℝ]W→L[ℝ]W) (Z Y : W)
    (hExp : ∀X,AnalyticAt ℝ Exp X) (p : V×ℝ) :
    AnalyticAt ℝ (bilinearFlux Exp D L R Z Y) p := by
  let fst : V×ℝ→L[ℝ]V := ContinuousLinearMap.fst ℝ V ℝ
  let snd : V×ℝ→L[ℝ]ℝ := ContinuousLinearMap.snd ℝ V ℝ
  have hPlus : AnalyticAt ℝ (fun u : V×ℝ=>Exp u.1) p :=
    (hExp p.1).comp (f:=fun u : V×ℝ=>u.1) (fst.analyticAt p)
  have hMinus : AnalyticAt ℝ (fun u : V×ℝ=>Exp (-u.1)) p :=
    (hExp (-p.1)).comp (f:=fun u : V×ℝ=>-u.1) (fst.analyticAt p).neg
  have hGrad : AnalyticAt ℝ (fun u : V×ℝ=>D (Exp u.1)) p :=
    (D.analyticAt (Exp p.1)).comp (f:=fun u : V×ℝ=>Exp u.1) hPlus
  let M : ℝ→L[ℝ]W := (ContinuousLinearMap.id ℝ ℝ).smulRight Y
  have hPerturb : AnalyticAt ℝ (fun u : V×ℝ=>Z+u.2 • Y) p :=
    analyticAt_const.add ((M.analyticAt p.2).comp (f:=fun u : V×ℝ=>u.2) (snd.analyticAt p))
  exact (analytic_bilinear_apply L _ _ p hMinus hGrad).add
    (analytic_bilinear_apply L _ _ p hMinus (analytic_bilinear_apply R _ _ p hPlus hPerturb))

private theorem bilinearFlux_strict_X {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Exp : V→V) (D : V→L[ℝ]W) (L R : V→L[ℝ]W→L[ℝ]W) (Z Y : W) (e : V)
    (hExp : HasStrictFDerivAt Exp (1 : V→L[ℝ]V) 0) (hZero : Exp 0=e)
    (hD : D e=0) (hL : L e=ContinuousLinearMap.id ℝ W)
    (hR : R e=ContinuousLinearMap.id ℝ W) :
    HasStrictFDerivAt (fun X=>bilinearFlux Exp D L R Z Y (X,0))
      (D+R.flip Z-L.flip Z) 0 := by
  have hId : HasStrictFDerivAt (id : V→V) (ContinuousLinearMap.id ℝ V) 0 := hasStrictFDerivAt_id 0
  have hExpNeg : HasStrictFDerivAt (fun X=>Exp (-X)) (-1 : V→L[ℝ]V) 0 := by
    have hAt : HasStrictFDerivAt Exp (1 : V→L[ℝ]V) (-(0 : V)) := by
      simpa only [neg_zero] using hExp
    convert hAt.comp (0 : V) hId.neg using 1
    apply ContinuousLinearMap.ext
    intro X
    rfl
  have hGrad := D.hasStrictFDerivAt.comp (0 : V) hExp
  have hLeft := L.hasStrictFDerivAt.comp (0 : V) hExpNeg
  have hRight := (R.hasStrictFDerivAt.comp (0 : V) hExp).clm_apply (hasStrictFDerivAt_const Z 0)
  have hFirst := hLeft.clm_apply hGrad
  have hSecond := hLeft.clm_apply hRight
  have H := hFirst.add hSecond
  have hDerivative :
      ((L (Exp (-0))).comp (D.comp (1 : V→L[ℝ]V))+(L.comp (-1 : V→L[ℝ]V)).flip (D (Exp 0)))+
        ((L (Exp (-0))).comp (((R (Exp 0)).comp (0 : V→L[ℝ]W))+(R.comp (1 : V→L[ℝ]V)).flip Z)+
          (L.comp (-1 : V→L[ℝ]V)).flip ((R (Exp 0)) Z))=D+R.flip Z-L.flip Z := by
    rw [neg_zero,hZero,hD,hL,hR]
    apply ContinuousLinearMap.ext
    intro X
    simp only [add_apply,sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,one_apply_eq_self,ContinuousLinearMap.id_apply,
      neg_apply,zero_apply,map_zero,map_neg,add_zero,zero_add]
    abel
  rw [hDerivative] at H
  simpa only [bilinearFlux,zero_smul,add_zero,Pi.add_def] using H

private theorem bilinearFlux_strict_t {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Exp : V→V) (D : V→L[ℝ]W) (L R : V→L[ℝ]W→L[ℝ]W) (Z Y : W) (e : V)
    (hZero : Exp 0=e) (hD : D e=0) (hL : L e=ContinuousLinearMap.id ℝ W)
    (hR : R e=ContinuousLinearMap.id ℝ W) :
    HasStrictFDerivAt (fun t : ℝ=>bilinearFlux Exp D L R Z Y (0,t))
      ((ContinuousLinearMap.id ℝ ℝ).smulRight Y) 0 := by
  have hFn : (fun t : ℝ=>bilinearFlux Exp D L R Z Y (0,t))=(fun t=>Z+t • Y) := by
    funext t
    simp only [bilinearFlux,neg_zero,hZero,hD,hL,hR,ContinuousLinearMap.id_apply,zero_add]
  rw [hFn]
  exact ((hasStrictFDerivAt_id (0 : ℝ)).smul_const Y).const_add Z

private theorem strict_joint_of_analytic_partials {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (f : V×ℝ→W) (A : V→L[ℝ]W) (B : ℝ→L[ℝ]W)
    (hAnalytic : AnalyticAt ℝ f (0 : V×ℝ))
    (hX : HasStrictFDerivAt (fun X=>f (X,0)) A 0)
    (hT : HasStrictFDerivAt (fun t : ℝ=>f (0,t)) B 0) :
    HasStrictFDerivAt f (A.coprod B) (0 : V×ℝ) := by
  let F : V×ℝ→L[ℝ]W := fderiv ℝ f (0 : V×ℝ)
  have hCont : ContDiffAt ℝ 1 f (0 : V×ℝ) := hAnalytic.contDiffAt
  have hFull : HasStrictFDerivAt f F (0 : V×ℝ) := hCont.hasStrictFDerivAt (by norm_num)
  have hLeft : F.comp (ContinuousLinearMap.inl ℝ V ℝ)=A :=
    (hFull.hasFDerivAt.comp (0 : V) (hasFDerivAt_prodMk_left (0 : V) (0 : ℝ))).unique hX.hasFDerivAt
  have hRight : F.comp (ContinuousLinearMap.inr ℝ V ℝ)=B :=
    (hFull.hasFDerivAt.comp (0 : ℝ) (hasFDerivAt_prodMk_right (0 : V) (0 : ℝ))).unique hT.hasFDerivAt
  have hPair := ContinuousLinearMap.coprod_comp_inl_inr F
  rw [hLeft,hRight] at hPair
  rw [hPair]
  exact hFull

private abbrev matrixFluxLeft
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)→L[ℝ]
      MorreyCoefficientSpace n (q*q) ((n : ℝ)-2+γ)→L[ℝ]
        MorreyCoefficientSpace n (q*q) ((n : ℝ)-2+γ) :=
  selectedAction (k:=q*q) (m:=q*q) (q:=q*q) n hn γ hγ hγTwo ((n : ℝ)-2+γ)
    (matrixMorreyCoefficientProduct E R)

private abbrev matrixFluxRight
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)→L[ℝ]
      MorreyCoefficientSpace n (q*q) ((n : ℝ)-2+γ)→L[ℝ]
        MorreyCoefficientSpace n (q*q) ((n : ℝ)-2+γ) :=
  selectedAction (k:=q*q) (m:=q*q) (q:=q*q) n hn γ hγ hγTwo ((n : ℝ)-2+γ)
    (matrixMorreyCoefficientProduct E R).flip

private theorem matrixFluxLeft_unit
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z) :
    matrixFluxLeft n hn γ hγ hγTwo q E R (matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E)=
      ContinuousLinearMap.id ℝ (MorreyCoefficientSpace n (q*q) ((n : ℝ)-2+γ)) := by
  apply selectedAction_constant_unit n hn γ hγ hγTwo ((n : ℝ)-2+γ)
    (matrixMorreyCoefficientProduct E R) _ (E 1)
  · intro z
    rw [matrixMorreyCoefficientProduct_apply,hRE,one_mul,hER]
  · exact nativeMorreyConstant_ae n (q*q) ((n : ℝ)-2+γ) (E 1)

private theorem matrixFluxRight_unit
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z) :
    matrixFluxRight n hn γ hγ hγTwo q E R (matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E)=
      ContinuousLinearMap.id ℝ (MorreyCoefficientSpace n (q*q) ((n : ℝ)-2+γ)) := by
  apply selectedAction_constant_unit n hn γ hγ hγTwo ((n : ℝ)-2+γ)
    (matrixMorreyCoefficientProduct E R).flip _ (E 1)
  · intro z
    change matrixMorreyCoefficientProduct E R z (E 1)=z
    rw [matrixMorreyCoefficientProduct_apply,hRE,mul_one,hER]
  · exact nativeMorreyConstant_ae n (q*q) ((n : ℝ)-2+γ) (E 1)

private def matrixFlux
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (Z Y : MorreyCoefficientSpace n (q*q) ((n : ℝ)-2+γ)) :
    (NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)×ℝ)→
      MorreyCoefficientSpace n (q*q) ((n : ℝ)-2+γ) :=
  bilinearFlux (matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER)
    (nativeMorreyGradientClass (n:=n) (q:=q*q) ((n : ℝ)-2+γ))
    (matrixFluxLeft n hn γ hγ hγTwo q E R) (matrixFluxRight n hn γ hγ hγTwo q E R) Z Y

private theorem matrixFlux_zero_parameter
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (Z Y : MorreyCoefficientSpace n (q*q) ((n : ℝ)-2+γ)) (t : ℝ) :
    matrixFlux n hn γ hγ hγTwo q E R hRE hER Z Y (0,t)=Z+t • Y := by
  have hGrad : nativeMorreyGradientClass (n:=n) (q:=q*q) ((n : ℝ)-2+γ)
      (matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E)=0 :=
    nativeMorreyConstant_gradient n (q*q) ((n : ℝ)-2+γ) (E 1)
  simp only [matrixFlux,bilinearFlux,neg_zero,
    matrixNativeMorreyExp_zero n hn γ hγ hγTwo q E R hRE hER,
    hGrad,matrixFluxLeft_unit n hn γ hγ hγTwo q E R hRE hER,
    matrixFluxRight_unit n hn γ hγ hγTwo q E R hRE hER,
    ContinuousLinearMap.id_apply,zero_add]

private theorem matrixFlux_analytic
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (Z Y : MorreyCoefficientSpace n (q*q) ((n : ℝ)-2+γ))
    (p : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)×ℝ) :
    AnalyticAt ℝ (matrixFlux n hn γ hγ hγTwo q E R hRE hER Z Y) p :=
  bilinearFlux_analytic _ _ _ _ _ _ (matrixNativeMorreyExp_analytic n hn γ hγ hγTwo q E R hRE hER) p

private theorem matrixFlux_strict_X
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (Z Y : MorreyCoefficientSpace n (q*q) ((n : ℝ)-2+γ)) :
    HasStrictFDerivAt (fun X=>matrixFlux n hn γ hγ hγTwo q E R hRE hER Z Y (X,0))
      (nativeMorreyGradientClass (n:=n) (q:=q*q) ((n : ℝ)-2+γ)+
        (matrixFluxRight n hn γ hγ hγTwo q E R).flip Z-
          (matrixFluxLeft n hn γ hγ hγTwo q E R).flip Z) 0 :=
  bilinearFlux_strict_X _ _ _ _ _ _ (matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E)
    (matrixNativeMorreyExp_hasStrictFDerivAt_zero n hn γ hγ hγTwo q E R hRE hER)
    (matrixNativeMorreyExp_zero n hn γ hγ hγTwo q E R hRE hER)
    (nativeMorreyConstant_gradient n (q*q) ((n : ℝ)-2+γ) (E 1))
    (matrixFluxLeft_unit n hn γ hγ hγTwo q E R hRE hER)
    (matrixFluxRight_unit n hn γ hγ hγTwo q E R hRE hER)

private theorem matrixFlux_strict_t
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (Z Y : MorreyCoefficientSpace n (q*q) ((n : ℝ)-2+γ)) :
    HasStrictFDerivAt (fun t : ℝ=>matrixFlux n hn γ hγ hγTwo q E R hRE hER Z Y (0,t))
      ((ContinuousLinearMap.id ℝ ℝ).smulRight Y) 0 :=
  bilinearFlux_strict_t _ _ _ _ _ _ (matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E)
    (matrixNativeMorreyExp_zero n hn γ hγ hγTwo q E R hRE hER)
    (nativeMorreyConstant_gradient n (q*q) ((n : ℝ)-2+γ) (E 1))
    (matrixFluxLeft_unit n hn γ hγ hγTwo q E R hRE hER)
    (matrixFluxRight_unit n hn γ hγ hγTwo q E R hRE hER)

private theorem encoded_matrix_flux_formula {q : ℕ}
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q)) (hRE : ∀T,R (E T)=T)
    (u v a z y : Ambient (q*q)) (t : ℝ) :
    matrixMorreyCoefficientProduct E R u a+
      matrixMorreyCoefficientProduct E R u (matrixMorreyCoefficientProduct E R (z+t • y) v)=
      E (R u*R a+(R u*(R z+t • R y))*R v) := by
  calc
    _=E (R u*R a)+E (R u*(R (z+t • y)*R v)) := by
      rw [matrixMorreyCoefficientProduct_apply,matrixMorreyCoefficientProduct_apply,
        matrixMorreyCoefficientProduct_apply,hRE]
    _=E (R u*R a+R u*(R (z+t • y)*R v)) := (E.map_add _ _).symm
    _=_ := by rw [R.map_add,R.map_smul,mul_assoc]

private theorem matrixFlux_ae
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z) :
    let ν := (n : ℝ)-2+γ
    let Exp := matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER
    let D := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    ∀(Z Y : MorreyCoefficientSpace n (q*q) ν)
      (X : NativeMorreySobolevSpace n (q*q) ν) (t : ℝ),
      ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
        coefficientValue ν (matrixFlux n hn γ hγ hγTwo q E R hRE hER Z Y (X,t)) x=
          fun i=>E (R (mapValue ν (Exp (-X)) x)*R (coefficientValue ν (D (Exp X)) x i)+
            (R (mapValue ν (Exp (-X)) x)*(R (coefficientValue ν Z x i)+t • R (coefficientValue ν Y x i)))*
              R (mapValue ν (Exp X) x)) := by
  intro ν Exp D Z Y X t
  have H := action_flux_ae n hn γ hγ hγTwo (q*q) (matrixMorreyCoefficientProduct E R)
    (Exp (-X)) (Exp X) (D (Exp X)) Z Y t
  filter_upwards [H] with x hx
  apply hx.trans
  funext i
  exact encoded_matrix_flux_formula E R hRE _ _ _ _ _ t

private theorem encoded_commutator_sum {q : ℕ}
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (a u z l r : Ambient (q*q))
    (hl : l=matrixMorreyCoefficientProduct E R u z)
    (hr : r=matrixMorreyCoefficientProduct E R z u) :
    (a+r)-l=a+E (R z*R u-R u*R z) := by
  rw [hl,hr,matrixMorreyCoefficientProduct_apply,matrixMorreyCoefficientProduct_apply,E.map_sub]
  abel

private theorem matrixFlux_derivative_ae
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    let ν := (n : ℝ)-2+γ
    let D := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    let L := matrixFluxLeft n hn γ hγ hγTwo q E R
    let T := matrixFluxRight n hn γ hγ hγTwo q E R
    ∀(Z : MorreyCoefficientSpace n (q*q) ν) (H : NativeMorreySobolevSpace n (q*q) ν),
      ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
        coefficientValue ν ((D+T.flip Z-L.flip Z) H) x=
          fun i=>coefficientValue ν (D H) x i+
            E (R (coefficientValue ν Z x i)*R (mapValue ν H x)-
              R (mapValue ν H x)*R (coefficientValue ν Z x i)) := by
  intro ν D L T Z H
  have hAdd := coefficientValue_add ν (D H) (T H Z)
  have hSub := coefficientValue_sub ν (D H+T H Z) (L H Z)
  have hLeft : coefficientValue ν (L H Z)=ᵐ[volume.restrict (ball (0 : Domain n) 1)]
      (fun x i=>matrixMorreyCoefficientProduct E R (mapValue ν H x) (coefficientValue ν Z x i)) :=
    selectedAction_value_ae n hn γ hγ hγTwo ν (matrixMorreyCoefficientProduct E R) H Z
  have hRight : coefficientValue ν (T H Z)=ᵐ[volume.restrict (ball (0 : Domain n) 1)]
      (fun x i=>matrixMorreyCoefficientProduct E R (coefficientValue ν Z x i) (mapValue ν H x)) := by
    simpa only [ContinuousLinearMap.flip_apply] using
      selectedAction_value_ae n hn γ hγ hγTwo ν (matrixMorreyCoefficientProduct E R).flip H Z
  filter_upwards [hAdd,hSub,hLeft,hRight] with x ha hs hl hr
  funext i
  calc
    _=coefficientValue ν (D H+T H Z) x i-coefficientValue ν (L H Z) x i := congrFun hs i
    _=(coefficientValue ν (D H) x i+coefficientValue ν (T H Z) x i)-coefficientValue ν (L H Z) x i :=
      congrArg (fun z : Ambient (q*q)=>z-coefficientValue ν (L H Z) x i) (congrFun ha i)
    _=_ := encoded_commutator_sum E R _ _ _ _ _ (congrFun hl i) (congrFun hr i)

private theorem matrixFlux_raw_transport
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z) :
    let ν := (n : ℝ)-2+γ
    let Exp := matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER
    let D := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    ∀(Z Y : MorreyCoefficientSpace n (q*q) ν)
      (p : NativeMorreySobolevSpace n (q*q) ν×ℝ)
      (pm pp : Domain n→Ambient (q*q)) (DP Zr Yr : Domain n→Gradient n (q*q)),
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
        mapValue ν (Exp (-p.1)) x=pm x ∧ mapValue ν (Exp p.1) x=pp x ∧
          coefficientValue ν (D (Exp p.1)) x=DP x ∧ coefficientValue ν Z x=Zr x ∧
            coefficientValue ν Y x=Yr x) →
      ∃hFlux : ∀i,MemLp (fun x=>E (R (pm x)*R (DP x i)+
          (R (pm x)*(R (Zr x i)+p.2 • R (Yr x i)))*R (pp x))) 2
          (volume.restrict (ball (0 : Domain n) 1)),
        morreyCoefficientRecover (n:=n) (q:=q*q) ν (matrixFlux n hn γ hγ hγTwo q E R hRE hER Z Y p)=
          hsUnitBallL2Class (fun x i=>E (R (pm x)*R (DP x i)+
            (R (pm x)*(R (Zr x i)+p.2 • R (Yr x i)))*R (pp x))) hFlux := by
  intro ν Exp D Z Y p pm pp DP Zr Yr hRaw
  apply coefficient_recover_of_ae ν (matrixFlux n hn γ hγ hγTwo q E R hRE hER Z Y p)
  have hCanon := matrixFlux_ae n hn γ hγ hγTwo q E R hRE hER Z Y p.1 p.2
  filter_upwards [hCanon,hRaw] with x hc hr
  apply hc.trans
  funext i
  rw [hr.1,hr.2.1,congrFun hr.2.2.1 i,congrFun hr.2.2.2.1 i,congrFun hr.2.2.2.2 i]

/-- The actual stronger-class matrix Coulomb flux is uniquely determined
by its original coefficient field. It is jointly analytic and its strict
linearizations are the original gradient plus the commutator and the
original connection variation. -/
theorem existsUnique_native_matrix_coulomb_flux
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (Z Y : MorreyCoefficientSpace n (q*q) ((n : ℝ)-2+γ)) :
    let ν := (n : ℝ)-2+γ
    let S := NativeMorreySobolevSpace n (q*q) ν
    let M := MorreyCoefficientSpace n (q*q) ν
    let value : S→Domain n→Ambient (q*q) := fun U=>nativeMorreyMapClass (n:=n) (q:=q*q) ν U
    let field : M→Domain n→Gradient n (q*q) := fun F x i=>WithLp.toLp 2
      (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
    let D : S→L[ℝ]M := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    let Exp : S→S := matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER
    ∃! Φ : S×ℝ→M,
      (∀p : S×ℝ,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
        field (Φ p) x=fun i=>E (R (value (Exp (-p.1)) x)*R (field (D (Exp p.1)) x i)+
          (R (value (Exp (-p.1)) x)*(R (field Z x i)+p.2 • R (field Y x i)))*R (value (Exp p.1) x))) ∧
      (∀p : S×ℝ,AnalyticAt ℝ Φ p) ∧
      (∃A : S→L[ℝ]M,
        HasStrictFDerivAt (fun X=>Φ (X,0)) A 0 ∧
        HasStrictFDerivAt Φ (A.coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight Y)) (0 : S×ℝ) ∧
        ∀H : S,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
          field (A H) x=fun i=>field (D H) x i+
            E (R (field Z x i)*R (value H x)-R (value H x)*R (field Z x i))) ∧
      HasStrictFDerivAt (fun t : ℝ=>Φ (0,t)) ((ContinuousLinearMap.id ℝ ℝ).smulRight Y) 0 ∧
      (∀(p : S×ℝ) (pm pp : Domain n→Ambient (q*q)) (DP Zr Yr : Domain n→Gradient n (q*q)),
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
          value (Exp (-p.1)) x=pm x ∧ value (Exp p.1) x=pp x ∧
            field (D (Exp p.1)) x=DP x ∧ field Z x=Zr x ∧ field Y x=Yr x) →
        ∃hFlux : ∀i,MemLp (fun x=>E (R (pm x)*R (DP x i)+
            (R (pm x)*(R (Zr x i)+p.2 • R (Yr x i)))*R (pp x))) 2
            (volume.restrict (ball (0 : Domain n) 1)),
          morreyCoefficientRecover (n:=n) (q:=q*q) ν (Φ p)=
            hsUnitBallL2Class (fun x i=>E (R (pm x)*R (DP x i)+
              (R (pm x)*(R (Zr x i)+p.2 • R (Yr x i)))*R (pp x))) hFlux) ∧
      (∀t : ℝ,Φ (0,t)=Z+t • Y) := by
  intro ν S M value field D Exp
  let Φ : S×ℝ→M := matrixFlux n hn γ hγ hγTwo q E R hRE hER Z Y
  refine ⟨Φ,⟨?_,?_,?_,?_,?_,?_⟩,?_⟩
  · intro p
    exact matrixFlux_ae n hn γ hγ hγTwo q E R hRE hER Z Y p.1 p.2
  · intro p
    exact matrixFlux_analytic n hn γ hγ hγTwo q E R hRE hER Z Y p
  · refine ⟨D+(matrixFluxRight n hn γ hγ hγTwo q E R).flip Z-
      (matrixFluxLeft n hn γ hγ hγTwo q E R).flip Z,?_,?_,?_⟩
    · exact matrixFlux_strict_X n hn γ hγ hγTwo q E R hRE hER Z Y
    · exact strict_joint_of_analytic_partials Φ _ _
        (matrixFlux_analytic n hn γ hγ hγTwo q E R hRE hER Z Y 0)
        (matrixFlux_strict_X n hn γ hγ hγTwo q E R hRE hER Z Y)
        (matrixFlux_strict_t n hn γ hγ hγTwo q E R hRE hER Z Y)
    · exact matrixFlux_derivative_ae n hn γ hγ hγTwo q E R Z
  · exact matrixFlux_strict_t n hn γ hγ hγTwo q E R hRE hER Z Y
  · exact matrixFlux_raw_transport n hn γ hγ hγTwo q E R hRE hER Z Y
  · exact matrixFlux_zero_parameter n hn γ hγ hγTwo q E R hRE hER Z Y
  · rintro Ψ ⟨hΨ,_hAnalytic,_hDerivative,_hParam,_hRaw,_hBase⟩
    funext p
    apply coefficientValue_injective_ae ν
    filter_upwards [hΨ p,matrixFlux_ae n hn γ hγ hγTwo q E R hRE hER Z Y p.1 p.2] with x hx hy
    exact hx.trans hy.symm

end StationaryHarmonicMaps.Analysis

end
