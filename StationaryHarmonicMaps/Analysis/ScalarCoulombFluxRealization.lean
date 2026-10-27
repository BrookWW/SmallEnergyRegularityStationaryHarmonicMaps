module

public import StationaryHarmonicMaps.Analysis.NativeMorreyMatrixFlux
public import StationaryHarmonicMaps.Analysis.MatrixNativeMorreyFramePerturbation
import StationaryHarmonicMaps.Analysis.HilbertSchmidtDecoding

/-!
# Realization of the scalar-path flux by the same original frame

The actual exponential perturbation retains its original two-term weak
gradient and special-orthogonal values. Its scalar-path connection is the
same actual flux coefficient class, with the original matrix order.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

noncomputable section

namespace StationaryHarmonicMaps.Analysis

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

private theorem coefficient_recover_of_ae {n q : ℕ} (ν : ℝ) (F : MorreyCoefficientSpace n q ν)
    (Fr : Domain n→Gradient n q)
    (hAE : coefficientValue ν F=ᵐ[volume.restrict (ball (0 : Domain n) 1)]Fr) :
    ∃hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)),
      morreyCoefficientRecover (n:=n) (q:=q) ν F=hsUnitBallL2Class Fr hFr := by
  have hFr (i : Fin n) : MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)) :=
    (coefficientValue_memLp ν F i).ae_eq (hAE.mono fun x hx=>congrFun hx i)
  exact ⟨hFr,(coefficientValue_class ν F).trans
    ((hsUnitBallL2Class_eq_iff_ae _ _ _ _).mpr fun i=>hAE.mono fun x hx=>congrFun hx i)⟩

private theorem scalar_gauged_connection_shift {q : ℕ}
    (P DP A : Ambient q→L[ℝ]Ambient q) (τ t : ℝ) :
    (star P*DP+star P*(τ • A)*P)+t • (star P*A*P)=
      star P*DP+star P*((τ+t) • A)*P := by
  apply ContinuousLinearMap.ext
  intro w
  change star P (DP w)+star P (τ • A (P w))+t • star P (A (P w))=
    star P (DP w)+star P ((τ+t) • A (P w))
  simp only [map_smul,map_add,add_smul]
  abel

private theorem scalar_flux_original_ae {n q : ℕ}
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q))
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q)) (τ t : ℝ)
    (pm pp : Domain n→Ambient (q*q)) (GP Zr Yr Fr : Domain n→Gradient n (q*q))
    (v r W : Domain n→Ambient (q*q)) (Dv DW : Domain n→Gradient n (q*q))
    (hFormula : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),Fr x=fun i=>e.symm
      (e (pm x)*e (GP x i)+(e (pm x)*(e (Zr x i)+t • e (Yr x i)))*e (pp x)))
    (hNeg : pm=ᵐ[volume.restrict (ball (0 : Domain n) 1)]r)
    (hPos : pp=ᵐ[volume.restrict (ball (0 : Domain n) 1)]v)
    (hGrad : GP=ᵐ[volume.restrict (ball (0 : Domain n) 1)]Dv)
    (hZ : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
      Zr x i=e.symm (star (e (p x))*e (Dp x i)+star (e (p x))*(τ • A x i)*e (p x)))
    (hY : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
      Yr x i=e.symm (star (e (p x))*A x i*e (p x)))
    (hConnection : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
      star (e (W x))*e (DW x i)+star (e (W x))*((τ+t) • A x i)*e (W x)=
        e (r x)*e (Dv x i)+e (r x)*(star (e (p x))*e (Dp x i)+
          star (e (p x))*((τ+t) • A x i)*e (p x))*e (v x)) :
    Fr=ᵐ[volume.restrict (ball (0 : Domain n) 1)]
      (fun x i=>e.symm (star (e (W x))*e (DW x i)+star (e (W x))*((τ+t) • A x i)*e (W x))) := by
  filter_upwards [hFormula,hNeg,hPos,hGrad,hZ,hY,hConnection] with x hF hN hP hD hZx hYx hC
  funext i
  calc
    _=e.symm (e (pm x)*e (GP x i)+(e (pm x)*(e (Zr x i)+t • e (Yr x i)))*e (pp x)) := congrFun hF i
    _=e.symm (e (r x)*e (Dv x i)+e (r x)*(star (e (p x))*e (Dp x i)+
        star (e (p x))*((τ+t) • A x i)*e (p x))*e (v x)) := by
      rw [hN,hP,congrFun hD i,hZx i,hYx i]
      simp only [ContinuousLinearEquiv.apply_symm_apply]
      rw [scalar_gauged_connection_shift]
    _=_ := congrArg e.symm (hC i).symm

private theorem mapValue_of_raw {n q : ℕ} (ν : ℝ)
    (U : NativeMorreySobolevSpace n q ν) (u : Domain n→Ambient q)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hU : nativeMorreyMapClass (n:=n) (q:=q) ν U=hu.toLp u) :
    mapValue ν U=ᵐ[volume.restrict (ball (0 : Domain n) 1)]u := by
  change ((nativeMorreyMapClass (n:=n) (q:=q) ν) U : Domain n→Ambient q)=ᵐ[_]u
  rw [hU]
  exact hu.coeFn_toLp

/-- The original scalar-path connection of the actual perturbed SO frame
is the same actual nonlinear flux, with its original weak gradient and
internally produced original coefficient integrability. -/
theorem scalar_native_coulomb_flux_realization
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (p : Domain n→Ambient (q*q)) (Dp : Domain n→Gradient n (q*q))
    (hp : MemW12 (ballDomain (0 : Domain n) 1) p Dp)
    (P : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ))
    (hPMap : nativeMorreyMapClass (n:=n) (q:=q*q) ((n : ℝ)-2+γ) P=hp.2.1.toLp p)
    (hPSO : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (e (p x))*e (p x)=1 ∧ (e (p x)).det=1)
    (A : Domain n→Fin n→(Ambient q→L[ℝ]Ambient q)) (τ : ℝ) :
    let ν := (n : ℝ)-2+γ
    let S := NativeMorreySobolevSpace n (q*q) ν
    let M := MorreyCoefficientSpace n (q*q) ν
    let E := e.symm.toContinuousLinearMap
    let R := e.toContinuousLinearMap
    let value : S→Domain n→Ambient (q*q) := fun H=>nativeMorreyMapClass (n:=n) (q:=q*q) ν H
    let field : M→Domain n→Gradient n (q*q) := fun F x i=>WithLp.toLp 2
      (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
    let D := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    let Exp := matrixNativeMorreyExp n hn γ hγ hγTwo q E R e.apply_symm_apply e.symm_apply_apply
    ∀(Z Y : M),
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
        field Z x i=e.symm (star (e (p x))*e (Dp x i)+star (e (p x))*(τ • A x i)*e (p x))) →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
        field Y x i=e.symm (star (e (p x))*A x i*e (p x))) →
      ∀(Φ : S×ℝ→M),
        (∀Q : S×ℝ,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),field (Φ Q) x=fun i=>e.symm
          (e (value (Exp (-Q.1)) x)*e (field (D (Exp Q.1)) x i)+
            (e (value (Exp (-Q.1)) x)*(e (field Z x i)+Q.2 • e (field Y x i)))*e (value (Exp Q.1) x))) →
      ∀(X : SkewMeanZeroNativeMorreySpace n q ν e) (t : ℝ),
      ∃(v : Domain n→Ambient (q*q)) (Dv : Domain n→Gradient n (q*q))
        (hv : MemW12 (ballDomain (0 : Domain n) 1) v Dv),
        nativeMorreyMapClass (n:=n) (q:=q*q) ν (Exp X.val.val)=hv.2.1.toLp v ∧
        nativeMorreyHSClass (n:=n) (q:=q*q) ν (Exp X.val.val)=hsUnitBallL2Class Dv hv.2.2 ∧
        let B := matrixMorreyCoefficientProduct E R
        let W := fun x=>B (p x) (v x)
        let DW := fun x i=>B (Dp x i) (v x)+B (p x) (Dv x i)
        let Q := matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R P (Exp X.val.val)
        let Cw := fun x i=>e.symm (star (e (W x))*e (DW x i)+star (e (W x))*((τ+t) • A x i)*e (W x))
        ∃hW : MemW12 (ballDomain (0 : Domain n) 1) W DW,
          nativeMorreyMapClass (n:=n) (q:=q*q) ν Q=hW.2.1.toLp W ∧
          nativeMorreyHSClass (n:=n) (q:=q*q) ν Q=hsUnitBallL2Class DW hW.2.2 ∧
          (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (e (W x))*e (W x)=1 ∧ (e (W x)).det=1) ∧
          (field (Φ (X.val.val,t))=ᵐ[volume.restrict (ball (0 : Domain n) 1)]Cw) ∧
          ∃hCw : ∀i,MemLp (fun x=>Cw x i) 2 (volume.restrict (ball (0 : Domain n) 1)),
            morreyCoefficientRecover (n:=n) (q:=q*q) ν (Φ (X.val.val,t))=hsUnitBallL2Class Cw hCw := by
  intro ν S M E R value field D Exp Z Y hZ hY Φ hFormula X t
  let hRaw := nativeMorrey_right_exp_frame_perturbation n hn γ hγ hγTwo q e p Dp hp P hPMap hPSO X A (τ+t)
  obtain ⟨v,Dv,hv,r,Dr,hr,hVMap,hVGrad,hRMap,_hRGrad,hProduct⟩ := hRaw
  refine ⟨v,Dv,hv,hVMap,hVGrad,?_⟩
  intro B W DW Q Cw
  obtain ⟨hW,hWMap,hWGrad,hWSO,hConnection⟩ := hProduct
  have hPos : value (Exp X.val.val)=ᵐ[volume.restrict (ball (0 : Domain n) 1)]v :=
    mapValue_of_raw ν _ v hv.2.1 hVMap
  have hNeg : value (Exp (-X.val.val))=ᵐ[volume.restrict (ball (0 : Domain n) 1)]r :=
    mapValue_of_raw ν _ r hr.2.1 hRMap
  have hGrad : field (D (Exp X.val.val))=ᵐ[volume.restrict (ball (0 : Domain n) 1)]Dv :=
    coefficientValue_of_raw ν Dv hv.2.2 _ hVGrad
  have hPhi : field (Φ (X.val.val,t))=ᵐ[volume.restrict (ball (0 : Domain n) 1)]Cw :=
    scalar_flux_original_ae e p Dp A τ t (value (Exp (-X.val.val))) (value (Exp X.val.val))
      (field (D (Exp X.val.val))) (field Z) (field Y) (field (Φ (X.val.val,t)))
      v r W Dv DW (hFormula (X.val.val,t)) hNeg hPos hGrad hZ hY hConnection
  exact ⟨hW,hWMap,hWGrad,hWSO,hPhi,coefficient_recover_of_ae ν _ Cw hPhi⟩

end StationaryHarmonicMaps.Analysis

end
