module

public import StationaryHarmonicMaps.Analysis.MatrixNativeMorreySkewExponential

/-!
# The actual inverse exponential of a skew native field

The original skew class and its negative give adjoint inverse exponential
values in the same fixed matrix coordinates, including every closed-ball point.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace StationaryHarmonicMaps.Analysis

/-- The negative native exponential is the adjoint of the positive one
at every closed-ball point. -/
theorem skew_nativeMorrey_exp_neg_eq_star
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (X : SkewMeanZeroNativeMorreySpace n q ((n : ℝ)-2+γ) e) :
    let E := e.symm.toContinuousLinearMap
    let R := e.toContinuousLinearMap
    let hRE : ∀T,R (E T)=T := e.apply_symm_apply
    let hER : ∀z,E (R z)=z := e.symm_apply_apply
    let Zp := matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER X.val.val
    let Zm := matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER (-X.val.val)
    ∀x : closedBall (0 : Domain n) 1,
      e (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo Zm x)=
        star (e (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo Zp x)) := by
  intro E R hRE hER Zp Zm x
  let A := Ambient q→L[ℝ]Ambient q
  letI : ContinuousStar A :=
    ⟨(ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).continuous⟩
  letI : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  let S : A := e (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo X.val.val x)
  have hS : star S=-S := skew_nativeMorrey_continuous_skew n hn γ hγ hγTwo q e X x
  have hNeg : nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo (-X.val.val) x=
      -nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo X.val.val x := by
    have H := (nativeMorreyContinuousEmbedding n hn γ hγ hγTwo (q*q)).map_neg X.val.val
    exact congrArg (fun W : C(closedBall (0 : Domain n) 1,Ambient (q*q))=>W x) H
  have hNegR : e (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo (-X.val.val) x)=-S :=
    (congrArg e hNeg).trans (e.map_neg _)
  have hp : e (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo Zp x)=NormedSpace.exp S :=
    matrixNativeMorreyExp_evaluation n hn γ hγ hγTwo q E R hRE hER X.val.val x
  have hm : e (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo Zm x)=
      NormedSpace.exp (e (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo (-X.val.val) x)) :=
    matrixNativeMorreyExp_evaluation n hn γ hγ hγTwo q E R hRE hER (-X.val.val) x
  have hStar : NormedSpace.exp (-S)=star (NormedSpace.exp S) :=
    (congrArg (fun T : A=>NormedSpace.exp T) hS.symm).trans (NormedSpace.star_exp S).symm
  exact hm.trans ((congrArg (fun T : A=>NormedSpace.exp T) hNegR).trans
    (hStar.trans (congrArg (fun T : A=>star T) hp.symm)))

theorem skew_nativeMorrey_exp_neg_ae_eq_star
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
    ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν Zm).val x)=
        star (e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν Zp).val x)) := by
  intro ν E R hRE hER Zp Zm
  have hInv := skew_nativeMorrey_exp_neg_eq_star n hn γ hγ hγTwo q e X
  filter_upwards [nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo Zp,
    nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo Zm,
    ae_restrict_mem measurableSet_ball] with x hP hM hxBall
  exact (congrArg e (hM hxBall)).symm.trans ((hInv ⟨x,ball_subset_closedBall hxBall⟩).trans
    (congrArg (fun z : Ambient (q*q)=>star (e z)) (hP hxBall)))

/-- The adjoint inverse identity holds for arbitrary original native
representatives of these same two exponential classes. -/
theorem skew_nativeMorrey_exp_neg_raw_eq_star
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
      ∀(r : Domain n→Ambient (q*q)) (Dr : Domain n→Gradient n (q*q))
        (hr : MemW12 (ballDomain (0 : Domain n) 1) r Dr),
        nativeMorreyMapClass (n:=n) (q:=q*q) ν Zm=hr.2.1.toLp r →
        ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),e (r x)=star (e (v x)) := by
  intro ν E R hRE hER Zp Zm v Dv hv hVMap r Dr hr hRMap
  have hInv := skew_nativeMorrey_exp_neg_ae_eq_star n hn γ hγ hγTwo q e X
  filter_upwards [hInv,hv.2.1.coeFn_toLp,hr.2.1.coeFn_toLp] with x hx hvx hrx
  have hV : (nativeMorreyMapClass (n:=n) (q:=q*q) ν Zp).val x=v x :=
    (congrArg (fun U : MapUnitBallL2 n (q*q)=>U.val x) hVMap).trans hvx
  have hR : (nativeMorreyMapClass (n:=n) (q:=q*q) ν Zm).val x=r x :=
    (congrArg (fun U : MapUnitBallL2 n (q*q)=>U.val x) hRMap).trans hrx
  exact (congrArg e hR).symm.trans (hx.trans (congrArg (fun z : Ambient (q*q)=>star (e z)) hV))

end StationaryHarmonicMaps.Analysis

end
