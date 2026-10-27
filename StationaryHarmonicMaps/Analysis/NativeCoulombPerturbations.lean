module
public import StationaryHarmonicMaps.Analysis.SkewLinearizedNeumannComposition
public import StationaryHarmonicMaps.Analysis.NativeMorreyMatrixFlux
public import StationaryHarmonicMaps.Analysis.MatrixNativeMorreyFluxSkew
public import StationaryHarmonicMaps.Analysis.NativeNeumannMorreyRaw
public import StationaryHarmonicMaps.Analysis.SkewMeanZeroNativeMorreyProjection
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Prod
import StationaryHarmonicMaps.Analysis.HilbertSchmidtDecoding
/-!
# Actual local native Coulomb perturbations

The original stronger coefficient is natural and skew, with small critical
norm. The actual matrix flux and its internally constructed skew Neumann
inverse give exponential solutions in every prescribed parameter neighborhood.
The same original Neumann equation and every finite native test are retained.
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


private theorem canonical_native {n q : ℕ} (ν : ℝ)
    (X : NativeMorreySobolevSpace n q ν) :
    MemW12 (ballDomain (0:Domain n) 1) (mapValue ν X)
      (coefficientValue ν (nativeMorreyGradientClass (n:=n) (q:=q) ν X)) := by
  obtain ⟨u,Du,hu,hMap,hGrad,_hGrowth⟩ := exists_raw_native_of_nativeMorreySobolev ν X
  have hUAE : mapValue ν X=ᵐ[volume.restrict (ball (0:Domain n) 1)]u := by
    change ((nativeMorreyMapClass (n:=n) (q:=q) ν) X : Domain n→Ambient q)=ᵐ[_]u
    rw [hMap]
    exact hu.2.1.coeFn_toLp
  have hDAE := coefficientValue_of_raw ν Du hu.2.2
    (nativeMorreyGradientClass (n:=n) (q:=q) ν X) hGrad
  exact hu.congr_ae hUAE.symm hDAE.symm

private theorem neumann_hs_inner_raw {n q : ℕ}
    (F G : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hG : ∀i,MemLp (fun x=>G x i) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    inner ℝ (hsUnitBallL2Class F hF) (hsUnitBallL2Class G hG)=
      ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (F x i) (G x i) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hsUnitBallL2Class_ae F hF,hsUnitBallL2Class_ae G hG] with x hxF hxG
  rw [hxF,hxG]
  exact hs_flatten_inner (F x) (G x)

private theorem exponential_flux_skew
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    let ν := (n:ℝ)-2+γ
    let S := NativeMorreySobolevSpace n (q*q) ν
    let M := MorreyCoefficientSpace n (q*q) ν
    let Exp := matrixNativeMorreyExp n hn γ hγ hγTwo q
      e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply e.symm_apply_apply
    let D := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    ∀(Z Y : M) (Φ : S×ℝ→M),
      (∀p : S×ℝ,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
        coefficientValue ν (Φ p) x=fun i=>e.symm
          (e (mapValue ν (Exp (-p.1)) x)*e (coefficientValue ν (D (Exp p.1)) x i)+
            (e (mapValue ν (Exp (-p.1)) x)*
              (e (coefficientValue ν Z x i)+p.2 • e (coefficientValue ν Y x i)))*
                e (mapValue ν (Exp p.1) x))) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
        star (e (coefficientValue ν Z x i))= -(e (coefficientValue ν Z x i))) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
        star (e (coefficientValue ν Y x i))= -(e (coefficientValue ν Y x i))) →
      ∀(X : SkewMeanZeroNativeMorreySpace n q ν e) (t : ℝ),
        ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
          skewMorreyCoordinateConstraint q e (coefficientValue ν (Φ (X.val.val,t)) x i)=0 := by
  intro ν S M Exp D Z Y Φ hΦ hZ hY X t
  let v := mapValue ν (Exp X.val.val)
  let Dv := coefficientValue ν (D (Exp X.val.val))
  have hv : MemW12 (ballDomain (0:Domain n) 1) v Dv := canonical_native ν (Exp X.val.val)
  have hVMap : nativeMorreyMapClass (n:=n) (q:=q*q) ν (Exp X.val.val)=hv.2.1.toLp v :=
    (Lp.toLp_coeFn _ hv.2.1).symm
  let r := mapValue ν (Exp (-X.val.val))
  have hr : MemLp r 2 (volume.restrict (ball (0:Domain n) 1)) := Lp.memLp _
  have hRMap : nativeMorreyMapClass (n:=n) (q:=q*q) ν (Exp (-X.val.val))=hr.toLp r :=
    (Lp.toLp_coeFn _ hr).symm
  let Zt : Domain n→Gradient n (q*q) := fun x i=>coefficientValue ν Z x i+t • coefficientValue ν Y x i
  have hZt : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
      star (e (Zt x i))= -(e (Zt x i)) := by
    filter_upwards [hZ,hY] with x hx hy
    intro i
    change star (e (coefficientValue ν Z x i+t • coefficientValue ν Y x i))= _
    rw [e.map_add,e.map_smul]
    change ContinuousLinearMap.adjoint
      (e (coefficientValue ν Z x i)+t • e (coefficientValue ν Y x i))= _
    rw [map_add,map_smul]
    change star (e (coefficientValue ν Z x i))+t • star (e (coefficientValue ν Y x i))= _
    rw [hx i,hy i,smul_neg]
    abel
  have hRaw := (skew_nativeMorrey_exp_raw_flux_skew n hn γ hγ hγTwo q e X
    v Dv hv hVMap r hr hRMap Zt hZt).2
  filter_upwards [hΦ (X.val.val,t),hRaw] with x hx hrx
  intro i
  have hPoint : coefficientValue ν (Φ (X.val.val,t)) x i=
      e.symm (e (r x)*e (Dv x i)+e (r x)*e (Zt x i)*e (v x)) := by
    rw [congrFun hx i]
    simp only [Zt,e.map_add,e.map_smul]
    rfl
  rw [hPoint]
  exact hrx i

private theorem neumann_skew_of_field
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n:ℝ))
    (q : ℕ) (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (F : MorreyCoefficientSpace n (q*q) ν)
    (hF : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
      skewMorreyCoordinateConstraint q e (coefficientValue ν F x i)=0) :
    let N := nativeNeumannMorreyResponse n hn ν hν hνn (q*q)
    let W : MeanZeroNativeMorreySpace n (q*q) ν :=
      ⟨N F,nativeNeumannMorreyResponse_mem_meanZero n hn ν hν hνn (q*q) F⟩
    W∈skewMeanZeroNativeMorreySubmodule n q ν e := by
  intro N W
  exact nativeNeumannMorreyResponse_preserves_fixed_kernel n hn ν hν hνn
    (q*q) (q*q) (skewMorreyCoordinateConstraint q e) F (coefficientValue ν F)
    (coefficientValue_memLp ν F) (coefficientValue_class ν F) hF

private theorem projection_neumann_zero_iff
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n:ℝ))
    (q : ℕ) (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    let V := SkewMeanZeroNativeMorreySpace n q ν e
    let N := nativeNeumannMorreyResponse n hn ν hν hνn (q*q)
    let N0 : MorreyCoefficientSpace n (q*q) ν→L[ℝ]MeanZeroNativeMorreySpace n (q*q) ν :=
      N.codRestrict (meanZeroNativeMorreySubmodule n (q*q) ν)
        (nativeNeumannMorreyResponse_mem_meanZero n hn ν hν hνn (q*q))
    ∀(P : MeanZeroNativeMorreySpace n (q*q) ν→L[ℝ]V),
      (∀Y : V,P Y.val=Y) →
      ∀(F : MorreyCoefficientSpace n (q*q) ν),
        (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
          skewMorreyCoordinateConstraint q e (coefficientValue ν F x i)=0) →
        (P (N0 F)=0 ↔ N F=0) := by
  intro V N N0 P hP F hF
  have hSkew := neumann_skew_of_field n hn ν hν hνn q e F hF
  let W : V := ⟨N0 F,hSkew⟩
  have hValue : P (N0 F)=W := hP W
  constructor
  · intro hZero
    have hW : W=0 := hValue.symm.trans hZero
    exact congrArg (fun X : V=>X.val.val) hW
  · intro hZero
    have hN0 : N0 F=0 := Subtype.ext hZero
    exact (congrArg P hN0).trans P.map_zero

private theorem natural_of_neumann_zero
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n:ℝ))
    (q : ℕ) (F : MorreyCoefficientSpace n q ν)
    (hZero : nativeNeumannMorreyResponse n hn ν hν hνn q F=0) :
    ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (coefficientValue ν F x i) (Dψ x i))
        (ball (0:Domain n) 1) volume ∧
      (∫x in ball (0:Domain n) 1,∑i : Fin n,
        inner ℝ (coefficientValue ν F x i) (Dψ x i))=0 := by
  intro ψ Dψ hψ
  refine ⟨integrable_column_pairing (volume.restrict (ball (0:Domain n) 1))
    (coefficientValue ν F) Dψ (coefficientValue_memLp ν F) hψ.2.2,?_⟩
  have H := (nativeNeumannMorreyResponse_characterization n hn ν hν hνn q F).2 ψ Dψ hψ
  have hGrad : nativeMorreyHSClass (n:=n) (q:=q) ν
      (nativeNeumannMorreyResponse n hn ν hν hνn q F)=0 :=
    (congrArg (nativeMorreyHSClass (n:=n) (q:=q) ν) hZero).trans
      (nativeMorreyHSClass (n:=n) (q:=q) ν).map_zero
  rw [hGrad,inner_zero_left] at H
  have hRaw := neumann_hs_inner_raw (coefficientValue ν F) Dψ
    (coefficientValue_memLp ν F) hψ.2.2
  rw [←coefficientValue_class ν F] at hRaw
  exact hRaw.symm.trans H.symm

private theorem parameter_zero_persists
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f : ℝ×V→V) (A : V≃L[ℝ]V) (c : V)
    (hf0 : f 0=0)
    (hf : HasStrictFDerivAt f
      (((ContinuousLinearMap.fst ℝ ℝ V).smulRight c)+
        (A : V→L[ℝ]V).comp (ContinuousLinearMap.snd ℝ ℝ V)) 0)
    (U : Set (ℝ×V)) (hU : U∈𝓝 (0 : ℝ×V)) :
    ∀ᶠt in 𝓝 (0 : ℝ),∃u : V,(t,u)∈U ∧ f (t,u)=0 := by
  let L : (ℝ×V)≃L[ℝ](ℝ×V) :=
    { toFun := fun z=>(z.1,z.1 • c+A z.2)
      invFun := fun z=>(z.1,A.symm (z.2-z.1 • c))
      left_inv := by
        intro z
        apply Prod.ext
        · rfl
        · change A.symm (z.1 • c+A z.2-z.1 • c)=z.2
          rw [add_sub_cancel_left,A.symm_apply_apply]
      right_inv := by
        intro z
        apply Prod.ext
        · rfl
        · change z.1 • c+A (A.symm (z.2-z.1 • c))=z.2
          rw [A.apply_symm_apply]
          abel
      map_add' := by
        intro x y
        apply Prod.ext
        · rfl
        · change (x.1+y.1) • c+A (x.2+y.2)=_
          rw [add_smul,map_add]
          change (x.1 • c+y.1 • c)+(A x.2+A y.2)=(x.1 • c+A x.2)+(y.1 • c+A y.2)
          abel
      map_smul' := by
        intro a x
        apply Prod.ext
        · rfl
        · change (a*x.1) • c+A (a • x.2)=a • (x.1 • c+A x.2)
          rw [map_smul,smul_add,smul_smul]
      continuous_toFun := continuous_fst.prodMk
        ((continuous_fst.smul continuous_const).add (A.continuous.comp continuous_snd))
      continuous_invFun := continuous_fst.prodMk
        (A.symm.continuous.comp (continuous_snd.sub (continuous_fst.smul continuous_const))) }
  let G : ℝ×V→ℝ×V := fun z=>(z.1,f z)
  have H := (ContinuousLinearMap.fst ℝ ℝ V).hasStrictFDerivAt.prodMk hf
  have hD : (ContinuousLinearMap.fst ℝ ℝ V).prod
      (((ContinuousLinearMap.fst ℝ ℝ V).smulRight c)+
        (A : V→L[ℝ]V).comp (ContinuousLinearMap.snd ℝ ℝ V))=
      (L : (ℝ×V)→L[ℝ](ℝ×V)) := by
    apply ContinuousLinearMap.ext
    intro z
    rfl
  rw [hD] at H
  have hG : HasStrictFDerivAt G (L : (ℝ×V)→L[ℝ](ℝ×V)) 0 := H
  have hG0 : G 0=0 := by
    apply Prod.ext
    · rfl
    · exact hf0
  have hMap : Filter.map G (𝓝 (0 : ℝ×V))=𝓝 (0 : ℝ×V) := by
    simpa only [hG0] using hG.map_nhds_eq_of_equiv (f':=L)
  have hImage : G '' U∈𝓝 (0 : ℝ×V) := by
    rw [←hMap]
    exact Filter.image_mem_map hU
  have hLine : Tendsto (fun t : ℝ=>(t,(0 : V))) (𝓝 0) (𝓝 (0 : ℝ×V)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  filter_upwards [hLine.eventually hImage] with t ht
  obtain ⟨z,hz,hGz⟩ := ht
  have hFirst : z.1=t := congrArg Prod.fst hGz
  have hSecond : f z=0 := congrArg Prod.snd hGz
  refine ⟨z.2,?_,?_⟩
  · rw [←hFirst]
    exact hz
  · rw [←hFirst]
    exact hSecond


private theorem composed_parameter_zero_persists
    {S M V : Type*}
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (inc : V→L[ℝ]S) (L : M→L[ℝ]V)
    (K : S→L[ℝ]M) (Y : M) (Φ : S×ℝ→M) (A : V≃L[ℝ]V)
    (hΦ : HasStrictFDerivAt Φ (K.coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight Y)) 0)
    (hA : L.comp (K.comp inc)=(A : V→L[ℝ]V))
    (hZero : L (Φ 0)=0)
    (U : Set (ℝ×V)) (hU : U∈𝓝 (0 : ℝ×V)) :
    ∀ᶠt in 𝓝 (0 : ℝ),∃u : V,(t,u)∈U ∧ L (Φ (inc u,t))=0 := by
  let J : (ℝ×V)→L[ℝ](S×ℝ) :=
    (inc.comp (ContinuousLinearMap.snd ℝ ℝ V)).prod (ContinuousLinearMap.fst ℝ ℝ V)
  let F : ℝ×V→V := fun z=>L (Φ (inc z.2,z.1))
  have hJ0 : J 0=0 := map_zero J
  have hΦJ : HasStrictFDerivAt (fun z : ℝ×V=>Φ (J z))
      ((K.coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight Y)).comp J) 0 := by
    have H : HasStrictFDerivAt Φ (K.coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight Y)) (J 0) :=
      hJ0.symm ▸ hΦ
    exact H.comp 0 J.hasStrictFDerivAt
  have H := L.hasStrictFDerivAt.comp (0 : ℝ×V) hΦJ
  have hDerivative : L.comp
      ((K.coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight Y)).comp J)=
      (ContinuousLinearMap.fst ℝ ℝ V).smulRight (L Y)+
        (A : V→L[ℝ]V).comp (ContinuousLinearMap.snd ℝ ℝ V) := by
    apply ContinuousLinearMap.ext
    intro z
    have hAz : L (K (inc z.2))=A z.2 :=
      congrArg (fun L : V→L[ℝ]V=>L z.2) hA
    change L (K (inc z.2)+z.1 • Y)=z.1 • L Y+A z.2
    rw [map_add,map_smul,hAz,add_comm]
  rw [hDerivative] at H
  have hF : HasStrictFDerivAt F
      ((ContinuousLinearMap.fst ℝ ℝ V).smulRight (L Y)+
        (A : V→L[ℝ]V).comp (ContinuousLinearMap.snd ℝ ℝ V)) 0 := H
  have hF0 : F 0=0 := by
    change L (Φ (inc 0,0))=0
    rw [map_zero]
    exact hZero
  exact parameter_zero_persists F A (L Y) hF0 hF U hU

private theorem native_neumann_parameter_zero_persists
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n:ℝ)) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    let S := NativeMorreySobolevSpace n (q*q) ν
    let M := MorreyCoefficientSpace n (q*q) ν
    let V := SkewMeanZeroNativeMorreySpace n q ν e
    letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
    letI : SeminormedAddCommGroup V :=
      (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
    letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
    let N0 := (nativeNeumannMorreyResponse n hn ν hν hνn (q*q)).codRestrict
      (meanZeroNativeMorreySubmodule n (q*q) ν)
      (nativeNeumannMorreyResponse_mem_meanZero n hn ν hν hνn (q*q))
    let inc := (meanZeroNativeMorreySubmodule n (q*q) ν).subtypeL.comp
      (skewMeanZeroNativeMorreySubmodule n q ν e).subtypeL
    ∀(P : MeanZeroNativeMorreySpace n (q*q) ν→L[ℝ]V)
      (K : S→L[ℝ]M) (Y : M) (Φ : S×ℝ→M) (A : V≃L[ℝ]V),
      HasStrictFDerivAt Φ (K.coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight Y)) (0:S×ℝ) →
      P.comp (N0.comp (K.comp inc))=(A : V→L[ℝ]V) →
      P (N0 (Φ 0))=0 →
      ∀U : Set (ℝ×V),U∈𝓝 (0:ℝ×V) →
        ∀ᶠt in 𝓝 (0:ℝ),∃u : V,(t,u)∈U ∧ P (N0 (Φ (u.val.val,t)))=0 := by
  let S := NativeMorreySobolevSpace n (q*q) ν
  let M := MorreyCoefficientSpace n (q*q) ν
  let V := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup V :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : CompleteSpace V := skewMeanZeroNativeMorreySpace_completeSpace n q ν e
  let N0 := (nativeNeumannMorreyResponse n hn ν hν hνn (q*q)).codRestrict
    (meanZeroNativeMorreySubmodule n (q*q) ν)
    (nativeNeumannMorreyResponse_mem_meanZero n hn ν hν hνn (q*q))
  let inc : V→L[ℝ]S := (meanZeroNativeMorreySubmodule n (q*q) ν).subtypeL.comp
    (skewMeanZeroNativeMorreySubmodule n q ν e).subtypeL
  refine fun P K Y Φ A hJoint hComposition hZero U hU=>?_
  exact composed_parameter_zero_persists (S:=S) (M:=M) (V:=V)
    inc (P.comp N0) K Y Φ A hJoint hComposition hZero U hU

private theorem projected_neumann_zero_at_origin
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n:ℝ)) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (Z : MorreyCoefficientSpace n (q*q) ν)
    (Φ : NativeMorreySobolevSpace n (q*q) ν×ℝ→MorreyCoefficientSpace n (q*q) ν)
    (hBase : Φ 0=Z)
    (hNatural : ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (coefficientValue ν Z x i) (Dψ x i))=0) :
    let V := SkewMeanZeroNativeMorreySpace n q ν e
    letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
    letI : SeminormedAddCommGroup V :=
      (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
    letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
    let N := nativeNeumannMorreyResponse n hn ν hν hνn (q*q)
    let N0 := N.codRestrict (meanZeroNativeMorreySubmodule n (q*q) ν)
      (nativeNeumannMorreyResponse_mem_meanZero n hn ν hν hνn (q*q))
    ∀P : MeanZeroNativeMorreySpace n (q*q) ν→L[ℝ]V,P (N0 (Φ 0))=0 := by
  let V := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup V :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  let N := nativeNeumannMorreyResponse n hn ν hν hνn (q*q)
  let N0 := N.codRestrict (meanZeroNativeMorreySubmodule n (q*q) ν)
    (nativeNeumannMorreyResponse_mem_meanZero n hn ν hν hνn (q*q))
  refine fun P=>?_
  have hNZ : N Z=0 := nativeNeumannMorreyResponse_eq_zero_of_natural n hn ν hν hνn (q*q)
    Z (coefficientValue ν Z) (coefficientValue_memLp ν Z) (coefficientValue_class ν Z) hNatural
  have hNBase : N0 (Φ 0)=0 := Subtype.ext ((congrArg N hBase).trans hNZ)
  exact (congrArg P hNBase).trans P.map_zero

private theorem neumann_local_solutions_of_projected
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n:ℝ)) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    let S := NativeMorreySobolevSpace n (q*q) ν
    let M := MorreyCoefficientSpace n (q*q) ν
    let V := SkewMeanZeroNativeMorreySpace n q ν e
    letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
    letI : SeminormedAddCommGroup V :=
      (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
    letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
    let N := nativeNeumannMorreyResponse n hn ν hν hνn (q*q)
    let N0 := N.codRestrict (meanZeroNativeMorreySubmodule n (q*q) ν)
      (nativeNeumannMorreyResponse_mem_meanZero n hn ν hν hνn (q*q))
    ∀(P : MeanZeroNativeMorreySpace n (q*q) ν→L[ℝ]V),
      (∀W : V,P W.val=W) → ∀(Φ : S×ℝ→M) (U : Set (ℝ×V)),
      (∀ᶠt in 𝓝 (0:ℝ),∃u : V,(t,u)∈U ∧ P (N0 (Φ (u.val.val,t)))=0) →
      (∀(u : V) (t : ℝ),∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
        skewMorreyCoordinateConstraint q e (coefficientValue ν (Φ (u.val.val,t)) x i)=0) →
      ∀ᶠt in 𝓝 (0:ℝ),∃u : V,(t,u)∈U ∧ N (Φ (u.val.val,t))=0 ∧
        ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (coefficientValue ν (Φ (u.val.val,t)) x i) (Dψ x i))
            (ball (0:Domain n) 1) volume ∧
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ
            (coefficientValue ν (Φ (u.val.val,t)) x i) (Dψ x i))=0 := by
  let S := NativeMorreySobolevSpace n (q*q) ν
  let M := MorreyCoefficientSpace n (q*q) ν
  let V := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup V :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  let N := nativeNeumannMorreyResponse n hn ν hν hνn (q*q)
  refine fun P hP Φ U hLocal hSkew=>?_
  filter_upwards [hLocal] with t ht
  obtain ⟨u,hu,hFu⟩ := ht
  have hTrue : N (Φ (u.val.val,t))=0 :=
    (projection_neumann_zero_iff n hn ν hν hνn q e P hP (Φ (u.val.val,t)) (hSkew u t)).mp hFu
  exact ⟨u,hu,hTrue,natural_of_neumann_zero n hn ν hν hνn (q*q) (Φ (u.val.val,t)) hTrue⟩

private theorem neumann_perturbation_of_actual_equivalence
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (q : ℕ) (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    let ν : ℝ := (n:ℝ)-2+γ
    let S := NativeMorreySobolevSpace n (q*q) ν
    let M := MorreyCoefficientSpace n (q*q) ν
    let V := SkewMeanZeroNativeMorreySpace n q ν e
    letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
    letI : SeminormedAddCommGroup V :=
      (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
    letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
    let value : S→Domain n→Ambient (q*q) := fun H=>nativeMorreyMapClass (n:=n) (q:=q*q) ν H
    let field : M→Domain n→Gradient n (q*q) := fun F x i=>WithLp.toLp 2
      (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
    let D : S→L[ℝ]M := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    let Exp : S→S := matrixNativeMorreyExp n hn γ hγ hγTwo q
      e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply e.symm_apply_apply
    ∀(Z Y : M),
      (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (field Z x i) (Dψ x i))=0) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
        star (e (field Z x i))= -(e (field Z x i))) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
        star (e (field Y x i))= -(e (field Y x i))) →
      ∀(Φ : S×ℝ→M) (K : S→L[ℝ]M),
        (∀p : S×ℝ,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
          field (Φ p) x=fun i=>e.symm
            (e (value (Exp (-p.1)) x)*e (field (D (Exp p.1)) x i)+
              (e (value (Exp (-p.1)) x)*(e (field Z x i)+p.2 • e (field Y x i)))*
                e (value (Exp p.1) x))) →
        HasStrictFDerivAt Φ (K.coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight Y)) (0:S×ℝ) →
        (∀H : S,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
          field (K H) x=fun i=>field (D H) x i+
            e.symm (e (field Z x i)*e (value H x)-e (value H x)*e (field Z x i))) →
        (∀t : ℝ,Φ (0,t)=Z+t • Y) →
        ∀(P : MeanZeroNativeMorreySpace n (q*q) ν→L[ℝ]V),
          (∀W : V,P W.val=W) →
          ∀(A : V≃L[ℝ]V),
            (∀(X : V) (ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
              MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
              (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ
                (field (D (A X).val.val) x i) (Dψ x i))=
              ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ
                (field (D X.val.val) x i+morreyMatrixCommutator q e (field Z x i) (value X.val.val x)) (Dψ x i)) →
        ∀U : Set (ℝ×V),U∈𝓝 (0 : ℝ×V) →
          ∀ᶠt in 𝓝 (0 : ℝ),∃u : V,(t,u)∈U ∧
            nativeNeumannMorreyResponse n hn ν
              (by
                have hnR : (2:ℝ)≤n := by exact_mod_cast hn
                dsimp only [ν]
                linarith)
              (by dsimp only [ν];linarith) (q*q) (Φ (u.val.val,t))=0 ∧
            ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
              MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
              IntegrableOn (fun x=>∑i : Fin n,inner ℝ (field (Φ (u.val.val,t)) x i) (Dψ x i))
                (ball (0:Domain n) 1) volume ∧
              (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (field (Φ (u.val.val,t)) x i) (Dψ x i))=0 := by
  let ν : ℝ := (n:ℝ)-2+γ
  let S := NativeMorreySobolevSpace n (q*q) ν
  let M := MorreyCoefficientSpace n (q*q) ν
  let V := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup V :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hν : 0≤ν := by dsimp only [ν];linarith
  have hνn : ν<(n:ℝ) := by dsimp only [ν];linarith
  refine fun Z Y hNatural hZ hY Φ K hFormula hJoint hK hBaseAll P hP A hA=>?_
  let N := nativeNeumannMorreyResponse n hn ν hν hνn (q*q)
  let N0 : M→L[ℝ]MeanZeroNativeMorreySpace n (q*q) ν :=
    N.codRestrict (meanZeroNativeMorreySubmodule n (q*q) ν)
      (nativeNeumannMorreyResponse_mem_meanZero n hn ν hν hνn (q*q))
  let inc : V→L[ℝ]S := (meanZeroNativeMorreySubmodule n (q*q) ν).subtypeL.comp
    (skewMeanZeroNativeMorreySubmodule n q ν e).subtypeL
  have hComposition : P.comp (N0.comp (K.comp inc))=(A : V→L[ℝ]V) := by
    apply skew_linearized_neumann_composition_eq n hn ν hν hνn q e (coefficientValue ν Z) hZ K
    · exact hK
    · exact hP
    · intro X ψ Dψ hψ
      exact hA X ψ Dψ hψ
  have hBase0 : Φ (0 : S×ℝ)=Z := by
    change Φ (0,0)=Z
    have H : Φ (0,0)=Z+(0:ℝ) • Y := hBaseAll 0
    exact H.trans (by rw [zero_smul,add_zero])
  have hZero : P (N0 (Φ 0))=0 :=
    projected_neumann_zero_at_origin n hn ν hν hνn q e Z Φ hBase0 hNatural P
  intro U hU
  have hLocal := native_neumann_parameter_zero_persists n hn ν hν hνn q e
    P K Y Φ A hJoint hComposition hZero U hU
  exact neumann_local_solutions_of_projected n hn ν hν hνn q e P hP Φ U hLocal
    (exponential_flux_skew n hn γ hγ hγTwo q e Z Y Φ hFormula hZ hY)


private theorem actual_neumann_perturbation_from_characteristics
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (q : ℕ) (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    let ν : ℝ := (n:ℝ)-2+γ
    let S := NativeMorreySobolevSpace n (q*q) ν
    let M := MorreyCoefficientSpace n (q*q) ν
    let V := SkewMeanZeroNativeMorreySpace n q ν e
    letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
    letI : SeminormedAddCommGroup V :=
      (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
    letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
    let value : S→Domain n→Ambient (q*q) := fun H=>nativeMorreyMapClass (n:=n) (q:=q*q) ν H
    let field : M→Domain n→Gradient n (q*q) := fun F x i=>WithLp.toLp 2
      (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
    let D : S→L[ℝ]M := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    let Exp : S→S := matrixNativeMorreyExp n hn γ hγ hγTwo q
      e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply e.symm_apply_apply
    ∃ε : ℝ,0<ε ∧ ∀(Z Y : M) (η : ℝ),
      (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (field Z x i) (Dψ x i))=0) →
      0≤η → η≤ε → criticalGradientMorreySquare (field Z) (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
        star (e (field Z x i))= -(e (field Z x i))) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
        star (e (field Y x i))= -(e (field Y x i))) →
      ∀(Φ : S×ℝ→M) (K : S→L[ℝ]M),
        (∀p : S×ℝ,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
          field (Φ p) x=fun i=>e.symm
            (e (value (Exp (-p.1)) x)*e (field (D (Exp p.1)) x i)+
              (e (value (Exp (-p.1)) x)*(e (field Z x i)+p.2 • e (field Y x i)))*
                e (value (Exp p.1) x))) →
        HasStrictFDerivAt Φ (K.coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight Y)) (0:S×ℝ) →
        (∀H : S,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
          field (K H) x=fun i=>field (D H) x i+
            e.symm (e (field Z x i)*e (value H x)-e (value H x)*e (field Z x i))) →
        (∀t : ℝ,Φ (0,t)=Z+t • Y) →
        ∀U : Set (ℝ×V),U∈𝓝 (0 : ℝ×V) →
          ∀ᶠt in 𝓝 (0 : ℝ),∃u : V,(t,u)∈U ∧
            nativeNeumannMorreyResponse n hn ν
              (by
                have hnR : (2:ℝ)≤n := by exact_mod_cast hn
                dsimp only [ν]
                linarith)
              (by dsimp only [ν];linarith) (q*q) (Φ (u.val.val,t))=0 ∧
            ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
              MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
              IntegrableOn (fun x=>∑i : Fin n,inner ℝ (field (Φ (u.val.val,t)) x i) (Dψ x i))
                (ball (0:Domain n) 1) volume ∧
              (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (field (Φ (u.val.val,t)) x i) (Dψ x i))=0 := by
  let ν : ℝ := (n:ℝ)-2+γ
  let S := NativeMorreySobolevSpace n (q*q) ν
  let M := MorreyCoefficientSpace n (q*q) ν
  let V := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup V :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hν : 0≤ν := by dsimp only [ν];linarith
  have hνn : ν<(n:ℝ) := by dsimp only [ν];linarith
  have hInv := exists_unique_skew_linearized_neumann_inverse n hn γ hγ hγTwo q e
  let ε := hInv.choose
  have hε : 0<ε := hInv.choose_spec.1
  refine ⟨ε,hε,?_⟩
  intro Z Y η hNatural hη hηle hCritical hZ hY Φ K hFormula hJoint hK hBaseAll
  have hAData := hInv.choose_spec.2 (coefficientValue ν Z) η (coefficientValue_memLp ν Z)
    hNatural hη hηle hCritical hZ
  let A := hAData.choose
  have hA := hAData.choose_spec.1.1
  have hProject := (exists_unique_bounded_skew_native_projection n hn γ hγ hγTwo).choose_spec.2 q e
  let P := hProject.choose
  have hP : ∀W : V,P W.val=W := hProject.choose_spec.1.2.2.1
  exact neumann_perturbation_of_actual_equivalence n hn γ hγ hγTwo q e
    Z Y hNatural hZ hY Φ K hFormula hJoint hK hBaseAll P hP A
      (fun X ψ Dψ hψ=>(hA X ψ Dψ hψ).2.2)


/-- Original stronger-class natural skew coefficients with small critical
norm admit actual nearby exponential Coulomb perturbations. Every chosen
neighborhood in the same original parameter/skew Banach space is retained. -/
theorem exists_small_native_coulomb_perturbations
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (q : ℕ) (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    let ν : ℝ := (n:ℝ)-2+γ
    let S := NativeMorreySobolevSpace n (q*q) ν
    let M := MorreyCoefficientSpace n (q*q) ν
    let V := SkewMeanZeroNativeMorreySpace n q ν e
    letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
    letI : SeminormedAddCommGroup V :=
      (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
    letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
    let value : S→Domain n→Ambient (q*q) := fun H=>nativeMorreyMapClass (n:=n) (q:=q*q) ν H
    let field : M→Domain n→Gradient n (q*q) := fun F x i=>WithLp.toLp 2
      (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
    let D : S→L[ℝ]M := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    let Exp : S→S := matrixNativeMorreyExp n hn γ hγ hγTwo q
      e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply e.symm_apply_apply
    ∃ε : ℝ,0<ε ∧ ∀(Z Y : M) (η : ℝ),
      (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (field Z x i) (Dψ x i))=0) →
      0≤η → η≤ε → criticalGradientMorreySquare (field Z) (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
        star (e (field Z x i))= -(e (field Z x i))) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
        star (e (field Y x i))= -(e (field Y x i))) →
      ∃Φ : S×ℝ→M,
        (∀p : S×ℝ,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
          field (Φ p) x=fun i=>e.symm
            (e (value (Exp (-p.1)) x)*e (field (D (Exp p.1)) x i)+
              (e (value (Exp (-p.1)) x)*(e (field Z x i)+p.2 • e (field Y x i)))*
                e (value (Exp p.1) x))) ∧
        (∀p : S×ℝ,AnalyticAt ℝ Φ p) ∧
        (∀t : ℝ,Φ (0,t)=Z+t • Y) ∧
        ∀U : Set (ℝ×V),U∈𝓝 (0 : ℝ×V) →
          ∀ᶠt in 𝓝 (0 : ℝ),∃u : V,(t,u)∈U ∧
            nativeNeumannMorreyResponse n hn ν
              (by
                have hnR : (2:ℝ)≤n := by exact_mod_cast hn
                dsimp only [ν]
                linarith)
              (by dsimp only [ν];linarith) (q*q) (Φ (u.val.val,t))=0 ∧
            ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
              MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
              IntegrableOn (fun x=>∑i : Fin n,inner ℝ (field (Φ (u.val.val,t)) x i) (Dψ x i))
                (ball (0:Domain n) 1) volume ∧
              (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (field (Φ (u.val.val,t)) x i) (Dψ x i))=0 := by
  let ν : ℝ := (n:ℝ)-2+γ
  let S := NativeMorreySobolevSpace n (q*q) ν
  let M := MorreyCoefficientSpace n (q*q) ν
  let V := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup V :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  have hLocal := actual_neumann_perturbation_from_characteristics n hn γ hγ hγTwo q e
  let ε := hLocal.choose
  have hε : 0<ε := hLocal.choose_spec.1
  refine ⟨ε,hε,?_⟩
  intro Z Y η hNatural hη hηle hCritical hZ hY
  have hFlux := existsUnique_native_matrix_coulomb_flux n hn γ hγ hγTwo q
    e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply e.symm_apply_apply Z Y
  let Φ := hFlux.choose
  have hΦ := hFlux.choose_spec.1
  refine ⟨Φ,hΦ.1,hΦ.2.1,hΦ.2.2.2.2.2,?_⟩
  let K := hΦ.2.2.1.choose
  have hJoint := hΦ.2.2.1.choose_spec.2.1
  have hK := hΦ.2.2.1.choose_spec.2.2
  exact hLocal.choose_spec.2 Z Y η hNatural hη hηle hCritical hZ hY Φ K hΦ.1 hJoint hK hΦ.2.2.2.2.2

private theorem actual_neumann_perturbation_from_characteristics_effective
    (n : ℕ) (hn : 2≤n)
    (q : ℕ) (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖e.symm T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2) :
    let ν : ℝ := (n:ℝ)-2+(1 : ℝ)
    let S := NativeMorreySobolevSpace n (q*q) ν
    let M := MorreyCoefficientSpace n (q*q) ν
    let V := SkewMeanZeroNativeMorreySpace n q ν e
    letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
    letI : SeminormedAddCommGroup V :=
      (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
    letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
    let value : S→Domain n→Ambient (q*q) := fun H=>nativeMorreyMapClass (n:=n) (q:=q*q) ν H
    let field : M→Domain n→Gradient n (q*q) := fun F x i=>WithLp.toLp 2
      (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
    let D : S→L[ℝ]M := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    let Exp : S→S := matrixNativeMorreyExp n hn (1 : ℝ) (by norm_num) (by norm_num) q
      e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply e.symm_apply_apply
    ∀(Z Y : M) (η : ℝ),
      (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (field Z x i) (Dψ x i))=0) →
      0≤η → η≤(effectiveSkewNeumannAmplitude n q : ℝ) → criticalGradientMorreySquare (field Z) (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
        star (e (field Z x i))= -(e (field Z x i))) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
        star (e (field Y x i))= -(e (field Y x i))) →
      ∀(Φ : S×ℝ→M) (K : S→L[ℝ]M),
        (∀p : S×ℝ,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
          field (Φ p) x=fun i=>e.symm
            (e (value (Exp (-p.1)) x)*e (field (D (Exp p.1)) x i)+
              (e (value (Exp (-p.1)) x)*(e (field Z x i)+p.2 • e (field Y x i)))*
                e (value (Exp p.1) x))) →
        HasStrictFDerivAt Φ (K.coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight Y)) (0:S×ℝ) →
        (∀H : S,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
          field (K H) x=fun i=>field (D H) x i+
            e.symm (e (field Z x i)*e (value H x)-e (value H x)*e (field Z x i))) →
        (∀t : ℝ,Φ (0,t)=Z+t • Y) →
        ∀U : Set (ℝ×V),U∈𝓝 (0 : ℝ×V) →
          ∀ᶠt in 𝓝 (0 : ℝ),∃u : V,(t,u)∈U ∧
            nativeNeumannMorreyResponse n hn ν
              (by
                have hnR : (2:ℝ)≤n := by exact_mod_cast hn
                dsimp only [ν]
                linarith)
              (by dsimp only [ν];linarith) (q*q) (Φ (u.val.val,t))=0 ∧
            ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
              MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
              IntegrableOn (fun x=>∑i : Fin n,inner ℝ (field (Φ (u.val.val,t)) x i) (Dψ x i))
                (ball (0:Domain n) 1) volume ∧
              (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (field (Φ (u.val.val,t)) x i) (Dψ x i))=0 := by
  have hγ : 0 < (1 : ℝ) := by norm_num
  have hγTwo : (1 : ℝ) < 2 := by norm_num
  let ν : ℝ := (n:ℝ)-2+(1 : ℝ)
  let S := NativeMorreySobolevSpace n (q*q) ν
  let M := MorreyCoefficientSpace n (q*q) ν
  let V := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup V :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hν : 0≤ν := by dsimp only [ν];linarith
  have hνn : ν<(n:ℝ) := by dsimp only [ν];linarith
  have hInv := effective_unique_skew_linearized_neumann_inverse_one n hn q e hE
  change ∀ (Z Y : M) (η : ℝ), _
  intro Z Y η hNatural hη hηle hCritical hZ hY Φ K hFormula hJoint hK hBaseAll
  have hAData := hInv (coefficientValue ν Z) η (coefficientValue_memLp ν Z)
    hNatural hη hηle hCritical hZ
  let A := hAData.choose
  have hA := hAData.choose_spec.1.1
  have hProject := (exists_unique_bounded_skew_native_projection n hn (1 : ℝ) hγ hγTwo).choose_spec.2 q e
  let P := hProject.choose
  have hP : ∀W : V,P W.val=W := hProject.choose_spec.1.2.2.1
  exact neumann_perturbation_of_actual_equivalence n hn (1 : ℝ) hγ hγTwo q e
    Z Y hNatural hZ hY Φ K hFormula hJoint hK hBaseAll P hP A
      (fun X ψ Dψ hψ=>(hA X ψ Dψ hψ).2.2)


/-- Original stronger-class natural skew coefficients with small critical
norm admit actual nearby exponential Coulomb perturbations. Every chosen
neighborhood in the same original parameter/skew Banach space is retained. -/
theorem effective_small_native_coulomb_perturbations
    (n : ℕ) (hn : 2≤n)
    (q : ℕ) (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖e.symm T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2) :
    let ν : ℝ := (n:ℝ)-2+(1 : ℝ)
    let S := NativeMorreySobolevSpace n (q*q) ν
    let M := MorreyCoefficientSpace n (q*q) ν
    let V := SkewMeanZeroNativeMorreySpace n q ν e
    letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
    letI : SeminormedAddCommGroup V :=
      (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
    letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
    let value : S→Domain n→Ambient (q*q) := fun H=>nativeMorreyMapClass (n:=n) (q:=q*q) ν H
    let field : M→Domain n→Gradient n (q*q) := fun F x i=>WithLp.toLp 2
      (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
    let D : S→L[ℝ]M := nativeMorreyGradientClass (n:=n) (q:=q*q) ν
    let Exp : S→S := matrixNativeMorreyExp n hn (1 : ℝ) (by norm_num) (by norm_num) q
      e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply e.symm_apply_apply
    ∀(Z Y : M) (η : ℝ),
      (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (field Z x i) (Dψ x i))=0) →
      0≤η → η≤(effectiveSkewNeumannAmplitude n q : ℝ) → criticalGradientMorreySquare (field Z) (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
        star (e (field Z x i))= -(e (field Z x i))) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
        star (e (field Y x i))= -(e (field Y x i))) →
      ∃Φ : S×ℝ→M,
        (∀p : S×ℝ,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
          field (Φ p) x=fun i=>e.symm
            (e (value (Exp (-p.1)) x)*e (field (D (Exp p.1)) x i)+
              (e (value (Exp (-p.1)) x)*(e (field Z x i)+p.2 • e (field Y x i)))*
                e (value (Exp p.1) x))) ∧
        (∀p : S×ℝ,AnalyticAt ℝ Φ p) ∧
        (∀t : ℝ,Φ (0,t)=Z+t • Y) ∧
        ∀U : Set (ℝ×V),U∈𝓝 (0 : ℝ×V) →
          ∀ᶠt in 𝓝 (0 : ℝ),∃u : V,(t,u)∈U ∧
            nativeNeumannMorreyResponse n hn ν
              (by
                have hnR : (2:ℝ)≤n := by exact_mod_cast hn
                dsimp only [ν]
                linarith)
              (by dsimp only [ν];linarith) (q*q) (Φ (u.val.val,t))=0 ∧
            ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
              MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
              IntegrableOn (fun x=>∑i : Fin n,inner ℝ (field (Φ (u.val.val,t)) x i) (Dψ x i))
                (ball (0:Domain n) 1) volume ∧
              (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (field (Φ (u.val.val,t)) x i) (Dψ x i))=0 := by
  have hγ : 0 < (1 : ℝ) := by norm_num
  have hγTwo : (1 : ℝ) < 2 := by norm_num
  let ν : ℝ := (n:ℝ)-2+(1 : ℝ)
  let S := NativeMorreySobolevSpace n (q*q) ν
  let M := MorreyCoefficientSpace n (q*q) ν
  let V := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup V := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup V :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ V := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  have hLocal := actual_neumann_perturbation_from_characteristics_effective n hn q e hE
  change ∀ (Z Y : M) (η : ℝ), _
  intro Z Y η hNatural hη hηle hCritical hZ hY
  have hFlux := existsUnique_native_matrix_coulomb_flux n hn (1 : ℝ) hγ hγTwo q
    e.symm.toContinuousLinearMap e.toContinuousLinearMap e.apply_symm_apply e.symm_apply_apply Z Y
  let Φ := hFlux.choose
  have hΦ := hFlux.choose_spec.1
  refine ⟨Φ,hΦ.1,hΦ.2.1,hΦ.2.2.2.2.2,?_⟩
  let K := hΦ.2.2.1.choose
  have hJoint := hΦ.2.2.1.choose_spec.2.1
  have hK := hΦ.2.2.1.choose_spec.2.2
  exact hLocal Z Y η hNatural hη hηle hCritical hZ hY Φ K hΦ.1 hJoint hK hΦ.2.2.2.2.2

end StationaryHarmonicMaps.Analysis
end
