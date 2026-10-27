module

public import StationaryHarmonicMaps.Analysis.SkewLinearizedNeumann
public import StationaryHarmonicMaps.Analysis.SkewMeanZeroNativeMorreyProjection
public import StationaryHarmonicMaps.Analysis.NativeNeumannMorreyRaw
import StationaryHarmonicMaps.Analysis.HilbertSchmidtDecoding

/-!
# The actual projected Neumann linearization

The original derivative-plus-commutator flux is sent through the same native
Neumann operator and the genuine skew projection. Its value already belongs
to the original closed skew kernel, and its native tests identify the actual
linearized equivalence.
-/

public section
open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal
noncomputable section
namespace StationaryHarmonicMaps.Analysis

private abbrev mapValue {n q : ℕ} (ν : ℝ) (X : NativeMorreySobolevSpace n q ν) :
    Domain n→Ambient q := nativeMorreyMapClass (n:=n) (q:=q) ν X

private abbrev gradientValue {n q : ℕ} (ν : ℝ) (X : NativeMorreySobolevSpace n q ν) :
    Domain n→Gradient n q := fun x i=>WithLp.toLp 2
      (fun j : Fin q=>nativeMorreyHSClass (n:=n) (q:=q) ν X x (finProdFinEquiv (i,j)))

private abbrev coefficientValue {n q : ℕ} (ν : ℝ) (F : MorreyCoefficientSpace n q ν) :
    Domain n→Gradient n q := fun x i=>WithLp.toLp 2
      (fun j : Fin q=>morreyCoefficientRecover (n:=n) (q:=q) ν F x (finProdFinEquiv (i,j)))

private theorem coefficientValue_memLp {n q : ℕ} (ν : ℝ) (F : MorreyCoefficientSpace n q ν) :
    ∀i,MemLp (fun x=>coefficientValue ν F x i) 2 (volume.restrict (ball (0:Domain n) 1)) :=
  fun i=>memLp_hs_unflatten _ (Lp.memLp (morreyCoefficientRecover (n:=n) (q:=q) ν F)) i

private theorem coefficientValue_class {n q : ℕ} (ν : ℝ) (F : MorreyCoefficientSpace n q ν) :
    morreyCoefficientRecover (n:=n) (q:=q) ν F=
      hsUnitBallL2Class (coefficientValue ν F) (coefficientValue_memLp ν F) := by
  symm
  apply Lp.ext
  exact (hsUnitBallL2Class_ae (coefficientValue ν F) (coefficientValue_memLp ν F)).trans
    (Eventually.of_forall fun x=>hs_flatten_unflatten (morreyCoefficientRecover (n:=n) (q:=q) ν F x))

private theorem canonical_native {n q : ℕ} (ν : ℝ) (X : MeanZeroNativeMorreySpace n q ν) :
    MemW12 (ballDomain (0:Domain n) 1) (mapValue ν X.val) (gradientValue ν X.val) := by
  obtain ⟨u,Du,hu,_hMean,hMap,hGrad,_hGrowth⟩ := exists_raw_native_of_meanZeroNativeMorrey ν X
  have hUAE : mapValue ν X.val=ᵐ[volume.restrict (ball (0:Domain n) 1)]u := by
    change ((nativeMorreyMapClass (n:=n) (q:=q) ν) X.val : Domain n→Ambient q)=ᵐ[_]u
    rw [hMap]
    exact hu.2.1.coeFn_toLp
  have hDAE : gradientValue ν X.val=ᵐ[volume.restrict (ball (0:Domain n) 1)]Du := by
    have hHS := hsUnitBallL2Class_ae Du hu.2.2
    rw [←hGrad] at hHS
    filter_upwards [hHS] with x hx
    funext i
    ext j
    have H := congrArg (fun z : Ambient (n*q)=>z (finProdFinEquiv (i,j))) hx
    simpa only [hsFlatten,gradientValue,finProdFinEquiv.symm_apply_apply] using H
  exact hu.congr_ae hUAE.symm hDAE.symm

private theorem canonical_skew {n q : ℕ} (ν : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (X : SkewMeanZeroNativeMorreySpace n q ν e) :
    (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (e (mapValue ν X.val.val x))=-(e (mapValue ν X.val.val x))) ∧
    (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,
      star (e (gradientValue ν X.val.val x i))=-(e (gradientValue ν X.val.val x i))) := by
  have hData := exists_raw_native_of_skewMeanZeroNativeMorrey ν e X
  let u := hData.choose
  let Du := hData.choose_spec.choose
  let hu := hData.choose_spec.choose_spec.choose
  have hChar := hData.choose_spec.choose_spec.choose_spec
  have hMap := hChar.2.1
  have hGrad := hChar.2.2.1
  have hU := hChar.2.2.2.1
  have hD := hChar.2.2.2.2.1
  have hUAE : mapValue ν X.val.val=ᵐ[volume.restrict (ball (0:Domain n) 1)]u := by
    change ((nativeMorreyMapClass (n:=n) (q:=q*q) ν) X.val.val : Domain n→Ambient (q*q))=ᵐ[_]u
    rw [hMap]
    exact hu.2.1.coeFn_toLp
  have hDAE : gradientValue ν X.val.val=ᵐ[volume.restrict (ball (0:Domain n) 1)]Du := by
    have hHS := hsUnitBallL2Class_ae Du hu.2.2
    rw [←hGrad] at hHS
    filter_upwards [hHS] with x hx
    funext i
    ext j
    have H := congrArg (fun z : Ambient (n*(q*q))=>z (finProdFinEquiv (i,j))) hx
    simpa only [hsFlatten,gradientValue,finProdFinEquiv.symm_apply_apply] using H
  constructor
  · filter_upwards [hUAE,hU] with x hx hux
    rw [hx]
    exact hux
  · filter_upwards [hDAE,hD] with x hx hdx
    intro i
    rw [congrFun hx i]
    exact hdx i

private theorem forcing_fixed_kernel {n q : ℕ} (ν : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (Z : Domain n→Gradient n (q*q))
    (hZ : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,star (e (Z x i))=-(e (Z x i)))
    (K : NativeMorreySobolevSpace n (q*q) ν→L[ℝ]MorreyCoefficientSpace n (q*q) ν)
    (hK : ∀H : NativeMorreySobolevSpace n (q*q) ν,
      ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),coefficientValue ν (K H) x=
        fun i=>gradientValue ν H x i+morreyMatrixCommutator q e (Z x i) (mapValue ν H x))
    (X : SkewMeanZeroNativeMorreySpace n q ν e) :
    ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,
      skewMorreyCoordinateConstraint q e (coefficientValue ν (K X.val.val) x i)=0 := by
  have hX := canonical_skew ν e X
  filter_upwards [hK X.val.val,hZ,hX.1,hX.2] with x hx hz hu hd
  intro i
  rw [congrFun hx i,map_add]
  have hD := (skewMorreyCoordinateConstraint_eq_zero_iff q e _).mpr (hd i)
  have hB := morreyMatrixCommutator_preserves_skew_kernel q e (Z x i) (mapValue ν X.val.val x)
    (hz i) ((skewMorreyCoordinateConstraint_eq_zero_iff q e _).mpr hu)
  exact (congrArg₂ (·+·) hD hB).trans (zero_add _)

private theorem projected_response_tests
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n:ℝ)) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (Z : Domain n→Gradient n (q*q))
    (hZ : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,star (e (Z x i))=-(e (Z x i)))
    (K : NativeMorreySobolevSpace n (q*q) ν→L[ℝ]MorreyCoefficientSpace n (q*q) ν)
    (hK : ∀H : NativeMorreySobolevSpace n (q*q) ν,
      ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),coefficientValue ν (K H) x=
        fun i=>gradientValue ν H x i+morreyMatrixCommutator q e (Z x i) (mapValue ν H x)) :
    let S := SkewMeanZeroNativeMorreySpace n q ν e
    letI : NormedAddCommGroup S := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
    letI : SeminormedAddCommGroup S :=
      (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
    letI : NormedSpace ℝ S := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
    ∀(P : MeanZeroNativeMorreySpace n (q*q) ν→L[ℝ]S),
      (∀Y : S,P Y.val=Y) →
      ∀(X : S) (ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        let W : MeanZeroNativeMorreySpace n (q*q) ν :=
          ⟨nativeNeumannMorreyResponse n hn ν hν hνn (q*q) (K X.val.val),
            nativeNeumannMorreyResponse_mem_meanZero n hn ν hν hνn (q*q) (K X.val.val)⟩
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν (P W).val.val x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ
          (gradientValue ν X.val.val x i+morreyMatrixCommutator q e (Z x i) (mapValue ν X.val.val x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν (P W).val.val x i) (Dψ x i))=
          ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ
            (gradientValue ν X.val.val x i+morreyMatrixCommutator q e (Z x i) (mapValue ν X.val.val x)) (Dψ x i) := by
  let S := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup S := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup S :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ S := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  refine fun P hP X ψ Dψ hψ=>?_
  let F := K X.val.val
  let W : MeanZeroNativeMorreySpace n (q*q) ν :=
    ⟨nativeNeumannMorreyResponse n hn ν hν hνn (q*q) F,
      nativeNeumannMorreyResponse_mem_meanZero n hn ν hν hνn (q*q) F⟩
  have hW : W∈skewMeanZeroNativeMorreySubmodule n q ν e :=
    nativeNeumannMorreyResponse_preserves_fixed_kernel n hn ν hν hνn (q*q) (q*q)
      (skewMorreyCoordinateConstraint q e) F (coefficientValue ν F)
      (coefficientValue_memLp ν F) (coefficientValue_class ν F)
      (forcing_fixed_kernel ν e Z hZ K hK X)
  let Y : S := ⟨W,hW⟩
  have hValue : P W=Y := hP Y
  have hNative := canonical_native ν (P W).val
  have hMapEq : nativeMorreyMapClass (n:=n) (q:=q*q) ν (P W).val.val=
      nativeMorreyMapClass (n:=n) (q:=q*q) ν W.val :=
    congrArg (fun U : S=>nativeMorreyMapClass (n:=n) (q:=q*q) ν U.val.val) hValue
  have hMap : nativeMorreyMapClass (n:=n) (q:=q*q) ν W.val=
      hNative.2.1.toLp (mapValue ν (P W).val.val) := hMapEq.symm.trans
    (Lp.toLp_coeFn (nativeMorreyMapClass (n:=n) (q:=q*q) ν (P W).val.val) hNative.2.1).symm
  have hTests := nativeNeumannMorreyResponse_raw_tests n hn ν hν hνn (q*q)
    F (coefficientValue ν F) (coefficientValue_memLp ν F) (coefficientValue_class ν F)
    (mapValue ν (P W).val.val) (gradientValue ν (P W).val.val) hNative hMap ψ Dψ hψ
  have hAE : (fun x=>∑i : Fin n,inner ℝ (coefficientValue ν F x i) (Dψ x i))=ᵐ[
      volume.restrict (ball (0:Domain n) 1)]
      (fun x=>∑i : Fin n,inner ℝ
        (gradientValue ν X.val.val x i+morreyMatrixCommutator q e (Z x i) (mapValue ν X.val.val x)) (Dψ x i)) := by
    filter_upwards [hK X.val.val] with x hx
    exact congrArg (fun G : Gradient n (q*q)=>∑i : Fin n,inner ℝ (G i) (Dψ x i)) hx
  exact ⟨hTests.1,hTests.2.1.congr hAE,hTests.2.2.trans (integral_congr_ae hAE)⟩

/-- The actual Neumann response of the fully characterized original flux
linearization, followed by the genuine skew retraction, is the same bounded
map as the original variational linearized equivalence. -/
theorem skew_linearized_neumann_composition_eq
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n:ℝ)) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (Z : Domain n→Gradient n (q*q))
    (hZ : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,star (e (Z x i))=-(e (Z x i)))
    (K : NativeMorreySobolevSpace n (q*q) ν→L[ℝ]MorreyCoefficientSpace n (q*q) ν) :
    let S := SkewMeanZeroNativeMorreySpace n q ν e
    letI : NormedAddCommGroup S := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
    letI : SeminormedAddCommGroup S :=
      (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
    letI : NormedSpace ℝ S := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
    let value : NativeMorreySobolevSpace n (q*q) ν→Domain n→Ambient (q*q) :=
      fun H=>nativeMorreyMapClass (n:=n) (q:=q*q) ν H
    let gradient : NativeMorreySobolevSpace n (q*q) ν→Domain n→Gradient n (q*q) :=
      fun H x i=>WithLp.toLp 2 (fun j : Fin (q*q)=>nativeMorreyHSClass (n:=n) (q:=q*q) ν H x (finProdFinEquiv (i,j)))
    let field : MorreyCoefficientSpace n (q*q) ν→Domain n→Gradient n (q*q) :=
      fun F x i=>WithLp.toLp 2 (fun j : Fin (q*q)=>morreyCoefficientRecover (n:=n) (q:=q*q) ν F x (finProdFinEquiv (i,j)))
    (∀H : NativeMorreySobolevSpace n (q*q) ν,∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
      field (K H) x=fun i=>gradient H x i+morreyMatrixCommutator q e (Z x i) (value H x)) →
    ∀(P : MeanZeroNativeMorreySpace n (q*q) ν→L[ℝ]S),
      (∀Y : S,P Y.val=Y) → ∀(A : S≃L[ℝ]S),
      (∀(X : S) (ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradient (A X).val.val x i) (Dψ x i))=
          ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ
            (gradient X.val.val x i+morreyMatrixCommutator q e (Z x i) (value X.val.val x)) (Dψ x i)) →
      let N₀ := (nativeNeumannMorreyResponse n hn ν hν hνn (q*q)).codRestrict
        (meanZeroNativeMorreySubmodule n (q*q) ν)
        (nativeNeumannMorreyResponse_mem_meanZero n hn ν hν hνn (q*q))
      let inc := (meanZeroNativeMorreySubmodule n (q*q) ν).subtypeL.comp
        (skewMeanZeroNativeMorreySubmodule n q ν e).subtypeL
      P.comp (N₀.comp (K.comp inc))=A.toContinuousLinearMap := by
  let S := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup S := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup S :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ S := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  refine fun hK P hP A hA=>?_
  apply skew_linearized_neumann_maps_unique n q ν e Z
  · exact fun X ψ Dψ hψ=>(projected_response_tests n hn ν hν hνn q e Z hZ K hK P hP X ψ Dψ hψ).2.2
  · exact hA

end StationaryHarmonicMaps.Analysis
end
