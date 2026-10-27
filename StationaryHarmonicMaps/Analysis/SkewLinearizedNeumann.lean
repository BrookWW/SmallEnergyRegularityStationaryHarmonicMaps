module

public import StationaryHarmonicMaps.Analysis.SkewNaturalCoefficientNeumannInverse

/-!
# The actual linearized Coulomb Neumann variational equation

The same skew identity perturbation is characterized by every original
native Neumann test against the literal derivative plus commutator flux.
-/

public section
open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff
noncomputable section
namespace StationaryHarmonicMaps.Analysis

private abbrev mapValue {n q : ℕ} (ν : ℝ) (X : MeanZeroNativeMorreySpace n q ν) :
    Domain n → Ambient q := (nativeMorreyMapClass (n:=n) (q:=q) ν) X.val

private abbrev gradientValue {n q : ℕ} (ν : ℝ) (X : MeanZeroNativeMorreySpace n q ν) :
    Domain n → Gradient n q := fun x i=>WithLp.toLp 2
      (fun j : Fin q=>(nativeMorreyHSClass (n:=n) (q:=q) ν) X.val x (finProdFinEquiv (i,j)))

private theorem canonical_native {n q : ℕ} (ν : ℝ) (X : MeanZeroNativeMorreySpace n q ν) :
    MemW12 (ballDomain (0:Domain n) 1) (mapValue ν X) (gradientValue ν X) ∧
    (⨍x in ball (0:Domain n) 1,mapValue ν X x)=0 ∧
    ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (gradientValue ν X x))≤
        ‖meanZeroNativeMorreyGradientClass n q ν X‖^2*r^ν := by
  obtain ⟨u,Du,hu,hMean,hMap,hGrad,hGrowth⟩ := exists_raw_native_of_meanZeroNativeMorrey ν X
  have hUAE : mapValue ν X=ᵐ[volume.restrict (ball (0:Domain n) 1)] u := by
    change ((nativeMorreyMapClass (n:=n) (q:=q) ν) X.val : Domain n→Ambient q)=ᵐ[_]u
    rw [hMap]
    exact hu.2.1.coeFn_toLp
  have hDAE : gradientValue ν X=ᵐ[volume.restrict (ball (0:Domain n) 1)]Du := by
    have hHS := hsUnitBallL2Class_ae Du hu.2.2
    rw [←hGrad] at hHS
    filter_upwards [hHS] with x hx
    funext i
    ext j
    have H := congrArg (fun z : Ambient (n*q)=>z (finProdFinEquiv (i,j))) hx
    simpa only [hsFlatten,gradientValue,finProdFinEquiv.symm_apply_apply] using H
  refine ⟨hu.congr_ae hUAE.symm hDAE.symm,(average_congr hUAE).trans hMean,?_⟩
  intro a ha r hr
  have hDAE' : gradientValue ν X=ᵐ[volume.restrict (ball a r∩ball (0:Domain n) 1)]Du :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hDAE
  calc
    _=∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Du x) :=
      integral_congr_ae (hDAE'.mono fun x hx=>congrArg hsNormSq hx)
    _≤_ := hGrowth a ha r hr

private theorem canonical_integral_zero {n q : ℕ} (ν : ℝ)
    (X : MeanZeroNativeMorreySpace n q ν) :
    (∫x in ball (0:Domain n) 1,mapValue ν X x)=0 := by
  have hMean := (canonical_native ν X).2.1
  rw [average_eq] at hMean
  have hV : 0<(volume.restrict (ball (0:Domain n) 1)).real univ := by
    rw [measureReal_restrict_apply_univ]
    exact HolderToCK.ball_volume_real_pos 0 (by norm_num)
  exact (smul_eq_zero.mp hMean).resolve_left (inv_ne_zero hV.ne')

private theorem gradientValue_add {n q : ℕ} (ν : ℝ) (X Y : MeanZeroNativeMorreySpace n q ν) :
    gradientValue ν (X+Y)=ᵐ[volume.restrict (ball (0:Domain n) 1)]
      (fun x i=>gradientValue ν X x i+gradientValue ν Y x i) := by
  have hClass : (nativeMorreyHSClass (n:=n) (q:=q) ν) (X+Y).val=
      (nativeMorreyHSClass (n:=n) (q:=q) ν) X.val+(nativeMorreyHSClass (n:=n) (q:=q) ν) Y.val :=
    (nativeMorreyHSClass (n:=n) (q:=q) ν).map_add X.val Y.val
  have H := Lp.coeFn_add ((nativeMorreyHSClass (n:=n) (q:=q) ν) X.val)
    ((nativeMorreyHSClass (n:=n) (q:=q) ν) Y.val)
  rw [←hClass] at H
  filter_upwards [H] with x hx
  funext i
  ext j
  exact congrArg (fun z : Ambient (n*q)=>z (finProdFinEquiv (i,j))) hx


private theorem canonical_pairing_integrable {n q : ℕ} (ν : ℝ)
    (X : MeanZeroNativeMorreySpace n q ν)
    (ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
    (hψ : MemW12 (ballDomain (0:Domain n) 1) ψ Dψ) :
    IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν X x i) (Dψ x i)) (ball (0:Domain n) 1) volume :=
  integrable_column_pairing (volume.restrict (ball (0:Domain n) 1))
    (gradientValue ν X) Dψ (canonical_native ν X).1.2.2 hψ.2.2

private theorem field_pairing_add {n q : ℕ} (μ : Measure (Domain n))
    (F G D : Domain n→Gradient n q)
    (hF : Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (D x i)) μ)
    (hG : Integrable (fun x=>∑i : Fin n,inner ℝ (G x i) (D x i)) μ) :
    Integrable (fun x=>∑i : Fin n,inner ℝ (F x i+G x i) (D x i)) μ ∧
    (∫x,∑i : Fin n,inner ℝ (F x i+G x i) (D x i) ∂μ)=
      (∫x,∑i : Fin n,inner ℝ (F x i) (D x i) ∂μ)+
      ∫x,∑i : Fin n,inner ℝ (G x i) (D x i) ∂μ := by
  have hDensity (x : Domain n) : (∑i : Fin n,inner ℝ (F x i+G x i) (D x i))=
      (∑i : Fin n,inner ℝ (F x i) (D x i))+(∑i : Fin n,inner ℝ (G x i) (D x i)) := by
    simp only [inner_add_left,Finset.sum_add_distrib]
  have hAE : (fun x=>∑i : Fin n,inner ℝ (F x i+G x i) (D x i))=ᵐ[μ]
      (fun x=>(∑i : Fin n,inner ℝ (F x i) (D x i))+(∑i : Fin n,inner ℝ (G x i) (D x i))) :=
    Eventually.of_forall hDensity
  exact ⟨(hF.add hG).congr hAE.symm,(integral_congr_ae hAE).trans (integral_add hF hG)⟩

private theorem gradient_pairing_add {n q : ℕ} (ν : ℝ)
    (X Y : MeanZeroNativeMorreySpace n q ν)
    (ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
    (hψ : MemW12 (ballDomain (0:Domain n) 1) ψ Dψ) :
    (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν (X+Y) x i) (Dψ x i))=
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν X x i) (Dψ x i))+
      ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν Y x i) (Dψ x i) := by
  have hAdd := field_pairing_add (volume.restrict (ball (0:Domain n) 1))
    (gradientValue ν X) (gradientValue ν Y) Dψ
    (canonical_pairing_integrable ν X ψ Dψ hψ) (canonical_pairing_integrable ν Y ψ Dψ hψ)
  have hAE : (fun x=>∑i : Fin n,inner ℝ (gradientValue ν (X+Y) x i) (Dψ x i))=ᵐ[
      volume.restrict (ball (0:Domain n) 1)]
      (fun x=>∑i : Fin n,inner ℝ (gradientValue ν X x i+gradientValue ν Y x i) (Dψ x i)) := by
    filter_upwards [gradientValue_add ν X Y] with x hx
    simp only [congrFun hx]
  exact (integral_congr_ae hAE).trans hAdd.2

private theorem identity_response_tests {n m q : ℕ} (ν : ℝ)
    (S : Submodule ℝ (MeanZeroNativeMorreySpace n q ν))
    (B : Ambient m→L[ℝ](Ambient q→L[ℝ]Ambient q)) (Z : Domain n→Gradient n m)
    (T : MeanZeroNativeMorreySpace n q ν→L[ℝ]MeanZeroNativeMorreySpace n q ν)
    (hT : ∀(X : MeanZeroNativeMorreySpace n q ν)
      (ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν (T X) x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν (T X) x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i))
    (A : S→L[ℝ]S) (hA : ∀X : S,(A X).val=X.val+T X.val) :
    ∀(X : S) (ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν (A X).val x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ
        (gradientValue ν X.val x i+B (Z x i) (mapValue ν X.val x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν (A X).val x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ
          (gradientValue ν X.val x i+B (Z x i) (mapValue ν X.val x)) (Dψ x i) := by
  intro X ψ Dψ hψ
  have hTX := hT X.val ψ Dψ hψ
  have hAdd := field_pairing_add (volume.restrict (ball (0:Domain n) 1))
    (gradientValue ν X.val) (fun x i=>B (Z x i) (mapValue ν X.val x)) Dψ
    (canonical_pairing_integrable ν X.val ψ Dψ hψ) hTX.2.1
  refine ⟨canonical_pairing_integrable ν (A X).val ψ Dψ hψ,hAdd.1,?_⟩
  calc
    _=(∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν X.val x i) (Dψ x i))+
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν (T X.val) x i) (Dψ x i) := by
      exact (congrArg (fun Y : MeanZeroNativeMorreySpace n q ν=>
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν Y x i) (Dψ x i)) (hA X)).trans
          (gradient_pairing_add ν X.val (T X.val) ψ Dψ hψ)
    _=(∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν X.val x i) (Dψ x i))+
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X.val x)) (Dψ x i) :=
      congrArg (fun I=>_+I) hTX.2.2
    _=_ := hAdd.2.symm


private theorem canonical_eq_of_tests {n q : ℕ} (ν : ℝ)
    (X Y : MeanZeroNativeMorreySpace n q ν)
    (hTests : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν X x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν Y x i) (Dψ x i)) : X=Y := by
  have hEqual := native_meanZero_gradient_response_unique_ae (0:Domain n) (by norm_num : (0:ℝ)<1)
    (mapValue ν X) (mapValue ν Y) (gradientValue ν X) (gradientValue ν Y)
    (canonical_native ν X).1 (canonical_native ν Y).1
    (canonical_integral_zero ν X) (canonical_integral_zero ν Y) hTests
  apply Subtype.ext
  apply nativeMorreyMapClass_injective (n:=n) (q:=q) ν
  exact Lp.ext hEqual.1

/-- Full original native linearized Neumann tests determine the actual
skew mean-zero bounded map uniquely. -/
theorem skew_linearized_neumann_maps_unique (n q : ℕ) (ν : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (Z : Domain n→Gradient n (q*q)) :
    let S := SkewMeanZeroNativeMorreySpace n q ν e
    letI : NormedAddCommGroup S := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
    letI : SeminormedAddCommGroup S :=
      (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
    letI : NormedSpace ℝ S := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
    ∀L M : S→L[ℝ]S,
      (∀X : S,
        let u : Domain n→Ambient (q*q) := (nativeMorreyMapClass (n:=n) (q:=q*q) ν) X.val.val
        let Du : Domain n→Gradient n (q*q) := fun x i=>WithLp.toLp 2
          (fun j : Fin (q*q)=>(nativeMorreyHSClass (n:=n) (q:=q*q) ν) X.val.val x (finProdFinEquiv (i,j)))
        let Y : S := L X
        let DY : Domain n→Gradient n (q*q) := fun x i=>WithLp.toLp 2
          (fun j : Fin (q*q)=>(nativeMorreyHSClass (n:=n) (q:=q*q) ν) Y.val.val x (finProdFinEquiv (i,j)))
        ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (DY x i) (Dψ x i))=
            ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ
              (Du x i+morreyMatrixCommutator q e (Z x i) (u x)) (Dψ x i)) →
      (∀X : S,
        let u : Domain n→Ambient (q*q) := (nativeMorreyMapClass (n:=n) (q:=q*q) ν) X.val.val
        let Du : Domain n→Gradient n (q*q) := fun x i=>WithLp.toLp 2
          (fun j : Fin (q*q)=>(nativeMorreyHSClass (n:=n) (q:=q*q) ν) X.val.val x (finProdFinEquiv (i,j)))
        let Y : S := M X
        let DY : Domain n→Gradient n (q*q) := fun x i=>WithLp.toLp 2
          (fun j : Fin (q*q)=>(nativeMorreyHSClass (n:=n) (q:=q*q) ν) Y.val.val x (finProdFinEquiv (i,j)))
        ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (DY x i) (Dψ x i))=
            ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ
              (Du x i+morreyMatrixCommutator q e (Z x i) (u x)) (Dψ x i)) → L=M := by
  let S := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup S := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup S :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ S := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  refine fun L M hL hM=>?_
  apply ContinuousLinearMap.ext
  intro X
  apply Subtype.ext
  exact canonical_eq_of_tests ν (L X).val (M X).val
    (fun ψ Dψ hψ=>(hL X ψ Dψ hψ).trans (hM X ψ Dψ hψ).symm)

/-- Original small critical natural skew coefficients construct the unique
actual inverse of the linearized Coulomb Neumann problem on the genuine
skew native space, with full ordinary integrability and every native test. -/
theorem exists_unique_skew_linearized_neumann_inverse
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (q : ℕ) (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    let ν : ℝ := (n:ℝ)-2+γ
    let S := SkewMeanZeroNativeMorreySpace n q ν e
    letI : NormedAddCommGroup S := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
    letI : SeminormedAddCommGroup S :=
      (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
    letI : NormedSpace ℝ S := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
    ∃ε : ℝ,0<ε ∧ ∀(Z : Domain n→Gradient n (q*q)) (η : ℝ),
      (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
      (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) →
      0≤η → η≤ε → criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
      (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,star (e (Z x i))=-(e (Z x i))) →
      ∃!A : S≃L[ℝ]S,
        (∀X : S,
          let u : Domain n→Ambient (q*q) := (nativeMorreyMapClass (n:=n) (q:=q*q) ν) X.val.val
          let Du : Domain n→Gradient n (q*q) := fun x i=>WithLp.toLp 2
            (fun j : Fin (q*q)=>(nativeMorreyHSClass (n:=n) (q:=q*q) ν) X.val.val x (finProdFinEquiv (i,j)))
          let Y : S := A X
          let DY : Domain n→Gradient n (q*q) := fun x i=>WithLp.toLp 2
            (fun j : Fin (q*q)=>(nativeMorreyHSClass (n:=n) (q:=q*q) ν) Y.val.val x (finProdFinEquiv (i,j)))
          ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
            MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
            IntegrableOn (fun x=>∑i : Fin n,inner ℝ (DY x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
            IntegrableOn (fun x=>∑i : Fin n,inner ℝ
              (Du x i+morreyMatrixCommutator q e (Z x i) (u x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
            (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (DY x i) (Dψ x i))=
              ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ
                (Du x i+morreyMatrixCommutator q e (Z x i) (u x)) (Dψ x i)) ∧ ‖(A.symm : S→L[ℝ]S)‖≤2 := by
  let ν : ℝ := (n:ℝ)-2+γ
  let S := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup S := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup S :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ S := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  have hData := exists_small_skew_natural_neumann_morrey_inverse n hn γ hγ hγTwo
  have hThreshold := hData.choose_spec.2 q e
  let ε := hThreshold.choose
  have hε : 0<ε := hThreshold.choose_spec.1
  have Hε := hThreshold.choose_spec.2
  refine ⟨ε,hε,?_⟩
  intro Z η hZ hNatural hη hηle hCritical hSkew
  have hOperator := Hε Z η hZ hNatural hη hηle hCritical hSkew
  let T := hOperator.choose
  have hT := hOperator.choose_spec.1.2
  have hInverse := hOperator.choose_spec.2.2
  let A := hInverse.choose
  have hA := hInverse.choose_spec.1
  have hRaw := identity_response_tests ν (skewMeanZeroNativeMorreySubmodule n q ν e)
    (morreyMatrixCommutator q e) Z T hT A.toContinuousLinearMap hA.1
  refine ⟨A,⟨hRaw,hA.2⟩,?_⟩
  intro D hD
  have hEqual := skew_linearized_neumann_maps_unique n q ν e Z D.toContinuousLinearMap A.toContinuousLinearMap
    (fun X ψ Dψ hψ=>(hD.1 X ψ Dψ hψ).2.2) (fun X ψ Dψ hψ=>(hRaw X ψ Dψ hψ).2.2)
  apply ContinuousLinearEquiv.ext
  funext X
  exact congrArg (fun L : S→L[ℝ]S=>L X) hEqual

end StationaryHarmonicMaps.Analysis
end
