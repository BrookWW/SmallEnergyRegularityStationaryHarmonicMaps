module

public import StationaryHarmonicMaps.Analysis.NativeMorreyMeanZero
public import StationaryHarmonicMaps.Analysis.NaturalCoefficientNeumannPowerGrowth
public import StationaryHarmonicMaps.Analysis.NeumannGradientProjection
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtDecoding

/-!
# The actual small natural-coefficient Neumann operator

The original critical natural coefficient acts on the mean-zero native
stronger Morrey graph. The compensated response supplies actual native
classes, all original Neumann pairings and the small operator bound.
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

private theorem canonical_response_unique {n q : ℕ} (ν : ℝ)
    (F : Domain n→Gradient n q) (Y W : MeanZeroNativeMorreySpace n q ν)
    (hY : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν Y x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (F x i) (Dψ x i))
    (hW : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν W x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (F x i) (Dψ x i)) : Y=W := by
  have hEq := native_meanZero_gradient_response_unique_ae (0:Domain n) (by norm_num : (0:ℝ)<1)
    (mapValue ν Y) (mapValue ν W) (gradientValue ν Y) (gradientValue ν W)
    (canonical_native ν Y).1 (canonical_native ν W).1 (canonical_integral_zero ν Y)
    (canonical_integral_zero ν W) (fun ψ Dψ hψ=>(hY ψ Dψ hψ).trans (hW ψ Dψ hψ).symm)
  apply Subtype.ext
  apply nativeMorreyMapClass_injective (n:=n) (q:=q) ν
  exact Lp.ext hEq.1

private theorem gradient_norm_sq_le {n q : ℕ} (ν K : ℝ)
    (F : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0:Domain n) 1)))
    (Y : MeanZeroNativeMorreySpace n q ν)
    (hY : (nativeMorreyHSClass (n:=n) (q:=q) ν) Y.val=hsUnitBallL2Class F hF)
    (hGrowth : ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (F x))≤K*r^ν) :
    ‖meanZeroNativeMorreyGradientClass n q ν Y‖^2≤K := by
  change ‖(nativeMorreyGradientClass (n:=n) (q:=q) ν) Y.val‖^2≤K
  rw [morreyCoefficient_norm_sq ν F hF ((nativeMorreyGradientClass (n:=n) (q:=q) ν) Y.val) hY]
  apply csSup_le
  · exact ⟨(1:ℝ)^(-ν)*(∫x in ball (0:Domain n) 1∩ball (0:Domain n) 1,hsNormSq (F x)),
      0,mem_ball_self (by norm_num),1,by norm_num,rfl⟩
  · rintro e ⟨a,ha,r,hr,rfl⟩
    calc
      _≤r^(-ν)*(K*r^ν) := mul_le_mul_of_nonneg_left (hGrowth a ha r hr) (Real.rpow_nonneg hr.le _)
      _=K := by rw [mul_left_comm,←Real.rpow_add hr,neg_add_cancel,Real.rpow_zero,mul_one]

private theorem exists_class_of_raw_response {n q : ℕ} (ν K : ℝ)
    (F : Domain n→Gradient n q) (g : Domain n→Ambient q) (Q : Domain n→Gradient n q)
    (hg : MemW12 (ballDomain (0:Domain n) 1) g Q)
    (hMean : (∫x in ball (0:Domain n) 1,g x)=0) (hK : 0≤K)
    (hGrowth : ∀a∈ball (0:Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Q x))≤K*r^ν)
    (hTests : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (F x i) (Dψ x i)) :
    ∃Y : MeanZeroNativeMorreySpace n q ν,
      (∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν Y x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν Y x i) (Dψ x i))=
          ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (F x i) (Dψ x i)) ∧
      ‖meanZeroNativeMorreyGradientClass n q ν Y‖^2≤K := by
  have hAvg : (⨍x in ball (0:Domain n) 1,g x)=0 := by rw [average_eq,hMean,smul_zero]
  obtain ⟨Y,⟨_hMapY,hGradY⟩,_hYUnique⟩ :=
    (existsUnique_meanZeroNativeMorrey_iff (n:=n) (q:=q) ν g Q hg).mpr ⟨hAvg,K,hK,hGrowth⟩
  have hQAE : gradientValue ν Y=ᵐ[volume.restrict (ball (0:Domain n) 1)]Q := by
    have hHS := hsUnitBallL2Class_ae Q hg.2.2
    rw [←hGradY] at hHS
    filter_upwards [hHS] with x hx
    funext i
    ext j
    have H := congrArg (fun z : Ambient (n*q)=>z (finProdFinEquiv (i,j))) hx
    simpa only [hsFlatten,gradientValue,finProdFinEquiv.symm_apply_apply] using H
  have hChar (ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
      (hψ : MemW12 (ballDomain (0:Domain n) 1) ψ Dψ) :
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν Y x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν Y x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (F x i) (Dψ x i) := by
    obtain ⟨hQI,hFI,hEq⟩ := hTests ψ Dψ hψ
    have hPair : (fun x=>∑i : Fin n,inner ℝ (gradientValue ν Y x i) (Dψ x i))=ᵐ[volume.restrict (ball (0:Domain n) 1)]
        (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) := by
      filter_upwards [hQAE] with x hx
      rw [hx]
    exact ⟨hQI.congr hPair.symm,hFI,(integral_congr_ae hPair).trans hEq⟩
  exact ⟨Y,hChar,gradient_norm_sq_le ν K Q hg.2.2 Y hGradY hGrowth⟩

private theorem response_norm_bound {n k q : ℕ} (ν S L η M : ℝ)
    (hS : 0≤S) (hL : 0≤L) (hη : 0≤η) (hM : 0≤M)
    (X : MeanZeroNativeMorreySpace n k ν) (Y : MeanZeroNativeMorreySpace n q ν)
    (hYN : ‖Y‖≤S*‖meanZeroNativeMorreyGradientClass n q ν Y‖)
    (hYSq : ‖meanZeroNativeMorreyGradientClass n q ν Y‖^2≤
      L*M^2*η^2*‖meanZeroNativeMorreyGradientClass n k ν X‖^2) :
    ‖Y‖≤(S*Real.sqrt L)*M*η*‖X‖ := by
  let G := ‖meanZeroNativeMorreyGradientClass n k ν X‖
  have hG : 0≤G := norm_nonneg _
  let A := Real.sqrt L*M*η*G
  have hA : 0≤A := by dsimp only [A];positivity
  have hASq : A^2=L*M^2*η^2*G^2 := by
    dsimp only [A]
    rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt hL]
  have hYGradient : ‖meanZeroNativeMorreyGradientClass n q ν Y‖≤A := by
    have hBound : ‖meanZeroNativeMorreyGradientClass n q ν Y‖^2≤A^2 := hYSq.trans_eq hASq.symm
    nlinarith only [hBound,hA,norm_nonneg (meanZeroNativeMorreyGradientClass n q ν Y)]
  have hGX : G≤‖X‖ := by
    change ‖X.val.val.2‖≤max ‖X.val.val.1‖ ‖X.val.val.2‖
    exact le_max_right _ _
  calc
    _≤S*‖meanZeroNativeMorreyGradientClass n q ν Y‖ := hYN
    _≤S*A := mul_le_mul_of_nonneg_left hYGradient hS
    _=(S*Real.sqrt L*M*η)*G := by dsimp only [A];ring
    _≤(S*Real.sqrt L*M*η)*‖X‖ := mul_le_mul_of_nonneg_left hGX (by positivity)
    _=_ := by ring

private theorem bounded_class_of_raw_response {n m k q : ℕ} (ν S L η : ℝ)
    (hS : 0≤S) (hL : 0≤L) (hη : 0≤η)
    (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q)) (Z : Domain n→Gradient n m)
    (X : MeanZeroNativeMorreySpace n k ν)
    (Hnorm : ∀Y : MeanZeroNativeMorreySpace n q ν,
      ‖Y‖≤S*‖meanZeroNativeMorreyGradientClass n q ν Y‖)
    (hRawResponse : ∃(g : Domain n→Ambient q) (Q : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) g Q ∧
      (∫x in ball (0:Domain n) 1,g x)=0 ∧
      (∀i,MemLp (fun x=>B (Z x i) (mapValue ν X x)) 2 (volume.restrict (ball (0:Domain n) 1))) ∧
      (∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
          ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)) ∧
      ∀(a : Domain n) (r : ℝ),0<r →
        (∫x in ball a r∩ball (0:Domain n) 1,hsNormSq (Q x))≤
          L*‖B‖^2*η^2*‖meanZeroNativeMorreyGradientClass n k ν X‖^2*r^ν) :
    ∃!Y : MeanZeroNativeMorreySpace n q ν,
      (∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν Y x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν Y x i) (Dψ x i))=
          ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)) ∧
      ‖Y‖≤(S*Real.sqrt L)*‖B‖*η*‖X‖ := by
  let u := mapValue ν X
  let G := ‖meanZeroNativeMorreyGradientClass n k ν X‖
  have hG : 0≤G := norm_nonneg _
  obtain ⟨g,Q,hg,hMean,_hRaw,hTests,hGrowth⟩ := hRawResponse
  let K := L*‖B‖^2*η^2*G^2
  have hK : 0≤K := by dsimp only [K];positivity
  obtain ⟨Y,hChar,hYSq⟩ := exists_class_of_raw_response ν K (fun x i=>B (Z x i) (u x)) g Q hg
    hMean hK (fun a _ha r hr=>hGrowth a r hr) hTests
  have hYBound : ‖Y‖≤(S*Real.sqrt L)*‖B‖*η*‖X‖ :=
    response_norm_bound ν S L η ‖B‖ hS hL hη (norm_nonneg B) X Y (Hnorm Y) hYSq
  refine ⟨Y,⟨hChar,hYBound⟩,?_⟩
  intro W hW
  exact canonical_response_unique ν (fun x i=>B (Z x i) (u x)) W Y
    (fun ψ Dψ hψ=>(hW.1 ψ Dψ hψ).2.2) (fun ψ Dψ hψ=>(hChar ψ Dψ hψ).2.2)

/-- Original critical natural coefficient data construct exactly one
actual mean-zero native stronger-Morrey response class for each input.
Its canonical raw representatives satisfy every original native Neumann
pairing, and its norm has the uniform small coefficient. -/
theorem exists_unique_natural_coefficient_neumann_morrey_response
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀(m k q : ℕ)
      (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
      (Z : Domain n→Gradient n m) (η : ℝ),
      (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
      (∀(ψ : Domain n→Ambient m) (Dψ : Domain n→Gradient n m),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) →
      0≤η → criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀X : MeanZeroNativeMorreySpace n k ((n:ℝ)-2+γ),
        let u : Domain n→Ambient k := (nativeMorreyMapClass (n:=n) (q:=k) ((n:ℝ)-2+γ)) X.val
        ∃!Y : MeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ),
          let Q : Domain n→Gradient n q := fun x i=>WithLp.toLp 2
            (fun j : Fin q=>(nativeMorreyHSClass (n:=n) (q:=q) ((n:ℝ)-2+γ)) Y.val x (finProdFinEquiv (i,j)))
          (∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
            MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
            IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
            IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
            (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
              ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) ∧
          ‖Y‖≤C*‖B‖*η*‖X‖ := by
  let ν : ℝ := (n:ℝ)-2+γ
  have hData := exists_natural_coefficient_neumann_full_power_growth n hn γ hγ hγTwo
  let L := hData.choose
  have hL : 0<L := hData.choose_spec.1
  have HL := hData.choose_spec.2
  have hNormData := exists_meanZeroNativeMorrey_norm_le_gradient n ν
  let S := hNormData.choose
  have hS : 0<S := hNormData.choose_spec.1
  have Hnorm := hNormData.choose_spec.2
  let C := S*Real.sqrt L
  have hC : 0<C := mul_pos hS (Real.sqrt_pos.mpr hL)
  refine ⟨C,hC,?_⟩
  intro m k q B Z η hZ hNatural hη hCritical X
  have hXNative := canonical_native ν X
  exact bounded_class_of_raw_response ν S L η hS.le hL.le hη B Z X (Hnorm q)
    (HL m k q B Z (mapValue ν X) (gradientValue ν X) η
      (‖meanZeroNativeMorreyGradientClass n k ν X‖^2) hZ hNatural hXNative.1 hη hCritical
      (sq_nonneg _) hXNative.2.2)

private theorem mapValue_add {n q : ℕ} (ν : ℝ) (X Y : MeanZeroNativeMorreySpace n q ν) :
    mapValue ν (X+Y)=ᵐ[volume.restrict (ball (0:Domain n) 1)](fun x=>mapValue ν X x+mapValue ν Y x) := by
  have hClass : (nativeMorreyMapClass (n:=n) (q:=q) ν) (X+Y).val=
      (nativeMorreyMapClass (n:=n) (q:=q) ν) X.val+(nativeMorreyMapClass (n:=n) (q:=q) ν) Y.val :=
    (nativeMorreyMapClass (n:=n) (q:=q) ν).map_add X.val Y.val
  change ((nativeMorreyMapClass (n:=n) (q:=q) ν) (X+Y).val : Domain n→Ambient q)=ᵐ[_]_
  rw [hClass]
  exact Lp.coeFn_add _ _

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

private theorem mapValue_smul {n q : ℕ} (ν c : ℝ) (X : MeanZeroNativeMorreySpace n q ν) :
    mapValue ν (c • X)=ᵐ[volume.restrict (ball (0:Domain n) 1)](fun x=>c • mapValue ν X x) := by
  have hClass : (nativeMorreyMapClass (n:=n) (q:=q) ν) (c • X).val=
      c • (nativeMorreyMapClass (n:=n) (q:=q) ν) X.val :=
    (nativeMorreyMapClass (n:=n) (q:=q) ν).map_smul c X.val
  change ((nativeMorreyMapClass (n:=n) (q:=q) ν) (c • X).val : Domain n→Ambient q)=ᵐ[_]_
  rw [hClass]
  exact Lp.coeFn_smul c _

private theorem gradientValue_smul {n q : ℕ} (ν c : ℝ) (X : MeanZeroNativeMorreySpace n q ν) :
    gradientValue ν (c • X)=ᵐ[volume.restrict (ball (0:Domain n) 1)]
      (fun x i=>c • gradientValue ν X x i) := by
  have hClass : (nativeMorreyHSClass (n:=n) (q:=q) ν) (c • X).val=
      c • (nativeMorreyHSClass (n:=n) (q:=q) ν) X.val :=
    (nativeMorreyHSClass (n:=n) (q:=q) ν).map_smul c X.val
  have H := Lp.coeFn_smul c ((nativeMorreyHSClass (n:=n) (q:=q) ν) X.val)
  rw [←hClass] at H
  filter_upwards [H] with x hx
  funext i
  ext j
  exact congrArg (fun z : Ambient (n*q)=>z (finProdFinEquiv (i,j))) hx

private theorem response_add {n m k q : ℕ} (ν : ℝ)
    (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q)) (Z : Domain n→Gradient n m)
    (X Y : MeanZeroNativeMorreySpace n k ν) (A D : MeanZeroNativeMorreySpace n q ν)
    (hA : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν A x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν A x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i))
    (hD : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν D x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν Y x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν D x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν Y x)) (Dψ x i)) :
    ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν (A+D) x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν (X+Y) x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν (A+D) x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν (X+Y) x)) (Dψ x i) := by
  intro ψ Dψ hψ
  let μ := volume.restrict (ball (0:Domain n) 1)
  let LA := fun x=>∑i : Fin n,inner ℝ (gradientValue ν A x i) (Dψ x i)
  let LD := fun x=>∑i : Fin n,inner ℝ (gradientValue ν D x i) (Dψ x i)
  let RA := fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)
  let RD := fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν Y x)) (Dψ x i)
  have hLA : Integrable LA μ := (hA ψ Dψ hψ).1
  have hLD : Integrable LD μ := (hD ψ Dψ hψ).1
  have hRA : Integrable RA μ := (hA ψ Dψ hψ).2.1
  have hRD : Integrable RD μ := (hD ψ Dψ hψ).2.1
  have hLeft : (fun x=>∑i : Fin n,inner ℝ (gradientValue ν (A+D) x i) (Dψ x i))=ᵐ[μ]
      (fun x=>LA x+LD x) := by
    filter_upwards [gradientValue_add ν A D] with x hx
    calc
      _=∑i : Fin n,inner ℝ (gradientValue ν A x i+gradientValue ν D x i) (Dψ x i) :=
        Finset.sum_congr rfl (fun i _=>congrArg (fun z : Ambient q=>inner ℝ z (Dψ x i)) (congrFun hx i))
      _=LA x+LD x := by simp only [inner_add_left,Finset.sum_add_distrib,LA,LD]
  have hRight : (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν (X+Y) x)) (Dψ x i))=ᵐ[μ]
      (fun x=>RA x+RD x) := by
    filter_upwards [mapValue_add ν X Y] with x hx
    simp only [hx,map_add,inner_add_left,Finset.sum_add_distrib,RA,RD]
  refine ⟨(hLA.add hLD).congr hLeft.symm,(hRA.add hRD).congr hRight.symm,?_⟩
  calc
    _=∫x,LA x+LD x ∂μ := integral_congr_ae hLeft
    _=(∫x,LA x ∂μ)+(∫x,LD x ∂μ) := integral_add hLA hLD
    _=(∫x,RA x ∂μ)+(∫x,RD x ∂μ) := congrArg₂ (fun a b : ℝ=>a+b)
      (hA ψ Dψ hψ).2.2 (hD ψ Dψ hψ).2.2
    _=∫x,RA x+RD x ∂μ := (integral_add hRA hRD).symm
    _=_ := (integral_congr_ae hRight).symm

private theorem response_smul {n m k q : ℕ} (ν c : ℝ)
    (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q)) (Z : Domain n→Gradient n m)
    (X : MeanZeroNativeMorreySpace n k ν) (A : MeanZeroNativeMorreySpace n q ν)
    (hA : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν A x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν A x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)) :
    ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν (c • A) x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν (c • X) x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν (c • A) x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν (c • X) x)) (Dψ x i) := by
  intro ψ Dψ hψ
  let μ := volume.restrict (ball (0:Domain n) 1)
  let L := fun x=>∑i : Fin n,inner ℝ (gradientValue ν A x i) (Dψ x i)
  let R := fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)
  have hL : Integrable L μ := (hA ψ Dψ hψ).1
  have hR : Integrable R μ := (hA ψ Dψ hψ).2.1
  have hLeft : (fun x=>∑i : Fin n,inner ℝ (gradientValue ν (c • A) x i) (Dψ x i))=ᵐ[μ]
      (fun x=>c*L x) := by
    filter_upwards [gradientValue_smul ν c A] with x hx
    calc
      _=∑i : Fin n,inner ℝ (c • gradientValue ν A x i) (Dψ x i) :=
        Finset.sum_congr rfl (fun i _=>congrArg (fun z : Ambient q=>inner ℝ z (Dψ x i)) (congrFun hx i))
      _=c*L x := by simp only [real_inner_smul_left,Finset.mul_sum,L]
  have hRight : (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν (c • X) x)) (Dψ x i))=ᵐ[μ]
      (fun x=>c*R x) := by
    filter_upwards [mapValue_smul ν c X] with x hx
    simp only [hx,map_smul,real_inner_smul_left,Finset.mul_sum,R]
  refine ⟨(hL.const_mul c).congr hLeft.symm,(hR.const_mul c).congr hRight.symm,?_⟩
  calc
    _=∫x,c*L x ∂μ := integral_congr_ae hLeft
    _=c*(∫x,L x ∂μ) := integral_const_mul _ _
    _=c*(∫x,R x ∂μ) := congrArg (fun t : ℝ=>c*t) (hA ψ Dψ hψ).2.2
    _=∫x,c*R x ∂μ := (integral_const_mul _ _).symm
    _=_ := (integral_congr_ae hRight).symm

private theorem operator_of_unique_responses {n m k q : ℕ} (ν C η : ℝ)
    (hC : 0≤C) (hη : 0≤η)
    (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q)) (Z : Domain n→Gradient n m)
    (Hclass : ∀X : MeanZeroNativeMorreySpace n k ν,
      ∃!Y : MeanZeroNativeMorreySpace n q ν,
        (∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν Y x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν Y x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)) ∧ ‖Y‖≤C*‖B‖*η*‖X‖) :
    letI : NormedAddCommGroup (MeanZeroNativeMorreySpace n k ν) := Submodule.normedAddCommGroup _
    letI : NormedAddCommGroup (MeanZeroNativeMorreySpace n q ν) := Submodule.normedAddCommGroup _
    ∃!T : MeanZeroNativeMorreySpace n k ν→L[ℝ]MeanZeroNativeMorreySpace n q ν,
      ‖T‖≤C*‖B‖*η ∧ ∀X : MeanZeroNativeMorreySpace n k ν,
        ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν (T X) x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν (T X) x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i) := by
  letI : NormedAddCommGroup (MeanZeroNativeMorreySpace n k ν) := Submodule.normedAddCommGroup _
  letI : NormedAddCommGroup (MeanZeroNativeMorreySpace n q ν) := Submodule.normedAddCommGroup _
  let T : MeanZeroNativeMorreySpace n k ν→MeanZeroNativeMorreySpace n q ν := fun X : MeanZeroNativeMorreySpace n k ν=>(Hclass X).choose
  have hT (X : MeanZeroNativeMorreySpace n k ν) :
      (∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (gradientValue ν (T X) x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (gradientValue ν (T X) x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (mapValue ν X x)) (Dψ x i)) ∧ ‖T X‖≤C*‖B‖*η*‖X‖ := (Hclass X).choose_spec.1
  have hAdd (X Y : MeanZeroNativeMorreySpace n k ν) : T (X+Y)=T X+T Y := by
    have hSum := response_add ν B Z X Y (T X) (T Y) (hT X).1 (hT Y).1
    exact canonical_response_unique ν (fun x i=>B (Z x i) (mapValue ν (X+Y) x))
      (T (X+Y)) (T X+T Y) (fun ψ Dψ hψ=>((hT (X+Y)).1 ψ Dψ hψ).2.2)
      (fun ψ Dψ hψ=>(hSum ψ Dψ hψ).2.2)
  have hSmul (c : ℝ) (X : MeanZeroNativeMorreySpace n k ν) : T (c • X)=c • T X := by
    have hScale := response_smul ν c B Z X (T X) (hT X).1
    exact canonical_response_unique ν (fun x i=>B (Z x i) (mapValue ν (c • X) x))
      (T (c • X)) (c • T X) (fun ψ Dψ hψ=>((hT (c • X)).1 ψ Dψ hψ).2.2)
      (fun ψ Dψ hψ=>(hScale ψ Dψ hψ).2.2)
  let A : MeanZeroNativeMorreySpace n k ν→ₗ[ℝ]MeanZeroNativeMorreySpace n q ν :=
    { toFun:=T
      map_add':=hAdd
      map_smul':=fun c X=>hSmul c X }
  let L := A.mkContinuous (C*‖B‖*η) (fun X=>(hT X).2)
  have hBound : ‖L‖≤C*‖B‖*η :=
    ContinuousLinearMap.opNorm_le_bound L (by positivity) (fun X=>(hT X).2)
  refine ⟨L,⟨hBound,fun X=>(hT X).1⟩,?_⟩
  intro M hM
  apply ContinuousLinearMap.ext
  intro X
  exact canonical_response_unique ν (fun x i=>B (Z x i) (mapValue ν X x)) (M X) (L X)
    (fun ψ Dψ hψ=>(hM.2 X ψ Dψ hψ).2.2) (fun ψ Dψ hψ=>((hT X).1 ψ Dψ hψ).2.2)

/-- The actual original critical natural coefficient defines exactly one
bounded real-linear operator between the actual mean-zero native stronger
Morrey spaces. Every input is characterized by the original uncentered
forcing and all native Neumann tests. -/
theorem exists_unique_natural_coefficient_neumann_morrey_operator
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀(m k q : ℕ)
      (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
      (Z : Domain n→Gradient n m) (η : ℝ),
      (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
      (∀(ψ : Domain n→Ambient m) (Dψ : Domain n→Gradient n m),
        MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
        (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) →
      0≤η → criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
      letI : NormedAddCommGroup (MeanZeroNativeMorreySpace n k ((n:ℝ)-2+γ)) := Submodule.normedAddCommGroup _
      letI : NormedAddCommGroup (MeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ)) := Submodule.normedAddCommGroup _
      ∃!T : MeanZeroNativeMorreySpace n k ((n:ℝ)-2+γ)→L[ℝ]MeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ),
        ‖T‖≤C*‖B‖*η ∧ ∀X : MeanZeroNativeMorreySpace n k ((n:ℝ)-2+γ),
          let u : Domain n→Ambient k := (nativeMorreyMapClass (n:=n) (q:=k) ((n:ℝ)-2+γ)) X.val
          let Q : Domain n→Gradient n q := fun x i=>WithLp.toLp 2
            (fun j : Fin q=>(nativeMorreyHSClass (n:=n) (q:=q) ((n:ℝ)-2+γ)) (T X).val x (finProdFinEquiv (i,j)))
          ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
            MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
            IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
            IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
            (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
              ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i) := by
  have hData := exists_unique_natural_coefficient_neumann_morrey_response n hn γ hγ hγTwo
  let C := hData.choose
  have hC : 0<C := hData.choose_spec.1
  have Hclass := hData.choose_spec.2
  refine ⟨C,hC,?_⟩
  intro m k q B Z η hZ hNatural hη hCritical
  letI : NormedAddCommGroup (MeanZeroNativeMorreySpace n k ((n:ℝ)-2+γ)) := Submodule.normedAddCommGroup _
  letI : NormedAddCommGroup (MeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ)) := Submodule.normedAddCommGroup _
  exact operator_of_unique_responses ((n:ℝ)-2+γ) C η hC.le hη B Z
    (Hclass m k q B Z η hZ hNatural hη hCritical)

end StationaryHarmonicMaps.Analysis

end
