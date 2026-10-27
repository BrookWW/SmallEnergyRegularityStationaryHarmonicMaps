module

public import StationaryHarmonicMaps.Analysis.NativeMorreySobolevBanach
import StationaryHarmonicMaps.Analysis.NativeMorreyMeanZero
import StationaryHarmonicMaps.Analysis.StrongMorreyNativeAlgebra
import HarmonicMaps.Analysis.SobolevAECongruence

/-!
# Unique actual bilinear product classes

Original stronger native data supply their actual value bounds and the
same two-term weak Leibniz graph. The full native Banach norm controls
the original means and gradient amplitudes. Product classes retain the
literal original product almost everywhere on the entire source ball.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace StationaryHarmonicMaps.Analysis

theorem nativeMorreyHSClass_eq_of_native_map {n q : ℕ} (ν : ℝ)
    (u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
    (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (X : NativeMorreySobolevSpace n q ν)
    (hMap : nativeMorreyMapClass (n:=n) (q:=q) ν X=hNative.2.1.toLp u) :
    nativeMorreyHSClass (n:=n) (q:=q) ν X=hsUnitBallL2Class Du hNative.2.2 := by
  obtain ⟨v,Dv,hV,hVMap,hVGrad,_hGrowth⟩ := exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=q) ν X
  have hClass : hV.2.1.toLp v=hNative.2.1.toLp u := hVMap.symm.trans hMap
  have hAE : v=ᵐ[volume.restrict (ball (0 : Domain n) 1)]u :=
    (MemLp.toLp_eq_toLp_iff hV.2.1 hNative.2.1).mp hClass
  have hDAE : Dv=ᵐ[volume.restrict (ball (0 : Domain n) 1)]Du :=
    hV.1.ae_eq_of_ae_eq_map hNative.1 hAE
  have hCols (i : Fin n) : (fun x=>Dv x i)=ᵐ[volume.restrict (ball (0 : Domain n) 1)](fun x=>Du x i) :=
    hDAE.mono fun x hx=>congrArg (fun A : Gradient n q=>A i) hx
  exact hVGrad.trans ((hsUnitBallL2Class_eq_iff_ae Dv Du hV.2.2 hNative.2.2).mpr hCols)

private theorem native_map_norm_le {n q : ℕ} (ν : ℝ) (X : NativeMorreySobolevSpace n q ν) :
    ‖nativeMorreyMapClass (n:=n) (q:=q) ν X‖≤‖X‖ := by
  change ‖X.val.1‖≤max ‖X.val.1‖ ‖X.val.2‖
  exact le_max_left _ _

private theorem native_gradient_norm_le {n q : ℕ} (ν : ℝ) (X : NativeMorreySobolevSpace n q ν) :
    ‖nativeMorreyGradientClass (n:=n) (q:=q) ν X‖≤‖X‖ := by
  change ‖X.val.2‖≤max ‖X.val.1‖ ‖X.val.2‖
  exact le_max_right _ _

private theorem original_mean_norm_le_native {n q : ℕ} (ν : ℝ)
    (u : Domain n→Ambient q) (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (X : NativeMorreySobolevSpace n q ν)
    (hMap : nativeMorreyMapClass (n:=n) (q:=q) ν X=hu.toLp u) :
    ‖(⨍x in ball (0 : Domain n) 1,u x)‖≤
      (Real.sqrt (volume.real (ball (0 : Domain n) 1)))⁻¹*‖X‖ := by
  have hAvg : unitBallAverageL2 n q (nativeMorreyMapClass (n:=n) (q:=q) ν X)=
      ⨍x in ball (0 : Domain n) 1,u x :=
    (congrArg (unitBallAverageL2 n q) hMap).trans (unitBallAverageL2_apply_raw u hu)
  calc
    _=‖unitBallAverageL2 n q (nativeMorreyMapClass (n:=n) (q:=q) ν X)‖ := (congrArg norm hAvg).symm
    _≤‖unitBallAverageL2 n q‖*‖nativeMorreyMapClass (n:=n) (q:=q) ν X‖ := (unitBallAverageL2 n q).le_opNorm _
    _≤_ := mul_le_mul (unitBallAverageL2_norm_le n q) (native_map_norm_le ν X)
      (norm_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))

private theorem morrey_norm_sq_le_of_growth {n q : ℕ} (ν K : ℝ)
    (F : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (Z : MorreyCoefficientSpace n q ν) (hZ : morreyCoefficientRecover ν Z=hsUnitBallL2Class F hF)
    (hGrowth : ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))≤K*r^ν) :
    ‖Z‖^2≤K := by
  rw [morreyCoefficient_norm_sq ν F hF Z hZ]
  have hNe : {e : ℝ | ∃a∈ball (0 : Domain n) 1,∃r : ℝ,0<r ∧
      e=r^(-ν)*(∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))}.Nonempty :=
    ⟨(2 : ℝ)^(-ν)*(∫x in ball (0 : Domain n) 2∩ball (0 : Domain n) 1,hsNormSq (F x)),
      0,mem_ball_self (by norm_num),2,by norm_num,rfl⟩
  apply csSup_le hNe
  rintro e ⟨a,ha,r,hr,rfl⟩
  have hCancel : r^(-ν)*r^ν=1 := by rw [←Real.rpow_add hr,neg_add_cancel,Real.rpow_zero]
  calc
    _≤r^(-ν)*(K*r^ν) := mul_le_mul_of_nonneg_left (hGrowth a ha r hr) (Real.rpow_nonneg hr.le _)
    _=K := by rw [mul_left_comm,hCancel,mul_one]

private theorem native_map_norm_le_of_ae_bound {n q : ℕ} (ν M : ℝ)
    (W : Domain n→Ambient q)
    (hW : MemLp W 2 (volume.restrict (ball (0 : Domain n) 1)))
    (Z : NativeMorreySobolevSpace n q ν)
    (hMap : nativeMorreyMapClass (n:=n) (q:=q) ν Z=hW.toLp W)
    (hM : 0≤M) (hBound : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖W x‖≤M) :
    ‖nativeMorreyMapClass (n:=n) (q:=q) ν Z‖≤Real.sqrt (volume.real (ball (0 : Domain n) 1))*M := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hWLp : MemLp W 2 μ := hW
  have hAE : ∀ᵐx∂μ,‖hWLp.toLp W x‖≤M := by
    filter_upwards [hWLp.coeFn_toLp,hBound] with x hx hb
    rw [hx]
    exact hb
  have H := Lp.norm_le_of_ae_bound (f:=hWLp.toLp W) hM hAE
  have hMass : (measureUnivNNReal μ : ℝ)=volume.real (ball (0 : Domain n) 1) := by
    change μ.real univ=volume.real (ball (0 : Domain n) 1)
    exact measureReal_restrict_apply_univ (ball (0 : Domain n) 1)
  have H' : ‖hW.toLp W‖≤Real.sqrt (volume.real (ball (0 : Domain n) 1))*M := by
    simpa only [hMass,ENNReal.toReal_ofNat,←one_div,←Real.sqrt_eq_rpow] using H
  exact (congrArg (fun U : MapUnitBallL2 n q=>‖U‖) hMap).trans_le H'

private theorem native_norm_le_of_raw_bounds {n q : ℕ} (ν M K : ℝ)
    (W : Domain n→Ambient q) (DW : Domain n→Gradient n q)
    (hNative : MemW12 (ballDomain (0 : Domain n) 1) W DW)
    (Z : NativeMorreySobolevSpace n q ν)
    (hMap : nativeMorreyMapClass (n:=n) (q:=q) ν Z=hNative.2.1.toLp W)
    (hGrad : nativeMorreyHSClass (n:=n) (q:=q) ν Z=hsUnitBallL2Class DW hNative.2.2)
    (hM : 0≤M) (hK : 0≤K)
    (hBound : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖W x‖≤M)
    (hGrowth : ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (DW x))≤K*r^ν) :
    ‖Z‖≤max (Real.sqrt (volume.real (ball (0 : Domain n) 1))*M) (Real.sqrt K) := by
  have hMapBound := native_map_norm_le_of_ae_bound ν M W hNative.2.1 Z hMap hM hBound
  have hGradSq : ‖nativeMorreyGradientClass (n:=n) (q:=q) ν Z‖^2≤K :=
    morrey_norm_sq_le_of_growth ν K DW hNative.2.2 (nativeMorreyGradientClass (n:=n) (q:=q) ν Z) hGrad hGrowth
  have hGradBound : ‖nativeMorreyGradientClass (n:=n) (q:=q) ν Z‖≤Real.sqrt K := by
    have hRoot := Real.sq_sqrt hK
    have hn := norm_nonneg (nativeMorreyGradientClass (n:=n) (q:=q) ν Z)
    have hr := Real.sqrt_nonneg K
    nlinarith only [hGradSq,hRoot,hn,hr]
  change max ‖nativeMorreyMapClass (n:=n) (q:=q) ν Z‖ ‖nativeMorreyGradientClass (n:=n) (q:=q) ν Z‖≤_
  exact max_le_max hMapBound hGradBound

private theorem bilinear_growth_coefficient_bound (b L x y U V Ku Kv : ℝ)
    (hU0 : 0≤U) (hV0 : 0≤V) (hKu0 : 0≤Ku) (hKv0 : 0≤Kv)
    (hU : U≤L*x) (hV : V≤L*y) (hKu : Ku≤x^2) (hKv : Kv≤y^2) :
    2*b^2*(U^2*Kv+V^2*Ku)≤(2*b*L*x*y)^2 := by
  have hUSq := pow_le_pow_left₀ hU0 hU 2
  have hVSq := pow_le_pow_left₀ hV0 hV 2
  rw [mul_pow] at hUSq hVSq
  have hFirst : U^2*Kv≤(L^2*x^2)*y^2 :=
    mul_le_mul hUSq hKv hKv0 (mul_nonneg (sq_nonneg L) (sq_nonneg x))
  have hSecond : V^2*Ku≤(L^2*y^2)*x^2 :=
    mul_le_mul hVSq hKu hKu0 (mul_nonneg (sq_nonneg L) (sq_nonneg y))
  have hSum : U^2*Kv+V^2*Ku≤2*L^2*x^2*y^2 :=
    (add_le_add hFirst hSecond).trans_eq (by ring)
  exact (mul_le_mul_of_nonneg_left hSum (mul_nonneg (by norm_num) (sq_nonneg b))).trans_eq (by ring)

private theorem native_map_ae_of_raw {n q : ℕ} (ν : ℝ)
    (u : Domain n→Ambient q) (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (X : NativeMorreySobolevSpace n q ν)
    (hMap : nativeMorreyMapClass (n:=n) (q:=q) ν X=hu.toLp u) :
    ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),(nativeMorreyMapClass (n:=n) (q:=q) ν X).val x=u x := by
  filter_upwards [hu.coeFn_toLp] with x hx
  exact (congrArg (fun U : MapUnitBallL2 n q=>U.val x) hMap).trans hx

theorem existsUnique_nativeMorrey_bilinear_product_bound
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    let ν := (n : ℝ)-2+γ
    ∃C : ℝ,0<C ∧ ∀(m k q : ℕ)
      (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
      (X : NativeMorreySobolevSpace n m ν) (Y : NativeMorreySobolevSpace n k ν),
      (∃! Z : NativeMorreySobolevSpace n q ν,
        ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
          (nativeMorreyMapClass (n:=n) (q:=q) ν Z).val x=
            B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x)
              ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x)) ∧
      ∀Z : NativeMorreySobolevSpace n q ν,
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
          (nativeMorreyMapClass (n:=n) (q:=q) ν Z).val x=
            B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x)
              ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x)) →
        ‖Z‖≤C*‖B‖*‖X‖*‖Y‖ := by
  intro ν
  have hStrongData :
    ∃ C : ℝ, 0 < C ∧ ∀ (m k q : ℕ)
      (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q))
      (u : Domain n → Ambient m) (Du : Domain n → Gradient n m) (Ku : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ Ku →
      (∀ a ∈ ball (0 : Domain n) 1, ∀ r : ℝ, 0 < r →
        (∫ x in ball a r ∩ ball (0 : Domain n) 1, hsNormSq (Du x)) ≤
          Ku * r^((n : ℝ)-2+γ)) →
      ∀ (v : Domain n → Ambient k) (Dv : Domain n → Gradient n k) (Kv : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) v Dv → 0 ≤ Kv →
      (∀ a ∈ ball (0 : Domain n) 1, ∀ r : ℝ, 0 < r →
        (∫ x in ball a r ∩ ball (0 : Domain n) 1, hsNormSq (Dv x)) ≤
          Kv * r^((n : ℝ)-2+γ)) →
      let Mu := ‖(⨍ x in ball (0 : Domain n) 1, u x)‖ + C * Real.sqrt Ku
      let Mv := ‖(⨍ x in ball (0 : Domain n) 1, v x)‖ + C * Real.sqrt Kv
      let W := fun x => B (u x) (v x)
      let DW := fun x i => B (Du x i) (v x) + B (u x) (Dv x i)
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖u x‖ ≤ Mu) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖v x‖ ≤ Mv) ∧
      MemW12 (ballDomain (0 : Domain n) 1) W DW ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖W x‖ ≤ ‖B‖ * Mu * Mv) ∧
      0 ≤ 2 * ‖B‖^2 * (Mu^2 * Kv + Mv^2 * Ku) ∧
      ∀ a ∈ ball (0 : Domain n) 1, ∀ r : ℝ, 0 < r →
        IntegrableOn (fun x => hsNormSq (DW x)) (ball a r ∩ ball (0 : Domain n) 1) volume ∧
        (∫ x in ball a r ∩ ball (0 : Domain n) 1, hsNormSq (DW x)) ≤
          (2 * ‖B‖^2 * (Mu^2 * Kv + Mv^2 * Ku)) * r^((n : ℝ)-2+γ) :=
    exists_stronger_morrey_native_bilinear_product n hn γ hγ hγTwo
  obtain ⟨H,hH,Hproduct⟩ := hStrongData
  let V := volume.real (ball (0 : Domain n) 1)
  let T := (Real.sqrt V)⁻¹
  let L := T+H
  have hT : 0≤T := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hL : 0≤L := add_nonneg hT hH.le
  have hTerm : 0≤Real.sqrt V*L^2 := mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg L)
  let C := 1+Real.sqrt V*L^2+2*L
  have hC : 0<C := by dsimp only [C];linarith only [hTerm,hL]
  have hCMap : Real.sqrt V*L^2≤C := by dsimp only [C];linarith only [hL]
  have hCGrad : 2*L≤C := by dsimp only [C];linarith only [hTerm]
  refine ⟨C,hC,?_⟩
  intro m k q B X Y
  have hDataX : ∃(u : Domain n→Ambient m) (Du : Domain n→Gradient n m)
      (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du),
      nativeMorreyMapClass (n:=n) (q:=m) ν X=hu.2.1.toLp u ∧
      nativeMorreyHSClass (n:=n) (q:=m) ν X=hsUnitBallL2Class Du hu.2.2 ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤‖nativeMorreyGradientClass (n:=n) (q:=m) ν X‖^2*r^ν :=
    exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=m) ν X
  have hDataY : ∃(v : Domain n→Ambient k) (Dv : Domain n→Gradient n k)
      (hv : MemW12 (ballDomain (0 : Domain n) 1) v Dv),
      nativeMorreyMapClass (n:=n) (q:=k) ν Y=hv.2.1.toLp v ∧
      nativeMorreyHSClass (n:=n) (q:=k) ν Y=hsUnitBallL2Class Dv hv.2.2 ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dv x))≤‖nativeMorreyGradientClass (n:=n) (q:=k) ν Y‖^2*r^ν :=
    exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=k) ν Y
  obtain ⟨u,Du,hu,hXMap,_hXGrad,hGX⟩ := hDataX
  obtain ⟨v,Dv,hv,hYMap,_hYGrad,hGY⟩ := hDataY
  let Ku := ‖nativeMorreyGradientClass (n:=n) (q:=m) ν X‖^2
  let Kv := ‖nativeMorreyGradientClass (n:=n) (q:=k) ν Y‖^2
  let Mu := ‖(⨍x in ball (0 : Domain n) 1,u x)‖+H*Real.sqrt Ku
  let Mv := ‖(⨍x in ball (0 : Domain n) 1,v x)‖+H*Real.sqrt Kv
  let W := fun x=>B (u x) (v x)
  let DW := fun x i=>B (Du x i) (v x)+B (u x) (Dv x i)
  have hProductData :
      (∀ᵐz∂volume.restrict (ball (0 : Domain n) 1),‖u z‖≤Mu) ∧
      (∀ᵐz∂volume.restrict (ball (0 : Domain n) 1),‖v z‖≤Mv) ∧
      MemW12 (ballDomain (0 : Domain n) 1) W DW ∧
      (∀ᵐz∂volume.restrict (ball (0 : Domain n) 1),‖W z‖≤‖B‖*Mu*Mv) ∧
      0≤2*‖B‖^2*(Mu^2*Kv+Mv^2*Ku) ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        IntegrableOn (fun z=>hsNormSq (DW z)) (ball a r∩ball (0 : Domain n) 1) volume ∧
        (∫z in ball a r∩ball (0 : Domain n) 1,hsNormSq (DW z))≤
          (2*‖B‖^2*(Mu^2*Kv+Mv^2*Ku))*r^ν :=
    Hproduct m k q B u Du Ku hu (sq_nonneg _) hGX v Dv Kv hv (sq_nonneg _) hGY
  obtain ⟨_hUAE,_hVAE,hWNative,hWBound,hCoeff,hWQueries⟩ := hProductData
  let b := ‖B‖
  let M := b*Mu*Mv
  let K := 2*b^2*(Mu^2*Kv+Mv^2*Ku)
  have hMu0 : 0≤Mu := add_nonneg (norm_nonneg _) (mul_nonneg hH.le (Real.sqrt_nonneg _))
  have hMv0 : 0≤Mv := add_nonneg (norm_nonneg _) (mul_nonneg hH.le (Real.sqrt_nonneg _))
  have hM0 : 0≤M := mul_nonneg (mul_nonneg (norm_nonneg B) hMu0) hMv0
  have hK0 : 0≤K := hCoeff
  have hWGrowth : ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (DW x))≤K*r^ν :=
    fun a ha r hr=>(hWQueries a ha r hr).2
  have hExistsZ : ∃! Z : NativeMorreySobolevSpace n q ν,
      nativeMorreyMapClass (n:=n) (q:=q) ν Z=hWNative.2.1.toLp W ∧
      nativeMorreyHSClass (n:=n) (q:=q) ν Z=hsUnitBallL2Class DW hWNative.2.2 :=
    (existsUnique_nativeMorreySobolev_iff_power_growth ν W DW hWNative).mpr ⟨K,hK0,hWGrowth⟩
  obtain ⟨Z,⟨hZMap,hZGrad⟩,_hZUnique⟩ := hExistsZ
  let x := ‖X‖
  let y := ‖Y‖
  have hx : 0≤x := norm_nonneg _
  have hy : 0≤y := norm_nonneg _
  have hb : 0≤b := norm_nonneg B
  have hMeanX : ‖(⨍z in ball (0 : Domain n) 1,u z)‖≤T*x := original_mean_norm_le_native ν u hu.2.1 X hXMap
  have hMeanY : ‖(⨍z in ball (0 : Domain n) 1,v z)‖≤T*y := original_mean_norm_le_native ν v hv.2.1 Y hYMap
  have hDX := native_gradient_norm_le ν X
  have hDY := native_gradient_norm_le ν Y
  have hKu : Ku≤x^2 := pow_le_pow_left₀ (norm_nonneg _) hDX 2
  have hKv : Kv≤y^2 := pow_le_pow_left₀ (norm_nonneg _) hDY 2
  have hMu : Mu≤L*x := by
    dsimp only [Mu,Ku]
    rw [Real.sqrt_sq (norm_nonneg _)]
    calc
      _≤T*x+H*x := add_le_add hMeanX (mul_le_mul_of_nonneg_left hDX hH.le)
      _=L*x := by dsimp only [L];ring
  have hMv : Mv≤L*y := by
    dsimp only [Mv,Kv]
    rw [Real.sqrt_sq (norm_nonneg _)]
    calc
      _≤T*y+H*y := add_le_add hMeanY (mul_le_mul_of_nonneg_left hDY hH.le)
      _=L*y := by dsimp only [L];ring
  have hM : M≤b*L^2*x*y := by
    calc
      _=b*(Mu*Mv) := by dsimp only [M];ring
      _≤b*((L*x)*(L*y)) := mul_le_mul_of_nonneg_left
        (mul_le_mul hMu hMv hMv0 (mul_nonneg hL hx)) hb
      _=_ := by ring
  have hK : K≤(2*b*L*x*y)^2 := bilinear_growth_coefficient_bound b L x y Mu Mv Ku Kv
    hMu0 hMv0 (sq_nonneg _) (sq_nonneg _) hMu hMv hKu hKv
  have hRootK : Real.sqrt K≤2*b*L*x*y := by
    have Hroot := Real.sqrt_le_sqrt hK
    rw [Real.sqrt_sq (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb) hL) hx) hy)] at Hroot
    exact Hroot
  have hPhysical : Real.sqrt V*M≤C*b*x*y := by
    calc
      _≤Real.sqrt V*(b*L^2*x*y) := mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg _)
      _=(Real.sqrt V*L^2)*(b*x*y) := by ring
      _≤C*(b*x*y) := mul_le_mul_of_nonneg_right hCMap (mul_nonneg (mul_nonneg hb hx) hy)
      _=_ := by ring
  have hGradient : Real.sqrt K≤C*b*x*y := hRootK.trans (by
    calc
      _=(2*L)*(b*x*y) := by ring
      _≤C*(b*x*y) := mul_le_mul_of_nonneg_right hCGrad (mul_nonneg (mul_nonneg hb hx) hy)
      _=_ := by ring)
  have hNorm : ‖Z‖≤C*b*x*y :=
    (native_norm_le_of_raw_bounds ν M K W DW hWNative Z hZMap hZGrad hM0 hK0 hWBound hWGrowth).trans
      (max_le hPhysical hGradient)
  have hXAE := native_map_ae_of_raw ν u hu.2.1 X hXMap
  have hYAE := native_map_ae_of_raw ν v hv.2.1 Y hYMap
  have hZAE := native_map_ae_of_raw ν W hWNative.2.1 Z hZMap
  have hProduct : ∀ᵐz∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν Z).val z=
        B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val z)
          ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val z) := by
    filter_upwards [hXAE,hYAE,hZAE] with z hzX hzY hzZ
    exact hzZ.trans (congrArg₂ (fun a : Ambient m=>fun b : Ambient k=>B a b) hzX.symm hzY.symm)
  have hUnique (Z' : NativeMorreySobolevSpace n q ν)
      (hZ' : ∀ᵐz∂volume.restrict (ball (0 : Domain n) 1),
        (nativeMorreyMapClass (n:=n) (q:=q) ν Z').val z=
          B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val z)
            ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val z)) : Z'=Z := by
    apply nativeMorreyMapClass_injective (n:=n) (q:=q) ν
    apply Lp.ext
    filter_upwards [hZ',hProduct] with z hz' hz
    exact hz'.trans hz.symm
  refine ⟨⟨Z,hProduct,hUnique⟩,?_⟩
  intro Z' hZ'
  exact (congrArg (fun Q : NativeMorreySobolevSpace n q ν=>‖Q‖) (hUnique Z' hZ')).trans_le hNorm

theorem nativeMorrey_bilinear_raw_leibniz
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (m k q : ℕ) (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q)) :
    let ν := (n : ℝ)-2+γ
    ∀(u : Domain n→Ambient m) (Du : Domain n→Gradient n m)
      (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
      (X : NativeMorreySobolevSpace n m ν),
      nativeMorreyMapClass (n:=n) (q:=m) ν X=hu.2.1.toLp u →
      ∀(v : Domain n→Ambient k) (Dv : Domain n→Gradient n k)
        (hv : MemW12 (ballDomain (0 : Domain n) 1) v Dv)
        (Y : NativeMorreySobolevSpace n k ν),
        nativeMorreyMapClass (n:=n) (q:=k) ν Y=hv.2.1.toLp v →
        ∀Z : NativeMorreySobolevSpace n q ν,
          (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
            (nativeMorreyMapClass (n:=n) (q:=q) ν Z).val x=
              B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x)
                ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x)) →
          let W := fun x=>B (u x) (v x)
          let DW := fun x i=>B (Du x i) (v x)+B (u x) (Dv x i)
          ∃hW : MemW12 (ballDomain (0 : Domain n) 1) W DW,
            nativeMorreyMapClass (n:=n) (q:=q) ν Z=hW.2.1.toLp W ∧
            nativeMorreyHSClass (n:=n) (q:=q) ν Z=hsUnitBallL2Class DW hW.2.2 := by
  intro ν u Du hu X hXMap v Dv hv Y hYMap Z hProduct W DW
  have hStrongData :
    ∃ C : ℝ, 0 < C ∧ ∀ (m k q : ℕ)
      (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q))
      (u : Domain n → Ambient m) (Du : Domain n → Gradient n m) (Ku : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0 ≤ Ku →
      (∀ a ∈ ball (0 : Domain n) 1, ∀ r : ℝ, 0 < r →
        (∫ x in ball a r ∩ ball (0 : Domain n) 1, hsNormSq (Du x)) ≤
          Ku * r^((n : ℝ)-2+γ)) →
      ∀ (v : Domain n → Ambient k) (Dv : Domain n → Gradient n k) (Kv : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) v Dv → 0 ≤ Kv →
      (∀ a ∈ ball (0 : Domain n) 1, ∀ r : ℝ, 0 < r →
        (∫ x in ball a r ∩ ball (0 : Domain n) 1, hsNormSq (Dv x)) ≤
          Kv * r^((n : ℝ)-2+γ)) →
      let Mu := ‖(⨍ x in ball (0 : Domain n) 1, u x)‖ + C * Real.sqrt Ku
      let Mv := ‖(⨍ x in ball (0 : Domain n) 1, v x)‖ + C * Real.sqrt Kv
      let W := fun x => B (u x) (v x)
      let DW := fun x i => B (Du x i) (v x) + B (u x) (Dv x i)
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖u x‖ ≤ Mu) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖v x‖ ≤ Mv) ∧
      MemW12 (ballDomain (0 : Domain n) 1) W DW ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1), ‖W x‖ ≤ ‖B‖ * Mu * Mv) ∧
      0 ≤ 2 * ‖B‖^2 * (Mu^2 * Kv + Mv^2 * Ku) ∧
      ∀ a ∈ ball (0 : Domain n) 1, ∀ r : ℝ, 0 < r →
        IntegrableOn (fun x => hsNormSq (DW x)) (ball a r ∩ ball (0 : Domain n) 1) volume ∧
        (∫ x in ball a r ∩ ball (0 : Domain n) 1, hsNormSq (DW x)) ≤
          (2 * ‖B‖^2 * (Mu^2 * Kv + Mv^2 * Ku)) * r^((n : ℝ)-2+γ) :=
    exists_stronger_morrey_native_bilinear_product n hn γ hγ hγTwo
  obtain ⟨_H,_hH,Hproduct⟩ := hStrongData
  have hXGrad := nativeMorreyHSClass_eq_of_native_map ν u Du hu X hXMap
  have hYGrad := nativeMorreyHSClass_eq_of_native_map ν v Dv hv Y hYMap
  let Ku := ‖nativeMorreyGradientClass (n:=n) (q:=m) ν X‖^2
  let Kv := ‖nativeMorreyGradientClass (n:=n) (q:=k) ν Y‖^2
  have hGX : ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤Ku*r^ν :=
    morreyCoefficient_power_growth ν Du hu.2.2 (nativeMorreyGradientClass (n:=n) (q:=m) ν X) hXGrad
  have hGY : ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dv x))≤Kv*r^ν :=
    morreyCoefficient_power_growth ν Dv hv.2.2 (nativeMorreyGradientClass (n:=n) (q:=k) ν Y) hYGrad
  have hW : MemW12 (ballDomain (0 : Domain n) 1) W DW :=
    (Hproduct m k q B u Du Ku hu (sq_nonneg _) hGX v Dv Kv hv (sq_nonneg _) hGY).2.2.1
  have hXAE := native_map_ae_of_raw ν u hu.2.1 X hXMap
  have hYAE := native_map_ae_of_raw ν v hv.2.1 Y hYMap
  have hZAE : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν Z).val x=W x := by
    filter_upwards [hProduct,hXAE,hYAE] with x hz hx hy
    exact hz.trans (congrArg₂ (fun a : Ambient m=>fun b : Ambient k=>B a b) hx hy)
  have hZMap : nativeMorreyMapClass (n:=n) (q:=q) ν Z=hW.2.1.toLp W := by
    apply Lp.ext
    filter_upwards [hZAE,hW.2.1.coeFn_toLp] with x hz hw
    exact hz.trans hw.symm
  exact ⟨hW,hZMap,nativeMorreyHSClass_eq_of_native_map ν W DW hW Z hZMap⟩

end StationaryHarmonicMaps.Analysis

end
