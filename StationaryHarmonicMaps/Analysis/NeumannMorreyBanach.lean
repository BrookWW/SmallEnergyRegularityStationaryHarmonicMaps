module

public import StationaryHarmonicMaps.Analysis.NativeMorreySobolevBanach
public import StationaryHarmonicMaps.Analysis.NeumannGradientProjection
public import StationaryHarmonicMaps.Analysis.NeumannFullPowerGrowth
import HarmonicMaps.Analysis.SobolevPoincare

/-!
# Actual Neumann responses in the Morrey Banach graph

The full native Neumann identity and the original mean-zero normalization
uniquely specify an element of the actual native Morrey graph. The response
has a dimension-free target-coordinate norm bound from the original forcing.
-/

public section

open HarmonicMaps StationaryHarmonicMaps.Analysis MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

noncomputable section

namespace StationaryHarmonicMaps.Analysis

private theorem hsClass_inner_raw {n q : ℕ}
    (F G : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hG : ∀i,MemLp (fun x=>G x i) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    inner ℝ (hsUnitBallL2Class (n:=n) (q:=q) F hF) (hsUnitBallL2Class (n:=n) (q:=q) G hG)=
      ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (F x i) (G x i) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hsUnitBallL2Class_ae F hF,hsUnitBallL2Class_ae G hG] with x hxF hxG
  rw [hxF,hxG]
  exact hs_flatten_inner (F x) (G x)

private theorem mapClass_integral_raw {n q : ℕ} (ν : ℝ)
    (X : NativeMorreySobolevSpace n q ν) (u : Domain n→Ambient q)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hX : nativeMorreyMapClass (n:=n) (q:=q) ν X=hu.toLp u) :
    (∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν X).val x)=
      ∫x in ball (0 : Domain n) 1,u x := by
  rw [hX]
  exact integral_congr_ae hu.coeFn_toLp

private theorem neumann_morrey_class_unique {n q : ℕ} (ν : ℝ)
    (F : MorreyCoefficientSpace n q ν) (X Y : NativeMorreySobolevSpace n q ν)
    (hXM : (∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν X).val x)=0)
    (hYM : (∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν Y).val x)=0)
    (hX : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ),
      inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν X) (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2)=
        inner ℝ (morreyCoefficientRecover (n:=n) (q:=q) ν F) (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2))
    (hY : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ),
      inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν Y) (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2)=
        inner ℝ (morreyCoefficientRecover (n:=n) (q:=q) ν F) (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2)) : X=Y := by
  obtain ⟨u,Du,hu,hUMap,hUGrad,_hUGrowth⟩ := exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=q) ν X
  obtain ⟨v,Dv,hv,hVMap,hVGrad,_hVGrowth⟩ := exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=q) ν Y
  have huMean : (∫x in ball (0 : Domain n) 1,u x)=0 := by
    rw [←mapClass_integral_raw ν X u hu.2.1 hUMap]
    exact hXM
  have hvMean : (∫x in ball (0 : Domain n) 1,v x)=0 := by
    rw [←mapClass_integral_raw ν Y v hv.2.1 hVMap]
    exact hYM
  have hTests : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
      (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Du x i) (Dψ x i))=
        ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Dv x i) (Dψ x i) := by
    intro ψ Dψ hψ
    have H := (hX ψ Dψ hψ).trans (hY ψ Dψ hψ).symm
    rw [hUGrad,hVGrad,hsClass_inner_raw,hsClass_inner_raw] at H
    exact H
  have hAE := (native_meanZero_gradient_response_unique_ae 0 (by norm_num : (0 : ℝ)<1)
    u v Du Dv hu hv huMean hvMean hTests).1
  exact (nativeMorreySobolev_eq_iff_ae ν u v hu.2.1 hv.2.1 X Y hUMap hVMap).mpr hAE

private theorem exists_raw_neumann_morrey_response
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ))
    (q : ℕ) (F : MorreyCoefficientSpace n q ν) :
    ∃(u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
      (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du) (L : ℝ),
      0<L ∧ (∫x in ball (0 : Domain n) 1,u x)=0 ∧
      (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤(L*‖F‖^2)*r^ν) ∧
      ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
        (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ),
        inner ℝ (hsUnitBallL2Class (n:=n) (q:=q) Du hu.2.2) (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2)=
          inner ℝ (morreyCoefficientRecover (n:=n) (q:=q) ν F) (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2) := by
  obtain ⟨L,hL,HGrowth⟩ := exists_native_neumann_full_real_power_growth n hn ν hν hνn
  obtain ⟨G,hG,hF,hGrowth⟩ := exists_raw_field_of_morreyCoefficient (n:=n) (q:=q) ν F
  obtain ⟨u,Du,hu,hMean,_hEnergy,hTests⟩ := exists_neumann_gradient_projection
    (0 : Domain n) (by norm_num : (0 : ℝ)<1) G hG
  have hOutput : ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤(L*‖F‖^2)*r^ν :=
    HGrowth q u Du G (‖F‖^2) hu hG (sq_nonneg _) hGrowth
      (fun ψ Dψ hψ=>(hTests ψ Dψ hψ).2.2)
  refine ⟨u,Du,hu,L,hL,hMean,hOutput,?_⟩
  intro ψ Dψ hψ
  rw [hF,hsClass_inner_raw,hsClass_inner_raw]
  exact (hTests ψ Dψ hψ).2.2

/-- The actual full native Neumann identity determines a unique mean-zero
native Morrey graph for every original finite Morrey coefficient class. -/
theorem existsUnique_native_neumann_morrey_class
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ))
    (q : ℕ) (F : MorreyCoefficientSpace n q ν) :
    ∃! X : NativeMorreySobolevSpace n q ν,
      (∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν X).val x)=0 ∧
      ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
        (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ),
        inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν X) (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2)=
          inner ℝ (morreyCoefficientRecover (n:=n) (q:=q) ν F) (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2) := by
  obtain ⟨u,Du,hu,L,hL,hMean,hOutput,hTests⟩ := exists_raw_neumann_morrey_response n hn ν hν hνn q F
  have hNativeClass : ∃! X : NativeMorreySobolevSpace n q ν,
      nativeMorreyMapClass (n:=n) (q:=q) ν X=hu.2.1.toLp u ∧
      nativeMorreyHSClass (n:=n) (q:=q) ν X=hsUnitBallL2Class (n:=n) (q:=q) Du hu.2.2 :=
    (existsUnique_nativeMorreySobolev_iff_power_growth (n:=n) (q:=q) ν u Du hu).mpr
      ⟨L*‖F‖^2,mul_nonneg hL.le (sq_nonneg _),hOutput⟩
  obtain ⟨X,⟨hXMap,hXGrad⟩,_hXUnique⟩ := hNativeClass
  have hXMean := (mapClass_integral_raw ν X u hu.2.1 hXMap).trans hMean
  have hXN : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ),
      inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν X) (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2)=
        inner ℝ (morreyCoefficientRecover (n:=n) (q:=q) ν F) (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2) := by
    intro ψ Dψ hψ
    rw [hXGrad]
    exact hTests ψ Dψ hψ
  exact ⟨X,⟨hXMean,hXN⟩,fun Y hY=>neumann_morrey_class_unique ν F Y X hY.1 hXMean hY.2 hXN⟩

private theorem morrey_norm_sq_le_raw_growth {n q : ℕ} (ν K : ℝ)
    (Du : Domain n→Gradient n q)
    (hDu : ∀i,MemLp (fun x=>Du x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (Z : MorreyCoefficientSpace n q ν)
    (hZ : morreyCoefficientRecover (n:=n) (q:=q) ν Z=hsUnitBallL2Class Du hDu)
    (H : ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤K*r^ν) : ‖Z‖^2≤K := by
  rw [morreyCoefficient_norm_sq ν Du hDu Z hZ]
  have hNE : {e : ℝ | ∃a∈ball (0 : Domain n) 1,∃r : ℝ,0<r ∧
      e=r^(-ν)*(∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))}.Nonempty :=
    ⟨(1 : ℝ)^(-ν)*(∫x in ball (0 : Domain n) 1∩ball (0 : Domain n) 1,hsNormSq (Du x)),
      0,mem_ball_self (by norm_num),1,by norm_num,rfl⟩
  apply csSup_le hNE
  rintro _ ⟨a,ha,r,hr,rfl⟩
  have HC := mul_le_mul_of_nonneg_left (H a ha r hr) (Real.rpow_nonneg hr.le (-ν))
  have hCancel : r^(-ν)*r^ν=1 := by rw [←Real.rpow_add hr,neg_add_cancel,Real.rpow_zero]
  exact HC.trans_eq (by rw [mul_left_comm,hCancel,mul_one])

private theorem native_norm_sq_le_mean_zero_growth {n q : ℕ} (ν K : ℝ) (hK : 0≤K)
    (X : NativeMorreySobolevSpace n q ν) (u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (hMean : (⨍x in ball (0 : Domain n) 1,u x)=0)
    (hXMap : nativeMorreyMapClass (n:=n) (q:=q) ν X=hu.2.1.toLp u)
    (hXGrad : nativeMorreyHSClass (n:=n) (q:=q) ν X=hsUnitBallL2Class (n:=n) (q:=q) Du hu.2.2)
    (hOutput : ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤K*r^ν) :
    ‖X‖^2≤(1+(2 : ℝ)^(n+1)*(2 : ℝ)^ν)*K := by
  let P := (2 : ℝ)^(n+1)
  let T := (2 : ℝ)^ν
  have hP : 0≤P := pow_nonneg (by norm_num) _
  have hT : 0≤T := Real.rpow_nonneg (by norm_num) _
  have hGradient : ‖nativeMorreyGradientClass (n:=n) (q:=q) ν X‖^2≤K :=
    morrey_norm_sq_le_raw_growth ν K Du hu.2.2 (nativeMorreyGradientClass (n:=n) (q:=q) ν X) hXGrad hOutput
  have hTotal : (∫x in ball (0 : Domain n) 1,hsNormSq (Du x))≤K*T := by
    simpa only [inter_eq_right.mpr (ball_subset_ball (by norm_num : (1 : ℝ)≤2))] using
      hOutput 0 (mem_ball_self (by norm_num : (0 : ℝ)<1)) 2 (by norm_num)
  have hPoincare : (∫x in ball (0 : Domain n) 1,‖u x‖^2)≤P*(∫x in ball (0 : Domain n) 1,hsNormSq (Du x)) := by
    have H := hu.poincare_ball (by norm_num : (0 : ℝ)<1)
    rw [hMean] at H
    simpa only [sub_zero,one_pow,mul_one] using H
  have huLp : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)) := hu.2.1
  have hMap' : nativeMorreyMapClass (n:=n) (q:=q) ν X=huLp.toLp u := hXMap
  have hMapSq : ‖nativeMorreyMapClass (n:=n) (q:=q) ν X‖^2=∫x in ball (0 : Domain n) 1,‖u x‖^2 := by
    calc
      _=‖huLp.toLp u‖^2 := congrArg (fun U : MapUnitBallL2 n q=>‖U‖^2) hMap'
      _=∫x in ball (0 : Domain n) 1,‖(huLp.toLp u) x‖^2 := l2_euclidean_norm_sq _ (huLp.toLp u)
      _=_ := integral_congr_ae (huLp.coeFn_toLp.mono fun x hx=>congrArg (fun z : Ambient q=>‖z‖^2) hx)
  have hMapBound : ‖nativeMorreyMapClass (n:=n) (q:=q) ν X‖^2≤(P*T)*K := by
    rw [hMapSq]
    exact hPoincare.trans ((mul_le_mul_of_nonneg_left hTotal hP).trans_eq (by ring))
  have hMax : ‖X‖^2=max (‖nativeMorreyMapClass (n:=n) (q:=q) ν X‖^2)
      (‖nativeMorreyGradientClass (n:=n) (q:=q) ν X‖^2) := by
    change (max ‖X.val.1‖ ‖X.val.2‖)^2=max (‖X.val.1‖^2) (‖X.val.2‖^2)
    by_cases hLe : ‖X.val.1‖≤‖X.val.2‖
    · rw [max_eq_right hLe,max_eq_right (pow_le_pow_left₀ (norm_nonneg _) hLe 2)]
    · have hGe := (not_le.mp hLe).le
      rw [max_eq_left hGe,max_eq_left (pow_le_pow_left₀ (norm_nonneg _) hGe 2)]
  rw [hMax]
  apply max_le
  · exact hMapBound.trans (mul_le_mul_of_nonneg_right (by linarith : P*T≤1+P*T) hK)
  · exact hGradient.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hP hT] : (1 : ℝ)≤1+P*T) hK)

/-- A uniform bound for the unique actual Neumann class holds before the
target dimension and all original forcing and response data are chosen. -/
theorem exists_uniform_native_neumann_morrey_class_bound
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) :
    ∃C : ℝ,0<C ∧ ∀(q : ℕ) (F : MorreyCoefficientSpace n q ν)
      (X : NativeMorreySobolevSpace n q ν),
      (∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν X).val x)=0 →
      (∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
        (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ),
        inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν X) (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2)=
          inner ℝ (morreyCoefficientRecover (n:=n) (q:=q) ν F) (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2)) →
      ‖X‖≤C*‖F‖ := by
  obtain ⟨L,hL,HGrowth⟩ := exists_native_neumann_full_real_power_growth n hn ν hν hνn
  let A := 1+(2 : ℝ)^(n+1)*(2 : ℝ)^ν
  have hA : 0<A := by dsimp only [A];positivity
  let C := Real.sqrt (A*L)
  have hC : 0<C := Real.sqrt_pos.mpr (mul_pos hA hL)
  have hCSq : C^2=A*L := Real.sq_sqrt (mul_nonneg hA.le hL.le)
  refine ⟨C,hC,?_⟩
  intro q F X hMean hTests
  obtain ⟨u,Du,hu,hXMap,hXGrad,_hXGrowth⟩ := exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=q) ν X
  obtain ⟨G,hG,hF,hGrowth⟩ := exists_raw_field_of_morreyCoefficient (n:=n) (q:=q) ν F
  have hNat : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
      (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Du x i) (Dψ x i))=
        ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (G x i) (Dψ x i) := by
    intro ψ Dψ hψ
    have H := hTests ψ Dψ hψ
    rw [hXGrad,hF,hsClass_inner_raw,hsClass_inner_raw] at H
    exact H
  have hOutput : ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤(L*‖F‖^2)*r^ν :=
    HGrowth q u Du G (‖F‖^2) hu hG (sq_nonneg _) hGrowth hNat
  have hUMean : (⨍x in ball (0 : Domain n) 1,u x)=0 := by
    rw [average_eq,←mapClass_integral_raw ν X u hu.2.1 hXMap,hMean,smul_zero]
  have hSq : ‖X‖^2≤(C*‖F‖)^2 := by
    have H := native_norm_sq_le_mean_zero_growth ν (L*‖F‖^2) (mul_nonneg hL.le (sq_nonneg _))
      X u Du hu hUMean hXMap hXGrad hOutput
    exact H.trans_eq (by rw [mul_pow,hCSq];dsimp only [A];ring)
  exact (sq_le_sq₀ (norm_nonneg X) (mul_nonneg hC.le (norm_nonneg F))).mp hSq

end StationaryHarmonicMaps.Analysis

end
