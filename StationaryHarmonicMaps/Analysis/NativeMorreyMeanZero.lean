module

public import StationaryHarmonicMaps.Analysis.NativeMorreySobolevBanach
import Mathlib.Analysis.InnerProductSpace.Adjoint
import HolderToCK.Foundation.BallVolume
import HarmonicMaps.Analysis.SobolevPoincare

/-!
# Actual mean-zero native Morrey--Sobolev classes

The map L2 class has its literal original Bochner average as a continuous
linear map. The mean-zero kernel is a closed subspace of the actual
native Morrey--Sobolev Banach space.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped Topology ENNReal

noncomputable section

namespace StationaryHarmonicMaps.Analysis

private def unitBallConstantLpMap (n q : ℕ) : Ambient q→L[ℝ]MapUnitBallL2 n q := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  exact Lp.constL 2 μ ℝ

private theorem unitBallConstantLpMap_ae {n q : ℕ} (c : Ambient q) :
    (unitBallConstantLpMap n q c : Domain n→Ambient q)=ᵐ[volume.restrict (ball (0 : Domain n) 1)]
      (fun _=>c) := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  exact Lp.coeFn_const 2 μ c

private def unitBallAveragingAdjoint (n q : ℕ) : MapUnitBallL2 n q→L[ℝ]Ambient q :=
  (volume.real (ball (0 : Domain n) 1))⁻¹ • (unitBallConstantLpMap n q).adjoint

private theorem unitBallAveragingAdjoint_apply {n q : ℕ} (U : MapUnitBallL2 n q) :
    unitBallAveragingAdjoint n q U=⨍x in ball (0 : Domain n) 1,U x := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hU : MemLp U 2 μ := Lp.memLp U
  have hI : Integrable U μ := hU.integrable (by norm_num)
  have hV : μ.real univ=volume.real (ball (0 : Domain n) 1) :=
    measureReal_restrict_apply_univ (ball (0 : Domain n) 1)
  apply ext_inner_right ℝ
  intro c
  calc
    _=(volume.real (ball (0 : Domain n) 1))⁻¹*inner ℝ U (unitBallConstantLpMap n q c) := by
      change inner ℝ ((volume.real (ball (0 : Domain n) 1))⁻¹ • (unitBallConstantLpMap n q).adjoint U) c=_
      rw [real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left]
    _=(volume.real (ball (0 : Domain n) 1))⁻¹*(∫x,inner ℝ (U x) c ∂μ) := by
      rw [L2.inner_def]
      congr 1
      exact integral_congr_ae ((unitBallConstantLpMap_ae c).mono fun x hx=>congrArg (inner ℝ (U x)) hx)
    _=(volume.real (ball (0 : Domain n) 1))⁻¹*inner ℝ (∫x,U x ∂μ) c := by
      congr 1
      simpa only [real_inner_comm] using integral_inner hI c
    _=inner ℝ (⨍x,U x ∂μ) c := by rw [average_eq,real_inner_smul_left,hV]

private theorem unitBallAveragingAdjoint_norm_le (n q : ℕ) :
    ‖unitBallAveragingAdjoint n q‖≤(Real.sqrt (volume.real (ball (0 : Domain n) 1)))⁻¹ := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let V := volume.real (ball (0 : Domain n) 1)
  have hV : 0<V := HolderToCK.ball_volume_real_pos 0 (by norm_num)
  have hMass : μ.real univ=V := measureReal_restrict_apply_univ (ball (0 : Domain n) 1)
  have hConst : ‖unitBallConstantLpMap n q‖≤Real.sqrt V := by
    have H := Lp.norm_constL_le (E:=Ambient q) (p:=2) (μ:=μ) ℝ
    change ‖unitBallConstantLpMap n q‖≤μ.real univ^((1 : ℝ)/(2 : ENNReal).toReal) at H
    simpa only [hMass,ENNReal.toReal_ofNat,←Real.sqrt_eq_rpow] using H
  have hCancel : V⁻¹*Real.sqrt V=(Real.sqrt V)⁻¹ := by
    have hs := Real.sq_sqrt hV.le
    have hp := Real.sqrt_pos.mpr hV
    field_simp
    nlinarith only [hs,hp]
  calc
    _=V⁻¹*‖unitBallConstantLpMap n q‖ := by
      change ‖V⁻¹ • (unitBallConstantLpMap n q).adjoint‖=_
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hV.le),LinearIsometryEquiv.norm_map]
    _≤V⁻¹*Real.sqrt V := mul_le_mul_of_nonneg_left hConst (inv_nonneg.mpr hV.le)
    _=_ := hCancel

@[expose] def unitBallAverageL2 (n q : ℕ) : MapUnitBallL2 n q→L[ℝ]Ambient q := by
  let L : MapUnitBallL2 n q→ₗ[ℝ]Ambient q :=
    { toFun := fun U=>⨍x in ball (0 : Domain n) 1,U x
      map_add' := by
        intro U V
        rw [←unitBallAveragingAdjoint_apply (U+V)]
        exact ((unitBallAveragingAdjoint n q).map_add U V).trans
          (congrArg₂ (fun u v : Ambient q=>u+v) (unitBallAveragingAdjoint_apply U) (unitBallAveragingAdjoint_apply V))
      map_smul' := by
        intro c U
        simp only [RingHom.id_apply]
        rw [←unitBallAveragingAdjoint_apply (c • U)]
        exact ((unitBallAveragingAdjoint n q).map_smul c U).trans
          (congrArg (fun u : Ambient q=>c • u) (unitBallAveragingAdjoint_apply U)) }
  exact L.mkContinuous (Real.sqrt (volume.real (ball (0 : Domain n) 1)))⁻¹ fun U=>by
    change ‖(⨍x in ball (0 : Domain n) 1,U x)‖≤_
    rw [←unitBallAveragingAdjoint_apply U]
    exact ((unitBallAveragingAdjoint n q).le_opNorm U).trans
      (mul_le_mul_of_nonneg_right (unitBallAveragingAdjoint_norm_le n q) (norm_nonneg U))

theorem unitBallAverageL2_apply {n q : ℕ} (U : MapUnitBallL2 n q) :
    unitBallAverageL2 n q U=⨍x in ball (0 : Domain n) 1,U x := rfl

theorem unitBallAverageL2_norm_le (n q : ℕ) :
    ‖unitBallAverageL2 n q‖≤(Real.sqrt (volume.real (ball (0 : Domain n) 1)))⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  intro U
  rw [unitBallAverageL2_apply,←unitBallAveragingAdjoint_apply U]
  exact ((unitBallAveragingAdjoint n q).le_opNorm U).trans
    (mul_le_mul_of_nonneg_right (unitBallAveragingAdjoint_norm_le n q) (norm_nonneg U))

theorem unitBallAverageL2_apply_raw {n q : ℕ} (u : Domain n→Ambient q)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1))) :
    unitBallAverageL2 n q (hu.toLp u)=⨍x in ball (0 : Domain n) 1,u x := by
  rw [unitBallAverageL2_apply]
  exact average_congr hu.coeFn_toLp

@[expose] def nativeMorreyAverage (n q : ℕ) (ν : ℝ) :
    NativeMorreySobolevSpace n q ν→L[ℝ]Ambient q :=
  (unitBallAverageL2 n q).comp (nativeMorreyMapClass (n:=n) (q:=q) ν)

theorem nativeMorreyAverage_apply_raw {n q : ℕ} (ν : ℝ)
    (u : Domain n→Ambient q) (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (X : NativeMorreySobolevSpace n q ν)
    (hMap : nativeMorreyMapClass (n:=n) (q:=q) ν X=hu.toLp u) :
    nativeMorreyAverage n q ν X=⨍x in ball (0 : Domain n) 1,u x := by
  change unitBallAverageL2 n q (nativeMorreyMapClass (n:=n) (q:=q) ν X)=_
  rw [hMap,unitBallAverageL2_apply_raw]

@[expose] def meanZeroNativeMorreySubmodule (n q : ℕ) (ν : ℝ) :
    Submodule ℝ (NativeMorreySobolevSpace n q ν) := (nativeMorreyAverage n q ν).ker

abbrev MeanZeroNativeMorreySpace (n q : ℕ) (ν : ℝ) :=
  ↥(meanZeroNativeMorreySubmodule n q ν)

instance meanZeroNativeMorreySpace_normedSpace (n q : ℕ) (ν : ℝ) :
    NormedSpace ℝ (MeanZeroNativeMorreySpace n q ν) where
  toModule := (meanZeroNativeMorreySubmodule n q ν).module
  norm_smul_le c X := by
    change ‖c • X.val.val‖≤‖c‖*‖X.val.val‖
    exact norm_smul_le c X.val.val

theorem isClosed_meanZeroNativeMorreySubmodule (n q : ℕ) (ν : ℝ) :
    IsClosed (meanZeroNativeMorreySubmodule n q ν : Set (NativeMorreySobolevSpace n q ν)) :=
  (nativeMorreyAverage n q ν).isClosed_ker

instance meanZeroNativeMorreySpace_completeSpace (n q : ℕ) (ν : ℝ) :
    CompleteSpace (MeanZeroNativeMorreySpace n q ν) := by
  letI : IsClosed (meanZeroNativeMorreySubmodule n q ν : Set (NativeMorreySobolevSpace n q ν)) :=
    isClosed_meanZeroNativeMorreySubmodule n q ν
  exact IsClosed.completeSpace_coe

theorem mem_meanZeroNativeMorreySubmodule_iff {n q : ℕ} (ν : ℝ)
    (u : Domain n→Ambient q) (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (X : NativeMorreySobolevSpace n q ν)
    (hMap : nativeMorreyMapClass (n:=n) (q:=q) ν X=hu.toLp u) :
    X∈meanZeroNativeMorreySubmodule n q ν ↔ (⨍x in ball (0 : Domain n) 1,u x)=0 := by
  change nativeMorreyAverage n q ν X=0 ↔ _
  rw [nativeMorreyAverage_apply_raw ν u hu X hMap]

theorem exists_raw_native_of_meanZeroNativeMorrey {n q : ℕ} (ν : ℝ)
    (X : MeanZeroNativeMorreySpace n q ν) :
    ∃(u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
      (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du),
      (⨍x in ball (0 : Domain n) 1,u x)=0 ∧
      nativeMorreyMapClass (n:=n) (q:=q) ν X.val=hNative.2.1.toLp u ∧
      nativeMorreyHSClass (n:=n) (q:=q) ν X.val=hsUnitBallL2Class Du hNative.2.2 ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤‖nativeMorreyGradientClass (n:=n) (q:=q) ν X.val‖^2*r^ν := by
  let Y : NativeMorreySobolevSpace n q ν := X.val
  have hData : ∃(u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
      (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du),
      nativeMorreyMapClass (n:=n) (q:=q) ν Y=hNative.2.1.toLp u ∧
      nativeMorreyHSClass (n:=n) (q:=q) ν Y=hsUnitBallL2Class Du hNative.2.2 ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤‖nativeMorreyGradientClass (n:=n) (q:=q) ν Y‖^2*r^ν :=
    exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=q) ν Y
  obtain ⟨u,Du,hNative,hMap,hGrad,hGrowth⟩ := hData
  have hMean := (mem_meanZeroNativeMorreySubmodule_iff ν u hNative.2.1 X.val hMap).mp X.property
  exact ⟨u,Du,hNative,hMean,hMap,hGrad,hGrowth⟩

theorem existsUnique_meanZeroNativeMorrey_iff {n q : ℕ} (ν : ℝ)
    (u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
    (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du) :
    (∃! X : MeanZeroNativeMorreySpace n q ν,
      nativeMorreyMapClass (n:=n) (q:=q) ν X.val=hNative.2.1.toLp u ∧
      nativeMorreyHSClass (n:=n) (q:=q) ν X.val=hsUnitBallL2Class Du hNative.2.2) ↔
      (⨍x in ball (0 : Domain n) 1,u x)=0 ∧
      ∃K : ℝ,0≤K ∧ ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤K*r^ν := by
  constructor
  · rintro ⟨X,⟨hMap,hGrad⟩,_hUnique⟩
    have hMean := (mem_meanZeroNativeMorreySubmodule_iff ν u hNative.2.1 X.val hMap).mp X.property
    exact ⟨hMean,‖nativeMorreyGradientClass (n:=n) (q:=q) ν X.val‖^2,sq_nonneg _,
      morreyCoefficient_power_growth ν Du hNative.2.2 (nativeMorreyGradientClass (n:=n) (q:=q) ν X.val) hGrad⟩
  · rintro ⟨hMean,hGrowth⟩
    have hExists : ∃! Y : NativeMorreySobolevSpace n q ν,
        nativeMorreyMapClass (n:=n) (q:=q) ν Y=hNative.2.1.toLp u ∧
        nativeMorreyHSClass (n:=n) (q:=q) ν Y=hsUnitBallL2Class Du hNative.2.2 :=
      (existsUnique_nativeMorreySobolev_iff_power_growth ν u Du hNative).mpr hGrowth
    obtain ⟨Y,⟨hYMap,hYGrad⟩,hYUnique⟩ := hExists
    have hYMean : Y∈meanZeroNativeMorreySubmodule n q ν :=
      (mem_meanZeroNativeMorreySubmodule_iff ν u hNative.2.1 Y hYMap).mpr hMean
    let X : MeanZeroNativeMorreySpace n q ν := ⟨Y,hYMean⟩
    refine ⟨X,⟨hYMap,hYGrad⟩,?_⟩
    rintro Z ⟨hZMap,hZGrad⟩
    apply Subtype.ext
    exact hYUnique Z.val ⟨hZMap,hZGrad⟩

@[expose] def meanZeroNativeMorreyGradientClass (n q : ℕ) (ν : ℝ) :
    MeanZeroNativeMorreySpace n q ν→L[ℝ]MorreyCoefficientSpace n q ν :=
  (nativeMorreyGradientClass (n:=n) (q:=q) ν).comp (meanZeroNativeMorreySubmodule n q ν).subtypeL

private theorem actual_mean_zero_energy_bound {n q : ℕ} (ν K : ℝ)
    (u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
    (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (hMean : (⨍x in ball (0 : Domain n) 1,u x)=0)
    (hGrowth : ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤K*r^ν) :
    (∫x in ball (0 : Domain n) 1,‖u x‖^2)≤(2 : ℝ)^(n+1)*K*(2 : ℝ)^ν := by
  have hPoincare : (∫x in ball (0 : Domain n) 1,‖u x‖^2)≤
      (2 : ℝ)^(n+1)*(∫x in ball (0 : Domain n) 1,hsNormSq (Du x)) := by
    have H := hNative.poincare_ball (by norm_num : (0 : ℝ)<1)
    rw [hMean] at H
    simpa only [sub_zero,one_pow,mul_one] using H
  have hEnergy : (∫x in ball (0 : Domain n) 1,hsNormSq (Du x))≤K*(2 : ℝ)^ν := by
    simpa only [inter_eq_right.mpr (ball_subset_ball (by norm_num : (1 : ℝ)≤2))] using
      hGrowth 0 (mem_ball_self (by norm_num : (0 : ℝ)<1)) 2 (by norm_num)
  exact hPoincare.trans ((mul_le_mul_of_nonneg_left hEnergy (by positivity)).trans_eq (by ring))

theorem exists_meanZeroNativeMorrey_norm_le_gradient (n : ℕ) (ν : ℝ) :
    ∃C : ℝ,0<C ∧ ∀(q : ℕ) (X : MeanZeroNativeMorreySpace n q ν),
      ‖X‖≤C*‖meanZeroNativeMorreyGradientClass n q ν X‖ := by
  let P := (2 : ℝ)^(n+1)*(2 : ℝ)^ν
  have hP : 0≤P := mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
  let C := 1+Real.sqrt P
  have hC : 0<C := by dsimp only [C];positivity
  have hCOne : 1≤C := by dsimp only [C];linarith [Real.sqrt_nonneg P]
  have hPC : P≤C^2 := by
    have hRoot := Real.sq_sqrt hP
    have hNonneg := Real.sqrt_nonneg P
    dsimp only [C]
    nlinarith only [hRoot,hNonneg]
  refine ⟨C,hC,?_⟩
  intro q X
  obtain ⟨u,Du,hNative,hMean,hMap,hGrad,hGrowth⟩ := exists_raw_native_of_meanZeroNativeMorrey (n:=n) (q:=q) ν X
  let G := ‖meanZeroNativeMorreyGradientClass n q ν X‖
  have hG : 0≤G := norm_nonneg _
  have hMapEnergy : (∫x in ball (0 : Domain n) 1,‖u x‖^2)≤P*G^2 := by
    have H := actual_mean_zero_energy_bound ν (G^2) u Du hNative hMean hGrowth
    exact H.trans_eq (by dsimp only [P];ring)
  have hGradSq : G^2=sSup {e : ℝ | ∃a∈ball (0 : Domain n) 1,∃r : ℝ,0<r ∧
      e=r^(-ν)*(∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))} :=
    morreyCoefficient_norm_sq ν Du hNative.2.2 (nativeMorreyGradientClass (n:=n) (q:=q) ν X.val) hGrad
  have hTotalSq : ‖X‖^2=max (∫x in ball (0 : Domain n) 1,‖u x‖^2) (G^2) :=
    (nativeMorreySobolev_norm_sq ν u Du hNative X.val hMap hGrad).trans
      (congrArg (fun r : ℝ=>max (∫x in ball (0 : Domain n) 1,‖u x‖^2) r) hGradSq.symm)
  have hMapBound : (∫x in ball (0 : Domain n) 1,‖u x‖^2)≤(C*G)^2 :=
    hMapEnergy.trans ((mul_le_mul_of_nonneg_right hPC (sq_nonneg G)).trans_eq (mul_pow C G 2).symm)
  have hGradBound : G^2≤(C*G)^2 := by
    have hCG : G≤C*G := le_mul_of_one_le_left hG hCOne
    exact pow_le_pow_left₀ hG hCG 2
  have hSq : ‖X‖^2≤(C*G)^2 := hTotalSq.trans_le (max_le hMapBound hGradBound)
  have hNorm := norm_nonneg X
  have hCG : 0≤C*G := mul_nonneg hC.le hG
  change ‖X‖≤C*G
  nlinarith only [hSq,hNorm,hCG]

theorem meanZeroNativeMorreyGradientClass_injective (n q : ℕ) (ν : ℝ) :
    Function.Injective (meanZeroNativeMorreyGradientClass n q ν) := by
  letI : NormedAddCommGroup (MeanZeroNativeMorreySpace n q ν) := Submodule.normedAddCommGroup _
  obtain ⟨C,hC,hBound⟩ := exists_meanZeroNativeMorrey_norm_le_gradient n ν
  exact ((meanZeroNativeMorreyGradientClass n q ν).antilipschitz_of_bound
    (K:=⟨C,hC.le⟩) (hBound q)).injective

end StationaryHarmonicMaps.Analysis

end
