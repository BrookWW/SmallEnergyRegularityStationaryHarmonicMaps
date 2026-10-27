module

public import StationaryHarmonicMaps.Analysis.SkewMorreyProjectionCoefficient
public import StationaryHarmonicMaps.Analysis.MatrixNativeMorreyConstant
public import StationaryHarmonicMaps.Analysis.NativeMorreyBilinearProduct

/-!
# The actual bounded skew projection of mean-zero native graphs

The literal coefficient half skew part acts through the original constant
native graph and the proved actual native bilinear multiplication.
Mean zero and the full original weak-gradient meaning are retained.
-/

public section
open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff
noncomputable section
namespace StationaryHarmonicMaps.Analysis

private abbrev scalarUnit : Ambient 1 := EuclideanSpace.single 0 1

private def scalarLinearCoefficient {m d : ℕ} (L : Ambient m→L[ℝ]Ambient d) :
    Ambient 1→L[ℝ](Ambient m→L[ℝ]Ambient d) :=
  (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 1=>ℝ) 0).smulRight L

private theorem scalarLinearCoefficient_one {m d : ℕ} (L : Ambient m→L[ℝ]Ambient d)
    (u : Ambient m) : scalarLinearCoefficient L scalarUnit u=L u := by
  simp only [scalarLinearCoefficient,scalarUnit,ContinuousLinearMap.smulRight_apply,
    PiLp.proj_apply,PiLp.single_apply,ite_true,one_smul]

private theorem scalarLinearCoefficient_zero {m d : ℕ} (L : Ambient m→L[ℝ]Ambient d)
    (u : Ambient m) : scalarLinearCoefficient L 0 u=0 :=
  congrArg (fun A : Ambient m→L[ℝ]Ambient d=>A u) (map_zero (scalarLinearCoefficient L))

private theorem scalarLinearCoefficient_norm_le {m d : ℕ} (L : Ambient m→L[ℝ]Ambient d) :
    ‖scalarLinearCoefficient L‖≤‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (scalarLinearCoefficient L) (norm_nonneg L)
  intro z
  change ‖z 0 • L‖≤‖L‖*‖z‖
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le z 0) (norm_nonneg L)).trans_eq (mul_comm _ _)

private abbrev fullNativeLinear (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m d : ℕ} (L : Ambient m→L[ℝ]Ambient d) :
    NativeMorreySobolevSpace n m ((n:ℝ)-2+γ)→L[ℝ]NativeMorreySobolevSpace n d ((n:ℝ)-2+γ) :=
  nativeMorreyBilinear n hn γ hγ hγTwo (scalarLinearCoefficient L)
    (nativeMorreyConstant n 1 ((n:ℝ)-2+γ) scalarUnit)

private theorem fullNativeLinear_map_ae (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m d : ℕ} (L : Ambient m→L[ℝ]Ambient d)
    (X : NativeMorreySobolevSpace n m ((n:ℝ)-2+γ)) :
    ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=d) ((n:ℝ)-2+γ)
        (fullNativeLinear n hn γ hγ hγTwo L X)).val x=
        L ((nativeMorreyMapClass (n:=n) (q:=m) ((n:ℝ)-2+γ) X).val x) := by
  have H := nativeMorreyBilinearProduct_ae n hn γ hγ hγTwo (scalarLinearCoefficient L)
    (nativeMorreyConstant n 1 ((n:ℝ)-2+γ) scalarUnit) X
  change ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
    (nativeMorreyMapClass (n:=n) (q:=d) ((n:ℝ)-2+γ)
      (nativeMorreyBilinearProduct n hn γ hγ hγTwo (scalarLinearCoefficient L)
        (nativeMorreyConstant n 1 ((n:ℝ)-2+γ) scalarUnit) X)).val x=_
  filter_upwards [H,nativeMorreyConstant_ae n 1 ((n:ℝ)-2+γ) scalarUnit] with x hx hc
  exact hx.trans (by rw [hc,scalarLinearCoefficient_one])

private theorem fullNativeLinear_raw (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m d : ℕ} (L : Ambient m→L[ℝ]Ambient d)
    (u : Domain n→Ambient m) (Du : Domain n→Gradient n m)
    (hu : MemW12 (ballDomain (0:Domain n) 1) u Du)
    (X : NativeMorreySobolevSpace n m ((n:ℝ)-2+γ))
    (hMap : nativeMorreyMapClass (n:=n) (q:=m) ((n:ℝ)-2+γ) X=hu.2.1.toLp u) :
    ∃hL : MemW12 (ballDomain (0:Domain n) 1) (fun x=>L (u x)) (fun x i=>L (Du x i)),
      nativeMorreyMapClass (n:=n) (q:=d) ((n:ℝ)-2+γ) (fullNativeLinear n hn γ hγ hγTwo L X)=
        hL.2.1.toLp (fun x=>L (u x)) ∧
      nativeMorreyHSClass (n:=n) (q:=d) ((n:ℝ)-2+γ) (fullNativeLinear n hn γ hγ hγTwo L X)=
        hsUnitBallL2Class (fun x i=>L (Du x i)) hL.2.2 := by
  have H := nativeMorreyBilinearProduct_raw_leibniz n hn γ hγ hγTwo (scalarLinearCoefficient L)
    (fun _=>scalarUnit) (fun _ _=>0) (nativeMorreyConstant_memW12 n 1 scalarUnit)
    (nativeMorreyConstant n 1 ((n:ℝ)-2+γ) scalarUnit)
    (nativeMorreyConstant_map n 1 ((n:ℝ)-2+γ) scalarUnit) u Du hu X hMap
  simpa only [fullNativeLinear,nativeMorreyBilinear_apply,scalarLinearCoefficient_one,
    scalarLinearCoefficient_zero,zero_add] using H

private theorem original_mean_zero_integral {n q : ℕ} (ν : ℝ)
    (X : MeanZeroNativeMorreySpace n q ν) :
    (∫x in ball (0:Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν X.val).val x)=0 := by
  have H : (⨍x in ball (0:Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν X.val).val x)=0 := X.property
  rw [average_eq] at H
  have hV : 0<(volume.restrict (ball (0:Domain n) 1)).real univ := by
    rw [measureReal_restrict_apply_univ]
    exact HolderToCK.ball_volume_real_pos 0 (by norm_num)
  exact (smul_eq_zero.mp H).resolve_left (inv_ne_zero hV.ne')

private theorem fullNativeLinear_mem_meanZero (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m d : ℕ} (L : Ambient m→L[ℝ]Ambient d)
    (X : MeanZeroNativeMorreySpace n m ((n:ℝ)-2+γ)) :
    fullNativeLinear n hn γ hγ hγTwo L X.val∈meanZeroNativeMorreySubmodule n d ((n:ℝ)-2+γ) := by
  let ν : ℝ := (n:ℝ)-2+γ
  let μ := volume.restrict (ball (0:Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let U := nativeMorreyMapClass (n:=n) (q:=m) ν X.val
  have hU : MemLp U 2 μ := Lp.memLp U
  have hUI : Integrable U μ := hU.integrable (by norm_num)
  have hMean : (∫x in ball (0:Domain n) 1,
      (nativeMorreyMapClass (n:=n) (q:=d) ν (fullNativeLinear n hn γ hγ hγTwo L X.val)).val x)=0 := by
    calc
      _=∫x,L (U x) ∂μ := integral_congr_ae (fullNativeLinear_map_ae n hn γ hγ hγTwo L X.val)
      _=L (∫x,U x ∂μ) := L.integral_comp_comm hUI
      _=0 := by rw [original_mean_zero_integral ν X,map_zero]
  change nativeMorreyAverage n d ν _=0
  change (⨍x in ball (0:Domain n) 1,
    (nativeMorreyMapClass (n:=n) (q:=d) ν (fullNativeLinear n hn γ hγ hγTwo L X.val)).val x)=0
  rw [average_eq,hMean,smul_zero]

private theorem fullNativeLinear_norm_bound (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m d : ℕ} (L : Ambient m→L[ℝ]Ambient d) (C : ℝ) (hC : 0≤C)
    (hB : ‖nativeMorreyBilinear n hn γ hγ hγTwo (scalarLinearCoefficient L)‖≤C*‖scalarLinearCoefficient L‖) :
    ‖fullNativeLinear n hn γ hγ hγTwo L‖≤
      C*‖L‖*‖nativeMorreyConstant n 1 ((n:ℝ)-2+γ) scalarUnit‖ := by
  have hAt := (nativeMorreyBilinear n hn γ hγ hγTwo (scalarLinearCoefficient L)).le_opNorm
    (nativeMorreyConstant n 1 ((n:ℝ)-2+γ) scalarUnit)
  exact hAt.trans (mul_le_mul_of_nonneg_right
    (hB.trans (mul_le_mul_of_nonneg_left (scalarLinearCoefficient_norm_le L) hC)) (norm_nonneg _))

private theorem maps_equal_of_same_native_values {n q : ℕ} (ν : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (A D : MeanZeroNativeMorreySpace n (q*q) ν→L[ℝ]SkewMeanZeroNativeMorreySpace n q ν e)
    (hA : ∀X : MeanZeroNativeMorreySpace n (q*q) ν,
      ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
        (nativeMorreyMapClass (n:=n) (q:=q*q) ν (A X).val.val).val x=
          skewMorreyProjectionCoefficient q e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν X.val).val x))
    (hD : ∀X : MeanZeroNativeMorreySpace n (q*q) ν,
      ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
        (nativeMorreyMapClass (n:=n) (q:=q*q) ν (D X).val.val).val x=
          skewMorreyProjectionCoefficient q e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν X.val).val x)) : A=D := by
  apply ContinuousLinearMap.ext
  intro X
  apply Subtype.ext
  apply Subtype.ext
  apply nativeMorreyMapClass_injective (n:=n) (q:=q*q) ν
  apply Lp.ext
  filter_upwards [hA X,hD X] with x hx hDx
  exact hx.trans hDx.symm

private theorem projection_native_value {n q : ℕ} (ν : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (A : MeanZeroNativeMorreySpace n (q*q) ν→L[ℝ]SkewMeanZeroNativeMorreySpace n q ν e)
    (hA : ∀X : MeanZeroNativeMorreySpace n (q*q) ν,
      ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
        (nativeMorreyMapClass (n:=n) (q:=q*q) ν (A X).val.val).val x=
          skewMorreyProjectionCoefficient q e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν X.val).val x))
    (Y : SkewMeanZeroNativeMorreySpace n q ν e) : A Y.val=Y := by
  let U := nativeMorreyMapClass (n:=n) (q:=q*q) ν Y.val.val
  have hU : MemLp U 2 (volume.restrict (ball (0:Domain n) 1)) := Lp.memLp U
  have hSkew : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),star (e (U x))= -(e (U x)) :=
    (mem_skewMeanZeroNativeMorreySubmodule_iff ν e U hU Y.val (Lp.toLp_coeFn U hU).symm).mp Y.property
  apply Subtype.ext
  apply Subtype.ext
  apply nativeMorreyMapClass_injective (n:=n) (q:=q*q) ν
  apply Lp.ext
  filter_upwards [hA Y.val,hSkew] with x hx hs
  exact hx.trans (skewMorreyProjectionCoefficient_eq_self q e (U x) hs)

private theorem projection_fullNative_value (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (q : ℕ) (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (A : MeanZeroNativeMorreySpace n (q*q) ((n:ℝ)-2+γ)→L[ℝ]SkewMeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ) e)
    (hA : ∀X : MeanZeroNativeMorreySpace n (q*q) ((n:ℝ)-2+γ),
      ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
        (nativeMorreyMapClass (n:=n) (q:=q*q) ((n:ℝ)-2+γ) (A X).val.val).val x=
          skewMorreyProjectionCoefficient q e ((nativeMorreyMapClass (n:=n) (q:=q*q) ((n:ℝ)-2+γ) X.val).val x))
    (X : MeanZeroNativeMorreySpace n (q*q) ((n:ℝ)-2+γ)) :
    (A X).val.val=fullNativeLinear n hn γ hγ hγTwo (skewMorreyProjectionCoefficient q e) X.val := by
  apply nativeMorreyMapClass_injective (n:=n) (q:=q*q) ((n:ℝ)-2+γ)
  apply Lp.ext
  filter_upwards [hA X,fullNativeLinear_map_ae n hn γ hγ hγTwo (skewMorreyProjectionCoefficient q e) X.val] with x hx hFx
  exact hx.trans hFx.symm

private theorem exists_projection_map (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (q : ℕ) (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    ∃!A : MeanZeroNativeMorreySpace n (q*q) ((n:ℝ)-2+γ)→L[ℝ]
      SkewMeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ) e,
      ∀X : MeanZeroNativeMorreySpace n (q*q) ((n:ℝ)-2+γ),
        ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
          (nativeMorreyMapClass (n:=n) (q:=q*q) ((n:ℝ)-2+γ) (A X).val.val).val x=
            skewMorreyProjectionCoefficient q e
              ((nativeMorreyMapClass (n:=n) (q:=q*q) ((n:ℝ)-2+γ) X.val).val x) := by
  let ν : ℝ := (n:ℝ)-2+γ
  let V := MeanZeroNativeMorreySpace n (q*q) ν
  let M := meanZeroNativeMorreySubmodule n (q*q) ν
  let S := skewMeanZeroNativeMorreySubmodule n q ν e
  let P := skewMorreyProjectionCoefficient q e
  let F := fullNativeLinear n hn γ hγ hγTwo P
  let I : V→L[ℝ]NativeMorreySobolevSpace n (q*q) ν := F.comp M.subtypeL
  have hI (X : V) : I X∈M := fullNativeLinear_mem_meanZero n hn γ hγ hγTwo P X
  let A₀ : V→L[ℝ]V := I.codRestrict M hI
  have hSkew (X : V) : A₀ X∈S := by
    let U := nativeMorreyMapClass (n:=n) (q:=q*q) ν (A₀ X).val
    have hU : MemLp U 2 (volume.restrict (ball (0:Domain n) 1)) := Lp.memLp U
    apply (mem_skewMeanZeroNativeMorreySubmodule_iff ν e U hU (A₀ X) (Lp.toLp_coeFn U hU).symm).mpr
    have H := fullNativeLinear_map_ae n hn γ hγ hγTwo P X.val
    filter_upwards [H] with x hx
    exact (congrArg (fun z : Ambient (q*q)=>star (e z)) hx).trans
      ((skewMorreyProjectionCoefficient_skew q e _).trans (congrArg (fun z : Ambient (q*q)=>-(e z)) hx.symm))
  let A : V→L[ℝ]SkewMeanZeroNativeMorreySpace n q ν e := A₀.codRestrict S hSkew
  have hA (X : V) : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q*q) ν (A X).val.val).val x=
        P ((nativeMorreyMapClass (n:=n) (q:=q*q) ν X.val).val x) :=
    fullNativeLinear_map_ae n hn γ hγ hγTwo P X.val
  refine ⟨A,hA,?_⟩
  intro D hD
  exact maps_equal_of_same_native_values ν e D A hD hA

private theorem projection_bound_pointwise (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (q : ℕ) (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (C : ℝ) (hC : 0≤C)
    (hB : ‖nativeMorreyBilinear n hn γ hγ hγTwo (scalarLinearCoefficient (skewMorreyProjectionCoefficient q e))‖≤
      C*‖scalarLinearCoefficient (skewMorreyProjectionCoefficient q e)‖)
    (A : MeanZeroNativeMorreySpace n (q*q) ((n:ℝ)-2+γ)→L[ℝ]SkewMeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ) e)
    (hA : ∀X : MeanZeroNativeMorreySpace n (q*q) ((n:ℝ)-2+γ),
      ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
        (nativeMorreyMapClass (n:=n) (q:=q*q) ((n:ℝ)-2+γ) (A X).val.val).val x=
          skewMorreyProjectionCoefficient q e ((nativeMorreyMapClass (n:=n) (q:=q*q) ((n:ℝ)-2+γ) X.val).val x))
    (X : MeanZeroNativeMorreySpace n (q*q) ((n:ℝ)-2+γ)) :
    ‖A X‖≤(C*‖skewMorreyProjectionCoefficient q e‖*‖nativeMorreyConstant n 1 ((n:ℝ)-2+γ) scalarUnit‖)*‖X‖ := by
  let F := fullNativeLinear n hn γ hγ hγTwo (skewMorreyProjectionCoefficient q e)
  have hValue := projection_fullNative_value n hn γ hγ hγTwo q e A hA X
  have hNormValue : ‖A X‖=‖F X.val‖ := by
    change ‖(A X).val.val‖=‖F X.val‖
    exact congrArg (fun Y : NativeMorreySobolevSpace n (q*q) ((n:ℝ)-2+γ)=>‖Y‖) hValue
  calc
    _=‖F X.val‖ := hNormValue
    _≤‖F‖*‖X.val‖ := F.le_opNorm X.val
    _≤_ := mul_le_mul_of_nonneg_right
      (fullNativeLinear_norm_bound n hn γ hγ hγTwo (skewMorreyProjectionCoefficient q e) C hC hB) (norm_nonneg X.val)

private theorem projection_raw_native (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (q : ℕ) (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (A : MeanZeroNativeMorreySpace n (q*q) ((n:ℝ)-2+γ)→L[ℝ]SkewMeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ) e)
    (hA : ∀X : MeanZeroNativeMorreySpace n (q*q) ((n:ℝ)-2+γ),
      ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
        (nativeMorreyMapClass (n:=n) (q:=q*q) ((n:ℝ)-2+γ) (A X).val.val).val x=
          skewMorreyProjectionCoefficient q e ((nativeMorreyMapClass (n:=n) (q:=q*q) ((n:ℝ)-2+γ) X.val).val x))
    (X : MeanZeroNativeMorreySpace n (q*q) ((n:ℝ)-2+γ))
    (u : Domain n→Ambient (q*q)) (Du : Domain n→Gradient n (q*q))
    (hu : MemW12 (ballDomain (0:Domain n) 1) u Du)
    (hMap : nativeMorreyMapClass (n:=n) (q:=q*q) ((n:ℝ)-2+γ) X.val=hu.2.1.toLp u) :
    ∃hP : MemW12 (ballDomain (0:Domain n) 1)
        (fun x=>skewMorreyProjectionCoefficient q e (u x)) (fun x i=>skewMorreyProjectionCoefficient q e (Du x i)),
      (⨍x in ball (0:Domain n) 1,skewMorreyProjectionCoefficient q e (u x))=0 ∧
      nativeMorreyMapClass (n:=n) (q:=q*q) ((n:ℝ)-2+γ) (A X).val.val=
        hP.2.1.toLp (fun x=>skewMorreyProjectionCoefficient q e (u x)) ∧
      nativeMorreyHSClass (n:=n) (q:=q*q) ((n:ℝ)-2+γ) (A X).val.val=
        hsUnitBallL2Class (fun x i=>skewMorreyProjectionCoefficient q e (Du x i)) hP.2.2 := by
  have H := fullNativeLinear_raw n hn γ hγ hγTwo (skewMorreyProjectionCoefficient q e) u Du hu X.val hMap
  let hP := H.choose
  have hValue := projection_fullNative_value n hn γ hγ hγTwo q e A hA X
  have hPMap := (congrArg (nativeMorreyMapClass (n:=n) (q:=q*q) ((n:ℝ)-2+γ)) hValue).trans H.choose_spec.1
  have hPGrad := (congrArg (nativeMorreyHSClass (n:=n) (q:=q*q) ((n:ℝ)-2+γ)) hValue).trans H.choose_spec.2
  have hMean : (⨍x in ball (0:Domain n) 1,skewMorreyProjectionCoefficient q e (u x))=0 :=
    (mem_meanZeroNativeMorreySubmodule_iff ((n:ℝ)-2+γ) _ hP.2.1 (A X).val.val hPMap).mp (A X).val.property
  exact ⟨hP,hMean,hPMap,hPGrad⟩

/-! The defining AE value determines the whole bounded projection. -/

theorem skew_native_projection_maps_unique {n q : ℕ} (ν : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (A D : MeanZeroNativeMorreySpace n (q*q) ν→L[ℝ]SkewMeanZeroNativeMorreySpace n q ν e)
    (hA : ∀X : MeanZeroNativeMorreySpace n (q*q) ν,
      ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
        (nativeMorreyMapClass (n:=n) (q:=q*q) ν (A X).val.val).val x=
          skewMorreyProjectionCoefficient q e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν X.val).val x))
    (hD : ∀X : MeanZeroNativeMorreySpace n (q*q) ν,
      ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
        (nativeMorreyMapClass (n:=n) (q:=q*q) ν (D X).val.val).val x=
          skewMorreyProjectionCoefficient q e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν X.val).val x)) : A=D := by
  exact maps_equal_of_same_native_values ν e A D hA hD

/-- The complete original half skew part gives a unique actual bounded
projection of mean-zero native graphs, with raw map and gradient meaning,
identity on the same skew subspace and the unchanged inherited norm. -/
theorem exists_unique_bounded_skew_native_projection
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    let ν : ℝ := (n:ℝ)-2+γ
    ∃C : ℝ,0<C ∧ ∀(q : ℕ) (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)),
      let S := SkewMeanZeroNativeMorreySpace n q ν e
      letI : NormedAddCommGroup S := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
      letI : SeminormedAddCommGroup S :=
        (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
      letI : NormedSpace ℝ S := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
      ∃!A : MeanZeroNativeMorreySpace n (q*q) ν→L[ℝ]S,
        (∀X : MeanZeroNativeMorreySpace n (q*q) ν,
          ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),
            (nativeMorreyMapClass (n:=n) (q:=q*q) ν (A X).val.val).val x=
              skewMorreyProjectionCoefficient q e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν X.val).val x)) ∧
        (∀(X : MeanZeroNativeMorreySpace n (q*q) ν)
          (u : Domain n→Ambient (q*q)) (Du : Domain n→Gradient n (q*q))
          (hu : MemW12 (ballDomain (0:Domain n) 1) u Du),
          nativeMorreyMapClass (n:=n) (q:=q*q) ν X.val=hu.2.1.toLp u →
          ∃hP : MemW12 (ballDomain (0:Domain n) 1)
              (fun x=>skewMorreyProjectionCoefficient q e (u x)) (fun x i=>skewMorreyProjectionCoefficient q e (Du x i)),
            (⨍x in ball (0:Domain n) 1,skewMorreyProjectionCoefficient q e (u x))=0 ∧
            nativeMorreyMapClass (n:=n) (q:=q*q) ν (A X).val.val=
              hP.2.1.toLp (fun x=>skewMorreyProjectionCoefficient q e (u x)) ∧
            nativeMorreyHSClass (n:=n) (q:=q*q) ν (A X).val.val=
              hsUnitBallL2Class (fun x i=>skewMorreyProjectionCoefficient q e (Du x i)) hP.2.2) ∧
        (∀Y : S,A Y.val=Y) ∧
        A.comp (skewMeanZeroNativeMorreySubmodule n q ν e).subtypeL=ContinuousLinearMap.id ℝ S ∧
        ‖A‖≤C*‖skewMorreyProjectionCoefficient q e‖ := by
  let ν : ℝ := (n:ℝ)-2+γ
  have hBound := exists_nativeMorreyBilinear_norm_bound n hn γ hγ hγTwo
  let C₀ := hBound.choose
  have hC₀ : 0<C₀ := hBound.choose_spec.1
  let U := nativeMorreyConstant n 1 ν scalarUnit
  let C := C₀*(1+‖U‖)
  have hC : 0<C := mul_pos hC₀ (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg U))
  refine ⟨C,hC,?_⟩
  intro q e
  let S := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup S := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup S :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ S := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  have hExists := exists_projection_map n hn γ hγ hγTwo q e
  let A := hExists.choose
  have hA := hExists.choose_spec.1
  have hValue (Y : S) : A Y.val=Y := projection_native_value ν e A hA Y
  have hRight : A.comp (skewMeanZeroNativeMorreySubmodule n q ν e).subtypeL=ContinuousLinearMap.id ℝ S := by
    apply ContinuousLinearMap.ext
    intro Y
    exact hValue Y
  have hNorm : ‖A‖≤C*‖skewMorreyProjectionCoefficient q e‖ := by
    apply ContinuousLinearMap.opNorm_le_bound A (mul_nonneg hC.le (norm_nonneg (skewMorreyProjectionCoefficient q e)))
    intro X
    have H := projection_bound_pointwise n hn γ hγ hγTwo q e C₀ hC₀.le
      (hBound.choose_spec.2 1 (q*q) (q*q) (scalarLinearCoefficient (skewMorreyProjectionCoefficient q e))) A hA X
    have hCoeff : C₀*‖skewMorreyProjectionCoefficient q e‖*‖U‖≤C*‖skewMorreyProjectionCoefficient q e‖ := by
      calc
        _=C₀*‖U‖*‖skewMorreyProjectionCoefficient q e‖ := by ring
        _≤C₀*(1+‖U‖)*‖skewMorreyProjectionCoefficient q e‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith only [norm_nonneg U] : ‖U‖≤1+‖U‖) hC₀.le)
          (norm_nonneg (skewMorreyProjectionCoefficient q e))
        _=_ := rfl
    exact H.trans (mul_le_mul_of_nonneg_right hCoeff (norm_nonneg X))
  refine ⟨A,⟨hA,?_,hValue,hRight,hNorm⟩,?_⟩
  · intro X u Du hu hMap
    exact projection_raw_native n hn γ hγ hγTwo q e A hA X u Du hu hMap
  · intro D hD
    exact hExists.choose_spec.2 D hD.1

end StationaryHarmonicMaps.Analysis
end
