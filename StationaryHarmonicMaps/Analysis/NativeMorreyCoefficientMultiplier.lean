module

public import StationaryHarmonicMaps.Analysis.NativeMorreySobolevBanach
import StationaryHarmonicMaps.Analysis.NativeMorreyMeanZero
import StationaryHarmonicMaps.Analysis.StrongerMorreyMeanBound
import StationaryHarmonicMaps.Analysis.NaturalCoefficientNeumannKernel

/-!
# Actual native Morrey maps acting on original coefficient classes

The actual native graph supplies its own stronger gradient growth and
original-value bound. Multiplication acts on every raw L2 representative
of that map and every raw representative of the original coefficient.
The same full-HS product determines one genuine Morrey coefficient class.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

noncomputable section

namespace StationaryHarmonicMaps.Analysis

private theorem multiplier_native_map_norm_le {n k : ℕ} (ν : ℝ)
    (X : NativeMorreySobolevSpace n k ν) :
    ‖nativeMorreyMapClass (n:=n) (q:=k) ν X‖≤‖X‖ := by
  change ‖X.val.1‖≤max ‖X.val.1‖ ‖X.val.2‖
  exact le_max_left _ _

private theorem multiplier_native_gradient_norm_le {n k : ℕ} (ν : ℝ)
    (X : NativeMorreySobolevSpace n k ν) :
    ‖nativeMorreyGradientClass (n:=n) (q:=k) ν X‖≤‖X‖ := by
  change ‖X.val.2‖≤max ‖X.val.1‖ ‖X.val.2‖
  exact le_max_right _ _

private theorem multiplier_original_mean_norm_le {n k : ℕ} (ν : ℝ)
    (u : Domain n→Ambient k)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (X : NativeMorreySobolevSpace n k ν)
    (hMap : nativeMorreyMapClass (n:=n) (q:=k) ν X=hu.toLp u) :
    ‖(⨍x in ball (0 : Domain n) 1,u x)‖≤
      (Real.sqrt (volume.real (ball (0 : Domain n) 1)))⁻¹*‖X‖ := by
  have hAvg : unitBallAverageL2 n k (nativeMorreyMapClass (n:=n) (q:=k) ν X)=
      ⨍x in ball (0 : Domain n) 1,u x :=
    (congrArg (unitBallAverageL2 n k) hMap).trans (unitBallAverageL2_apply_raw u hu)
  calc
    _=‖unitBallAverageL2 n k (nativeMorreyMapClass (n:=n) (q:=k) ν X)‖ := (congrArg norm hAvg).symm
    _≤‖unitBallAverageL2 n k‖*‖nativeMorreyMapClass (n:=n) (q:=k) ν X‖ :=
      (unitBallAverageL2 n k).le_opNorm _
    _≤_ := mul_le_mul (unitBallAverageL2_norm_le n k) (multiplier_native_map_norm_le ν X)
      (norm_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))

private theorem exists_uniform_native_morrey_original_ae_bound
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀(k : ℕ)
      (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ))
      (u : Domain n→Ambient k)
      (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1))),
      nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X=hu.toLp u →
      ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤C*‖X‖ := by
  obtain ⟨H,hH,Hmean⟩ := exists_stronger_morrey_ae_bound_by_mean n hn γ hγ hγTwo
  let A := (Real.sqrt (volume.real (ball (0 : Domain n) 1)))⁻¹
  have hA : 0≤A := inv_nonneg.mpr (Real.sqrt_nonneg _)
  refine ⟨A+H,by dsimp only [A] at hA ⊢;linarith,?_⟩
  intro k X u hu hMap
  let ν := (n : ℝ)-2+γ
  have hData : ∃(v : Domain n→Ambient k) (Dv : Domain n→Gradient n k)
      (hv : MemW12 (ballDomain (0 : Domain n) 1) v Dv),
      nativeMorreyMapClass (n:=n) (q:=k) ν X=hv.2.1.toLp v ∧
      nativeMorreyHSClass (n:=n) (q:=k) ν X=hsUnitBallL2Class (n:=n) (q:=k) Dv hv.2.2 ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dv x))≤
          ‖nativeMorreyGradientClass (n:=n) (q:=k) ν X‖^2*r^ν :=
    exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=k) ν X
  obtain ⟨v,Dv,hv,hVMap,_hVGrad,hGrowth⟩ := hData
  let K := ‖nativeMorreyGradientClass (n:=n) (q:=k) ν X‖^2
  obtain ⟨_V,_hV,_hAE,_hPoint,hBound⟩ := Hmean k v Dv K hv (sq_nonneg _) hGrowth
  have hM : ‖(⨍x in ball (0 : Domain n) 1,v x)‖+H*Real.sqrt K≤(A+H)*‖X‖ := by
    dsimp only [K]
    rw [Real.sqrt_sq (norm_nonneg _)]
    calc
      _≤A*‖X‖+H*‖X‖ := add_le_add (multiplier_original_mean_norm_le ν v hv.2.1 X hVMap)
        (mul_le_mul_of_nonneg_left (multiplier_native_gradient_norm_le ν X) hH.le)
      _=_ := by ring
  have hVLp : MemLp v 2 (volume.restrict (ball (0 : Domain n) 1)) := hv.2.1
  have hClass : hVLp.toLp v=hu.toLp u := hVMap.symm.trans hMap
  have hVU : v=ᵐ[volume.restrict (ball (0 : Domain n) 1)]u :=
    (MemLp.toLp_eq_toLp_iff hVLp hu).mp hClass
  filter_upwards [hBound,hVU] with x hx hxu
  rw [←hxu]
  exact hx.trans hM

private theorem exists_raw_native_map_class {n k : ℕ} (ν : ℝ)
    (X : NativeMorreySobolevSpace n k ν) :
    ∃(u : Domain n→Ambient k)
      (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1))),
      nativeMorreyMapClass (n:=n) (q:=k) ν X=hu.toLp u := by
  obtain ⟨u,Du,hu,hMap,_hGrad,_hGrowth⟩ := exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=k) ν X
  exact ⟨u,hu.2.1,hMap⟩

private theorem bounded_native_coefficient_product_growth {n k m q : ℕ} (ν M : ℝ)
    (hM : 0≤M)
    (B : Ambient k →L[ℝ] (Ambient m →L[ℝ] Ambient q))
    (u : Domain n→Ambient k)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hBound : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M)
    (Fr : Domain n→Gradient n m)
    (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (F : MorreyCoefficientSpace n m ν)
    (hF : morreyCoefficientRecover (n:=n) (q:=m) ν F=hsUnitBallL2Class (n:=n) (q:=m) Fr hFr) :
    (∀i,MemLp (fun x=>B (u x) (Fr x i)) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (fun i=>B (u x) (Fr x i)))≤
          (M*‖B‖*‖F‖)^2*r^ν := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  obtain ⟨hP,_hE⟩ := bilinear_hs_energy_of_bounded_right μ B.flip u hu.aestronglyMeasurable
    M hBound Fr hFr
  have hP' (i : Fin n) : MemLp (fun x=>B (u x) (Fr x i)) 2 μ := by
    simpa only [ContinuousLinearMap.flip_apply] using hP i
  refine ⟨hP',?_⟩
  intro a ha r hr
  let S := ball a r∩ball (0 : Domain n) 1
  have hμ : volume.restrict S≤μ := Measure.restrict_mono_set volume inter_subset_right
  have hFrS (i : Fin n) : MemLp (fun x=>Fr x i) 2 (volume.restrict S) := (hFr i).mono_measure hμ
  have hBoundS := hBound.filter_mono (ae_mono hμ)
  obtain ⟨_hPS,hES⟩ := bilinear_hs_energy_of_bounded_right (volume.restrict S) B.flip u
    (hu.mono_measure hμ).aestronglyMeasurable M hBoundS Fr hFrS
  have hGrowth := morreyCoefficient_power_growth (n:=n) (q:=m) ν Fr hFr F hF a ha r hr
  calc
    _≤(‖B‖*M)^2*(∫x in S,hsNormSq (Fr x)) := by
      simpa only [ContinuousLinearMap.flip_apply,ContinuousLinearMap.opNorm_flip,abs_of_nonneg hM] using hES
    _≤(‖B‖*M)^2*(‖F‖^2*r^ν) := mul_le_mul_of_nonneg_left hGrowth (sq_nonneg _)
    _=_ := by ring

private theorem coefficient_product_class_of_representatives {n k m q : ℕ}
    (B : Ambient k →L[ℝ] (Ambient m →L[ℝ] Ambient q))
    (u v : Domain n→Ambient k)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hv : MemLp v 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hUV : hu.toLp u=hv.toLp v)
    (Fr Gr : Domain n→Gradient n m)
    (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hGr : ∀i,MemLp (fun x=>Gr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hFG : hsUnitBallL2Class (n:=n) (q:=m) Fr hFr=hsUnitBallL2Class (n:=n) (q:=m) Gr hGr)
    (hP : ∀i,MemLp (fun x=>B (u x) (Fr x i)) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    ∃hR : ∀i,MemLp (fun x=>B (v x) (Gr x i)) 2 (volume.restrict (ball (0 : Domain n) 1)),
      hsUnitBallL2Class (n:=n) (q:=q) (fun x i=>B (u x) (Fr x i)) hP=
        hsUnitBallL2Class (n:=n) (q:=q) (fun x i=>B (v x) (Gr x i)) hR := by
  have hUAE : u=ᵐ[volume.restrict (ball (0 : Domain n) 1)]v :=
    (MemLp.toLp_eq_toLp_iff hu hv).mp hUV
  have hFAE := (hsUnitBallL2Class_eq_iff_ae (n:=n) (q:=m) Fr Gr hFr hGr).mp hFG
  have hPAE (i : Fin n) : (fun x=>B (u x) (Fr x i))=ᵐ[volume.restrict (ball (0 : Domain n) 1)]
      (fun x=>B (v x) (Gr x i)) := by
    filter_upwards [hUAE,hFAE i] with x hx hxi
    rw [hx,hxi]
  have hR (i : Fin n) : MemLp (fun x=>B (v x) (Gr x i)) 2
      (volume.restrict (ball (0 : Domain n) 1)) := (hP i).ae_eq (hPAE i)
  exact ⟨hR,(hsUnitBallL2Class_eq_iff_ae (n:=n) (q:=q) _ _ hP hR).mpr hPAE⟩

private theorem multiplier_coefficient_norm_sq_le_growth {n q : ℕ} (ν K : ℝ)
    (P : Domain n→Gradient n q)
    (hP : ∀i,MemLp (fun x=>P x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (Z : MorreyCoefficientSpace n q ν)
    (hZ : morreyCoefficientRecover (n:=n) (q:=q) ν Z=hsUnitBallL2Class (n:=n) (q:=q) P hP)
    (hGrowth : ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (P x))≤K*r^ν) : ‖Z‖^2≤K := by
  rw [morreyCoefficient_norm_sq (n:=n) (q:=q) ν P hP Z hZ]
  have hNe : {e : ℝ | ∃a∈ball (0 : Domain n) 1,∃r : ℝ,0<r ∧
      e=r^(-ν)*(∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (P x))}.Nonempty :=
    ⟨(1 : ℝ)^(-ν)*(∫x in ball (0 : Domain n) 1∩ball (0 : Domain n) 1,hsNormSq (P x)),
      0,mem_ball_self (by norm_num),1,by norm_num,rfl⟩
  apply csSup_le hNe
  rintro _ ⟨a,ha,r,hr,rfl⟩
  have H := mul_le_mul_of_nonneg_left (hGrowth a ha r hr) (Real.rpow_nonneg hr.le (-ν))
  have hCancel : r^(-ν)*r^ν=1 := by rw [←Real.rpow_add hr,neg_add_cancel,Real.rpow_zero]
  exact H.trans_eq (by rw [mul_left_comm,hCancel,mul_one])

private theorem exists_raw_coefficient_class {n m : ℕ} (σ : ℝ)
    (F : MorreyCoefficientSpace n m σ) :
    ∃(Fr : Domain n→Gradient n m)
      (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1))),
      morreyCoefficientRecover (n:=n) (q:=m) σ F=hsUnitBallL2Class (n:=n) (q:=m) Fr hFr := by
  obtain ⟨Fr,hFr,hF,_hGrowth⟩ := exists_raw_field_of_morreyCoefficient (n:=n) (q:=m) σ F
  exact ⟨Fr,hFr,hF⟩

private theorem exists_native_coefficient_product_for_representatives
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ : ℝ) (k m q : ℕ)
    (B : Ambient k →L[ℝ] (Ambient m →L[ℝ] Ambient q))
    (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ))
    (F : MorreyCoefficientSpace n m σ)
    (u : Domain n→Ambient k)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hU : nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X=hu.toLp u)
    (Fr : Domain n→Gradient n m)
    (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hF : morreyCoefficientRecover (n:=n) (q:=m) σ F=hsUnitBallL2Class (n:=n) (q:=m) Fr hFr) :
    ∃(hP : ∀i,MemLp (fun x=>B (u x) (Fr x i)) 2 (volume.restrict (ball (0 : Domain n) 1)))
      (Z : MorreyCoefficientSpace n q σ),
      morreyCoefficientRecover (n:=n) (q:=q) σ Z=
        hsUnitBallL2Class (n:=n) (q:=q) (fun x i=>B (u x) (Fr x i)) hP := by
  obtain ⟨C,hC,Hbound⟩ := exists_uniform_native_morrey_original_ae_bound n hn γ hγ hγTwo
  let M := C*‖X‖
  have hM : 0≤M := mul_nonneg hC.le (norm_nonneg _)
  have hBound : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M := Hbound k X u hu hU
  obtain ⟨hP,hGrowth⟩ := bounded_native_coefficient_product_growth (n:=n) (k:=k) (m:=m) (q:=q)
    σ M hM B u hu hBound Fr hFr F hF
  let P := fun x i=>B (u x) (Fr x i)
  have hZExists : ∃!Z : MorreyCoefficientSpace n q σ,
      morreyCoefficientRecover (n:=n) (q:=q) σ Z=hsUnitBallL2Class (n:=n) (q:=q) P hP :=
    (existsUnique_morreyCoefficient_iff_power_growth (n:=n) (q:=q) σ P hP).mpr
      ⟨(M*‖B‖*‖F‖)^2,sq_nonneg _,hGrowth⟩
  exact ⟨hP,hZExists.choose,hZExists.choose_spec.1⟩

private theorem bounded_coefficient_product_norm {n k m q : ℕ} (σ M : ℝ)
    (hM : 0≤M)
    (B : Ambient k →L[ℝ] (Ambient m →L[ℝ] Ambient q))
    (u : Domain n→Ambient k)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hBound : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M)
    (Fr : Domain n→Gradient n m)
    (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (F : MorreyCoefficientSpace n m σ)
    (hF : morreyCoefficientRecover (n:=n) (q:=m) σ F=hsUnitBallL2Class (n:=n) (q:=m) Fr hFr)
    (Z : MorreyCoefficientSpace n q σ)
    (hP : ∀i,MemLp (fun x=>B (u x) (Fr x i)) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hZ : morreyCoefficientRecover (n:=n) (q:=q) σ Z=
      hsUnitBallL2Class (n:=n) (q:=q) (fun x i=>B (u x) (Fr x i)) hP) :
    ‖Z‖≤M*‖B‖*‖F‖ := by
  obtain ⟨_hP,hGrowth⟩ := bounded_native_coefficient_product_growth (n:=n) (k:=k) (m:=m) (q:=q)
    σ M hM B u hu hBound Fr hFr F hF
  have hSq : ‖Z‖^2≤(M*‖B‖*‖F‖)^2 :=
    multiplier_coefficient_norm_sq_le_growth (n:=n) (q:=q) σ ((M*‖B‖*‖F‖)^2)
      (fun x i=>B (u x) (Fr x i)) hP Z hZ hGrowth
  exact (sq_le_sq₀ (norm_nonneg Z) (mul_nonneg (mul_nonneg hM (norm_nonneg B)) (norm_nonneg F))).mp hSq

/-- The original stronger native map and original coefficient class of
any real exponent determine exactly one class for the literal pointwise
bilinear product on every raw L2 representative. No graph, growth or
boundedness certificate for raw representatives is assumed. -/
theorem existsUnique_native_morrey_coefficient_product
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ : ℝ) (k m q : ℕ) (B : Ambient k →L[ℝ] (Ambient m →L[ℝ] Ambient q))
    (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ))
    (F : MorreyCoefficientSpace n m σ) :
    ∃! Z : MorreyCoefficientSpace n q σ,
      ∀(u : Domain n→Ambient k)
        (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1))),
        nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X=hu.toLp u →
        ∀(Fr : Domain n→Gradient n m)
          (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1))),
          morreyCoefficientRecover (n:=n) (q:=m) σ F=
            hsUnitBallL2Class (n:=n) (q:=m) Fr hFr →
          ∃hP : ∀i,MemLp (fun x=>B (u x) (Fr x i)) 2 (volume.restrict (ball (0 : Domain n) 1)),
            morreyCoefficientRecover (n:=n) (q:=q) σ Z=
              hsUnitBallL2Class (n:=n) (q:=q) (fun x i=>B (u x) (Fr x i)) hP := by
  have hUData : ∃(u : Domain n→Ambient k)
      (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1))),
      nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X=hu.toLp u :=
    exists_raw_native_map_class (n:=n) (k:=k) ((n : ℝ)-2+γ) X
  obtain ⟨u,hu,hU⟩ := hUData
  have hFData : ∃(Fr : Domain n→Gradient n m)
      (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1))),
      morreyCoefficientRecover (n:=n) (q:=m) σ F=hsUnitBallL2Class (n:=n) (q:=m) Fr hFr :=
    exists_raw_coefficient_class (n:=n) (m:=m) σ F
  obtain ⟨Fr,hFr,hF⟩ := hFData
  have hRawProduct : ∃(hP : ∀i,MemLp (fun x=>B (u x) (Fr x i)) 2
      (volume.restrict (ball (0 : Domain n) 1))) (Z : MorreyCoefficientSpace n q σ),
      morreyCoefficientRecover (n:=n) (q:=q) σ Z=
        hsUnitBallL2Class (n:=n) (q:=q) (fun x i=>B (u x) (Fr x i)) hP :=
    exists_native_coefficient_product_for_representatives n hn γ hγ hγTwo σ k m q B X F u hu hU Fr hFr hF
  obtain ⟨hP,Z,hZ⟩ := hRawProduct
  refine ⟨Z,?_,?_⟩
  · intro v hv hV Gr hGr hG
    have hUV : hu.toLp u=hv.toLp v := hU.symm.trans hV
    have hFG : hsUnitBallL2Class (n:=n) (q:=m) Fr hFr=hsUnitBallL2Class (n:=n) (q:=m) Gr hGr :=
      hF.symm.trans hG
    obtain ⟨hR,hClass⟩ := coefficient_product_class_of_representatives (n:=n) (k:=k) (m:=m) (q:=q)
      B u v hu hv hUV Fr Gr hFr hGr hFG hP
    exact ⟨hR,hZ.trans hClass⟩
  · intro W hW
    obtain ⟨hPW,hWClass⟩ := hW u hu hU Fr hFr hF
    apply morreyCoefficientRecover_injective (n:=n) (q:=q) σ
    exact hWClass.trans hZ.symm

/-- The actual coefficient product has a constant depending only on the
strong native exponent data n,γ. In particular it is independent of the
coefficient exponent σ, all finite dimensions and all original classes. -/
theorem exists_uniform_native_morrey_coefficient_product_bound
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀(σ : ℝ) (k m q : ℕ)
      (B : Ambient k →L[ℝ] (Ambient m →L[ℝ] Ambient q))
      (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ))
      (F : MorreyCoefficientSpace n m σ) (Z : MorreyCoefficientSpace n q σ),
      (
      ∀(u : Domain n→Ambient k)
        (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1))),
        nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X=hu.toLp u →
        ∀(Fr : Domain n→Gradient n m)
          (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1))),
          morreyCoefficientRecover (n:=n) (q:=m) σ F=
            hsUnitBallL2Class (n:=n) (q:=m) Fr hFr →
          ∃hP : ∀i,MemLp (fun x=>B (u x) (Fr x i)) 2 (volume.restrict (ball (0 : Domain n) 1)),
            morreyCoefficientRecover (n:=n) (q:=q) σ Z=
              hsUnitBallL2Class (n:=n) (q:=q) (fun x i=>B (u x) (Fr x i)) hP) → ‖Z‖≤C*‖B‖*‖X‖*‖F‖ := by
  obtain ⟨C,hC,Hbound⟩ := exists_uniform_native_morrey_original_ae_bound n hn γ hγ hγTwo
  refine ⟨C,hC,?_⟩
  intro σ k m q B X F Z hCharacter
  have hUData : ∃(u : Domain n→Ambient k)
      (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1))),
      nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X=hu.toLp u :=
    exists_raw_native_map_class (n:=n) (k:=k) ((n : ℝ)-2+γ) X
  obtain ⟨u,hu,hU⟩ := hUData
  have hFData : ∃(Fr : Domain n→Gradient n m)
      (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1))),
      morreyCoefficientRecover (n:=n) (q:=m) σ F=hsUnitBallL2Class (n:=n) (q:=m) Fr hFr :=
    exists_raw_coefficient_class (n:=n) (m:=m) σ F
  obtain ⟨Fr,hFr,hF⟩ := hFData
  obtain ⟨hP,hZ⟩ := hCharacter u hu hU Fr hFr hF
  let M := C*‖X‖
  have hM : 0≤M := mul_nonneg hC.le (norm_nonneg _)
  have hBound : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖u x‖≤M := Hbound k X u hu hU
  have H := bounded_coefficient_product_norm (n:=n) (k:=k) (m:=m) (q:=q)
    σ M hM B u hu hBound Fr hFr F hF Z hP hZ
  exact H.trans_eq (by dsimp only [M];ring)

end StationaryHarmonicMaps.Analysis

end
