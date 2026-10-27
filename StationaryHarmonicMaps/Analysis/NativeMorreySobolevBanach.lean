module

public import StationaryHarmonicMaps.Analysis.MorreyCoefficientBanach
public import HarmonicMaps.Sobolev
import StationaryHarmonicMaps.Analysis.SobolevCutoff
import HarmonicMaps.Analysis.SobolevAECongruence

/-!
# Native Morrey--Sobolev graphs as a closed linear space

The map L2 class and its actual full-HS Morrey derivative class satisfy
the original negative-sign distributional weak-gradient identities.
All compact smooth scalar tests and every domain/target index appear
in the defining kernels. The inherited product norm is the maximum
of the original map L2 norm and the derivative Morrey norm.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped Topology ENNReal ContDiff

noncomputable section

namespace StationaryHarmonicMaps.Analysis

abbrev MapUnitBallL2 (n q : ℕ) :=
  Lp (Ambient q) 2 (volume.restrict (ball (0 : Domain n) 1))

abbrev NativeMorreyAmbient (n q : ℕ) (ν : ℝ) :=
  MapUnitBallL2 n q × MorreyCoefficientSpace n q ν

@[expose] def compactScalarL2Vector {n d : ℕ} (f : Domain n→ℝ)
    (hf : Continuous f) (hc : HasCompactSupport f) (j : Fin d) : MapUnitBallL2 n d :=
  (((hf.smul continuous_const).memLp_of_hasCompactSupport hc.smul_right).restrict
    (ball (0 : Domain n) 1)).toLp (fun x=>f x • EuclideanSpace.single j 1)

theorem compactScalarL2Vector_ae {n d : ℕ} (f : Domain n→ℝ)
    (hf : Continuous f) (hc : HasCompactSupport f) (j : Fin d) :
    (compactScalarL2Vector f hf hc j : Domain n→Ambient d)=ᵐ[volume.restrict (ball (0 : Domain n) 1)]
      (fun x=>f x • EuclideanSpace.single j 1) := by
  change (((((hf.smul continuous_const).memLp_of_hasCompactSupport hc.smul_right).restrict
    (ball (0 : Domain n) 1)).toLp (fun x=>f x • EuclideanSpace.single j 1)) : Domain n→Ambient d)=ᵐ[_]_
  exact MemLp.coeFn_toLp _

@[expose] def nativeMorreyGraphTestMap {n q : ℕ} (ν : ℝ) (i : Fin n) (j : Fin q)
    (ψ : Domain n→ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    NativeMorreyAmbient n q ν →L[ℝ] ℝ := by
  let dψ := fun x=>fderiv ℝ ψ x (EuclideanSpace.single i 1)
  have hdψ : Continuous dψ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdψ : HasCompactSupport dψ := hcψ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  let L : MapUnitBallL2 n q→L[ℝ]ℝ := innerSL ℝ (compactScalarL2Vector dψ hdψ hcdψ j)
  let R : HSUnitBallL2 n q→L[ℝ]ℝ :=
    innerSL ℝ (compactScalarL2Vector ψ hψ.continuous hcψ (finProdFinEquiv (i,j)))
  exact L.comp (ContinuousLinearMap.fst ℝ _ _)+
    R.comp ((morreyCoefficientRecover ν).comp (ContinuousLinearMap.snd ℝ _ _))

@[expose] def nativeMorreySobolevSubmodule (n q : ℕ) (ν : ℝ) :
    Submodule ℝ (NativeMorreyAmbient n q ν) :=
  ⨅i : Fin n,⨅j : Fin q,⨅ψ : Domain n→ℝ,⨅hψ : ContDiff ℝ ∞ ψ,
    ⨅hcψ : HasCompactSupport ψ,⨅_hsψ : tsupport ψ⊆ball (0 : Domain n) 1,
      (nativeMorreyGraphTestMap ν i j ψ hψ hcψ).ker

abbrev NativeMorreySobolevSpace (n q : ℕ) (ν : ℝ) :=
  ↥(nativeMorreySobolevSubmodule n q ν)

theorem mem_nativeMorreySobolevSubmodule_iff {n q : ℕ} (ν : ℝ) (X : NativeMorreyAmbient n q ν) :
    X∈nativeMorreySobolevSubmodule n q ν ↔
      ∀(i : Fin n) (j : Fin q) (ψ : Domain n→ℝ) (hψ : ContDiff ℝ ∞ ψ)
        (hcψ : HasCompactSupport ψ),tsupport ψ⊆ball (0 : Domain n) 1 →
        nativeMorreyGraphTestMap ν i j ψ hψ hcψ X=0 := by
  change X∈(⨅i : Fin n,⨅j : Fin q,⨅ψ : Domain n→ℝ,⨅hψ : ContDiff ℝ ∞ ψ,
    ⨅hcψ : HasCompactSupport ψ,⨅_hsψ : tsupport ψ⊆ball (0 : Domain n) 1,
      (nativeMorreyGraphTestMap ν i j ψ hψ hcψ).ker : Submodule ℝ (NativeMorreyAmbient n q ν)) ↔ _
  simp only [Submodule.mem_iInf,LinearMap.mem_ker]
  rfl

theorem isClosed_nativeMorreySobolevSubmodule (n q : ℕ) (ν : ℝ) :
    IsClosed (nativeMorreySobolevSubmodule n q ν : Set (NativeMorreyAmbient n q ν)) := by
  have hSet : (nativeMorreySobolevSubmodule n q ν : Set (NativeMorreyAmbient n q ν))=
      ⋂i : Fin n,⋂j : Fin q,⋂ψ : Domain n→ℝ,⋂hψ : ContDiff ℝ ∞ ψ,
        ⋂hcψ : HasCompactSupport ψ,⋂_hsψ : tsupport ψ⊆ball (0 : Domain n) 1,
          {X : NativeMorreyAmbient n q ν | nativeMorreyGraphTestMap ν i j ψ hψ hcψ X=0} := by
    ext X
    change X ∈ nativeMorreySobolevSubmodule n q ν ↔ _
    simp only [nativeMorreySobolevSubmodule,Submodule.mem_iInf,mem_iInter,LinearMap.mem_ker,mem_setOf_eq]
    rfl
  rw [hSet]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro ψ
  apply isClosed_iInter
  intro hψ
  apply isClosed_iInter
  intro hcψ
  apply isClosed_iInter
  intro _hsψ
  exact (nativeMorreyGraphTestMap ν i j ψ hψ hcψ).isClosed_ker

instance nativeMorreySobolevSpace_completeSpace (n q : ℕ) (ν : ℝ) :
    CompleteSpace (NativeMorreySobolevSpace n q ν) := by
  letI : IsClosed (nativeMorreySobolevSubmodule n q ν : Set (NativeMorreyAmbient n q ν)) :=
    isClosed_nativeMorreySobolevSubmodule n q ν
  exact IsClosed.completeSpace_coe

theorem compactScalarL2Vector_inner_raw {n d : ℕ} (f : Domain n→ℝ)
    (hf : Continuous f) (hc : HasCompactSupport f) (j : Fin d)
    (u : Domain n→Ambient d)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1))) :
    inner ℝ (compactScalarL2Vector f hf hc j) (hu.toLp u)=
      ∫x in ball (0 : Domain n) 1,f x*(u x) j := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [compactScalarL2Vector_ae f hf hc j,hu.coeFn_toLp] with x hx huX
  rw [hx,huX]
  simp only [real_inner_smul_left,EuclideanSpace.inner_single_left,map_one,one_mul]

theorem nativeMorreyGraphTestMap_apply_raw {n q : ℕ} (ν : ℝ)
    (u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hDu : ∀i,MemLp (fun x=>Du x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (Z : MorreyCoefficientSpace n q ν) (hZ : morreyCoefficientRecover ν Z=hsUnitBallL2Class Du hDu)
    (i : Fin n) (j : Fin q) (ψ : Domain n→ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    nativeMorreyGraphTestMap ν i j ψ hψ hcψ (hu.toLp u,Z)=
      (∫x in ball (0 : Domain n) 1,fderiv ℝ ψ x (EuclideanSpace.single i 1)*(u x) j)+
      (∫x in ball (0 : Domain n) 1,ψ x*(Du x i) j) := by
  let dψ := fun x=>fderiv ℝ ψ x (EuclideanSpace.single i 1)
  have hdψ : Continuous dψ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdψ : HasCompactSupport dψ := hcψ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  change inner ℝ (compactScalarL2Vector dψ hdψ hcdψ j) (hu.toLp u)+
    inner ℝ (compactScalarL2Vector ψ hψ.continuous hcψ (finProdFinEquiv (i,j)))
      (morreyCoefficientRecover ν Z)=_
  rw [hZ,compactScalarL2Vector_inner_raw dψ hdψ hcdψ j u hu]
  have H := compactScalarL2Vector_inner_raw ψ hψ.continuous hcψ (finProdFinEquiv (i,j))
    (hsFlatten Du) (memLp_hs_flatten Du hDu)
  change inner ℝ (compactScalarL2Vector ψ hψ.continuous hcψ (finProdFinEquiv (i,j)))
    (hsUnitBallL2Class Du hDu)=_ at H
  rw [H]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x=>by simp only [hsFlatten,finProdFinEquiv.symm_apply_apply]

private theorem coordinate_integral_smul {n q : ℕ} {μ : Measure (Domain n)}
    (f : Domain n→ℝ) (u : Domain n→Ambient q)
    (hI : Integrable (fun x=>f x • u x) μ) (j : Fin q) :
    (∫x,f x • u x ∂μ) j=∫x,f x*(u x) j ∂μ := by
  have H := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin q=>ℝ) j).integral_comp_comm hI
  calc
    _=∫x,(f x • u x) j ∂μ := H.symm
    _=_ := integral_congr_ae (Eventually.of_forall fun x=>rfl)

theorem nativeMorreyGraphTestMap_zero_of_native {n q : ℕ} (ν : ℝ)
    (u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
    (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (Z : MorreyCoefficientSpace n q ν)
    (hZ : morreyCoefficientRecover ν Z=hsUnitBallL2Class Du hNative.2.2)
    (i : Fin n) (j : Fin q) (ψ : Domain n→ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ⊆ball (0 : Domain n) 1) :
    nativeMorreyGraphTestMap ν i j ψ hψ hcψ (hNative.2.1.toLp u,Z)=0 := by
  have hEq := congrArg (fun z : Ambient q=>z j) (hNative.1.2.2 i ψ hψ hcψ hsψ)
  change (∫x in ball (0 : Domain n) 1,coordinateDerivative ψ hψ i x • u x) j=
    -(∫x in ball (0 : Domain n) 1,ψ x • Du x i) j at hEq
  have hLI : IntegrableOn (fun x=>coordinateDerivative ψ hψ i x • u x) (ball (0 : Domain n) 1) volume :=
    hNative.1.integrable_test_derivative i hψ hcψ hsψ
  have hRI : IntegrableOn (fun x=>ψ x • Du x i) (ball (0 : Domain n) 1) volume :=
    hNative.1.integrable_test_gradient i hψ hcψ hsψ
  rw [coordinate_integral_smul _ _ hLI j,coordinate_integral_smul _ _ hRI j] at hEq
  rw [nativeMorreyGraphTestMap_apply_raw ν u Du hNative.2.1 hNative.2.2 Z hZ i j ψ hψ hcψ]
  change (∫x in ball (0 : Domain n) 1,fderiv ℝ ψ x (EuclideanSpace.single i 1)*(u x) j)=
    -(∫x in ball (0 : Domain n) 1,ψ x*(Du x i) j) at hEq
  linarith only [hEq]

theorem nativeMorrey_pair_mem_of_native {n q : ℕ} (ν : ℝ)
    (u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
    (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (Z : MorreyCoefficientSpace n q ν)
    (hZ : morreyCoefficientRecover ν Z=hsUnitBallL2Class Du hNative.2.2) :
    (hNative.2.1.toLp u,Z)∈nativeMorreySobolevSubmodule n q ν := by
  apply (mem_nativeMorreySobolevSubmodule_iff ν (hNative.2.1.toLp u,Z)).mpr
  intro i j ψ hψ hcψ hsψ
  exact nativeMorreyGraphTestMap_zero_of_native ν u Du hNative Z hZ i j ψ hψ hcψ hsψ

theorem memW12_of_nativeMorrey_pair {n q : ℕ} (ν : ℝ)
    (u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hDu : ∀i,MemLp (fun x=>Du x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (Z : MorreyCoefficientSpace n q ν)
    (hZ : morreyCoefficientRecover ν Z=hsUnitBallL2Class Du hDu)
    (hPair : (hu.toLp u,Z)∈nativeMorreySobolevSubmodule n q ν) :
    MemW12 (ballDomain (0 : Domain n) 1) u Du := by
  have huLoc : LocallyIntegrableOn u (ball (0 : Domain n) 1) volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hu.locallyIntegrable (by norm_num))
  have hDuLoc (i : Fin n) : LocallyIntegrableOn (fun x=>Du x i) (ball (0 : Domain n) 1) volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict ((hDu i).locallyIntegrable (by norm_num))
  refine ⟨⟨huLoc,hDuLoc,?_⟩,hu,hDu⟩
  intro i ψ hψ hcψ hsψ
  let dψ := coordinateDerivative ψ hψ i
  have hdψ : Continuous dψ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdψ : HasCompactSupport dψ := hcψ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hsdψ : tsupport dψ⊆ball (0 : Domain n) 1 :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsψ
  have hLI : IntegrableOn (fun x=>dψ x • u x) (ball (0 : Domain n) 1) volume :=
    (integrable_compact_smul_of_locallyIntegrableOn (Ω:=ballDomain (0 : Domain n) 1) huLoc hdψ hcdψ hsdψ).integrableOn
  have hRI : IntegrableOn (fun x=>ψ x • Du x i) (ball (0 : Domain n) 1) volume :=
    (integrable_compact_smul_of_locallyIntegrableOn (Ω:=ballDomain (0 : Domain n) 1) (hDuLoc i) hψ.continuous hcψ hsψ).integrableOn
  have hTests : ∀i j ψ hψ hcψ,tsupport ψ⊆ball (0 : Domain n) 1 →
      nativeMorreyGraphTestMap ν i j ψ hψ hcψ (hu.toLp u,Z)=0 := by
    exact (mem_nativeMorreySobolevSubmodule_iff ν (hu.toLp u,Z)).mp hPair
  ext j
  change (∫x in ball (0 : Domain n) 1,dψ x • u x) j=
    -(∫x in ball (0 : Domain n) 1,ψ x • Du x i) j
  rw [coordinate_integral_smul _ _ hLI,coordinate_integral_smul _ _ hRI]
  have H := hTests i j ψ hψ hcψ hsψ
  rw [nativeMorreyGraphTestMap_apply_raw ν u Du hu hDu Z hZ i j ψ hψ hcψ] at H
  change (∫x in ball (0 : Domain n) 1,dψ x*(u x) j)+
    (∫x in ball (0 : Domain n) 1,ψ x*(Du x i) j)=0 at H
  linarith only [H]

@[expose] def nativeMorreyMapClass {n q : ℕ} (ν : ℝ) :
    NativeMorreySobolevSpace n q ν→L[ℝ]MapUnitBallL2 n q :=
  (ContinuousLinearMap.fst ℝ _ _).comp (nativeMorreySobolevSubmodule n q ν).subtypeL

@[expose] def nativeMorreyGradientClass {n q : ℕ} (ν : ℝ) :
    NativeMorreySobolevSpace n q ν→L[ℝ]MorreyCoefficientSpace n q ν :=
  (ContinuousLinearMap.snd ℝ _ _).comp (nativeMorreySobolevSubmodule n q ν).subtypeL

@[expose] def nativeMorreyHSClass {n q : ℕ} (ν : ℝ) :
    NativeMorreySobolevSpace n q ν→L[ℝ]HSUnitBallL2 n q :=
  (morreyCoefficientRecover ν).comp (nativeMorreyGradientClass (n:=n) (q:=q) ν)

theorem exists_raw_native_of_nativeMorreySobolev {n q : ℕ} (ν : ℝ)
    (X : NativeMorreySobolevSpace n q ν) :
    ∃(u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
      (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du),
      nativeMorreyMapClass (n:=n) (q:=q) ν X=hNative.2.1.toLp u ∧
      nativeMorreyHSClass (n:=n) (q:=q) ν X=hsUnitBallL2Class Du hNative.2.2 ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤‖nativeMorreyGradientClass (n:=n) (q:=q) ν X‖^2*r^ν := by
  let U : MapUnitBallL2 n q := X.val.1
  let Z : MorreyCoefficientSpace n q ν := X.val.2
  obtain ⟨Du,hDu,hZ,hGrowth⟩ := exists_raw_field_of_morreyCoefficient ν Z
  let u : Domain n→Ambient q := U
  have hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)) := Lp.memLp U
  have hU : hu.toLp u=U := Lp.toLp_coeFn U hu
  have hPair : (hu.toLp u,Z)∈nativeMorreySobolevSubmodule n q ν := by
    have hProd : ((hu.toLp u,Z) : NativeMorreyAmbient n q ν)=X.val := Prod.ext hU rfl
    exact Eq.mpr (congrArg (fun Y : NativeMorreyAmbient n q ν=>Y∈nativeMorreySobolevSubmodule n q ν) hProd) X.property
  have hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du :=
    memW12_of_nativeMorrey_pair ν u Du hu hDu Z hZ hPair
  exact ⟨u,Du,hNative,hU.symm,hZ,hGrowth⟩

theorem existsUnique_nativeMorreySobolev_iff_power_growth {n q : ℕ} (ν : ℝ)
    (u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
    (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du) :
    (∃! X : NativeMorreySobolevSpace n q ν,
      nativeMorreyMapClass (n:=n) (q:=q) ν X=hNative.2.1.toLp u ∧
      nativeMorreyHSClass (n:=n) (q:=q) ν X=hsUnitBallL2Class Du hNative.2.2) ↔
      ∃K : ℝ,0≤K ∧ ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤K*r^ν := by
  constructor
  · rintro ⟨X,⟨_hMap,hGrad⟩,_hUnique⟩
    exact ⟨‖nativeMorreyGradientClass (n:=n) (q:=q) ν X‖^2,sq_nonneg _,
      morreyCoefficient_power_growth ν Du hNative.2.2 (nativeMorreyGradientClass (n:=n) (q:=q) ν X) hGrad⟩
  · intro hGrowth
    have hExists : ∃! Z : MorreyCoefficientSpace n q ν,
        morreyCoefficientRecover ν Z=hsUnitBallL2Class Du hNative.2.2 :=
      (existsUnique_morreyCoefficient_iff_power_growth ν Du hNative.2.2).mpr hGrowth
    obtain ⟨Z,hZ,_hZUnique⟩ := hExists
    let X : NativeMorreySobolevSpace n q ν :=
      ⟨(hNative.2.1.toLp u,Z),nativeMorrey_pair_mem_of_native ν u Du hNative Z hZ⟩
    refine ⟨X,⟨rfl,hZ⟩,?_⟩
    rintro Y ⟨hYMap,hYGrad⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hYMap
    · apply morreyCoefficientRecover_injective ν
      exact hYGrad.trans hZ.symm

theorem nativeMorreySobolev_norm_sq {n q : ℕ} (ν : ℝ)
    (u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
    (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (X : NativeMorreySobolevSpace n q ν)
    (hMap : nativeMorreyMapClass (n:=n) (q:=q) ν X=hNative.2.1.toLp u)
    (hGrad : nativeMorreyHSClass (n:=n) (q:=q) ν X=hsUnitBallL2Class Du hNative.2.2) :
    ‖X‖^2=max (∫x in ball (0 : Domain n) 1,‖u x‖^2)
      (sSup {e : ℝ | ∃a∈ball (0 : Domain n) 1,∃r : ℝ,0<r ∧
        e=r^(-ν)*(∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))}) := by
  have hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)) := hNative.2.1
  have hMapSq : ‖nativeMorreyMapClass (n:=n) (q:=q) ν X‖^2=∫x in ball (0 : Domain n) 1,‖u x‖^2 := by
    calc
      _=‖hu.toLp u‖^2 := congrArg (fun U : MapUnitBallL2 n q=>‖U‖^2) hMap
      _=∫x in ball (0 : Domain n) 1,‖(hu.toLp u) x‖^2 := l2_euclidean_norm_sq _ (hu.toLp u)
      _=_ := integral_congr_ae (hu.coeFn_toLp.mono fun x hx=>congrArg (fun z : Ambient q=>‖z‖^2) hx)
  have hGradSq : ‖nativeMorreyGradientClass (n:=n) (q:=q) ν X‖^2=
      sSup {e : ℝ | ∃a∈ball (0 : Domain n) 1,∃r : ℝ,0<r ∧
        e=r^(-ν)*(∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))} :=
    morreyCoefficient_norm_sq ν Du hNative.2.2 (nativeMorreyGradientClass (n:=n) (q:=q) ν X) hGrad
  calc
    _=max (‖nativeMorreyMapClass (n:=n) (q:=q) ν X‖^2) (‖nativeMorreyGradientClass (n:=n) (q:=q) ν X‖^2) := by
      let a : ℝ := ‖nativeMorreyMapClass (n:=n) (q:=q) ν X‖
      let b : ℝ := ‖nativeMorreyGradientClass (n:=n) (q:=q) ν X‖
      change (max a b)^2=max (a^2) (b^2)
      by_cases hLe : a≤b
      · rw [max_eq_right hLe,max_eq_right (pow_le_pow_left₀ (norm_nonneg _) hLe 2)]
      · have hGe := (not_le.mp hLe).le
        rw [max_eq_left hGe,max_eq_left (pow_le_pow_left₀ (norm_nonneg _) hGe 2)]
    _=_ := congrArg₂ max hMapSq hGradSq

theorem nativeMorreyMapClass_injective {n q : ℕ} (ν : ℝ) :
    Function.Injective (nativeMorreyMapClass (n:=n) (q:=q) ν) := by
  intro X Y hXY
  obtain ⟨u,Du,hU,hXMap,hXGrad,_hXGrowth⟩ := exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=q) ν X
  obtain ⟨v,Dv,hV,hYMap,hYGrad,_hYGrowth⟩ := exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=q) ν Y
  have hMap : hU.2.1.toLp u=hV.2.1.toLp v := hXMap.symm.trans (hXY.trans hYMap)
  have hAE : u=ᵐ[volume.restrict (ball (0 : Domain n) 1)]v :=
    (MemLp.toLp_eq_toLp_iff hU.2.1 hV.2.1).mp hMap
  have hDAE : Du=ᵐ[volume.restrict (ball (0 : Domain n) 1)]Dv :=
    hU.1.ae_eq_of_ae_eq_map hV.1 hAE
  have hCols (i : Fin n) : (fun x=>Du x i)=ᵐ[volume.restrict (ball (0 : Domain n) 1)](fun x=>Dv x i) :=
    hDAE.mono fun x hx=>congrArg (fun A : Gradient n q=>A i) hx
  have hClass : hsUnitBallL2Class Du hU.2.2=hsUnitBallL2Class Dv hV.2.2 :=
    (hsUnitBallL2Class_eq_iff_ae Du Dv hU.2.2 hV.2.2).mpr hCols
  apply Subtype.ext
  apply Prod.ext
  · exact hXY
  · apply morreyCoefficientRecover_injective ν
    exact hXGrad.trans (hClass.trans hYGrad.symm)

theorem nativeMorreySobolev_eq_iff_ae {n q : ℕ} (ν : ℝ)
    (u v : Domain n→Ambient q)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hv : MemLp v 2 (volume.restrict (ball (0 : Domain n) 1)))
    (X Y : NativeMorreySobolevSpace n q ν)
    (hX : nativeMorreyMapClass (n:=n) (q:=q) ν X=hu.toLp u)
    (hY : nativeMorreyMapClass (n:=n) (q:=q) ν Y=hv.toLp v) :
    X=Y ↔ u=ᵐ[volume.restrict (ball (0 : Domain n) 1)]v := by
  constructor
  · intro hXY
    have hMap : hu.toLp u=hv.toLp v := hX.symm.trans
      ((congrArg (nativeMorreyMapClass (n:=n) (q:=q) ν) hXY).trans hY)
    exact (MemLp.toLp_eq_toLp_iff hu hv).mp hMap
  · intro hAE
    apply nativeMorreyMapClass_injective ν
    exact hX.trans (((MemLp.toLp_eq_toLp_iff hu hv).mpr hAE).trans hY.symm)

end StationaryHarmonicMaps.Analysis

end
