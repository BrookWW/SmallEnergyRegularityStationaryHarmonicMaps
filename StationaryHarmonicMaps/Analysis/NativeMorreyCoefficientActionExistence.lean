module

public import StationaryHarmonicMaps.Analysis.NativeMorreyCoefficientMultiplier
public import StationaryHarmonicMaps.Analysis.NativeMorreyBilinearProduct
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The actual bounded bilinear coefficient action

The stronger native map acts on every coefficient exponent through the
literal raw product. The unique bounded bilinear map retains the complete
original-representative characteristic on the whole unit ball.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

noncomputable section

namespace StationaryHarmonicMaps.Analysis

/-- The literal inherited normed group of the actual coefficient submodule. -/
abbrev canonicalMorreyCoefficientGroup (n q : ℕ) (σ : ℝ) :
    NormedAddCommGroup (MorreyCoefficientSpace n q σ) :=
  Submodule.normedAddCommGroup (morreyCoefficientSubmodule n q σ)
/-- The seminormed parent of the same inherited coefficient norm. -/
abbrev canonicalMorreyCoefficientSeminormedGroup (n q : ℕ) (σ : ℝ) :
    SeminormedAddCommGroup (MorreyCoefficientSpace n q σ) :=
  (Submodule.normedAddCommGroup (morreyCoefficientSubmodule n q σ)).toSeminormedAddCommGroup
/-- The literal inherited real normed-space structure of the coefficient class. -/
abbrev canonicalMorreyCoefficientNormedSpace (n q : ℕ) (σ : ℝ) :
    NormedSpace ℝ (MorreyCoefficientSpace n q σ) :=
  Submodule.normedSpace (morreyCoefficientSubmodule n q σ)

attribute [instance] canonicalMorreyCoefficientGroup canonicalMorreyCoefficientSeminormedGroup
  canonicalMorreyCoefficientNormedSpace

private def coefficientProduct
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ : ℝ) {k m q : ℕ} (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) (F : MorreyCoefficientSpace n m σ) :
    MorreyCoefficientSpace n q σ :=
  Classical.choose (existsUnique_native_morrey_coefficient_product n hn γ hγ hγTwo σ k m q B X F).exists

private theorem coefficientProduct_raw
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ : ℝ) {k m q : ℕ} (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) (F : MorreyCoefficientSpace n m σ)
    (u : Domain n→Ambient k)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hU : nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X=hu.toLp u)
    (Fr : Domain n→Gradient n m)
    (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hF : morreyCoefficientRecover (n:=n) (q:=m) σ F=hsUnitBallL2Class Fr hFr) :
    ∃hP : ∀i,MemLp (fun x=>B (u x) (Fr x i)) 2 (volume.restrict (ball (0 : Domain n) 1)),
      morreyCoefficientRecover (n:=n) (q:=q) σ (coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X F)=
        hsUnitBallL2Class (fun x i=>B (u x) (Fr x i)) hP :=
  Classical.choose_spec (existsUnique_native_morrey_coefficient_product n hn γ hγ hγTwo σ k m q B X F).exists u hu hU Fr hFr hF

private theorem rawMapData {n k : ℕ} (ν : ℝ) (X : NativeMorreySobolevSpace n k ν) :
    ∃(u : Domain n→Ambient k) (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1))),
      nativeMorreyMapClass (n:=n) (q:=k) ν X=hu.toLp u := by
  obtain ⟨u,Du,hu,hMap,_hGradient,_hGrowth⟩ := exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=k) ν X
  exact ⟨u,hu.2.1,hMap⟩

private theorem rawCoefficientData {n m : ℕ} (σ : ℝ) (F : MorreyCoefficientSpace n m σ) :
    ∃(Fr : Domain n→Gradient n m)
      (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1))),
      morreyCoefficientRecover (n:=n) (q:=m) σ F=hsUnitBallL2Class Fr hFr := by
  obtain ⟨Fr,hFr,hF,_hGrowth⟩ := exists_raw_field_of_morreyCoefficient (n:=n) (q:=m) σ F
  exact ⟨Fr,hFr,hF⟩

private theorem rawMap_add {n k : ℕ} (ν : ℝ)
    (X Y : NativeMorreySobolevSpace n k ν)
    (u v : Domain n→Ambient k)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hv : MemLp v 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hU : nativeMorreyMapClass (n:=n) (q:=k) ν X=hu.toLp u)
    (hV : nativeMorreyMapClass (n:=n) (q:=k) ν Y=hv.toLp v) :
    nativeMorreyMapClass (n:=n) (q:=k) ν (X+Y)=(hu.add hv).toLp (u+v) := by
  rw [map_add,hU,hV,MemLp.toLp_add]

private theorem rawMap_smul {n k : ℕ} (ν c : ℝ)
    (X : NativeMorreySobolevSpace n k ν) (u : Domain n→Ambient k)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hU : nativeMorreyMapClass (n:=n) (q:=k) ν X=hu.toLp u) :
    nativeMorreyMapClass (n:=n) (q:=k) ν (c • X)=(hu.const_smul c).toLp (c • u) := by
  rw [map_smul,hU]
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul c (hu.toLp u),(hu.const_smul c).coeFn_toLp,hu.coeFn_toLp] with x hx hy hz
  rw [hx,hy]
  simp only [Pi.smul_apply]
  rw [hz]

private theorem coefficientProduct_add_left
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ : ℝ) {k m q : ℕ} (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient q))
    (X Y : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) (F : MorreyCoefficientSpace n m σ) :
    coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B (X+Y) F=
      coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X F+coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B Y F := by
  obtain ⟨u,hu,hU⟩ := rawMapData (n:=n) (k:=k) ((n : ℝ)-2+γ) X
  obtain ⟨v,hv,hV⟩ := rawMapData (n:=n) (k:=k) ((n : ℝ)-2+γ) Y
  obtain ⟨Fr,hFr,hF⟩ := rawCoefficientData (n:=n) (m:=m) σ F
  obtain ⟨hP,hZ⟩ := coefficientProduct_raw (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X F u hu hU Fr hFr hF
  obtain ⟨hQ,hW⟩ := coefficientProduct_raw (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B Y F v hv hV Fr hFr hF
  obtain ⟨hR,hSum⟩ := coefficientProduct_raw (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B (X+Y) F (u+v)
    (hu.add hv) (rawMap_add _ X Y u v hu hv hU hV) Fr hFr hF
  apply morreyCoefficientRecover_injective (n:=n) (q:=q) σ
  rw [hSum,map_add,hZ,hW,←hsUnitBallL2Class_add]
  apply (hsUnitBallL2Class_eq_iff_ae _ _ _ _).mpr
  intro i
  exact Eventually.of_forall fun x=>by simp only [Pi.add_apply,map_add,add_apply]

private theorem coefficientProduct_add_right
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ : ℝ) {k m q : ℕ} (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) (F G : MorreyCoefficientSpace n m σ) :
    coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X (F+G)=
      coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X F+coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X G := by
  obtain ⟨u,hu,hU⟩ := rawMapData (n:=n) (k:=k) ((n : ℝ)-2+γ) X
  obtain ⟨Fr,hFr,hF⟩ := rawCoefficientData (n:=n) (m:=m) σ F
  obtain ⟨Gr,hGr,hG⟩ := rawCoefficientData (n:=n) (m:=m) σ G
  obtain ⟨hP,hZ⟩ := coefficientProduct_raw (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X F u hu hU Fr hFr hF
  obtain ⟨hQ,hW⟩ := coefficientProduct_raw (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X G u hu hU Gr hGr hG
  obtain ⟨hR,hSum⟩ := coefficientProduct_raw (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X (F+G) u hu hU
    (fun x i=>Fr x i+Gr x i) (fun i=>(hFr i).add (hGr i))
      (morreyCoefficientRecover_add_raw σ Fr Gr hFr hGr F G hF hG)
  apply morreyCoefficientRecover_injective (n:=n) (q:=q) σ
  rw [hSum,map_add,hZ,hW,←hsUnitBallL2Class_add]
  apply (hsUnitBallL2Class_eq_iff_ae _ _ _ _).mpr
  intro i
  exact Eventually.of_forall fun x=>(B (u x)).map_add (Fr x i) (Gr x i)

private theorem coefficientProduct_smul_left_of_raw
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ c : ℝ) {k m q : ℕ} (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) (F : MorreyCoefficientSpace n m σ)
    (u : Domain n→Ambient k)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hU : nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X=hu.toLp u)
    (Fr : Domain n→Gradient n m)
    (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hF : morreyCoefficientRecover (n:=n) (q:=m) σ F=hsUnitBallL2Class Fr hFr)
    (Z : MorreyCoefficientSpace n q σ)
    (hP : ∀i,MemLp (fun x=>B (u x) (Fr x i)) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hZ : morreyCoefficientRecover (n:=n) (q:=q) σ Z=hsUnitBallL2Class (fun x i=>B (u x) (Fr x i)) hP) :
    coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B (c • X) F=c • Z := by
  obtain ⟨hR,hScaled⟩ := coefficientProduct_raw (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B (c • X) F (c • u)
    (hu.const_smul c) (rawMap_smul _ c X u hu hU) Fr hFr hF
  have hClasses : hsUnitBallL2Class (n:=n) (q:=q) (fun x i=>B ((c • u) x) (Fr x i)) hR=
      hsUnitBallL2Class (fun x i=>c • B (u x) (Fr x i)) (fun i=>(hP i).const_smul c) := by
    apply (hsUnitBallL2Class_eq_iff_ae _ _ _ _).mpr
    intro i
    exact Eventually.of_forall fun x=>by simp only [Pi.smul_apply,map_smul,smul_apply]
  have hCandidate := morreyCoefficientRecover_smul_raw (n:=n) (q:=q) σ c
    (fun x i=>B (u x) (Fr x i)) hP Z hZ
  apply morreyCoefficientRecover_injective (n:=n) (q:=q) σ
  exact hScaled.trans (hClasses.trans hCandidate.symm)

private theorem coefficientProduct_smul_left
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ c : ℝ) {k m q : ℕ} (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) (F : MorreyCoefficientSpace n m σ) :
    coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B (c • X) F=
      c • coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X F := by
  obtain ⟨u,hu,hU⟩ := rawMapData (n:=n) (k:=k) ((n : ℝ)-2+γ) X
  obtain ⟨Fr,hFr,hF⟩ := rawCoefficientData (n:=n) (m:=m) σ F
  obtain ⟨hP,hZ⟩ := coefficientProduct_raw (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X F u hu hU Fr hFr hF
  exact coefficientProduct_smul_left_of_raw n hn γ hγ hγTwo σ c B X F u hu hU Fr hFr hF _ hP hZ

private theorem coefficientProduct_smul_right
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ c : ℝ) {k m q : ℕ} (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) (F : MorreyCoefficientSpace n m σ) :
    coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X (c • F)=
      c • coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X F := by
  obtain ⟨u,hu,hU⟩ := rawMapData (n:=n) (k:=k) ((n : ℝ)-2+γ) X
  obtain ⟨Fr,hFr,hF⟩ := rawCoefficientData (n:=n) (m:=m) σ F
  obtain ⟨hP,hZ⟩ := coefficientProduct_raw (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X F u hu hU Fr hFr hF
  obtain ⟨hR,hScaled⟩ := coefficientProduct_raw (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X (c • F) u hu hU
    (fun x i=>c • Fr x i) (fun i=>(hFr i).const_smul c)
      (morreyCoefficientRecover_smul_raw σ c Fr hFr F hF)
  apply morreyCoefficientRecover_injective (n:=n) (q:=q) σ
  rw [hScaled,map_smul,hZ,←hsUnitBallL2Class_smul]
  apply (hsUnitBallL2Class_eq_iff_ae _ _ _ _).mpr
  intro i
  exact Eventually.of_forall fun x=>(B (u x)).map_smul c (Fr x i)

private theorem exists_coefficientProduct_bound
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀(σ : ℝ) (k m q : ℕ)
      (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient q))
      (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) (F : MorreyCoefficientSpace n m σ),
      ‖coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X F‖≤C*‖B‖*‖X‖*‖F‖ := by
  obtain ⟨C,hC,Hbound⟩ := exists_uniform_native_morrey_coefficient_product_bound n hn γ hγ hγTwo
  refine ⟨C,hC,?_⟩
  intro σ k m q B X F
  exact Hbound σ k m q B X F _ (coefficientProduct_raw (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X F)

private theorem coefficient_class_eq_product_of_character
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ : ℝ) {k m q : ℕ} (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) (F : MorreyCoefficientSpace n m σ)
    (Z : MorreyCoefficientSpace n q σ)
    (hZ : ∀(u : Domain n→Ambient k) (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1))),
      nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X=hu.toLp u →
      ∀(Fr : Domain n→Gradient n m)
        (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1))),
        morreyCoefficientRecover (n:=n) (q:=m) σ F=hsUnitBallL2Class Fr hFr →
        ∃hP : ∀i,MemLp (fun x=>B (u x) (Fr x i)) 2 (volume.restrict (ball (0 : Domain n) 1)),
          morreyCoefficientRecover (n:=n) (q:=q) σ Z=
            hsUnitBallL2Class (fun x i=>B (u x) (Fr x i)) hP) :
    Z=coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B X F :=
  (existsUnique_native_morrey_coefficient_product n hn γ hγ hγTwo σ k m q B X F).unique hZ
    (coefficientProduct_raw n hn γ hγ hγTwo σ B X F)

private def coefficientLinearAction
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (σ : ℝ) {k m q : ℕ} (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient q)) :
    NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)→ₗ[ℝ]
      MorreyCoefficientSpace n m σ→ₗ[ℝ]MorreyCoefficientSpace n q σ :=
  LinearMap.mk₂ ℝ (coefficientProduct (k:=k) (m:=m) (q:=q) n hn γ hγ hγTwo σ B)
    (coefficientProduct_add_left n hn γ hγ hγTwo σ B)
    (fun c X F=>coefficientProduct_smul_left n hn γ hγ hγTwo σ c B X F)
    (coefficientProduct_add_right n hn γ hγ hγTwo σ B)
    (fun c X F=>coefficientProduct_smul_right n hn γ hγ hγTwo σ c B X F)

/-- The literal original bilinear product determines exactly one bounded
bilinear map on the actual native and coefficient Banach carriers. One
constant C(n,γ) controls all coefficient exponents and finite dimensions. -/
theorem exists_uniform_unique_native_morrey_coefficient_action
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀(σ : ℝ) (k m q : ℕ)
      (B : Ambient k→L[ℝ](Ambient m→L[ℝ]Ambient q)),
      ∃! T : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)→L[ℝ]
          MorreyCoefficientSpace n m σ→L[ℝ]MorreyCoefficientSpace n q σ,
        ‖T‖≤C*‖B‖ ∧
        ∀(X : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) (F : MorreyCoefficientSpace n m σ)
          (u : Domain n→Ambient k)
          (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1))),
          nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) X=hu.toLp u →
          ∀(Fr : Domain n→Gradient n m)
            (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1))),
            morreyCoefficientRecover (n:=n) (q:=m) σ F=hsUnitBallL2Class Fr hFr →
            ∃hP : ∀i,MemLp (fun x=>B (u x) (Fr x i)) 2 (volume.restrict (ball (0 : Domain n) 1)),
              morreyCoefficientRecover (n:=n) (q:=q) σ (T X F)=
                hsUnitBallL2Class (fun x i=>B (u x) (Fr x i)) hP := by
  let Hbound := exists_coefficientProduct_bound n hn γ hγ hγTwo
  let C : ℝ := Hbound.choose
  have hC : 0<C := Hbound.choose_spec.1
  refine ⟨C,hC,?_⟩
  intro σ k m q B
  let f : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)→ₗ[ℝ]
      MorreyCoefficientSpace n m σ→ₗ[ℝ]MorreyCoefficientSpace n q σ :=
    coefficientLinearAction n hn γ hγ hγTwo σ B
  have hBound : ∀X F,‖f X F‖≤(C*‖B‖)*‖X‖*‖F‖ := Hbound.choose_spec.2 σ k m q B
  let T : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)→L[ℝ]
      MorreyCoefficientSpace n m σ→L[ℝ]MorreyCoefficientSpace n q σ :=
    f.mkContinuous₂ (C*‖B‖) hBound
  have hNorm : ‖T‖≤C*‖B‖ :=
    ContinuousLinearMap.opNorm_le_bound₂ T (mul_nonneg hC.le (norm_nonneg B)) hBound
  refine ⟨T,⟨hNorm,?_⟩,?_⟩
  · intro X F u hu hU Fr hFr hF
    exact coefficientProduct_raw n hn γ hγ hγTwo σ B X F u hu hU Fr hFr hF
  · rintro S ⟨_hSNorm,hS⟩
    apply ContinuousLinearMap.ext
    intro X
    apply ContinuousLinearMap.ext
    intro F
    exact coefficient_class_eq_product_of_character n hn γ hγ hγTwo σ B X F (S X F) (hS X F)

end StationaryHarmonicMaps.Analysis

end
