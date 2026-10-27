module

public import StationaryHarmonicMaps.Analysis.NativeMorreyBilinearExistence
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Continuous multiplication of intrinsic native Morrey graphs

The selected class is characterized by the original AE bilinear value;
weak-gradient uniqueness fixes its full two-term Leibniz graph. The native
Banach carrier and its inherited maximum norm remain literal submodule data.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace StationaryHarmonicMaps.Analysis

/-- The original submodule normed group, exposed for canonical dictionary search. -/
abbrev canonicalNativeMorreyGroup (n q : ℕ) (ν : ℝ) :
    NormedAddCommGroup (NativeMorreySobolevSpace n q ν) :=
  Submodule.normedAddCommGroup (nativeMorreySobolevSubmodule n q ν)

/-- The seminormed parent of the original submodule normed group. -/
abbrev canonicalNativeMorreySeminormedGroup (n q : ℕ) (ν : ℝ) :
    SeminormedAddCommGroup (NativeMorreySobolevSpace n q ν) :=
  (Submodule.normedAddCommGroup (nativeMorreySobolevSubmodule n q ν)).toSeminormedAddCommGroup

/-- The original inherited real normed-space structure. -/
abbrev canonicalNativeMorreyNormedSpace (n q : ℕ) (ν : ℝ) :
    NormedSpace ℝ (NativeMorreySobolevSpace n q ν) :=
  Submodule.normedSpace (nativeMorreySobolevSubmodule n q ν)

attribute [instance] canonicalNativeMorreyGroup canonicalNativeMorreySeminormedGroup
  canonicalNativeMorreyNormedSpace

private theorem native_map_add_ae {n q : ℕ} (ν : ℝ)
    (X Y : NativeMorreySobolevSpace n q ν) :
    ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν (X+Y)).val x=
        (nativeMorreyMapClass (n:=n) (q:=q) ν X).val x+(nativeMorreyMapClass (n:=n) (q:=q) ν Y).val x := by
  have hAdd : nativeMorreyMapClass (n:=n) (q:=q) ν (X+Y)=
      nativeMorreyMapClass (n:=n) (q:=q) ν X+nativeMorreyMapClass (n:=n) (q:=q) ν Y :=
    (nativeMorreyMapClass (n:=n) (q:=q) ν).map_add X Y
  filter_upwards [Lp.coeFn_add (nativeMorreyMapClass (n:=n) (q:=q) ν X)
    (nativeMorreyMapClass (n:=n) (q:=q) ν Y)] with x hx
  exact (congrArg (fun U : MapUnitBallL2 n q=>U.val x) hAdd).trans hx

private theorem native_map_smul_ae {n q : ℕ} (ν c : ℝ)
    (X : NativeMorreySobolevSpace n q ν) :
    ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν (c • X)).val x=
        c • (nativeMorreyMapClass (n:=n) (q:=q) ν X).val x := by
  have hSmul : nativeMorreyMapClass (n:=n) (q:=q) ν (c • X)=
      c • nativeMorreyMapClass (n:=n) (q:=q) ν X :=
    (nativeMorreyMapClass (n:=n) (q:=q) ν).map_smul c X
  filter_upwards [Lp.coeFn_smul c (nativeMorreyMapClass (n:=n) (q:=q) ν X)] with x hx
  exact (congrArg (fun U : MapUnitBallL2 n q=>U.val x) hSmul).trans hx

private theorem nativeMorreyBilinearProduct_add_left_ae {n m k q : ℕ} (ν : ℝ)
    (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
    (X₁ X₂ : NativeMorreySobolevSpace n m ν) (Y : NativeMorreySobolevSpace n k ν)
    (Z₁ Z₂ : NativeMorreySobolevSpace n q ν)
    (hZ₁ : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν Z₁).val x=
        B ((nativeMorreyMapClass (n:=n) (q:=m) ν X₁).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x))
    (hZ₂ : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν Z₂).val x=
        B ((nativeMorreyMapClass (n:=n) (q:=m) ν X₂).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x)) :
    ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν (Z₁+Z₂)).val x=
        B ((nativeMorreyMapClass (n:=n) (q:=m) ν (X₁+X₂)).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x) := by
  filter_upwards [native_map_add_ae ν Z₁ Z₂,native_map_add_ae ν X₁ X₂,hZ₁,hZ₂] with x hz hx hz₁ hz₂
  calc
    _=(nativeMorreyMapClass (n:=n) (q:=q) ν Z₁).val x+(nativeMorreyMapClass (n:=n) (q:=q) ν Z₂).val x := hz
    _=B ((nativeMorreyMapClass (n:=n) (q:=m) ν X₁).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x)+
        B ((nativeMorreyMapClass (n:=n) (q:=m) ν X₂).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x) := congrArg₂ (fun a b : Ambient q=>a+b) hz₁ hz₂
    _=B ((nativeMorreyMapClass (n:=n) (q:=m) ν X₁).val x+(nativeMorreyMapClass (n:=n) (q:=m) ν X₂).val x)
        ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x) := by simp only [map_add,add_apply]
    _=_ := congrArg (fun a : Ambient m=>B a ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x)) hx.symm

private theorem nativeMorreyBilinearProduct_add_right_ae {n m k q : ℕ} (ν : ℝ)
    (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n m ν) (Y₁ Y₂ : NativeMorreySobolevSpace n k ν)
    (Z₁ Z₂ : NativeMorreySobolevSpace n q ν)
    (hZ₁ : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν Z₁).val x=
        B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y₁).val x))
    (hZ₂ : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν Z₂).val x=
        B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y₂).val x)) :
    ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν (Z₁+Z₂)).val x=
        B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν (Y₁+Y₂)).val x) := by
  filter_upwards [native_map_add_ae ν Z₁ Z₂,native_map_add_ae ν Y₁ Y₂,hZ₁,hZ₂] with x hz hy hz₁ hz₂
  calc
    _=(nativeMorreyMapClass (n:=n) (q:=q) ν Z₁).val x+(nativeMorreyMapClass (n:=n) (q:=q) ν Z₂).val x := hz
    _=B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y₁).val x)+
        B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y₂).val x) := congrArg₂ (fun a b : Ambient q=>a+b) hz₁ hz₂
    _=B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x)
        ((nativeMorreyMapClass (n:=n) (q:=k) ν Y₁).val x+(nativeMorreyMapClass (n:=n) (q:=k) ν Y₂).val x) := ((B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x)).map_add
      ((nativeMorreyMapClass (n:=n) (q:=k) ν Y₁).val x)
      ((nativeMorreyMapClass (n:=n) (q:=k) ν Y₂).val x)).symm
    _=_ := congrArg (fun a : Ambient k=>B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x) a) hy.symm

private theorem nativeMorreyBilinearProduct_smul_left_ae {n m k q : ℕ} (ν c : ℝ)
    (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n m ν) (Y : NativeMorreySobolevSpace n k ν)
    (Z : NativeMorreySobolevSpace n q ν)
    (hZ : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν Z).val x=
        B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x)) :
    ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν (c • Z)).val x=
        B ((nativeMorreyMapClass (n:=n) (q:=m) ν (c • X)).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x) := by
  filter_upwards [native_map_smul_ae ν c Z,native_map_smul_ae ν c X,hZ] with x hz hx hzx
  calc
    _=c • (nativeMorreyMapClass (n:=n) (q:=q) ν Z).val x := hz
    _=c • B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x) := congrArg (fun a : Ambient q=>c • a) hzx
    _=B (c • (nativeMorreyMapClass (n:=n) (q:=m) ν X).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x) := by simp only [map_smul,smul_apply]
    _=_ := congrArg (fun a : Ambient m=>B a ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x)) hx.symm

private theorem nativeMorreyBilinearProduct_smul_right_ae {n m k q : ℕ} (ν c : ℝ)
    (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n m ν) (Y : NativeMorreySobolevSpace n k ν)
    (Z : NativeMorreySobolevSpace n q ν)
    (hZ : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν Z).val x=
        B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x)) :
    ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν (c • Z)).val x=
        B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν (c • Y)).val x) := by
  filter_upwards [native_map_smul_ae ν c Z,native_map_smul_ae ν c Y,hZ] with x hz hy hzx
  calc
    _=c • (nativeMorreyMapClass (n:=n) (q:=q) ν Z).val x := hz
    _=c • B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x) ((nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x) := congrArg (fun a : Ambient q=>c • a) hzx
    _=B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x) (c • (nativeMorreyMapClass (n:=n) (q:=k) ν Y).val x) := ((B _).map_smul c _).symm
    _=_ := congrArg (fun a : Ambient k=>B ((nativeMorreyMapClass (n:=n) (q:=m) ν X).val x) a) hy.symm

private theorem native_map_eq_of_ae {n q : ℕ} (ν : ℝ)
    (X Y : NativeMorreySobolevSpace n q ν)
    (h : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν X).val x=
        (nativeMorreyMapClass (n:=n) (q:=q) ν Y).val x) : X=Y := by
  apply nativeMorreyMapClass_injective ν
  exact Lp.ext h

/-- The unique native class of the actual pointwise bilinear product. -/
@[expose] def nativeMorreyBilinearProduct
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m k q : ℕ} (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ))
    (Y : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) :
    NativeMorreySobolevSpace n q ((n : ℝ)-2+γ) :=
  Classical.choose (((Classical.choose_spec (existsUnique_nativeMorrey_bilinear_product_bound
    n hn γ hγ hγTwo)).2 m k q B X Y).1.exists)

/-- The selected class is the original AE product. -/
theorem nativeMorreyBilinearProduct_ae
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m k q : ℕ} (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ))
    (Y : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) :
    ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ((n : ℝ)-2+γ)
        (nativeMorreyBilinearProduct n hn γ hγ hγTwo B X Y)).val x=
        B ((nativeMorreyMapClass (n:=n) (q:=m) ((n : ℝ)-2+γ) X).val x)
          ((nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) Y).val x) :=
  Classical.choose_spec (((Classical.choose_spec (existsUnique_nativeMorrey_bilinear_product_bound
    n hn γ hγ hγTwo)).2 m k q B X Y).1.exists)

/-- Equality to the product depends only on its actual AE value, so every
choice with that value gives the same native class and gradient. -/
theorem nativeMorreyBilinearProduct_eq_iff
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m k q : ℕ} (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ))
    (Y : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ))
    (Z : NativeMorreySobolevSpace n q ((n : ℝ)-2+γ)) :
    Z=nativeMorreyBilinearProduct n hn γ hγ hγTwo B X Y ↔
      ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
        (nativeMorreyMapClass (n:=n) (q:=q) ((n : ℝ)-2+γ) Z).val x=
          B ((nativeMorreyMapClass (n:=n) (q:=m) ((n : ℝ)-2+γ) X).val x)
            ((nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) Y).val x) := by
  constructor
  · intro h
    subst Z
    exact nativeMorreyBilinearProduct_ae n hn γ hγ hγTwo B X Y
  · intro h
    apply native_map_eq_of_ae
    filter_upwards [h,nativeMorreyBilinearProduct_ae n hn γ hγ hγTwo B X Y] with x hz hx
    exact hz.trans hx.symm

theorem nativeMorreyBilinearProduct_add_left
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m k q : ℕ} (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
    (X₁ X₂ : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ))
    (Y : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) :
    nativeMorreyBilinearProduct n hn γ hγ hγTwo B (X₁+X₂) Y=
      nativeMorreyBilinearProduct n hn γ hγ hγTwo B X₁ Y+
        nativeMorreyBilinearProduct n hn γ hγ hγTwo B X₂ Y := by
  symm
  apply (nativeMorreyBilinearProduct_eq_iff n hn γ hγ hγTwo B (X₁+X₂) Y _).mpr
  exact nativeMorreyBilinearProduct_add_left_ae _ B X₁ X₂ Y _ _
    (nativeMorreyBilinearProduct_ae n hn γ hγ hγTwo B X₁ Y)
    (nativeMorreyBilinearProduct_ae n hn γ hγ hγTwo B X₂ Y)

theorem nativeMorreyBilinearProduct_add_right
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m k q : ℕ} (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ))
    (Y₁ Y₂ : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) :
    nativeMorreyBilinearProduct n hn γ hγ hγTwo B X (Y₁+Y₂)=
      nativeMorreyBilinearProduct n hn γ hγ hγTwo B X Y₁+
        nativeMorreyBilinearProduct n hn γ hγ hγTwo B X Y₂ := by
  symm
  apply (nativeMorreyBilinearProduct_eq_iff n hn γ hγ hγTwo B X (Y₁+Y₂) _).mpr
  exact nativeMorreyBilinearProduct_add_right_ae _ B X Y₁ Y₂ _ _
    (nativeMorreyBilinearProduct_ae n hn γ hγ hγTwo B X Y₁)
    (nativeMorreyBilinearProduct_ae n hn γ hγ hγTwo B X Y₂)

theorem nativeMorreyBilinearProduct_smul_left
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m k q : ℕ} (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q)) (c : ℝ)
    (X : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ))
    (Y : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) :
    nativeMorreyBilinearProduct n hn γ hγ hγTwo B (c • X) Y=
      c • nativeMorreyBilinearProduct n hn γ hγ hγTwo B X Y := by
  symm
  apply (nativeMorreyBilinearProduct_eq_iff n hn γ hγ hγTwo B (c • X) Y _).mpr
  exact nativeMorreyBilinearProduct_smul_left_ae _ c B X Y _ (nativeMorreyBilinearProduct_ae n hn γ hγ hγTwo B X Y)

theorem nativeMorreyBilinearProduct_smul_right
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m k q : ℕ} (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q)) (c : ℝ)
    (X : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ))
    (Y : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) :
    nativeMorreyBilinearProduct n hn γ hγ hγTwo B X (c • Y)=
      c • nativeMorreyBilinearProduct n hn γ hγ hγTwo B X Y := by
  symm
  apply (nativeMorreyBilinearProduct_eq_iff n hn γ hγ hγTwo B X (c • Y) _).mpr
  exact nativeMorreyBilinearProduct_smul_right_ae _ c B X Y _ (nativeMorreyBilinearProduct_ae n hn γ hγ hγTwo B X Y)

theorem exists_nativeMorreyBilinearProduct_bound
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀(m k q : ℕ)
      (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
      (X : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ))
      (Y : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)),
      ‖nativeMorreyBilinearProduct n hn γ hγ hγTwo B X Y‖≤C*‖B‖*‖X‖*‖Y‖ := by
  obtain ⟨C,hC,hAll⟩ := existsUnique_nativeMorrey_bilinear_product_bound n hn γ hγ hγTwo
  exact ⟨C,hC,fun m k q B X Y=>(hAll m k q B X Y).2 _
    (nativeMorreyBilinearProduct_ae n hn γ hγ hγTwo B X Y)⟩

/-- Actual multiplication of native stronger-Morrey classes is a continuous
bilinear map, using the intrinsic complete native norms. -/
@[expose] def nativeMorreyBilinear
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m k q : ℕ} (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q)) :
    NativeMorreySobolevSpace n m ((n : ℝ)-2+γ)→L[ℝ]
      NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)→L[ℝ]
        NativeMorreySobolevSpace n q ((n : ℝ)-2+γ) :=
by
  let f : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ)→ₗ[ℝ]
      NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)→ₗ[ℝ]
        NativeMorreySobolevSpace n q ((n : ℝ)-2+γ) :=
    LinearMap.mk₂ ℝ (nativeMorreyBilinearProduct n hn γ hγ hγTwo B)
      (nativeMorreyBilinearProduct_add_left n hn γ hγ hγTwo B)
      (nativeMorreyBilinearProduct_smul_left n hn γ hγ hγTwo B)
      (nativeMorreyBilinearProduct_add_right n hn γ hγ hγTwo B)
      (nativeMorreyBilinearProduct_smul_right n hn γ hγ hγTwo B)
  exact f.mkContinuousOfExistsBound₂ (by
    obtain ⟨C,_hC,hAll⟩ := exists_nativeMorreyBilinearProduct_bound n hn γ hγ hγTwo
    refine ⟨C*‖B‖,?_⟩
    intro X Y
    exact hAll m k q B X Y)

theorem nativeMorreyBilinear_apply
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m k q : ℕ} (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ))
    (Y : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) :
    nativeMorreyBilinear (m:=m) (k:=k) (q:=q) n hn γ hγ hγTwo B X Y=
      nativeMorreyBilinearProduct n hn γ hγ hγTwo B X Y := rfl

/-- The continuous bilinear bundle is uniquely characterized by the same
original AE product on every pair of intrinsic native classes. -/
theorem nativeMorreyBilinear_eq_iff
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m k q : ℕ} (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
    (A : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ)→L[ℝ]
      NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)→L[ℝ]
        NativeMorreySobolevSpace n q ((n : ℝ)-2+γ)) :
    A=nativeMorreyBilinear (m:=m) (k:=k) (q:=q) n hn γ hγ hγTwo B ↔
      ∀(X : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ))
        (Y : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)),
        ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
          (nativeMorreyMapClass (n:=n) (q:=q) ((n : ℝ)-2+γ) (A X Y)).val x=
            B ((nativeMorreyMapClass (n:=n) (q:=m) ((n : ℝ)-2+γ) X).val x)
              ((nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) Y).val x) := by
  constructor
  · intro hA
    subst A
    intro X Y
    exact nativeMorreyBilinearProduct_ae (m:=m) (k:=k) (q:=q) n hn γ hγ hγTwo B X Y
  · intro hA
    apply ContinuousLinearMap.ext
    intro X
    apply ContinuousLinearMap.ext
    intro Y
    exact (nativeMorreyBilinearProduct_eq_iff (m:=m) (k:=k) (q:=q)
      n hn γ hγ hγTwo B X Y (A X Y)).mpr (hA X Y)

/-- One coefficient depending only on the domain and exponent bounds all
target dimensions and every actual bilinear coefficient. -/
theorem exists_nativeMorreyBilinear_norm_bound
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀(m k q : ℕ)
      (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q)),
      ‖nativeMorreyBilinear (m:=m) (k:=k) (q:=q) n hn γ hγ hγTwo B‖≤C*‖B‖ := by
  have hProduct : ∃C : ℝ,0<C ∧ ∀(m k q : ℕ)
      (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
      (X : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ))
      (Y : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)),
      ‖nativeMorreyBilinearProduct n hn γ hγ hγTwo B X Y‖≤C*‖B‖*‖X‖*‖Y‖ :=
    exists_nativeMorreyBilinearProduct_bound n hn γ hγ hγTwo
  rcases hProduct with ⟨C,hC,hAll⟩
  refine ⟨C,hC,?_⟩
  intro m k q B
  have hBound (X : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ))
      (Y : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ)) :
      ‖nativeMorreyBilinear (m:=m) (k:=k) (q:=q) n hn γ hγ hγTwo B X Y‖≤(C*‖B‖)*‖X‖*‖Y‖ := by
    rw [nativeMorreyBilinear_apply]
    exact hAll m k q B X Y
  exact ContinuousLinearMap.opNorm_le_bound₂
    (nativeMorreyBilinear (m:=m) (k:=k) (q:=q) n hn γ hγ hγTwo B)
    (mul_nonneg hC.le (norm_nonneg B)) hBound

/-- The selected native product has the full raw Leibniz gradient for any
original native representatives of the two input classes. -/
theorem nativeMorreyBilinearProduct_raw_leibniz
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m k q : ℕ} (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
    (u : Domain n→Ambient m) (Du : Domain n→Gradient n m)
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (X : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ))
    (hX : nativeMorreyMapClass (n:=n) (q:=m) ((n : ℝ)-2+γ) X=hu.2.1.toLp u)
    (v : Domain n→Ambient k) (Dv : Domain n→Gradient n k)
    (hv : MemW12 (ballDomain (0 : Domain n) 1) v Dv)
    (Y : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ))
    (hY : nativeMorreyMapClass (n:=n) (q:=k) ((n : ℝ)-2+γ) Y=hv.2.1.toLp v) :
    let ν := (n : ℝ)-2+γ
    let W := fun x=>B (u x) (v x)
    let DW := fun x i=>B (Du x i) (v x)+B (u x) (Dv x i)
    let Z := nativeMorreyBilinearProduct n hn γ hγ hγTwo B X Y
    ∃hW : MemW12 (ballDomain (0 : Domain n) 1) W DW,
      nativeMorreyMapClass (n:=n) (q:=q) ν Z=hW.2.1.toLp W ∧
      nativeMorreyHSClass (n:=n) (q:=q) ν Z=hsUnitBallL2Class DW hW.2.2 :=
  nativeMorrey_bilinear_raw_leibniz n hn γ hγ hγTwo m k q B u Du hu X hX v Dv hv Y hY
    (nativeMorreyBilinearProduct n hn γ hγ hγTwo B X Y)
    (nativeMorreyBilinearProduct_ae n hn γ hγ hγTwo B X Y)

end StationaryHarmonicMaps.Analysis

end
