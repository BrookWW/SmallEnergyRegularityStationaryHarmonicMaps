module

public import StationaryHarmonicMaps.Analysis.NativeMorreyMeanZero
public import StationaryHarmonicMaps.Analysis.SobolevLinearOperations
import HarmonicMaps.Analysis.SobolevAECongruence
import StationaryHarmonicMaps.Analysis.SobolevCutoff

/-!
# Closed linear constraints on actual mean-zero native Morrey graphs

A fixed genuine coefficient map imposes its pointwise AE zero constraint
on the original map class. Its literal L2 lift gives a closed kernel.
The original weak gradient satisfies the same linear constraint by native
weak-gradient uniqueness, rather than by an additional derivative premise.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

noncomputable section

namespace StationaryHarmonicMaps.Analysis

abbrev canonicalMeanZeroNativeGroup (n m : ℕ) (ν : ℝ) :
    NormedAddCommGroup (MeanZeroNativeMorreySpace n m ν) :=
  Submodule.normedAddCommGroup (meanZeroNativeMorreySubmodule n m ν)

attribute [instance] canonicalMeanZeroNativeGroup

abbrev canonicalMeanZeroNativeSeminormedGroup (n m : ℕ) (ν : ℝ) :
    SeminormedAddCommGroup (MeanZeroNativeMorreySpace n m ν) :=
  (Submodule.normedAddCommGroup (meanZeroNativeMorreySubmodule n m ν)).toSeminormedAddCommGroup

attribute [instance] canonicalMeanZeroNativeSeminormedGroup

@[expose] def meanZeroNativeMorreyConstraintMap (n m k : ℕ) (ν : ℝ)
    (A : Ambient m→L[ℝ]Ambient k) :
    MeanZeroNativeMorreySpace n m ν→L[ℝ]MapUnitBallL2 n k :=
  (A.compLpL 2 (volume.restrict (ball (0 : Domain n) 1))).comp
    ((nativeMorreyMapClass (n:=n) (q:=m) ν).comp
      (meanZeroNativeMorreySubmodule n m ν).subtypeL)

@[expose] def constrainedMeanZeroNativeMorreySubmodule (n m k : ℕ) (ν : ℝ)
    (A : Ambient m→L[ℝ]Ambient k) :
    Submodule ℝ (MeanZeroNativeMorreySpace n m ν) :=
  (meanZeroNativeMorreyConstraintMap n m k ν A).ker

abbrev ConstrainedMeanZeroNativeMorreySpace (n m k : ℕ) (ν : ℝ)
    (A : Ambient m→L[ℝ]Ambient k) :=
  ↥(constrainedMeanZeroNativeMorreySubmodule n m k ν A)

instance constrainedMeanZeroNativeMorreySpace_normedSpace
    (n m k : ℕ) (ν : ℝ) (A : Ambient m→L[ℝ]Ambient k) :
    NormedSpace ℝ (ConstrainedMeanZeroNativeMorreySpace n m k ν A) :=
  Submodule.normedSpace (constrainedMeanZeroNativeMorreySubmodule n m k ν A)

theorem isClosed_constrainedMeanZeroNativeMorreySubmodule
    (n m k : ℕ) (ν : ℝ) (A : Ambient m→L[ℝ]Ambient k) :
    IsClosed (constrainedMeanZeroNativeMorreySubmodule n m k ν A :
      Set (MeanZeroNativeMorreySpace n m ν)) :=
  (meanZeroNativeMorreyConstraintMap n m k ν A).isClosed_ker

instance constrainedMeanZeroNativeMorreySpace_completeSpace
    (n m k : ℕ) (ν : ℝ) (A : Ambient m→L[ℝ]Ambient k) :
    CompleteSpace (ConstrainedMeanZeroNativeMorreySpace n m k ν A) := by
  letI : IsClosed (constrainedMeanZeroNativeMorreySubmodule n m k ν A :
      Set (MeanZeroNativeMorreySpace n m ν)) :=
    isClosed_constrainedMeanZeroNativeMorreySubmodule n m k ν A
  exact IsClosed.completeSpace_coe

theorem meanZeroNativeMorreyConstraintMap_ae_raw {n m k : ℕ}
    (ν : ℝ) (A : Ambient m→L[ℝ]Ambient k)
    (u : Domain n→Ambient m)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (X : MeanZeroNativeMorreySpace n m ν)
    (hMap : nativeMorreyMapClass (n:=n) (q:=m) ν X.val=hu.toLp u) :
    (meanZeroNativeMorreyConstraintMap n m k ν A X : Domain n→Ambient k)=ᵐ[
      volume.restrict (ball (0 : Domain n) 1)](fun x=>A (u x)) := by
  change (A.compLpL 2 (volume.restrict (ball (0 : Domain n) 1))
    (nativeMorreyMapClass (n:=n) (q:=m) ν X.val) : Domain n→Ambient k)=ᵐ[_]_
  rw [hMap]
  filter_upwards [A.coeFn_compLpL (hu.toLp u),hu.coeFn_toLp] with x hx huX
  rw [hx,huX]

theorem mem_constrainedMeanZeroNativeMorreySubmodule_iff {n m k : ℕ}
    (ν : ℝ) (A : Ambient m→L[ℝ]Ambient k)
    (u : Domain n→Ambient m)
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (X : MeanZeroNativeMorreySpace n m ν)
    (hMap : nativeMorreyMapClass (n:=n) (q:=m) ν X.val=hu.toLp u) :
    X∈constrainedMeanZeroNativeMorreySubmodule n m k ν A ↔
      (fun x=>A (u x))=ᵐ[volume.restrict (ball (0 : Domain n) 1)](fun _=>0) := by
  have hAE := meanZeroNativeMorreyConstraintMap_ae_raw ν A u hu X hMap
  have hZero : ((0 : MapUnitBallL2 n k) : Domain n→Ambient k)=ᵐ[
      volume.restrict (ball (0 : Domain n) 1)](fun _=>0) := Lp.coeFn_zero (Ambient k) 2 (volume.restrict (ball (0 : Domain n) 1))
  change meanZeroNativeMorreyConstraintMap n m k ν A X=0 ↔ _
  constructor
  · intro hX
    rw [hX] at hAE
    exact hAE.symm.trans hZero
  · intro hU
    apply Lp.ext
    exact hAE.trans (hU.trans hZero.symm)

/-- The original native weak derivative inherits a genuine fixed linear
constraint of the original map, without a derivative-constraint premise. -/
theorem native_linear_constraint_gradient_ae {n m k : ℕ} (Ω : OpenDomain n)
    (A : Ambient m→L[ℝ]Ambient k)
    (u : Domain n→Ambient m) (Du : Domain n→Gradient n m)
    (hu : MemW12Loc Ω u Du)
    (hA : (fun x=>A (u x))=ᵐ[volume.restrict Ω.val](fun _=>0)) :
    (fun x i=>A (Du x i))=ᵐ[volume.restrict Ω.val](fun (_ : Domain n) (_ : Fin n)=>0) := by
  have hAU := memW12Loc_continuousLinearMap hu A
  have hZero : HasWeakGradient Ω (fun _ : Domain n=>(0 : Ambient k)) (fun _ _=>0) :=
    (MemW12.zero Ω).1
  exact hAU.1.ae_eq_of_ae_eq_map hZero hA

/-- Every actual constrained class has a mean-zero native raw representative,
the same original full gradient growth and the produced derivative constraint. -/
theorem exists_raw_native_of_constrainedMeanZeroNativeMorrey {n m k : ℕ}
    (ν : ℝ) (A : Ambient m→L[ℝ]Ambient k)
    (X : ConstrainedMeanZeroNativeMorreySpace n m k ν A) :
    ∃(u : Domain n→Ambient m) (Du : Domain n→Gradient n m)
      (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du),
      (⨍x in ball (0 : Domain n) 1,u x)=0 ∧
      nativeMorreyMapClass (n:=n) (q:=m) ν X.val.val=hNative.2.1.toLp u ∧
      nativeMorreyHSClass (n:=n) (q:=m) ν X.val.val=hsUnitBallL2Class (n:=n) (q:=m) Du hNative.2.2 ∧
      (fun x=>A (u x))=ᵐ[volume.restrict (ball (0 : Domain n) 1)](fun _=>0) ∧
      (fun x i=>A (Du x i))=ᵐ[volume.restrict (ball (0 : Domain n) 1)](fun (_ : Domain n) (_ : Fin n)=>0) ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤
          ‖meanZeroNativeMorreyGradientClass n m ν X.val‖^2*r^ν := by
  have hData : ∃(u : Domain n→Ambient m) (Du : Domain n→Gradient n m)
      (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du),
      (⨍x in ball (0 : Domain n) 1,u x)=0 ∧
      nativeMorreyMapClass (n:=n) (q:=m) ν X.val.val=hNative.2.1.toLp u ∧
      nativeMorreyHSClass (n:=n) (q:=m) ν X.val.val=hsUnitBallL2Class (n:=n) (q:=m) Du hNative.2.2 ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤
          ‖meanZeroNativeMorreyGradientClass n m ν X.val‖^2*r^ν :=
    exists_raw_native_of_meanZeroNativeMorrey (n:=n) (q:=m) ν X.val
  obtain ⟨u,Du,hNative,hMean,hMap,hGrad,hGrowth⟩ := hData
  have hAU : (fun x=>A (u x))=ᵐ[volume.restrict (ball (0 : Domain n) 1)](fun _=>0) :=
    (mem_constrainedMeanZeroNativeMorreySubmodule_iff ν A u hNative.2.1 X.val hMap).mp X.property
  exact ⟨u,Du,hNative,hMean,hMap,hGrad,hAU,
    native_linear_constraint_gradient_ae _ A u Du hNative.to_memW12Loc hAU,hGrowth⟩

/-- Original native data give exactly one constrained mean-zero class if and
only if their actual mean vanishes, their complete growth is finite, and
the original raw values satisfy the fixed linear constraint almost everywhere. -/
theorem existsUnique_constrainedMeanZeroNativeMorrey_iff {n m k : ℕ}
    (ν : ℝ) (A : Ambient m→L[ℝ]Ambient k)
    (u : Domain n→Ambient m) (Du : Domain n→Gradient n m)
    (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du) :
    (∃! X : ConstrainedMeanZeroNativeMorreySpace n m k ν A,
      nativeMorreyMapClass (n:=n) (q:=m) ν X.val.val=hNative.2.1.toLp u ∧
      nativeMorreyHSClass (n:=n) (q:=m) ν X.val.val=hsUnitBallL2Class (n:=n) (q:=m) Du hNative.2.2) ↔
      ((⨍x in ball (0 : Domain n) 1,u x)=0 ∧
        ∃K : ℝ,0≤K ∧ ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
          (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤K*r^ν) ∧
      (fun x=>A (u x))=ᵐ[volume.restrict (ball (0 : Domain n) 1)](fun _=>0) := by
  constructor
  · rintro ⟨X,⟨hMap,hGrad⟩,_hUnique⟩
    have hUnderlying : ∃! Y : MeanZeroNativeMorreySpace n m ν,
        nativeMorreyMapClass (n:=n) (q:=m) ν Y.val=hNative.2.1.toLp u ∧
        nativeMorreyHSClass (n:=n) (q:=m) ν Y.val=hsUnitBallL2Class (n:=n) (q:=m) Du hNative.2.2 := by
      refine ⟨X.val,⟨hMap,hGrad⟩,?_⟩
      rintro Y ⟨hYMap,_hYGrad⟩
      apply Subtype.ext
      apply nativeMorreyMapClass_injective (n:=n) (q:=m) ν
      exact hYMap.trans hMap.symm
    exact ⟨(existsUnique_meanZeroNativeMorrey_iff (n:=n) (q:=m) ν u Du hNative).mp hUnderlying,
      (mem_constrainedMeanZeroNativeMorreySubmodule_iff ν A u hNative.2.1 X.val hMap).mp X.property⟩
  · rintro ⟨hMeanGrowth,hAU⟩
    have hExists : ∃! Y : MeanZeroNativeMorreySpace n m ν,
        nativeMorreyMapClass (n:=n) (q:=m) ν Y.val=hNative.2.1.toLp u ∧
        nativeMorreyHSClass (n:=n) (q:=m) ν Y.val=hsUnitBallL2Class (n:=n) (q:=m) Du hNative.2.2 :=
      (existsUnique_meanZeroNativeMorrey_iff (n:=n) (q:=m) ν u Du hNative).mpr hMeanGrowth
    obtain ⟨Y,⟨hMap,hGrad⟩,hUnique⟩ := hExists
    have hYA : Y∈constrainedMeanZeroNativeMorreySubmodule n m k ν A :=
      (mem_constrainedMeanZeroNativeMorreySubmodule_iff ν A u hNative.2.1 Y hMap).mpr hAU
    refine ⟨⟨Y,hYA⟩,⟨hMap,hGrad⟩,?_⟩
    rintro Z hZ
    exact Subtype.ext (hUnique Z.val hZ)

end StationaryHarmonicMaps.Analysis

end
