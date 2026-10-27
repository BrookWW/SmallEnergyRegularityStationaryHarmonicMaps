module

public import StationaryHarmonicMaps.Analysis.MeanZeroNativeMorreyConstraint
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Actual skew matrix fields in the mean-zero native Morrey space

Fixed matrix coordinates identify the skew constraint with the kernel of
adjoint plus identity. The same original weak gradient inherits skewness.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

noncomputable section

namespace StationaryHarmonicMaps.Analysis

/-- The coordinate expression of matrix adjoint plus identity. -/
@[expose] def skewMorreyCoordinateConstraint (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    Ambient (q*q)→L[ℝ]Ambient (q*q) :=
  e.symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.adjoint :
      (Ambient q→L[ℝ]Ambient q)≃ₗᵢ[ℝ](Ambient q→L[ℝ]Ambient q)).toContinuousLinearMap+
      ContinuousLinearMap.id ℝ (Ambient q→L[ℝ]Ambient q)).comp e.toContinuousLinearMap)

theorem skewMorreyCoordinateConstraint_apply (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) (z : Ambient (q*q)) :
    skewMorreyCoordinateConstraint q e z=e.symm (star (e z)+e z) := by
  change e.symm (ContinuousLinearMap.adjoint (e z)+e z)=_
  rw [ContinuousLinearMap.star_eq_adjoint]

theorem skewMorreyCoordinateConstraint_eq_zero_iff (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) (z : Ambient (q*q)) :
    skewMorreyCoordinateConstraint q e z=0 ↔ star (e z)=-(e z) := by
  rw [skewMorreyCoordinateConstraint_apply]
  have hZero : e.symm (star (e z)+e z)=0 ↔ star (e z)+e z=0 := by
    constructor
    · intro h
      have H := congrArg e h
      simpa only [ContinuousLinearEquiv.apply_symm_apply,map_zero] using H
    · intro h
      rw [h,map_zero]
  exact hZero.trans add_eq_zero_iff_eq_neg

/-- The literal closed kernel imposing AE skewness on a mean-zero native graph. -/
@[expose] def skewMeanZeroNativeMorreySubmodule (n q : ℕ) (ν : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    Submodule ℝ (MeanZeroNativeMorreySpace n (q*q) ν) :=
  constrainedMeanZeroNativeMorreySubmodule n (q*q) (q*q) ν (skewMorreyCoordinateConstraint q e)

abbrev SkewMeanZeroNativeMorreySpace (n q : ℕ) (ν : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :=
  ↥(skewMeanZeroNativeMorreySubmodule n q ν e)

theorem isClosed_skewMeanZeroNativeMorreySubmodule (n q : ℕ) (ν : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    IsClosed (skewMeanZeroNativeMorreySubmodule n q ν e :
      Set (MeanZeroNativeMorreySpace n (q*q) ν)) :=
  isClosed_constrainedMeanZeroNativeMorreySubmodule n (q*q) (q*q) ν (skewMorreyCoordinateConstraint q e)

instance skewMeanZeroNativeMorreySpace_normedSpace (n q : ℕ) (ν : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    NormedSpace ℝ (SkewMeanZeroNativeMorreySpace n q ν e) :=
  constrainedMeanZeroNativeMorreySpace_normedSpace n (q*q) (q*q) ν (skewMorreyCoordinateConstraint q e)

instance skewMeanZeroNativeMorreySpace_completeSpace (n q : ℕ) (ν : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    CompleteSpace (SkewMeanZeroNativeMorreySpace n q ν e) :=
  constrainedMeanZeroNativeMorreySpace_completeSpace n (q*q) (q*q) ν (skewMorreyCoordinateConstraint q e)

theorem mem_skewMeanZeroNativeMorreySubmodule_iff {n q : ℕ} (ν : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (u : Domain n→Ambient (q*q))
    (hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)))
    (X : MeanZeroNativeMorreySpace n (q*q) ν)
    (hMap : nativeMorreyMapClass (n:=n) (q:=q*q) ν X.val=hu.toLp u) :
    X∈skewMeanZeroNativeMorreySubmodule n q ν e ↔
      ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (e (u x))=-(e (u x)) := by
  change X∈constrainedMeanZeroNativeMorreySubmodule n (q*q) (q*q) ν
    (skewMorreyCoordinateConstraint q e) ↔ _
  rw [mem_constrainedMeanZeroNativeMorreySubmodule_iff ν _ u hu X hMap]
  constructor
  · intro h
    exact h.mono fun x hx=>(skewMorreyCoordinateConstraint_eq_zero_iff q e (u x)).mp hx
  · intro h
    exact h.mono fun x hx=>(skewMorreyCoordinateConstraint_eq_zero_iff q e (u x)).mpr hx

/-- The same original native map and all weak columns of a constrained class
are skew almost everywhere; derivative skewness is produced internally. -/
theorem exists_raw_native_of_skewMeanZeroNativeMorrey {n q : ℕ} (ν : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (X : SkewMeanZeroNativeMorreySpace n q ν e) :
    ∃(u : Domain n→Ambient (q*q)) (Du : Domain n→Gradient n (q*q))
      (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du),
      (⨍x in ball (0 : Domain n) 1,u x)=0 ∧
      nativeMorreyMapClass (n:=n) (q:=q*q) ν X.val.val=hNative.2.1.toLp u ∧
      nativeMorreyHSClass (n:=n) (q:=q*q) ν X.val.val=hsUnitBallL2Class Du hNative.2.2 ∧
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (e (u x))=-(e (u x))) ∧
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i : Fin n,
        star (e (Du x i))=-(e (Du x i))) ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤
          ‖meanZeroNativeMorreyGradientClass n (q*q) ν X.val‖^2*r^ν := by
  have hData := exists_raw_native_of_constrainedMeanZeroNativeMorrey ν
    (skewMorreyCoordinateConstraint q e) X
  obtain ⟨u,Du,hNative,hMean,hMap,hGrad,hU,hDu,hGrowth⟩ := hData
  refine ⟨u,Du,hNative,hMean,hMap,hGrad,?_,?_,hGrowth⟩
  · exact hU.mono fun x hx=>(skewMorreyCoordinateConstraint_eq_zero_iff q e (u x)).mp hx
  · filter_upwards [hDu] with x hx
    intro i
    exact (skewMorreyCoordinateConstraint_eq_zero_iff q e (Du x i)).mp (congrFun hx i)

/-- A unique skew mean-zero native class is equivalent to the literal original
mean, full gradient growth, and AE matrix skewness of the original map. -/
theorem existsUnique_skewMeanZeroNativeMorrey_iff {n q : ℕ} (ν : ℝ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (u : Domain n→Ambient (q*q)) (Du : Domain n→Gradient n (q*q))
    (hNative : MemW12 (ballDomain (0 : Domain n) 1) u Du) :
    (∃!X : SkewMeanZeroNativeMorreySpace n q ν e,
      nativeMorreyMapClass (n:=n) (q:=q*q) ν X.val.val=hNative.2.1.toLp u ∧
      nativeMorreyHSClass (n:=n) (q:=q*q) ν X.val.val=hsUnitBallL2Class Du hNative.2.2) ↔
      ((⨍x in ball (0 : Domain n) 1,u x)=0 ∧
        ∃K : ℝ,0≤K ∧ ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
          (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤K*r^ν) ∧
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (e (u x))=-(e (u x))) := by
  have H := existsUnique_constrainedMeanZeroNativeMorrey_iff ν (skewMorreyCoordinateConstraint q e) u Du hNative
  change (∃!X : ConstrainedMeanZeroNativeMorreySpace n (q*q) (q*q) ν (skewMorreyCoordinateConstraint q e),_ ) ↔ _
  rw [H]
  constructor
  · rintro ⟨hA,hU⟩
    exact ⟨hA,hU.mono fun x hx=>(skewMorreyCoordinateConstraint_eq_zero_iff q e (u x)).mp hx⟩
  · rintro ⟨hA,hU⟩
    exact ⟨hA,hU.mono fun x hx=>(skewMorreyCoordinateConstraint_eq_zero_iff q e (u x)).mpr hx⟩

end StationaryHarmonicMaps.Analysis

end
