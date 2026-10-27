module

public import StationaryHarmonicMaps.Analysis.SkewMeanZeroNativeMorrey
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The actual matrix commutator in full coefficient coordinates

The fixed coordinate equivalence transports the literal ordered matrix
commutator. The genuine skew matrix kernel is preserved in both inputs.
-/

public section
open HarmonicMaps
noncomputable section
namespace StationaryHarmonicMaps.Analysis

/-- The literal matrix commutator in the original fixed coordinates. -/
@[expose] def morreyMatrixCommutator (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    Ambient (q*q)→L[ℝ](Ambient (q*q)→L[ℝ]Ambient (q*q)) := by
  let M := ContinuousLinearMap.compL ℝ (Ambient q) (Ambient q) (Ambient q)
  let K := M-M.flip
  let L := ((ContinuousLinearMap.precompR (Ambient (q*q)) K).flip
    e.toContinuousLinearMap).comp e.toContinuousLinearMap
  exact ((ContinuousLinearMap.compL ℝ (Ambient (q*q))
    (Ambient q→L[ℝ]Ambient q) (Ambient (q*q))) e.symm.toContinuousLinearMap).comp L

theorem morreyMatrixCommutator_apply (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (z w : Ambient (q*q)) :
    morreyMatrixCommutator q e z w=e.symm (e z*e w-e w*e z) := rfl

/-- Two original skew matrices have an original skew commutator. -/
theorem morreyMatrixCommutator_skew (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (z w : Ambient (q*q)) (hz : star (e z)=-(e z)) (hw : star (e w)=-(e w)) :
    star (e (morreyMatrixCommutator q e z w))=-(e (morreyMatrixCommutator q e z w)) := by
  rw [morreyMatrixCommutator_apply,ContinuousLinearEquiv.apply_symm_apply,
    star_sub (e z*e w) (e w*e z),star_mul (e z) (e w),star_mul (e w) (e z),hz,hw,
    neg_mul_neg (e w) (e z),neg_mul_neg (e z) (e w),neg_sub]

/-- The literal fixed skew constraint is preserved by the actual commutator;
its second input is assumed only to lie in that same coefficient kernel. -/
theorem morreyMatrixCommutator_preserves_skew_kernel (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (z w : Ambient (q*q)) (hz : star (e z)=-(e z))
    (hw : skewMorreyCoordinateConstraint q e w=0) :
    skewMorreyCoordinateConstraint q e (morreyMatrixCommutator q e z w)=0 :=
  (skewMorreyCoordinateConstraint_eq_zero_iff q e _).mpr
    (morreyMatrixCommutator_skew q e z w hz ((skewMorreyCoordinateConstraint_eq_zero_iff q e w).mp hw))

end StationaryHarmonicMaps.Analysis
end
