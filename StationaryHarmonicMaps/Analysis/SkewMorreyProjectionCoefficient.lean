module

public import StationaryHarmonicMaps.Analysis.SkewMeanZeroNativeMorrey

/-!
# The literal skew projection in fixed matrix coordinates

The original identity-minus-adjoint formula is transported through the
same genuine matrix coordinate equivalence on the entire coefficient space.
-/

public section
open HarmonicMaps
noncomputable section
namespace StationaryHarmonicMaps.Analysis

/-- The literal half skew part in the original coefficient coordinates. -/
@[expose] def skewMorreyProjectionCoefficient (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    Ambient (q*q)→L[ℝ]Ambient (q*q) :=
  e.symm.toContinuousLinearMap.comp
    (((1/2:ℝ) • (ContinuousLinearMap.id ℝ (Ambient q→L[ℝ]Ambient q)-
      (ContinuousLinearMap.adjoint :
        (Ambient q→L[ℝ]Ambient q)≃ₗᵢ[ℝ](Ambient q→L[ℝ]Ambient q)).toContinuousLinearMap)).comp e.toContinuousLinearMap)

theorem skewMorreyProjectionCoefficient_apply (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) (z : Ambient (q*q)) :
    skewMorreyProjectionCoefficient q e z=e.symm ((1/2:ℝ) • (e z-star (e z))) := by
  change e.symm ((1/2:ℝ) • (e z-ContinuousLinearMap.adjoint (e z)))=_
  rw [ContinuousLinearMap.star_eq_adjoint]

theorem skewMorreyProjectionCoefficient_skew (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) (z : Ambient (q*q)) :
    star (e (skewMorreyProjectionCoefficient q e z))= -(e (skewMorreyProjectionCoefficient q e z)) := by
  rw [skewMorreyProjectionCoefficient_apply,ContinuousLinearEquiv.apply_symm_apply,
    star_smul,star_sub (e z) (star (e z)),star_star (e z)]
  simp only [star_trivial,←neg_sub (e z) (star (e z)),smul_neg]

theorem skewMorreyProjectionCoefficient_eq_self (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) (z : Ambient (q*q))
    (hz : star (e z)=-(e z)) : skewMorreyProjectionCoefficient q e z=z := by
  rw [skewMorreyProjectionCoefficient_apply,hz,sub_neg_eq_add]
  have H : (1/2:ℝ) • (e z+e z)=e z := by
    rw [smul_add,←add_smul]
    norm_num
  exact (congrArg e.symm H).trans (e.symm_apply_apply z)

theorem skewMorreyProjectionCoefficient_idempotent (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) (z : Ambient (q*q)) :
    skewMorreyProjectionCoefficient q e (skewMorreyProjectionCoefficient q e z)=skewMorreyProjectionCoefficient q e z :=
  skewMorreyProjectionCoefficient_eq_self q e _ (skewMorreyProjectionCoefficient_skew q e z)

theorem skewMorreyProjectionCoefficient_norm_le (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    ‖skewMorreyProjectionCoefficient q e‖≤‖e.symm.toContinuousLinearMap‖*‖e.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (skewMorreyProjectionCoefficient q e)
    (mul_nonneg (norm_nonneg e.symm.toContinuousLinearMap) (norm_nonneg e.toContinuousLinearMap))
  intro z
  have hSub : ‖e z-star (e z)‖≤2*‖e z‖ := by
    calc
      _≤‖e z‖+‖star (e z)‖ := norm_sub_le _ _
      _=2*‖e z‖ := by rw [norm_star (e z)];ring
  calc
    _=‖e.symm ((1/2:ℝ) • (e z-star (e z)))‖ := congrArg norm (skewMorreyProjectionCoefficient_apply q e z)
    _≤‖e.symm.toContinuousLinearMap‖*‖(1/2:ℝ) • (e z-star (e z))‖ := e.symm.toContinuousLinearMap.le_opNorm _
    _=‖e.symm.toContinuousLinearMap‖*((1/2:ℝ)*‖e z-star (e z)‖) := by rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    _≤‖e.symm.toContinuousLinearMap‖*((1/2:ℝ)*(2*‖e z‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hSub (by norm_num)) (norm_nonneg e.symm.toContinuousLinearMap)
    _=‖e.symm.toContinuousLinearMap‖*‖e z‖ := by ring
    _≤‖e.symm.toContinuousLinearMap‖*(‖e.toContinuousLinearMap‖*‖z‖) :=
      mul_le_mul_of_nonneg_left (e.toContinuousLinearMap.le_opNorm z) (norm_nonneg e.symm.toContinuousLinearMap)
    _=_ := (mul_assoc _ _ _).symm

end StationaryHarmonicMaps.Analysis
end
