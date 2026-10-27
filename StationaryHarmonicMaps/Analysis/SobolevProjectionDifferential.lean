module

public import StationaryHarmonicMaps.Analysis.C2TargetSobolevTangency
public import StationaryHarmonicMaps.Analysis.C1SobolevPostcompositionLocal
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import StationaryHarmonicMaps.Geometry.NormalProjectionProperties
public import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Differentiated projection identities along a Sobolev map

The ambient extension agrees with the actual normal projection on the target.
Its algebraic identities are differentiated only along the actual weak
Sobolev columns, by applying the C¹ chain rule to constraints that vanish on
the target. No projection identity on an ambient neighborhood is required.
-/

public section

open HarmonicMaps MeasureTheory Filter
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Idempotence differentiates along the actual weak columns of a target-valued map. -/
theorem ae_operatorField_differentiated_idempotence {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    {G : Ambient q → Ambient q →L[ℝ] Ambient q}
    (hG : ContDiff ℝ 1 G) (hcG : HasCompactSupport G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p) :
    ∀ᵐ x ∂volume.restrict Ω.val, ∀ i : Fin n,
      (fderiv ℝ G (u x) (Du x i)) * G (u x) +
        G (u x) * (fderiv ℝ G (u x) (Du x i)) =
          fderiv ℝ G (u x) (Du x i) := by
  let F (v : Ambient q) (y : Ambient q) := G y (G y v) - G y v
  have hFC1 (v : Ambient q) : ContDiff ℝ 1 (F v) :=
    (hG.clm_apply (hG.clm_apply contDiff_const)).sub (hG.clm_apply contDiff_const)
  have hcF (v : Ambient q) : HasCompactSupport (F v) :=
    hcG.comp_left (g := fun P : Ambient q →L[ℝ] Ambient q => P (P v) - P v) (by simp)
  have hFN (v : Ambient q) (p : N.Carrier) : F v p.val = 0 := by
    dsimp only [F]
    rw [hGN p]
    apply sub_eq_zero.mpr
    simpa only [mul_apply_eq_comp] using congrArg
      (fun P : Ambient q →L[ℝ] Ambient q => P v) (N.normalProjection_idempotent p)
  have hzero (j : Fin q) : ∀ᵐ x ∂volume.restrict Ω.val,
      ∀ i : Fin n, fderiv ℝ (F (EuclideanSpace.single j 1)) (u x) (Du x i) = 0 :=
    ae_fderiv_apply_eq_zero_of_target_zero N hu hN _ (hFC1 _) (hcF _) (hFN _)
  filter_upwards [ae_all_iff.2 hzero] with x hx
  intro i
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin q) ℝ).toBasis.ext
  intro j
  have hz := hx j i
  have hdG := (hG.differentiable (by simp) (u x)).hasFDerivAt
  have hder := (hdG.clm_apply (hdG.clm_apply
    (hasFDerivAt_const (EuclideanSpace.single j 1) (u x)))).sub
      (hdG.clm_apply (hasFDerivAt_const (EuclideanSpace.single j 1) (u x)))
  change HasFDerivAt (F (EuclideanSpace.single j 1)) _ (u x) at hder
  rw [hder.fderiv] at hz
  change (G (u x) (G (u x) 0 + (fderiv ℝ G (u x) (Du x i))
      (EuclideanSpace.single j 1)) +
      (fderiv ℝ G (u x) (Du x i)) (G (u x) (EuclideanSpace.single j 1))) -
    (G (u x) 0 + (fderiv ℝ G (u x) (Du x i)) (EuclideanSpace.single j 1)) = 0 at hz
  simp only [map_zero, zero_add] at hz
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
  change (fderiv ℝ G (u x) (Du x i)) (G (u x) (EuclideanSpace.single j 1)) +
    G (u x) ((fderiv ℝ G (u x) (Du x i)) (EuclideanSpace.single j 1)) =
      (fderiv ℝ G (u x) (Du x i)) (EuclideanSpace.single j 1)
  exact (add_comm _ _).trans (sub_eq_zero.mp hz)



/-- Self-adjointness differentiates along the same actual weak columns. -/
theorem ae_operatorField_derivative_selfAdjoint {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    {G : Ambient q → Ambient q →L[ℝ] Ambient q}
    (hG : ContDiff ℝ 1 G) (hcG : HasCompactSupport G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p) :
    ∀ᵐ x ∂volume.restrict Ω.val, ∀ i : Fin n,
      IsSelfAdjoint (fderiv ℝ G (u x) (Du x i)) := by
  let F (v : Ambient q) (y : Ambient q) := star (G y) v - G y v
  have hstar : ContDiff ℝ 1 (fun y => star (G y)) :=
    (starL' ℝ : (Ambient q →L[ℝ] Ambient q) ≃L[ℝ]
      (Ambient q →L[ℝ] Ambient q)).contDiff.comp hG
  have hFC1 (v : Ambient q) : ContDiff ℝ 1 (F v) :=
    (hstar.clm_apply contDiff_const).sub (hG.clm_apply contDiff_const)
  have hcF (v : Ambient q) : HasCompactSupport (F v) :=
    hcG.comp_left (g := fun P : Ambient q →L[ℝ] Ambient q => star P v - P v) (by
      exact sub_eq_zero.mpr (congrArg
        (fun P : Ambient q →L[ℝ] Ambient q => P v)
        (star_zero (Ambient q →L[ℝ] Ambient q))))
  have hFN (v : Ambient q) (p : N.Carrier) : F v p.val = 0 := by
    dsimp only [F]
    rw [hGN p, (N.normalProjection_isSelfAdjoint p).star_eq, sub_self]
  have hzero (j : Fin q) : ∀ᵐ x ∂volume.restrict Ω.val,
      ∀ i : Fin n, fderiv ℝ (F (EuclideanSpace.single j 1)) (u x) (Du x i) = 0 :=
    ae_fderiv_apply_eq_zero_of_target_zero N hu hN _ (hFC1 _) (hcF _) (hFN _)
  filter_upwards [ae_all_iff.2 hzero] with x hx
  intro i
  change star (fderiv ℝ G (u x) (Du x i)) = fderiv ℝ G (u x) (Du x i)
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin q) ℝ).toBasis.ext
  intro j
  have hz := hx j i
  have hdG := (hG.differentiable (by simp) (u x)).hasFDerivAt
  have hder := (hdG.star.clm_apply (hasFDerivAt_const
    (EuclideanSpace.single j 1) (u x))).sub
      (hdG.clm_apply (hasFDerivAt_const (EuclideanSpace.single j 1) (u x)))
  change HasFDerivAt (F (EuclideanSpace.single j 1)) _ (u x) at hder
  rw [hder.fderiv] at hz
  change (star (G (u x)) 0 + star (fderiv ℝ G (u x) (Du x i))
      (EuclideanSpace.single j 1)) -
    (G (u x) 0 + (fderiv ℝ G (u x) (Du x i)) (EuclideanSpace.single j 1)) = 0 at hz
  simp only [map_zero, zero_add] at hz
  simpa only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe] using sub_eq_zero.mp hz


end StationaryHarmonicMaps.Analysis

end
