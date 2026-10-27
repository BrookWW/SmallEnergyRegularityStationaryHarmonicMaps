module

public import StationaryHarmonicMaps.Analysis.SobolevLinearOperations
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# C¹ functions of the domain point and a Sobolev map

A finite-dimensional linear encoding realizes the pair `(x,u(x))` as a
Euclidean Sobolev map. The C¹ chain rule is then transported back through
the actual inverse. Its displayed columns are the two-variable differential
applied to `(e_i,Du_i)`.
-/

public section

open HarmonicMaps MeasureTheory
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The mixed C¹ chain rule preserves the actual Sobolev columns on every open domain. -/
theorem memW12Loc_mixed_postcompose_c1 {n q k : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (F : Domain n × Ambient q → Ambient k) (hF : ContDiff ℝ 1 F)
    {L : ℝ} (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) :
    MemW12Loc Ω (fun x => F (x, u x))
      (fun x i => fderiv ℝ F (x, u x) (EuclideanSpace.single i 1, Du x i)) := by
  let E : (Domain n × Ambient q) ≃L[ℝ] Ambient (n + q) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let I : Domain n →L[ℝ] Ambient (n + q) :=
    E.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Domain n) (Ambient q))
  let J : Ambient q →L[ℝ] Ambient (n + q) :=
    E.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Domain n) (Ambient q))
  have hid : MemW12Loc Ω (fun x : Domain n => x)
      (fun _ i => EuclideanSpace.single i 1) := by
    have H := memW12Loc_of_c1 Ω (f := (id : Domain n → Ambient n)) contDiff_id
    simp only [fderiv_id, ContinuousLinearMap.id_apply] at H
    rw [show (id : Domain n → Ambient n) = (fun x : Domain n => x) from
      funext (fun x => id_eq x)] at H
    exact H
  have hIW := memW12Loc_continuousLinearMap hid I
  have hJW := memW12Loc_continuousLinearMap hu J
  have hW : MemW12Loc Ω (fun x => I x + J (u x))
      (fun x i => I (EuclideanSpace.single i 1) + J (Du x i)) :=
    memW12Loc_add hIW hJW
  have hpair (x : Domain n) (y : Ambient q) : I x + J y = E (x, y) := by
    change E (x, 0) + E (0, y) = E (x, y)
    rw [← map_add]
    simp
  have hFE : ContDiff ℝ 1 (F ∘ E.symm) := hF.comp E.symm.contDiff
  have hDFE (z : Ambient (n + q)) :
      fderiv ℝ (F ∘ E.symm) z =
        (fderiv ℝ F (E.symm z)).comp E.symm.toContinuousLinearMap := by
    rw [fderiv_comp z (hF.differentiable (by simp) _) E.symm.differentiableAt]
    rw [E.symm.fderiv]
  have hbound (z : Ambient (n + q)) :
      ‖fderiv ℝ (F ∘ E.symm) z‖ ≤ L * ‖E.symm.toContinuousLinearMap‖ := by
    rw [hDFE]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hDF _) (norm_nonneg _))
  have H := memW12Loc_postcompose_c1 hW (F ∘ E.symm) hFE
    (L * ‖E.symm.toContinuousLinearMap‖) hbound
  have hmap : (F ∘ E.symm) ∘ (fun x => I x + J (u x)) =
      (fun x => F (x, u x)) := by
    funext x
    simp only [Function.comp_apply, hpair, E.symm_apply_apply]
  have hder : (fun x i => fderiv ℝ (F ∘ E.symm) (I x + J (u x))
      (I (EuclideanSpace.single i 1) + J (Du x i))) =
      (fun x i => fderiv ℝ F (x, u x) (EuclideanSpace.single i 1, Du x i)) := by
    funext x i
    rw [hDFE, hpair, hpair]
    simp only [ContinuousLinearMap.comp_apply, E.symm.coe_coe,
      E.symm_apply_apply]
  rw [hmap, hder] at H
  exact H

end StationaryHarmonicMaps.Analysis

end
