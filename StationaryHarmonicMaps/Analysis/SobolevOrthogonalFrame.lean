module

public import StationaryHarmonicMaps.Analysis.C1SobolevPostcompositionLocal
public import StationaryHarmonicMaps.Geometry.ProjectionCommutator
public import HarmonicMaps.Analysis.SobolevAECongruence
public import HarmonicMaps.SobolevRestriction
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Differentiated orthogonality of actual bounded Sobolev frames

A compact cutoff of each polynomial matrix constraint agrees with that
constraint near the essential range. The C¹ chain rule and uniqueness of the
actual weak gradient differentiate a.e. orthogonality without assuming that
identity for the derivative.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- A compact C¹ constraint vanishing along the actual map has zero weak derivative. -/
theorem ae_fderiv_eq_zero_of_comp_eq_zero {n m k : ℕ} {Ω : OpenDomain n}
    {p : Domain n → Ambient m} {Dp : Domain n → Gradient n m}
    (hp : MemW12Loc Ω p Dp) (F : Ambient m → Ambient k)
    (hF : ContDiff ℝ 1 F) (hcF : HasCompactSupport F)
    (hzero : ∀ᵐ x ∂volume.restrict Ω.val, F (p x) = 0) :
    ∀ᵐ x ∂volume.restrict Ω.val, ∀ i, fderiv ℝ F (p x) (Dp x i) = 0 := by
  obtain ⟨L, hL⟩ := (hcF.fderiv ℝ).exists_bound_of_continuous
    (hF.continuous_fderiv (by norm_num))
  have hw := memW12Loc_postcompose_c1 hp F hF L hL
  have hmap : F ∘ p =ᵐ[volume.restrict Ω.val] (0 : Domain n → Ambient k) := hzero
  have hD := hw.1.ae_eq_of_ae_eq_map (HasWeakGradient.zero Ω) hmap
  filter_upwards [hD] with x hx i
  simpa only [Pi.zero_apply] using congrFun hx i

/-- Orthogonality differentiates along the given Sobolev columns of the encoded frame. -/
theorem ae_orthogonal_frame_derivative {n m q : ℕ} {Ω : OpenDomain n}
    {p : Domain n → Ambient m} {Dp : Domain n → Gradient n m}
    (hp : MemW12Loc Ω p Dp)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q)) (M : ℝ)
    (hbound : ∀ᵐ x ∂volume.restrict Ω.val, ‖p x‖ ≤ M)
    (horth : ∀ᵐ x ∂volume.restrict Ω.val, star (R (p x)) * R (p x) = 1) :
    ∀ᵐ x ∂volume.restrict Ω.val, ∀ i,
      star (R (Dp x i)) * R (p x) + star (R (p x)) * R (Dp x i) = 0 := by
  let χ : ContDiffBump (0 : Ambient m) :=
    { rIn := |M| + 1, rOut := |M| + 2,
      rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let C (v : Ambient q) (z : Ambient m) := star (R z) (R z v) - v
  let F (v : Ambient q) (z : Ambient m) := χ z • C v z
  have hC (v : Ambient q) : ContDiff ℝ 1 (C v) := by
    have hstar : ContDiff ℝ 1 (fun z => star (R z)) :=
      (starL' ℝ : (Ambient q →L[ℝ] Ambient q) ≃L[ℝ]
        (Ambient q →L[ℝ] Ambient q)).contDiff.comp R.contDiff
    exact (hstar.clm_apply (R.contDiff.clm_apply contDiff_const)).sub contDiff_const
  have hF (v : Ambient q) : ContDiff ℝ 1 (F v) := χ.contDiff.smul (hC v)
  have hcF (v : Ambient q) : HasCompactSupport (F v) := χ.hasCompactSupport.smul_right
  have hzero (j : Fin q) : ∀ᵐ x ∂volume.restrict Ω.val, ∀ i,
      fderiv ℝ (F (EuclideanSpace.single j 1)) (p x) (Dp x i) = 0 := by
    apply ae_fderiv_eq_zero_of_comp_eq_zero hp _ (hF _) (hcF _)
    filter_upwards [horth] with x hx
    have hcv := congrArg (fun T : Ambient q →L[ℝ] Ambient q =>
      T (EuclideanSpace.single j 1)) hx
    change star (R (p x)) (R (p x) (EuclideanSpace.single j 1)) =
      EuclideanSpace.single j 1 at hcv
    simp only [F, C, hcv, sub_self, smul_zero]
  filter_upwards [hbound, ae_all_iff.2 hzero] with x hx hxzero i
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin q) ℝ).toBasis.ext
  intro j
  have hball : p x ∈ Metric.ball (0 : Ambient m) χ.rIn := by
    change dist (p x) 0 < |M| + 1
    rw [dist_zero_right]
    exact lt_of_le_of_lt (hx.trans (le_abs_self M)) (lt_add_one _)
  have hEq : F (EuclideanSpace.single j 1) =ᶠ[𝓝 (p x)] C (EuclideanSpace.single j 1) :=
    (χ.eventuallyEq_one_of_mem_ball hball).mono (fun z hz => by
      change χ z = (1 : ℝ) at hz
      change χ z • C (EuclideanSpace.single j 1) z = _
      rw [hz, one_smul])
  have hdR := R.hasFDerivAt (x := p x)
  have hder := (hdR.star.clm_apply
    (hdR.clm_apply (hasFDerivAt_const (EuclideanSpace.single j 1) (p x)))).sub
      (hasFDerivAt_const (EuclideanSpace.single j 1) (p x))
  change HasFDerivAt (C (EuclideanSpace.single j 1)) _ (p x) at hder
  have hz := hxzero j i
  rw [hEq.fderiv_eq, hder.fderiv] at hz
  change star (R (p x)) (R (p x) 0 + R (Dp x i) (EuclideanSpace.single j 1)) +
    star (R (Dp x i)) (R (p x) (EuclideanSpace.single j 1)) - 0 = 0 at hz
  simp only [map_zero, zero_add, sub_zero] at hz
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe]
  change star (R (Dp x i)) (R (p x) (EuclideanSpace.single j 1)) +
    star (R (p x)) (R (Dp x i) (EuclideanSpace.single j 1)) = 0
  exact (add_comm _ _).trans hz

end StationaryHarmonicMaps.Analysis

end
