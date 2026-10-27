module

public import StationaryHarmonicMaps.Geometry.NormalProjectionProperties
public import HarmonicMaps.Frozen.TubularProjection
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Smooth ambient normal extensions for the smooth target subclass

The actual tubular projection supplies a globally smooth map whose derivative
on the target is the tangent projection. Its derivative complement, multiplied
by a compact bump, is a smooth normal extension with bounded ambient derivative.
This construction is used only in the separate smooth-target bootstrap.
-/

public section

open HarmonicMaps Set Filter
open scoped ContDiff Manifold

namespace StationaryHarmonicMaps.SmoothTarget

private theorem exists_smooth_tangent_projection_extension {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ Q : Ambient q → Ambient q, ContDiff ℝ ∞ Q ∧
      ∀ p : (toC2 N).Carrier,
        fderiv ℝ Q p.val = ((toC2 N).tangentImage p).starProjection := by
  obtain ⟨ρ, hρ, _hρbase, hsub, _hUo, _hNearest, hTarget, _hLoc, _hBound,
    _hSnonempty, _hSbdd, _hSnonneg, _hSbound, Q, hQ, hQP, _hBounds⟩ :=
    tubularProjection_complete q N
  let V : Set (Ambient q) := {y | Metric.infDist y N.carrierSet < ρ}
  have hVo : IsOpen V := isOpen_lt (Metric.continuous_infDist_pt N.carrierSet) continuous_const
  have hVtube : V ⊆ tubularTube q N := by
    intro y hy
    apply hsub
    change Metric.infDist y N.carrierSet < 2 * ρ
    exact lt_trans (show Metric.infDist y N.carrierSet < ρ from hy) (by linarith only [hρ])
  refine ⟨Q, hQ, ?_⟩
  intro p
  let ps : N.Carrier := ⟨p.val, (toC2_carrierSet N) ▸ p.property⟩
  obtain ⟨hp, _hP, hD⟩ := hTarget ps
  have hpV : p.val ∈ V := by
    change Metric.infDist p.val N.carrierSet < ρ
    rw [Metric.infDist_zero_of_mem ps.property]
    exact hρ
  have hlocal := (tubularProjectionDerivative_characterization q N).1
    ⟨ps.val, hsub hp⟩ V Q hVo hpV hVtube hQ.contDiffOn (fun w hw => hQP w hw)
  exact hlocal.trans hD

private theorem exists_raw_smooth_normal_extension {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ G₀ : Ambient q → (Ambient q →L[ℝ] Ambient q), ContDiff ℝ ∞ G₀ ∧
      ∀ p : (toC2 N).Carrier, G₀ p.val = (toC2 N).normalProjection p := by
  obtain ⟨Q, hQ, hQD⟩ := exists_smooth_tangent_projection_extension N
  let G₀ : Ambient q → (Ambient q →L[ℝ] Ambient q) :=
    fun y => ContinuousLinearMap.id ℝ (Ambient q) - fderiv ℝ Q y
  have hG₀ : ContDiff ℝ ∞ G₀ := contDiff_const.sub (contDiff_infty_iff_fderiv.mp hQ).2
  refine ⟨G₀, hG₀, ?_⟩
  intro p
  calc
    G₀ p.val = ContinuousLinearMap.id ℝ (Ambient q) -
        ((toC2 N).tangentImage p).starProjection := by dsimp only [G₀]; rw [hQD]
    _ = ((toC2 N).tangentImage p)ᗮ.starProjection :=
      (Submodule.starProjection_orthogonal ((toC2 N).tangentImage p)).symm
    _ = _ := ((toC2 N).normalProjection_eq_starProjection p).symm

private theorem compactify_smooth_operator_field {q : ℕ}
    (K : Set (Ambient q)) (hK : IsCompact K)
    (G₀ : Ambient q → (Ambient q →L[ℝ] Ambient q)) (hG₀ : ContDiff ℝ ∞ G₀) :
    ∃ G : Ambient q → Ambient q →L[ℝ] Ambient q,
      ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      ∀ p : K, G p.val = G₀ p.val := by
  obtain ⟨r, hr, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let χ : ContDiffBump (0 : Ambient q) :=
    { rIn := r, rOut := r + 1, rIn_pos := hr, rIn_lt_rOut := lt_add_one r }
  let G : Ambient q → (Ambient q →L[ℝ] Ambient q) := fun y => χ y • G₀ y
  have hG : ContDiff ℝ ∞ G := χ.contDiff.smul hG₀
  have hts : tsupport G ⊆ tsupport (χ : Ambient q → ℝ) := by
    apply closure_mono
    intro y hy hzero
    change χ y = (0 : ℝ) at hzero
    apply hy
    change χ y • G₀ y = 0
    rw [hzero]
    exact zero_smul ℝ (G₀ y)
  have hcG : HasCompactSupport G :=
    χ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport G) hts
  refine ⟨G, hG, hcG, ?_⟩
  intro p
  have hp : p.val ∈ Metric.closedBall (0 : Ambient q) χ.rIn := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound p.val p.property
  change χ p.val • G₀ p.val = _
  rw [χ.one_of_mem_closedBall hp, one_smul]

private theorem exists_uniform_smooth_field_derivative_bound {q : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (G : Ambient q → E)
    (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y, ‖fderiv ℝ G y‖ ≤ L := by
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by simp)
  have hcD : HasCompactSupport (fderiv ℝ G) := hcG.fderiv ℝ
  obtain ⟨L, hL⟩ := hcD.exists_bound_of_continuous hD
  exact ⟨L, (norm_nonneg _).trans (hL 0), hL⟩

/-- A smooth target has a genuine compact smooth extension of its actual C² normal projection. -/
theorem exists_smooth_normal_projection_extension {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) :
    ∃ (G : Ambient q → Ambient q →L[ℝ] Ambient q) (L : ℝ),
      ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      (∀ p : (toC2 N).Carrier, G p.val = (toC2 N).normalProjection p) ∧
      0 ≤ L ∧ ∀ y, ‖fderiv ℝ G y‖ ≤ L := by
  obtain ⟨G₀, hG₀, hG₀N⟩ := exists_raw_smooth_normal_extension N
  obtain ⟨G, hG, hcG, hGN⟩ :=
    compactify_smooth_operator_field (toC2 N).carrierSet (toC2 N).isCompact G₀ hG₀
  obtain ⟨L, hL, hDG⟩ := exists_uniform_smooth_field_derivative_bound G hG hcG
  exact ⟨G, L, hG, hcG, (fun p => (hGN p).trans (hG₀N p)), hL, hDG⟩

end StationaryHarmonicMaps.SmoothTarget

end
