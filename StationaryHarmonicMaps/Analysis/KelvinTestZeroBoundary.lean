module

public import StationaryHarmonicMaps.Geometry.UnitInversion
public import StationaryHarmonicMaps.Analysis.ScaledBallCutoff
public import HarmonicMaps.Analysis.SmoothBallZeroBoundary

/-!
# Actual zero-boundary test differences for unit inversion

The singular-looking reflected compact test vanishes near the puncture.
A genuine smooth cutoff removes its isolated origin value, producing one
actual smooth map equal to the test difference at every nonzero point.
Its sphere values vanish, and the proved smooth zero-sphere closure gives
its genuine native W0 graph and original classical gradient.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open StationaryHarmonicMaps.Geometry
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Every original compact smooth test has an actual smooth native W0 inversion difference, with the exact derivative away from the puncture. -/
theorem exists_kelvin_test_zeroBoundary {n q : ℕ} (hn : 2≤n)
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ∃ φ : Domain n → Ambient q, ContDiff ℝ ∞ φ ∧
      HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) φ
        (fun x i => fderiv ℝ φ x (EuclideanSpace.single i 1)) ∧
      (∀ x : Domain n,x≠0 → φ x=ψ x-ψ (inversion (0 : Domain n) 1 x)) ∧
      (∀ x : Domain n,x≠0 → fderiv ℝ φ x=fderiv ℝ ψ x-
        (fderiv ℝ ψ (inversion (0 : Domain n) 1 x)).comp
          (fderiv ℝ (inversion (0 : Domain n) 1) x)) := by
  obtain ⟨R,hR,hZeroψ⟩ := hcψ.exists_pos_le_norm
  let δ : ℝ := 1/(4*(R+1))
  have hRp : 0<R+1 := by linarith
  have hδ : 0<δ := by dsimp only [δ]; positivity
  have hδInv : (2*δ)⁻¹=2*(R+1) := by
    dsimp only [δ]
    field_simp
    ring
  have hRInv : R≤(2*δ)⁻¹ := by rw [hδInv]; linarith
  obtain ⟨_M,_hM,Hcut⟩ := exists_scaled_ball_cutoff n
  obtain ⟨χ,hχ,_hcχ,hsχ,hχone,_hχbound,_hDχ⟩ := Hcut (0 : Domain n) δ hδ
  let I := inversion (0 : Domain n) 1
  let φ : Domain n → Ambient q := fun x => ψ x-(1-χ x) • ψ (I x)
  have hEq (x : Domain n) (hx : x≠0) : φ x=ψ x-ψ (I x) := by
    by_cases hχx : χ x=0
    · simp only [φ,hχx,sub_zero,one_smul]
    · have hxSupport : x∈tsupport χ := subset_tsupport χ hχx
      have hxNorm : ‖x‖<2*δ := by
        simpa only [Metric.mem_ball,dist_zero_right] using hsχ hxSupport
      have hNormPos : 0<‖x‖ := norm_pos_iff.mpr hx
      have hLarge : R≤‖I x‖ := by
        rw [show ‖I x‖=‖x‖⁻¹ from norm_unit_inversion x]
        exact hRInv.trans (by
          simpa only [one_div] using one_div_le_one_div_of_le hNormPos hxNorm.le)
      have hψZero : ψ (I x)=0 := hZeroψ _ hLarge
      simp only [φ,hψZero,smul_zero,sub_zero]
  have hφ : ContDiff ℝ ∞ φ := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x=0
    · subst x
      have hNearχ : ∀ᶠ y in 𝓝 (0 : Domain n),χ y=1 := by
        filter_upwards [Metric.ball_mem_nhds (0 : Domain n) hδ] with y hy
        exact hχone y (Metric.ball_subset_closedBall hy)
      have hNear : φ=ᶠ[𝓝 (0 : Domain n)] ψ := hNearχ.mono (fun y hy => by
        simp only [φ,hy,sub_self,zero_smul,sub_zero])
      exact hψ.contDiffAt.congr_of_eventuallyEq hNear
    · have hI : ContDiffAt ℝ ∞ I x :=
        contDiffAt_const.inversion contDiffAt_const contDiffAt_id hx
      exact hψ.contDiffAt.sub ((contDiffAt_const.sub hχ.contDiffAt).smul (hψ.contDiffAt.comp x hI))
  have hBoundary (x : Domain n) (hx : x∈Metric.sphere (0 : Domain n) 1) : φ x=0 := by
    have hNorm : ‖x‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
    have hx0 : x≠0 := by intro H; rw [H,norm_zero] at hNorm; norm_num at hNorm
    rw [hEq x hx0,show I x=x from inversion_of_mem_sphere hx,sub_self]
  have hW := smooth_zeroBoundary_ball hn (⟨1,by norm_num⟩ : PositiveRadius)
    univ isOpen_univ (subset_univ _) φ hφ.contDiffOn hBoundary
  refine ⟨φ,hφ,hW,hEq,?_⟩
  intro x hx
  have hNear : φ=ᶠ[𝓝 x] (fun y => ψ y-ψ (I y)) :=
    (eventually_ne_nhds hx).mono (fun y hy => hEq y hy)
  have hDI : HasFDerivAt I (fderiv ℝ I x) x :=
    (hasFDerivAt_unit_inversion x hx).differentiableAt.hasFDerivAt
  have hDS := (hψ.differentiable (by simp) x).hasFDerivAt.sub
    ((hψ.differentiable (by simp) (I x)).hasFDerivAt.comp x hDI)
  have hFun : (fun y => ψ y-ψ (I y))=ψ-(ψ ∘ I) := by funext y; rfl
  rw [hNear.fderiv_eq,hFun]
  exact hDS.fderiv


end StationaryHarmonicMaps.Analysis

end
