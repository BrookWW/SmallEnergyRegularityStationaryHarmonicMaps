module

public import StationaryHarmonicMaps.Analysis.WeightedKelvinTestZeroBoundary

/-!
# Actual smooth odd Kelvin gluing of compact interior maps

A genuine compact smooth map supported inside the unit ball has an actual
smooth extension equal to itself inside and to its negative weighted Kelvin
reflection outside. Smoothness at each sphere point follows from the
original support condition and continuity of inversion there. No collar
certificate, Sobolev reflection or reflected weak equation is assumed.
The extension need not have compact support or global finite energy.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open StationaryHarmonicMaps.Geometry
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual compact interior smooth data glue smoothly to their literal negative Kelvin reflection, with the full exterior derivative. -/
theorem exists_smooth_odd_kelvin_extension {n q : ℕ}
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
    (hsψ : tsupport ψ⊆Metric.ball (0:Domain n) 1) :
    ∃ U : Domain n → Ambient q,ContDiff ℝ ∞ U ∧
      (∀x : Domain n,‖x‖≤1 → U x=ψ x) ∧
      (∀x : Domain n,1≤‖x‖ → U x= -‖x‖^(2-(n:ℝ)) • ψ (inversion (0:Domain n) 1 x)) ∧
      (∀x : Domain n,‖x‖<1 → fderiv ℝ U x=fderiv ℝ ψ x) ∧
      (∀x v : Domain n,1<‖x‖ →
        fderiv ℝ U x v= -‖x‖^(2-(n:ℝ)) • fderiv ℝ ψ (inversion (0:Domain n) 1 x)
          (fderiv ℝ (inversion (0:Domain n) 1) x v)-
          ((2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x v) • ψ (inversion (0:Domain n) 1 x)) := by
  let I := inversion (0:Domain n) 1
  let w := fun x : Domain n=>‖x‖^(2-(n:ℝ))
  let U := fun x : Domain n=>if ‖x‖≤1 then ψ x else -w x • ψ (I x)
  have hSphereNot (x : Domain n) (hx : ‖x‖=1) : x∉tsupport ψ := by
    intro h
    have H := hsψ h
    rw [Metric.mem_ball,dist_zero_right,hx] at H
    exact (lt_irrefl (1:ℝ)) H
  have hInterior (x : Domain n) (hx : ‖x‖<1) : U=ᶠ[𝓝 x] ψ := by
    filter_upwards [continuous_norm.continuousAt.eventually_lt_const hx] with y hy
    exact if_pos hy.le
  have hExterior (x : Domain n) (hx : 1<‖x‖) :
      U=ᶠ[𝓝 x] (fun y=> -w y • ψ (I y)) := by
    filter_upwards [continuous_norm.continuousAt.eventually_const_lt hx] with y hy
    exact if_neg (not_le.mpr hy)
  have hUSmooth : ContDiff ℝ ∞ U := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    rcases lt_trichotomy ‖x‖ 1 with hx|hx|hx
    · exact hψ.contDiffAt.congr_of_eventuallyEq (hInterior x hx)
    · have hx0 : x≠0 := by intro H;rw [H,norm_zero] at hx;norm_num at hx
      have hIx : I x=x := inversion_of_mem_sphere (by simpa only [Metric.mem_sphere,dist_zero_right] using hx)
      have hNearψ : ∀ᶠy in 𝓝 x,ψ y=0 := by
        filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds (hSphereNot x hx)] with y hy
        exact image_eq_zero_of_notMem_tsupport hy
      have hNearI : ∀ᶠy in 𝓝 x,ψ (I y)=0 := by
        have hCont : ContinuousAt I x := (hasFDerivAt_unit_inversion x hx0).continuousAt
        change Tendsto I (𝓝 x) (𝓝 (I x)) at hCont
        rw [hIx] at hCont
        exact hCont.eventually hNearψ
      have hZero : U=ᶠ[𝓝 x] (fun _=>(0:Ambient q)) := by
        filter_upwards [hNearψ,hNearI] with y hy hIy
        dsimp only [U]
        split_ifs <;> simp only [hy,hIy,smul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hZero
    · have hx0 : x≠0 := norm_pos_iff.mp (zero_lt_one.trans hx)
      have hI : ContDiffAt ℝ ∞ I x := contDiffAt_const.inversion contDiffAt_const contDiffAt_id hx0
      have hw : ContDiffAt ℝ ∞ w x :=
        (contDiffAt_norm ℝ hx0).rpow_const_of_ne (norm_ne_zero_iff.mpr hx0)
      exact (hw.neg.smul (hψ.contDiffAt.comp x hI)).congr_of_eventuallyEq (hExterior x hx)
  refine ⟨U,hUSmooth,?_,?_,?_,?_⟩
  · intro x hx
    exact if_pos hx
  · intro x hx
    by_cases hInner : ‖x‖≤1
    · have hNorm : ‖x‖=1 := le_antisymm hInner hx
      have hψx : ψ x=0 := image_eq_zero_of_notMem_tsupport (hSphereNot x hNorm)
      have hIx : I x=x := inversion_of_mem_sphere (by simpa only [Metric.mem_sphere,dist_zero_right] using hNorm)
      change (if ‖x‖≤1 then ψ x else -w x • ψ (I x))= -w x • ψ (I x)
      rw [if_pos hInner,hIx,hψx,smul_zero]
    · exact if_neg hInner
  · intro x hx
    exact (hInterior x hx).fderiv_eq
  · intro x v hx
    have hx0 : x≠0 := norm_pos_iff.mp (zero_lt_one.trans hx)
    have hDI : HasFDerivAt I (fderiv ℝ I x) x :=
      (hasFDerivAt_unit_inversion x hx0).differentiableAt.hasFDerivAt
    have hw := hasFDerivAt_norm_real_power_of_ne_zero (2-(n:ℝ)) x hx0
    have hPower : (2-(n:ℝ))-2= -(n:ℝ) := by ring
    rw [hPower] at hw
    have hDS := (hw.neg.smul ((hψ.differentiable (by simp) (I x)).hasFDerivAt.comp x hDI))
    have hFun : (fun y=> -w y • ψ (I y))= -(fun y : Domain n=>‖y‖^(2-(n:ℝ))) • (ψ ∘ I) := by
      funext y
      rfl
    rw [(hExterior x hx).fderiv_eq,hFun,hDS.fderiv]
    simp only [Pi.neg_apply,neg_apply,add_apply,smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_eq_mul,Function.comp_apply]
    module

end StationaryHarmonicMaps.Analysis

end
