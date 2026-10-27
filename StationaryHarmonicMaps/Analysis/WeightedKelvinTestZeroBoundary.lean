module

public import StationaryHarmonicMaps.Analysis.KelvinTestZeroBoundary
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Genuine weighted Kelvin test differences

A compact smooth ambient test gives a globally smooth representative of
its weighted Kelvin difference away from the puncture. The original test
vanishes at reflected points near the puncture, so an actual origin cutoff
removes the singular expression. Sphere values vanish and give a native
zero-boundary graph. The full derivative retains the radial weight term.
No Sobolev reflection or reflected weak equation is asserted here.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open StationaryHarmonicMaps.Geometry
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Every real power of the Euclidean norm has the exact radial derivative at a nonzero point, including negative exponents. -/
theorem hasFDerivAt_norm_real_power_of_ne_zero {n : ℕ} (p : ℝ) (x : Domain n) (hx : x≠0) :
    HasFDerivAt (fun y : Domain n=>‖y‖^p)
      ((p*‖x‖^(p-2)) • innerSL ℝ x) x := by
  have hFun : (fun y : Domain n=>(‖y‖^2)^(p/2))=(fun y : Domain n=>‖y‖^p) := by
    funext y
    rw [← Real.rpow_two,← Real.rpow_mul (norm_nonneg y)]
    congr 1
    ring
  have hPower : (‖x‖^2)^(p/2-1)=‖x‖^(p-2) := by
    rw [← Real.rpow_two,← Real.rpow_mul (norm_nonneg x)]
    congr 1
    ring
  have H := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const
    (p:=p/2) (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)))
  rw [hFun,hPower] at H
  have hD : ((p/2*‖x‖^(p-2)) • (2 • innerSL ℝ x) : Domain n →L[ℝ] ℝ)=
      (p*‖x‖^(p-2)) • innerSL ℝ x := by
    ext v
    simp only [smul_apply,innerSL_apply_apply,smul_eq_mul]
    ring
  rw [hD] at H
  exact H

/-- The actual weighted Kelvin test difference is globally smooth, genuinely W0 on the unit ball, and has its full classical derivative away from the puncture. -/
theorem exists_weighted_kelvin_test_zeroBoundary {n q : ℕ} (hn : 2≤n)
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ∃ φ : Domain n → Ambient q, ContDiff ℝ ∞ φ ∧
      HasZeroBoundaryValues (ballDomain (0:Domain n) 1) φ
        (fun x i=>fderiv ℝ φ x (EuclideanSpace.single i 1)) ∧
      (∀x : Domain n,x≠0 → φ x=ψ x-‖x‖^(2-(n:ℝ)) • ψ (inversion (0:Domain n) 1 x)) ∧
      (∀(x v : Domain n),x≠0 →
        fderiv ℝ φ x v=fderiv ℝ ψ x v-
          ‖x‖^(2-(n:ℝ)) • fderiv ℝ ψ (inversion (0:Domain n) 1 x)
            (fderiv ℝ (inversion (0:Domain n) 1) x v)-
          ((2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x v) • ψ (inversion (0:Domain n) 1 x)) := by
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
  obtain ⟨χ,hχ,_hcχ,hsχ,hχone,_hχbound,_hDχ⟩ := Hcut (0:Domain n) δ hδ
  let I := inversion (0:Domain n) 1
  let w := fun x : Domain n=>‖x‖^(2-(n:ℝ))
  let φ : Domain n → Ambient q := fun x=>ψ x-(1-χ x) • (w x • ψ (I x))
  have hEq (x : Domain n) (hx : x≠0) : φ x=ψ x-w x • ψ (I x) := by
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
      have hNearχ : ∀ᶠy in 𝓝 (0:Domain n),χ y=1 := by
        filter_upwards [Metric.ball_mem_nhds (0:Domain n) hδ] with y hy
        exact hχone y (Metric.ball_subset_closedBall hy)
      have hNear : φ=ᶠ[𝓝 (0:Domain n)] ψ := hNearχ.mono (fun y hy=>by
        simp only [φ,hy,sub_self,zero_smul,sub_zero])
      exact hψ.contDiffAt.congr_of_eventuallyEq hNear
    · have hI : ContDiffAt ℝ ∞ I x :=
        contDiffAt_const.inversion contDiffAt_const contDiffAt_id hx
      have hw : ContDiffAt ℝ ∞ w x :=
        (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)
      exact hψ.contDiffAt.sub ((contDiffAt_const.sub hχ.contDiffAt).smul
        (hw.smul (hψ.contDiffAt.comp x hI)))
  have hBoundary (x : Domain n) (hx : x∈Metric.sphere (0:Domain n) 1) : φ x=0 := by
    have hNorm : ‖x‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
    have hx0 : x≠0 := by intro H; rw [H,norm_zero] at hNorm; norm_num at hNorm
    rw [hEq x hx0,show I x=x from inversion_of_mem_sphere hx]
    simp only [w,hNorm,Real.one_rpow,one_smul,sub_self]
  have hW := smooth_zeroBoundary_ball hn (⟨1,by norm_num⟩:PositiveRadius)
    univ isOpen_univ (subset_univ _) φ hφ.contDiffOn hBoundary
  refine ⟨φ,hφ,hW,hEq,?_⟩
  intro x v hx
  have hNear : φ=ᶠ[𝓝 x] (fun y=>ψ y-w y • ψ (I y)) :=
    (eventually_ne_nhds hx).mono (fun y hy=>hEq y hy)
  have hDI : HasFDerivAt I (fderiv ℝ I x) x :=
    (hasFDerivAt_unit_inversion x hx).differentiableAt.hasFDerivAt
  have hw := hasFDerivAt_norm_real_power_of_ne_zero (2-(n:ℝ)) x hx
  have hPower : (2-(n:ℝ))-2= -(n:ℝ) := by ring
  rw [hPower] at hw
  have hDS := (hψ.differentiable (by simp) x).hasFDerivAt.sub
    (hw.smul ((hψ.differentiable (by simp) (I x)).hasFDerivAt.comp x hDI))
  have hFun : (fun y=>ψ y-w y • ψ (I y))=ψ-(fun y : Domain n=>‖y‖^(2-(n:ℝ))) • (ψ ∘ I) := by
    funext y
    rfl
  rw [hNear.fderiv_eq,hFun,hDS.fderiv]
  simp only [sub_apply,add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_eq_mul]
  abel

end StationaryHarmonicMaps.Analysis

end
