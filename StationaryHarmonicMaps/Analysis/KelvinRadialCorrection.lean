module

public import StationaryHarmonicMaps.Analysis.ZeroBoundarySmoothIntegration
public import StationaryHarmonicMaps.Analysis.WeightedKelvinTestZeroBoundary

/-!
# Actual vanishing of the Kelvin radial correction

A compact ambient smooth test vanishes at inverted points near zero.
An actual origin cutoff therefore produces smooth radial test fields
agreeing with the literal singular-looking formula away from zero.
Their divergence is computed with the true first derivatives. Genuine
zero-boundary integration by parts gives the exact correction identity
for the original native map and columns.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open StationaryHarmonicMaps.Geometry
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- A compact ambient smooth test produces actual smooth Kelvin radial fields with their exact punctured values and divergence. -/
theorem exists_smooth_kelvin_radial_test_field {n q : ℕ}
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ∃ A : Fin n → Domain n → Ambient q,(∀i,ContDiff ℝ ∞ (A i)) ∧
      (∀(i : Fin n) (x : Domain n),x≠0 →
        A i x=(‖x‖^(-(n:ℝ))*x i) • ψ (inversion (0:Domain n) 1 x)) ∧
      (∀x : Domain n,x≠0 →
        (∑i : Fin n,fderiv ℝ (A i) x (EuclideanSpace.single i 1))=
          ‖x‖^(-(n:ℝ)) • (∑i : Fin n,x i •
            fderiv ℝ ψ (inversion (0:Domain n) 1 x)
              (fderiv ℝ (inversion (0:Domain n) 1) x (EuclideanSpace.single i 1)))) := by
  obtain ⟨R,hR,hZeroψ⟩ := hcψ.exists_pos_le_norm
  let δ : ℝ := 1/(4*(R+1))
  have hRp : 0<R+1 := by linarith
  have hδ : 0<δ := by dsimp only [δ];positivity
  have hδInv : (2*δ)⁻¹=2*(R+1) := by
    dsimp only [δ]
    field_simp
    ring
  have hRInv : R≤(2*δ)⁻¹ := by rw [hδInv];linarith
  obtain ⟨_M,_hM,Hcut⟩ := exists_scaled_ball_cutoff n
  obtain ⟨χ,hχ,_hcχ,hsχ,hχone,_hA,_hDχ⟩ := Hcut (0:Domain n) δ hδ
  let I := inversion (0:Domain n) 1
  let w := fun x : Domain n=>‖x‖^(-(n:ℝ))
  let A := fun (i : Fin n) (x : Domain n)=>(1-χ x) • ((w x*x i) • ψ (I x))
  have hEq (i : Fin n) (x : Domain n) (hx : x≠0) : A i x=(w x*x i) • ψ (I x) := by
    by_cases hχx : χ x=0
    · simp only [A,hχx,sub_zero,one_smul]
    · have hxSupport : x∈tsupport χ := subset_tsupport χ hχx
      have hxNorm : ‖x‖<2*δ := by
        simpa only [Metric.mem_ball,dist_zero_right] using hsχ hxSupport
      have hNormPos : 0<‖x‖ := norm_pos_iff.mpr hx
      have hLarge : R≤‖I x‖ := by
        rw [show ‖I x‖=‖x‖⁻¹ from norm_unit_inversion x]
        exact hRInv.trans (by simpa only [one_div] using
          one_div_le_one_div_of_le hNormPos hxNorm.le)
      have hψZero : ψ (I x)=0 := hZeroψ _ hLarge
      simp only [A,hψZero,smul_zero]
  have hSmooth (i : Fin n) : ContDiff ℝ ∞ (A i) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x=0
    · subst x
      have hNearχ : ∀ᶠy in 𝓝 (0:Domain n),χ y=1 := by
        filter_upwards [Metric.ball_mem_nhds (0:Domain n) hδ] with y hy
        exact hχone y (Metric.ball_subset_closedBall hy)
      have hNear : A i=ᶠ[𝓝 (0:Domain n)] (fun _=>(0:Ambient q)) := hNearχ.mono (fun y hy=>by
        simp only [A,hy,sub_self,zero_smul])
      exact contDiffAt_const.congr_of_eventuallyEq hNear
    · have hI : ContDiffAt ℝ ∞ I x := contDiffAt_const.inversion contDiffAt_const contDiffAt_id hx
      have hw : ContDiffAt ℝ ∞ w x :=
        (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)
      have hπ : ContDiffAt ℝ ∞ (fun y : Domain n=>y i) x :=
        (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin n=>ℝ) i).contDiff.contDiffAt
      exact (contDiffAt_const.sub hχ.contDiffAt).smul ((hw.mul hπ).smul (hψ.contDiffAt.comp x hI))
  refine ⟨A,hSmooth,hEq,?_⟩
  intro x hx
  have hDI : HasFDerivAt I (fderiv ℝ I x) x :=
    (hasFDerivAt_unit_inversion x hx).differentiableAt.hasFDerivAt
  have hw := hasFDerivAt_norm_real_power_of_ne_zero (-(n:ℝ)) x hx
  have hD (i : Fin n) : fderiv ℝ (A i) x (EuclideanSpace.single i 1)=
      (w x*x i) • fderiv ℝ ψ (I x) (fderiv ℝ I x (EuclideanSpace.single i 1))+
        (w x+(-(n:ℝ))*‖x‖^(-(n:ℝ)-2)*(x i)^2) • ψ (I x) := by
    let πi := PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin n=>ℝ) i
    have hNear : A i=ᶠ[𝓝 x] (fun y=>(w y*y i) • ψ (I y)) :=
      (eventually_ne_nhds hx).mono (fun y hy=>hEq i y hy)
    have H := (hw.mul πi.hasFDerivAt).smul
      ((hψ.differentiable (by simp) (I x)).hasFDerivAt.comp x hDI)
    have hFun : (fun y=>(w y*y i) • ψ (I y))=
        ((fun y : Domain n=>‖y‖^(-(n:ℝ)))*(πi : Domain n → ℝ)) • (ψ ∘ I) := rfl
    rw [hNear.fderiv_eq,hFun,H.fderiv]
    simp only [smul_apply,add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,πi,PiLp.proj_apply,
      EuclideanSpace.inner_single_right,conj_trivial,one_mul,Function.comp_apply,Pi.mul_apply,w,PiLp.single_apply,ite_true]
    module
  have hSumSq : (∑i : Fin n,x i^2)=‖x‖^2 := (EuclideanSpace.real_norm_sq_eq x).symm
  have hPower : ‖x‖^(-(n:ℝ)-2)*‖x‖^2=‖x‖^(-(n:ℝ)) := by
    rw [← Real.rpow_two,← Real.rpow_add (norm_pos_iff.mpr hx)]
    congr 1
    ring
  have hCoeff : (∑i : Fin n,(w x+(-(n:ℝ))*‖x‖^(-(n:ℝ)-2)*(x i)^2))=0 := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,hSumSq]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,w]
    rw [mul_assoc,hPower]
    ring
  simp_rw [hD]
  rw [Finset.sum_add_distrib,← Finset.sum_smul,hCoeff,zero_smul,add_zero,Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _=>by rw [smul_smul])

/-- The literal Kelvin radial correction has genuine integrable pairings and zero integral for the original native zero-boundary graph. -/
theorem zeroBoundary_kelvin_radial_correction {n q : ℕ} (hn : 1≤n)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : HasZeroBoundaryValues (ballDomain (0:Domain n) 1) u Du)
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    let I := inversion (0:Domain n) 1
    let L := fun x : Domain n=>∑i : Fin n,inner ℝ
      ((‖x‖^(-(n:ℝ))*x i) • ψ (I x)) (Du x i)
    let H := fun x : Domain n=>inner ℝ
      (‖x‖^(-(n:ℝ)) • (∑i : Fin n,x i •
        fderiv ℝ ψ (I x) (fderiv ℝ I x (EuclideanSpace.single i 1)))) (u x)
    IntegrableOn L (Metric.ball (0:Domain n) 1) volume ∧
      IntegrableOn H (Metric.ball (0:Domain n) 1) volume ∧
      IntegrableOn (fun x=>L x+H x) (Metric.ball (0:Domain n) 1) volume ∧
      (∫x in Metric.ball (0:Domain n) 1,L x+H x)=0 := by
  intro I L H
  letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  let μ := volume.restrict (Metric.ball (0:Domain n) 1)
  obtain ⟨A,hA,hVal,hDiv⟩ := exists_smooth_kelvin_radial_test_field ψ hψ hcψ
  obtain ⟨hLI,hHI,hEq⟩ := zeroBoundary_smooth_oneForm_integration_by_parts u Du hu A hA
  have hAE0 : ∀ᵐx : Domain n∂μ,x≠0 := by
    have H0 : ∀ᵐx : Domain n∂volume,x≠0 := by simp [ae_iff]
    exact H0.filter_mono (ae_mono Measure.restrict_le_self)
  have hLeft : (fun x=>∑i : Fin n,inner ℝ (A i x) (Du x i)) =ᵐ[μ] L := by
    filter_upwards [hAE0] with x hx
    exact Finset.sum_congr rfl (fun i _=>congrArg (fun v : Ambient q=>inner ℝ v (Du x i)) (hVal i x hx))
  have hRight : (fun x=>inner ℝ (∑i : Fin n,fderiv ℝ (A i) x (EuclideanSpace.single i 1)) (u x)) =ᵐ[μ] H := by
    filter_upwards [hAE0] with x hx
    exact congrArg (fun v : Ambient q=>inner ℝ v (u x)) (hDiv x hx)
  have hL : Integrable L μ := hLI.congr hLeft
  have hH : Integrable H μ := hHI.congr hRight
  refine ⟨hL,hH,hL.add hH,?_⟩
  rw [integral_add hL hH,← integral_congr_ae hLeft,← integral_congr_ae hRight,hEq]
  exact neg_add_cancel _

end StationaryHarmonicMaps.Analysis

end
