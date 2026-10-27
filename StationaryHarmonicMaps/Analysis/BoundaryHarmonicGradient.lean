module

public import StationaryHarmonicMaps.Analysis.BoundaryKelvinWeakPoisson
public import StationaryHarmonicMaps.Analysis.BoundaryKelvinEnergy
public import StationaryHarmonicMaps.Analysis.NativeHarmonicGradient
public import HolderToCK.Foundation.BallVolume

/-!
# Actual boundary off-support bounds for the original gradient

The original W0 map and raw weak flux equation produce the true harmonic
odd Kelvin graph on the query ball. Its actual local energy and Weyl
gradient bound control the same literal zero extension of the original
weak gradient. All essential and finite-exponent bounds are conclusions;
no reflected equation or boundary estimate is supplied as a premise.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original raw off-support Dirichlet data give a genuine boundary essential-gradient bound and every finite-exponent bound for the same zero-extended gradient. -/
theorem exists_boundary_offSupport_gradient_bounds (n : ℕ) (hn : 2≤n) :
    ∃ K : ℝ,0<K ∧ ∀ (q : ℕ) (a : Domain n),‖a‖=1 → ∀ (r : ℝ),0<r → r≤1 →
      ∀ (u : Domain n → Ambient q) (Du F : Domain n → Gradient n q),
        HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) u Du →
        (∀ i,MemLp (fun x=>F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) →
        HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
          (fun x i=>Du x i-F x i) (fun _=>(0 : Ambient q)) →
        F =ᵐ[volume.restrict (Metric.ball (0 : Domain n) 1∩Metric.ball a r)] (fun _=>(0 : Gradient n q)) →
        let D₀ := fun x i=>(Metric.ball (0 : Domain n) 1).indicator (fun y=>Du y i) x
        let M := K*(volume.real (Metric.ball a (r/2)))⁻¹*(∫ x in Metric.ball a r,hsNormSq (D₀ x))
        (∀ᵐ x ∂volume.restrict (Metric.ball a (r/2)),hsNormSq (D₀ x)≤M) ∧
          MemLp (fun x=>Real.sqrt (hsNormSq (D₀ x))) ⊤ (volume.restrict (Metric.ball a (r/2))) ∧
          ∀ p : ℝ,1≤p →
            MemLp (fun x=>Real.sqrt (hsNormSq (D₀ x))) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball a (r/2))) ∧
            IntegrableOn (fun x=>(Real.sqrt (hsNormSq (D₀ x)))^p) (Metric.ball a (r/2)) volume ∧
            (∫ x in Metric.ball a (r/2),(Real.sqrt (hsNormSq (D₀ x)))^p)≤
              volume.real (Metric.ball a (r/2))*(Real.sqrt M)^p := by
  obtain ⟨K,hK,Henergy⟩ := exists_odd_kelvin_boundary_gradient_energy_bound n hn
  refine ⟨K,hK,?_⟩
  intro q a ha r hr hrOne u Du F hu hF hEq hZero D₀ M
  let I := inversion (0 : Domain n) 1
  let w := fun x : Domain n=>‖x‖^(2-(n:ℝ))
  let C := fun x i=>∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • Du (I x) j
  let U := fun x : Domain n=>if ‖x‖≤1 then u x else -w x • u (I x)
  let Dext := fun (x : Domain n) (i : Fin n)=>if ‖x‖≤1 then Du x i else
    -w x • C x i-((2-(n:ℝ))*‖x‖^(-(n:ℝ))*inner ℝ x (EuclideanSpace.single i 1)) • u (I x)
  obtain ⟨hNative,hHarmonic⟩ := odd_kelvin_native_weak_harmonic_boundary_ball hn a ha r hr u Du F hu hF hEq hZero
  change MemW12 (ballDomain a r) U Dext at hNative
  change HolderToCK.WeakPoissonOn (ballDomain a r) Dext (fun _=>(0 : Ambient q)) at hHarmonic
  obtain ⟨_V,_hV,_hAE,_hLap,_hGrad,_hCols,_hPoint,hBound,_hTop,_hAll⟩ :=
    exists_smooth_harmonic_representative_with_original_gradient_ball hn a ⟨r,hr⟩ U Dext hNative hHarmonic
  obtain ⟨_hEnergyI,hEnergy⟩ := Henergy q u Du hu a ha r hr hrOne
  change (∫ x in Metric.ball a r,hsNormSq (Dext x))≤K*(∫ x in Metric.ball a r,hsNormSq (D₀ x)) at hEnergy
  have hM : (volume.real (Metric.ball a (r/2)))⁻¹*(∫ x in Metric.ball a r,hsNormSq (Dext x))≤M := by
    calc
      _ ≤ (volume.real (Metric.ball a (r/2)))⁻¹*(K*(∫ x in Metric.ball a r,hsNormSq (D₀ x))) :=
        mul_le_mul_of_nonneg_left hEnergy (inv_nonneg.mpr ENNReal.toReal_nonneg)
      _ = _ := by dsimp only [M];ring
  have hOriginalPoint (x : Domain n) : hsNormSq (D₀ x)≤hsNormSq (Dext x) := by
    by_cases hx : x∈Metric.ball (0 : Domain n) 1
    · have hxNorm : ‖x‖≤1 := (by simpa only [Metric.mem_ball,dist_zero_right] using hx : ‖x‖<1).le
      simp only [D₀,Dext,indicator_of_mem hx,if_pos hxNorm,le_refl]
    · simp only [D₀,indicator_of_notMem hx,hsNormSq,norm_zero,zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero]
      exact Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  let ν := volume.restrict (Metric.ball a (r/2))
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hBound₀ : ∀ᵐ x ∂ν,hsNormSq (D₀ x)≤M :=
    hBound.mono (fun x hx=>(hOriginalPoint x).trans (hx.trans hM))
  obtain ⟨hZeroNative,_hPoincare⟩ := zeroBoundary_zeroExtension_boundary_poincare u Du hu a ha r hr
  have hHalf : Metric.ball a (r/2)⊆Metric.ball a r := Metric.ball_subset_ball (by linarith only [hr])
  have hMeas : AEStronglyMeasurable (fun x=>Real.sqrt (hsNormSq (D₀ x))) ν :=
    (memLp_sqrt_sum_norm_sq D₀ (fun i=>(hZeroNative.2.2 i).mono_measure
      (Measure.restrict_mono_set volume hHalf))).aestronglyMeasurable
  have hNormBound : ∀ᵐ x ∂ν,‖Real.sqrt (hsNormSq (D₀ x))‖≤Real.sqrt M := by
    filter_upwards [hBound₀] with x hx
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hx
  refine ⟨hBound₀,MemLp.of_bound hMeas (Real.sqrt M) hNormBound,?_⟩
  intro p hp
  have hLp : MemLp (fun x=>Real.sqrt (hsNormSq (D₀ x))) (ENNReal.ofReal p) ν :=
    MemLp.of_bound hMeas (Real.sqrt M) hNormBound
  have hIntegral : Integrable (fun x=>(Real.sqrt (hsNormSq (D₀ x)))^p) ν := by
    simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using
      integrable_norm_rpow_of_memLp_real _ (by linarith only [hp] : 0≤p) hLp
  have hPower : ∀ᵐ x ∂ν,(Real.sqrt (hsNormSq (D₀ x)))^p≤(Real.sqrt M)^p := by
    filter_upwards [hNormBound] with x hx
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hx
    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) hx (by linarith only [hp])
  refine ⟨hLp,hIntegral,?_⟩
  simpa only [ν,integral_const,smul_eq_mul,measureReal_restrict_apply_univ] using
    integral_mono_ae hIntegral (integrable_const ((Real.sqrt M)^p)) hPower

/-- The same original raw off-support data give genuine boundary energy decay for the literal zero-extended gradient, with a constant depending only on dimension. -/
theorem exists_boundary_offSupport_gradient_energy_decay (n : ℕ) (hn : 2≤n) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) (a : Domain n),‖a‖=1 → ∀ (r : ℝ),0<r → r≤1 →
      ∀ (u : Domain n → Ambient q) (Du F : Domain n → Gradient n q),
        HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) u Du →
        (∀ i,MemLp (fun x=>F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) →
        HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1)
          (fun x i=>Du x i-F x i) (fun _=>(0 : Ambient q)) →
        F =ᵐ[volume.restrict (Metric.ball (0 : Domain n) 1∩Metric.ball a r)] (fun _=>(0 : Gradient n q)) →
        let D₀ := fun x i=>(Metric.ball (0 : Domain n) 1).indicator (fun y=>Du y i) x
        ∀ (θ : ℝ),0<θ → θ≤1/2 →
          (∫ x in Metric.ball a (θ*r),hsNormSq (D₀ x))≤
            C*θ^n*(∫ x in Metric.ball a r,hsNormSq (D₀ x)) := by
  obtain ⟨K,hK,Hbounds⟩ := exists_boundary_offSupport_gradient_bounds n hn
  let C := K*(2 : ℝ)^n
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  intro q a ha r hr hrOne u Du F hu hF hEq hZero D₀ θ hθ hθHalf
  obtain ⟨hBound,_hTop,_hLp⟩ := Hbounds q a ha r hr hrOne u Du F hu hF hEq hZero
  let M := K*(volume.real (Metric.ball a (r/2)))⁻¹*(∫ x in Metric.ball a r,hsNormSq (D₀ x))
  have hHalf : Metric.ball a (θ*r)⊆Metric.ball a (r/2) :=
    Metric.ball_subset_ball (by nlinarith only [hθHalf,hr])
  have hSub : Metric.ball a (θ*r)⊆Metric.ball a r :=
    hHalf.trans (Metric.ball_subset_ball (by linarith only [hr]))
  obtain ⟨hNative,_hPoincare⟩ := zeroBoundary_zeroExtension_boundary_poincare u Du hu a ha r hr
  have hSmall : ∀ᵐ x ∂volume.restrict (Metric.ball a (θ*r)),hsNormSq (D₀ x)≤M :=
    hBound.filter_mono (ae_mono (Measure.restrict_mono_set volume hHalf))
  have hMass : volume.real (Metric.ball a (r/2))=volume.real (Metric.ball (0 : Domain n) (r/2)) := by
    simp only [measureReal_def,Measure.addHaar_ball_center volume]
  calc
    _ ≤ ∫ _x in Metric.ball a (θ*r),M :=
      integral_mono_ae (hNative.integrable_hsNormSq.mono_set hSub) (integrableOn_const measure_ball_ne_top) hSmall
    _ = (volume.real (Metric.ball a (θ*r))*(volume.real (Metric.ball a (r/2)))⁻¹)*
        K*(∫ x in Metric.ball a r,hsNormSq (D₀ x)) := by
      simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,M]
      ring
    _ = _ := by rw [hMass,HolderToCK.ball_volume_ratio_half a hr hθ];dsimp only [C];ring

end StationaryHarmonicMaps.Analysis

end
