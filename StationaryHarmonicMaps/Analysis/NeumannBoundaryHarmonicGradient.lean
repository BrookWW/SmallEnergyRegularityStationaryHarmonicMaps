module

public import StationaryHarmonicMaps.Analysis.NeumannKelvinWeakPoisson
public import StationaryHarmonicMaps.Analysis.NeumannKelvinLocalEnergy
public import StationaryHarmonicMaps.Analysis.NativeHarmonicGradient

/-!
# Boundary essential-gradient bounds for the original Neumann response

The actual native reflection and natural weak equation supply a genuine
harmonic graph across the sphere. Its original same-cap energy controls the
same zero-extended original gradient on the half ball.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original native Neumann response data give a genuine boundary essential-gradient bound and every finite-exponent bound for the same zero-extended gradient. -/
theorem exists_neumann_boundary_offSupport_gradient_bounds (n : ℕ) (hn : 2≤n) :
    ∃ K : ℝ,0<K ∧ ∀ (q : ℕ) (a : Domain n),‖a‖=1 → ∀ (r : ℝ),0<r → r≤1/2 →
      ∀ (u : Domain n → Ambient q) (Du F : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) u Du →
        (∀ i,MemLp (fun x=>F x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) →
        (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          (∫x in Metric.ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Du x i) (Dψ x i))=
            ∫x in Metric.ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (F x i) (Dψ x i)) →
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
  let K := 1+2*(2 : ℝ)^(2*n)+2*((n : ℝ)-2)^2*(2 : ℝ)^(2*(n-2))*(4 : ℝ)^n
  have hK : 0<K := by dsimp only [K];positivity
  refine ⟨K,hK,?_⟩
  intro q a ha r hr hrHalf u Du F hu hF hTests hZero D₀ M
  let I := inversion (0 : Domain n) 1
  let V := fun x=>‖x‖^(n-2) • (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^(n-3) • u (t • x))
  let B := fun x j=>‖x‖^(n-2) • (∫t in (‖x‖⁻¹)^2..‖x‖⁻¹,t^(n-2) • Du (t • x) j)
  let O := fun x=>‖x‖^(2-(n : ℝ)) • u (I x)+((n : ℝ)-2) • V x
  let DO := fun x i=>‖x‖^(2-(n : ℝ)) •
    (∑j : Fin n,(fderiv ℝ I x (EuclideanSpace.single i 1)) j • Du (I x) j)+
      ((n : ℝ)-2) • (∑j : Fin n,((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j • B x j)
  let U := fun x=>if ‖x‖≤1 then u x else O x
  let Dext := fun x i=>if ‖x‖≤1 then Du x i else DO x i
  obtain ⟨hNative,hHarmonic⟩ := neumann_kelvin_native_weak_harmonic_boundary_ball hn a ha r hr hrHalf
    u Du F hu hF hTests hZero
  change MemW12 (ballDomain a r) U Dext at hNative
  change HolderToCK.WeakPoissonOn (ballDomain a r) Dext (fun _=>(0 : Ambient q)) at hHarmonic
  obtain ⟨_W,_hW,_hAE,_hLap,_hGrad,_hCols,_hPoint,hBound,_hTop,_hAll⟩ :=
    exists_smooth_harmonic_representative_with_original_gradient_ball hn a ⟨r,hr⟩ U Dext hNative hHarmonic
  obtain ⟨_hEI,hEnergy⟩ := neumann_kelvin_local_gradient_energy hn Du hu.2.2 a ha r hr hrHalf
  have hOriginalIntegral : (∫x in Metric.ball a r,hsNormSq (D₀ x))=
      ∫x in Metric.ball (0 : Domain n) 1∩Metric.ball a r,hsNormSq (Du x) := by
    have hPoint : (fun x=>hsNormSq (D₀ x))=(Metric.ball (0 : Domain n) 1).indicator (fun x=>hsNormSq (Du x)) := by
      funext x
      by_cases hx : x∈Metric.ball (0 : Domain n) 1
      · simp only [D₀,indicator_of_mem hx]
      · simp only [D₀,indicator_of_notMem hx,hsNormSq,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),Finset.sum_const_zero]
    rw [hPoint,setIntegral_indicator measurableSet_ball,inter_comm]
  change (∫x in Metric.ball a r,hsNormSq (Dext x))≤K*(∫x in Metric.ball (0 : Domain n) 1∩Metric.ball a r,hsNormSq (Du x)) at hEnergy
  rw [← hOriginalIntegral] at hEnergy
  have hM : (volume.real (Metric.ball a (r/2)))⁻¹*(∫x in Metric.ball a r,hsNormSq (Dext x))≤M := by
    exact (mul_le_mul_of_nonneg_left hEnergy (inv_nonneg.mpr ENNReal.toReal_nonneg)).trans_eq (by dsimp only [M];simp only [measureReal_def];ring)
  have hOriginalPoint (x : Domain n) : hsNormSq (D₀ x)≤hsNormSq (Dext x) := by
    by_cases hx : x∈Metric.ball (0 : Domain n) 1
    · have hxNorm : ‖x‖≤1 := (by simpa only [Metric.mem_ball,dist_zero_right] using hx : ‖x‖<1).le
      simp only [D₀,Dext,indicator_of_mem hx,if_pos hxNorm,le_refl]
    · simp only [D₀,indicator_of_notMem hx,hsNormSq,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),Finset.sum_const_zero]
      exact Finset.sum_nonneg fun _ _=>sq_nonneg _
  let ν := volume.restrict (Metric.ball a (r/2))
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hBound₀ : ∀ᵐx∂ν,hsNormSq (D₀ x)≤M := hBound.mono fun x hx=>(hOriginalPoint x).trans (hx.trans hM)
  have hD₀ (i : Fin n) : MemLp (fun x=>D₀ x i) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr (hu.2.2 i)
  have hMeas : AEStronglyMeasurable (fun x=>Real.sqrt (hsNormSq (D₀ x))) ν :=
    (memLp_sqrt_sum_norm_sq D₀ (fun i=>(hD₀ i).mono_measure Measure.restrict_le_self)).aestronglyMeasurable
  have hNormBound : ∀ᵐx∂ν,‖Real.sqrt (hsNormSq (D₀ x))‖≤Real.sqrt M := by
    filter_upwards [hBound₀] with x hx
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hx
  refine ⟨hBound₀,MemLp.of_bound hMeas (Real.sqrt M) hNormBound,?_⟩
  intro p hp
  have hLp : MemLp (fun x=>Real.sqrt (hsNormSq (D₀ x))) (ENNReal.ofReal p) ν := MemLp.of_bound hMeas (Real.sqrt M) hNormBound
  have hIntegral : Integrable (fun x=>(Real.sqrt (hsNormSq (D₀ x)))^p) ν := by
    simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using integrable_norm_rpow_of_memLp_real _ (by linarith only [hp] : 0≤p) hLp
  have hPower : ∀ᵐx∂ν,(Real.sqrt (hsNormSq (D₀ x)))^p≤(Real.sqrt M)^p := by
    filter_upwards [hNormBound] with x hx
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hx
    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) hx (by linarith only [hp])
  refine ⟨hLp,hIntegral,?_⟩
  simpa only [ν,integral_const,smul_eq_mul,measureReal_restrict_apply_univ] using
    integral_mono_ae hIntegral (integrable_const ((Real.sqrt M)^p)) hPower

end StationaryHarmonicMaps.Analysis

end
