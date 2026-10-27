module

public import StationaryHarmonicMaps.Analysis.WeakHarmonicDistribution
public import StationaryHarmonicMaps.Analysis.DistributionHarmonicRepresentative
public import StationaryHarmonicMaps.Analysis.HarmonicLpDecay
public import StationaryHarmonicMaps.Analysis.LpL1Bound
public import HarmonicMaps.Analysis.HarmonicDerivative
public import HarmonicMaps.Analysis.SobolevAECongruence
public import HarmonicMaps.SobolevRestriction
public import HolderToCK.Analysis.ClassicalWeakGradient

/-!
# Interior bounds for the same actual native harmonic gradient

The original graph and zero-forcing equation produce a distributional Weyl
representative. Weak-gradient uniqueness identifies its classical columns
with the same original Du almost everywhere. Harmonic derivative mean
bounds then give a genuine interior essential bound and every finite
exponent estimate for the original full Hilbert--Schmidt norm.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual native harmonic data produce a smooth representative with the same original gradient and its genuine interior L-infinity and all finite-exponent reverse-Holder bounds. -/
theorem exists_smooth_harmonic_representative_with_original_gradient_ball {n q : ℕ}
    (hn : 2≤n) (a : Domain n) (R : PositiveRadius)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12 (ballDomain a R.val) u Du)
    (hEq : HolderToCK.WeakPoissonOn (ballDomain a R.val) Du (fun _=>(0:Ambient q))) :
    ∃ U : Domain n → Ambient q,
      ContDiffOn ℝ ∞ U (Metric.ball a R.val) ∧
      U =ᵐ[volume.restrict (Metric.ball a R.val)] u ∧
      (∀x ∈ Metric.ball a R.val,Laplacian.laplacian U x=0) ∧
      Du =ᵐ[volume.restrict (Metric.ball a R.val)]
        (fun x i=>fderiv ℝ U x (EuclideanSpace.single i 1)) ∧
      (∀i,MemLp (fun x=>fderiv ℝ U x (EuclideanSpace.single i 1)) 2
        (volume.restrict (Metric.ball a R.val))) ∧
      let K := (volume.real (Metric.ball a (R.val/2)))⁻¹*
        (∫x in Metric.ball a R.val,hsNormSq (Du x))
      (∀x ∈ Metric.ball a (R.val/2),hsNormSq
        (fun i=>fderiv ℝ U x (EuclideanSpace.single i 1))≤K) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball a (R.val/2)),hsNormSq (Du x)≤K) ∧
      MemLp (fun x=>Real.sqrt (hsNormSq (Du x))) ⊤
        (volume.restrict (Metric.ball a (R.val/2))) ∧
      ∀p : ℝ,1≤p →
        MemLp (fun x=>Real.sqrt (hsNormSq (Du x))) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball a (R.val/2))) ∧
        IntegrableOn (fun x=>(Real.sqrt (hsNormSq (Du x)))^p) (Metric.ball a (R.val/2)) volume ∧
        (∫x in Metric.ball a (R.val/2),(Real.sqrt (hsNormSq (Du x)))^p)≤
          volume.real (Metric.ball a (R.val/2))*(Real.sqrt K)^p := by
  let Ω := ballDomain a R.val
  let μ := volume.restrict (Metric.ball a R.val)
  let ν := volume.restrict (Metric.ball a (R.val/2))
  have hDist (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hsη : tsupport η⊆Metric.ball a R.val) :
      (∫x in Metric.ball a R.val,Laplacian.laplacian η x • u x)=0 :=
    (distribution_laplacian_zero_of_weak_harmonic_graph Ω u Du hu.1 hEq η hη hcη hsη).2
  obtain ⟨U,hU,hAE,hLap⟩ := memLp_two_distribution_harmonic_smooth_representative_ball
    hn a R.val u hu.2.1 hDist
  have hULocal : MemW12Loc Ω U (fun x i=>fderiv ℝ U x (EuclideanSpace.single i 1)) :=
    HolderToCK.memW12Loc_of_contDiffOn_one Ω (hU.of_le (by simp))
  have hGrad : Du =ᵐ[μ] (fun x i=>fderiv ℝ U x (EuclideanSpace.single i 1)) :=
    hu.1.ae_eq_of_ae_eq_map hULocal.1 hAE.symm
  have hDG (i : Fin n) : MemLp (fun x=>fderiv ℝ U x (EuclideanSpace.single i 1)) 2 μ :=
    MemLp.ae_eq (hGrad.mono fun _ hx=>congrFun hx i) (hu.2.2 i)
  have hDGsq (i : Fin n) : Integrable (fun x=>‖fderiv ℝ U x (EuclideanSpace.single i 1)‖^2) μ :=
    (hDG i).integrable_norm_pow (by decide : (2:ℕ)≠0)
  let K := (volume.real (Metric.ball a (R.val/2)))⁻¹*(∫x,hsNormSq (Du x) ∂μ)
  have hK : 0≤K := mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    (integral_nonneg fun x=>hsNormSq_nonneg (Du x))
  have hHalf : Metric.ball a (R.val/2)⊆Metric.ball a R.val :=
    Metric.ball_subset_ball (by linarith only [R.property])
  have hPoint (x : Domain n) (hx : x∈Metric.ball a (R.val/2)) :
      hsNormSq (fun i=>fderiv ℝ U x (EuclideanSpace.single i 1))≤K := by
    have hCol (i : Fin n) : ‖fderiv ℝ U x (EuclideanSpace.single i 1)‖^2 ≤
        (volume.real (Metric.ball (0:Domain n) (R.val/2)))⁻¹*
          (∫y,‖fderiv ℝ U y (EuclideanSpace.single i 1)‖^2 ∂μ) := by
      obtain ⟨hSmooth,hHarm⟩ := harmonic_fderiv_column (Metric.ball a R.val) Metric.isOpen_ball U hU hLap i
      have H := harmonic_norm_rpow_le_half_ball_integral hn (by norm_num : (1:ℝ)≤2) a R
        (fun y=>fderiv ℝ U y (EuclideanSpace.single i 1)) hSmooth hHarm
        (by simpa only [Real.rpow_two,μ,IntegrableOn] using hDGsq i) hx
      simpa only [Real.rpow_two] using H
    have hEnergy : (∫y,hsNormSq (fun i=>fderiv ℝ U y (EuclideanSpace.single i 1)) ∂μ)=
        ∫y,hsNormSq (Du y) ∂μ := integral_congr_ae
      (hGrad.mono fun _ hx=>congrArg hsNormSq hx.symm)
    have hMass : volume.real (Metric.ball (0:Domain n) (R.val/2))=
        volume.real (Metric.ball a (R.val/2)) := by
      simp only [measureReal_def,Measure.addHaar_ball_center volume]
    calc
      _ ≤ ∑i : Fin n,(volume.real (Metric.ball (0:Domain n) (R.val/2)))⁻¹*
          (∫y,‖fderiv ℝ U y (EuclideanSpace.single i 1)‖^2 ∂μ) := Finset.sum_le_sum (fun i _=>hCol i)
      _ = (volume.real (Metric.ball (0:Domain n) (R.val/2)))⁻¹*
          (∫y,hsNormSq (fun i=>fderiv ℝ U y (EuclideanSpace.single i 1)) ∂μ) := by
        change (∑i : Fin n,(volume.real (Metric.ball (0:Domain n) (R.val/2)))⁻¹*
          (∫y,‖fderiv ℝ U y (EuclideanSpace.single i 1)‖^2 ∂μ))=
          (volume.real (Metric.ball (0:Domain n) (R.val/2)))⁻¹*
            (∫y,∑i : Fin n,‖fderiv ℝ U y (EuclideanSpace.single i 1)‖^2 ∂μ)
        rw [integral_finsetSum _ (fun i _=>hDGsq i),Finset.mul_sum]
      _ = K := by rw [hEnergy,hMass]
  have hAEHalf := ae_restrict_of_ae_restrict_of_subset hHalf hGrad
  have hBound : ∀ᵐ x ∂ν,hsNormSq (Du x)≤K := by
    filter_upwards [hAEHalf,ae_restrict_mem measurableSet_ball] with x hx hxB
    rw [hx]
    exact hPoint x hxB
  have hNormBound : ∀ᵐ x ∂ν,‖Real.sqrt (hsNormSq (Du x))‖≤Real.sqrt K := by
    filter_upwards [hBound] with x hx
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt hx
  have hSqrtMeas : AEStronglyMeasurable (fun x=>Real.sqrt (hsNormSq (Du x))) ν :=
    (memLp_sqrt_sum_norm_sq Du (fun i=>(hu.2.2 i).mono_measure (Measure.restrict_mono_set volume hHalf))).aestronglyMeasurable
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hLpTop : MemLp (fun x=>Real.sqrt (hsNormSq (Du x))) ⊤ ν :=
    MemLp.of_bound hSqrtMeas (Real.sqrt K) hNormBound
  refine ⟨U,hU,hAE,hLap,hGrad,hDG,hPoint,hBound,hLpTop,?_⟩
  intro p hp
  have hLp : MemLp (fun x=>Real.sqrt (hsNormSq (Du x))) (ENNReal.ofReal p) ν :=
    MemLp.of_bound hSqrtMeas (Real.sqrt K) hNormBound
  have hI : Integrable (fun x=>(Real.sqrt (hsNormSq (Du x)))^p) ν := by
    have H := integrable_norm_rpow_of_memLp_real _ (by linarith only [hp] : 0≤p) hLp
    simpa only [Real.norm_of_nonneg (Real.sqrt_nonneg _)] using H
  refine ⟨hLp,hI,?_⟩
  have hPower : ∀ᵐ x ∂ν,(Real.sqrt (hsNormSq (Du x)))^p≤(Real.sqrt K)^p := by
    filter_upwards [hNormBound] with x hx
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hx
    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) hx (by linarith only [hp])
  have H := integral_mono_ae hI (integrable_const ((Real.sqrt K)^p)) hPower
  simpa only [ν,integral_const,smul_eq_mul,measureReal_restrict_apply_univ] using H

end StationaryHarmonicMaps.Analysis

end
