module

public import StationaryHarmonicMaps.Analysis.ZeroExtensionCriticalMorrey
public import StationaryHarmonicMaps.Analysis.ConvolutionCriticalMorrey
public import StationaryHarmonicMaps.Analysis.SkewConvolution
public import StationaryHarmonicMaps.Analysis.PlanarGradientApproximation

/-!
# Actual smooth skew approximations with complete critical control

The original ball coefficient field is encoded, genuinely zero-extended,
and convolved with the actual normalized scaled kernels. The same decoded
fields are globally smooth and skew at every point. Their complete global
critical bound has factor 2^(n-2), and their original encoded columns
converge strongly in L2 on the original ball. No derivative of the original
field or its zero extension is assumed.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual arbitrary-dimensional L2 skew fields in the complete critical class admit genuine smooth skew approximants with uniform complete bounds and original-column strong L2 convergence. -/
theorem exists_smooth_skew_critical_approximation_unitBall {n q : ℕ} (hn : 2 ≤ n)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀ T, R (E T) = T) (hER : ∀ z, E (R z) = z)
    (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q))
    (hA : ∀ i, MemLp (fun x => A x i) 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (hAskew : ∀ i, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), star (A x i) = -A x i)
    (K : ℝ) (hK : 0 ≤ K)
    (hCritical : criticalGradientMorreySquare (fun x i => E (A x i))
      (Metric.ball (0 : Domain n) 1) ≤ ENNReal.ofReal K) :
    ∃ Aseq : ℕ → Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
      (∀ j i, ContDiff ℝ ∞ (fun x => Aseq j x i) ∧ MemLp (fun x => Aseq j x i) 2 volume) ∧
      (∀ j x i, star (Aseq j x i) = -Aseq j x i) ∧
      (∀ j, criticalGradientMorreySquare (fun x i => E (Aseq j x i)) univ ≤
        ENNReal.ofReal ((2 : ℝ)^(n-2)*K)) ∧
      ∀ i, Tendsto (fun j => eLpNorm (fun x => E (Aseq j x i)-E (A x i)) 2
        (volume.restrict (Metric.ball (0 : Domain n) 1))) atTop (𝓝 0) := by
  let Ω := ballDomain (0 : Domain n) 1
  let μ := volume.restrict Ω.val
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let F := fun x i => E (A x i)
  have hF (i : Fin n) : MemLp (fun x => F x i) 2 μ :=
    E.lipschitz.comp_memLp (map_zero E) (hA i)
  let f := fun x i => zeroExtensionOn Ω (fun y => F y i) x
  obtain ⟨hf,hfCritical⟩ := zeroExtension_unitBall_criticalMorrey_bound hn F hF K hK hCritical
  have hfI (i : Fin n) : Integrable (fun x => f x i) volume :=
    zeroExtensionOn_integrable Ω (fun x => F x i) ((hF i).integrable (by norm_num))
  have hfSkew (i : Fin n) : ∀ᵐ x ∂volume, star (R (f x i)) = -R (f x i) := by
    have hS : ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : Domain n) 1 → star (A x i) = -A x i :=
      (ae_restrict_iff' measurableSet_ball).mp (hAskew i)
    filter_upwards [hS] with x hx
    by_cases hxb : x ∈ Metric.ball (0 : Domain n) 1
    · simp only [f,zeroExtensionOn,Ω,ballDomain,indicator_of_mem hxb,F,hRE,hx hxb]
    · simp only [f,zeroExtensionOn,Ω,ballDomain,indicator_of_notMem hxb,map_zero]
      rw [neg_zero]
      change ContinuousLinearMap.adjoint (0 : Ambient q →L[ℝ] Ambient q) = 0
      exact map_zero ContinuousLinearMap.adjoint
  let ε : ℕ → PositiveRadius := fun j => ⟨1/((j : ℝ)+1),by positivity⟩
  have hε : Tendsto (fun j => (ε j).val) atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  let M := fun j x i => ∫ z, scaledMollifierKernel n (ε j) z • f (x-z) i
  let Aseq := fun j x i => R (M j x i)
  have hM (j : ℕ) (i : Fin n) : ContDiff ℝ ∞ (fun x => M j x i) ∧
      MemLp (fun x => M j x i) 2 volume :=
    scaledMollifier_convolution_contDiff_memLp (fun x => f x i) (hf i) (ε j)
  have hMCritical (j : ℕ) : criticalGradientMorreySquare (M j) univ ≤
      ENNReal.ofReal ((2 : ℝ)^(n-2)*K) :=
    criticalGradientMorreySquare_scaledMollifier_convolution_le f hf (ε j) hfCritical
  have hMSkew (j : ℕ) (x : Domain n) (i : Fin n) : star (R (M j x i)) = -R (M j x i) :=
    decoded_kernelConvolution_skew E R hRE (fun x => f x i) (hfI i) (hfSkew i)
      (scaledMollifierKernel n (ε j)) (scaledMollifierKernel_contDiff n (ε j)).continuous
      (scaledMollifierKernel_hasCompactSupport n (ε j)) x
  refine ⟨Aseq,?_,hMSkew,?_,?_⟩
  · intro j i
    exact ⟨R.contDiff.comp (hM j i).1,R.lipschitz.comp_memLp (map_zero R) (hM j i).2⟩
  · intro j
    simpa only [Aseq,hER] using hMCritical j
  · intro i
    have hGlobal := (tendsto_eLpNorm_mollification_centeredDilation_sub
      (fun x => f x i) (hfI i) (hf i) (0 : Domain n) (fun _j : ℕ => (1 : ℝ))
      tendsto_const_nhds (fun _j => one_ne_zero) ε hε).2
    have hMConv : Tendsto (fun j => eLpNorm (fun x => M j x i-f x i) 2 volume) atTop (𝓝 0) := by
      simpa only [zero_add,one_smul,sub_zero,M] using hGlobal
    have hEq (j : ℕ) : (fun x => E (Aseq j x i)-E (A x i)) =ᵐ[μ]
        (fun x => M j x i-f x i) := by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hxb : x ∈ Metric.ball (0 : Domain n) 1 := hx
      simp only [Aseq,hER,f,zeroExtensionOn,Ω,ballDomain,indicator_of_mem hxb,F]
    have hLe (j : ℕ) : eLpNorm (fun x => E (Aseq j x i)-E (A x i)) 2 μ ≤
        eLpNorm (fun x => M j x i-f x i) 2 volume := by
      rw [eLpNorm_congr_ae (hEq j)]
      exact eLpNorm_mono_measure _ Measure.restrict_le_self
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hMConv (fun _j => bot_le) hLe

end StationaryHarmonicMaps.Analysis

end
