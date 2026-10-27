module

public import StationaryHarmonicMaps.Analysis.VectorDistributionTests
public import StationaryHarmonicMaps.Analysis.PlanarGradientApproximation

/-!
# Smooth approximation of harmonic solenoidal fields on the whole ball

The original weak divergence and coefficient Laplacian identities pass to
one actual mollification. An inward dilation gives a smooth field satisfying
both identities on a neighborhood of the closed unit ball. The same fields
converge strongly in L2 on the whole original ball.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

private theorem solenoidal_scalar_test {n q : ℕ}
    (F : Domain n → Gradient n q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hDiv : HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) F (fun _ => 0))
    (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ ball (0 : Domain n) 1) :
    (∀ i, IntegrableOn (fun x => fderiv ℝ η x (EuclideanSpace.single i 1) • F x i)
      (ball (0 : Domain n) 1) volume) ∧
    (∫ x in ball (0 : Domain n) 1,
      ∑ i : Fin n, fderiv ℝ η x (EuclideanSpace.single i 1) • F x i) = 0 := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let d := fun (i : Fin n) (x : Domain n) => fderiv ℝ η x (EuclideanSpace.single i 1)
  have hInt (i : Fin n) : Integrable (fun x => d i x • F x i) μ :=
    ((show MemLp (fun x => F x i) 2 μ from hF i).integrable (by norm_num)).smul_of_top_right
      (((hη.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
        (hcη.fderiv_apply ℝ _) μ)
  refine ⟨hInt, ?_⟩
  ext j
  let v : Ambient q := EuclideanSpace.single j 1
  let ψ := fun x => η x • v
  have hψ : ContDiff ℝ ∞ ψ := hη.smul contDiff_const
  have hcψ : HasCompactSupport ψ := hcη.smul_right
  have hsψ : tsupport ψ ⊆ (ballDomain (0 : Domain n) 1).val :=
    (tsupport_smul_subset_left η (fun _ => v)).trans hsη
  have hDψ (x : Domain n) (i : Fin n) :
      fderiv ℝ ψ x (EuclideanSpace.single i 1) = d i x • v :=
    congrArg (fun L : Domain n →L[ℝ] Ambient q => L (EuclideanSpace.single i 1))
      ((hη.differentiable (by simp) x).hasFDerivAt.smul_const v).fderiv
  have hPoint (x : Domain n) :
      (∑ i : Fin n, inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        (∑ i : Fin n, d i x • F x i) j := by
    change _ = (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) j) (∑ i : Fin n, d i x • F x i)
    rw [map_sum]
    simp only [hDψ, real_inner_smul_right, v, EuclideanSpace.inner_single_right,
      conj_trivial, one_mul, map_smul, PiLp.proj_apply, smul_eq_mul]
  have H := (hDiv.2 ψ hψ hcψ hsψ).2.2
  rw [integral_congr_ae (Eventually.of_forall hPoint)] at H
  have Hcoord := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).integral_comp_comm
    (integrable_finsetSum Finset.univ (fun i _ => hInt i))
  change (∫ x in ball (0 : Domain n) 1, ∑ i : Fin n, d i x • F x i) j = 0
  exact Hcoord.symm.trans (by
    simpa only [PiLp.proj_apply, μ, ballDomain, inner_zero_left, integral_zero, neg_zero] using H)

private theorem kernelConvolution_solenoidal {n q : ℕ}
    (F : Domain n → Gradient n q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hDiv : HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) F (fun _ => 0))
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (x : Domain n) (hSample : ∀ y ∈ tsupport χ, x-y ∈ ball (0 : Domain n) 1) :
    (∑ i : Fin n, fderiv ℝ (fun y => ∫ z, χ z •
      zeroExtensionOn (ballDomain (0 : Domain n) 1) (fun w => F w i) (y-z)) x
        (EuclideanSpace.single i 1)) = 0 := by
  let Ω := ballDomain (0 : Domain n) 1
  letI : IsFiniteMeasure (volume.restrict Ω.val) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hI (i : Fin n) : IntegrableOn (fun y => F y i) Ω.val volume :=
    (show MemLp (fun y => F y i) 2 (volume.restrict Ω.val) from hF i).integrable (by norm_num)
  obtain ⟨hTestInt, hTest⟩ := solenoidal_scalar_test F hF hDiv (translatedKernelTest χ x)
    (translatedKernelTest_contDiff hχ x) (translatedKernelTest_hasCompactSupport hcχ x)
    (translatedKernelTest_tsupport_subset Ω x hSample)
  rw [integral_finsetSum _ (fun i _ => hTestInt i)] at hTest
  have hRef (z : Domain n) (i : Fin n) :
      fderiv ℝ (translatedKernelTest χ x) z (EuclideanSpace.single i 1) =
        -(fderiv ℝ χ (x-z) (EuclideanSpace.single i 1)) :=
    translatedKernelTest_coordinateDerivative hχ x z i
  simp only [hRef, neg_smul, integral_neg,
    Finset.sum_neg_distrib, neg_eq_zero] at hTest
  have hDeriv (i : Fin n) :
      fderiv ℝ (fun y => ∫ z, χ z • zeroExtensionOn Ω (fun w => F w i) (y-z)) x
        (EuclideanSpace.single i 1) =
        ∫ z in Ω.val, fderiv ℝ χ (x-z) (EuclideanSpace.single i 1) • F z i := by
    rw [HolderToCK.kernelConvolution_fderiv Ω _ (hI i) hχ hcχ]
    simp only [zeroExtensionOn, ← indicator_smul]
    exact integral_indicator Ω.property.measurableSet
  change (∑ i : Fin n, fderiv ℝ (fun y => ∫ z, χ z • zeroExtensionOn Ω (fun w => F w i) (y-z)) x
    (EuclideanSpace.single i 1)) = 0
  simp_rw [hDeriv]
  exact hTest

private theorem coordinateDerivative_comp_smul {n q : ℕ}
    (f : Domain n → Ambient q) (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : Domain n) (i : Fin n) :
    fderiv ℝ (fun y => f (t • y)) x (EuclideanSpace.single i 1) =
      t • fderiv ℝ f (t • x) (EuclideanSpace.single i 1) := by
  have hAff : HasFDerivAt (fun y : Domain n => t • y)
      (t • ContinuousLinearMap.id ℝ (Domain n)) x := (hasFDerivAt_id x).const_smul t
  have H := ((hf.differentiable (by simp) (t • x)).hasFDerivAt.comp x hAff).fderiv
  change (fderiv ℝ (f ∘ (fun y : Domain n => t • y)) x) (EuclideanSpace.single i 1) = _
  rw [H]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul]

/-- The actual vector Laplacian of a smooth dilation has the exact square scaling factor. -/
theorem smooth_vector_laplacian_comp_smul {n q : ℕ}
    (f : Domain n → Ambient q) (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : Domain n) :
    Laplacian.laplacian (fun y => f (t • y)) x = t^2 • Laplacian.laplacian f (t • x) := by
  have hComp : ContDiff ℝ ∞ (fun y => f (t • y)) := hf.comp (contDiff_id.const_smul t)
  let d := fun (i : Fin n) (y : Domain n) => fderiv ℝ f y (EuclideanSpace.single i 1)
  have hd (i : Fin n) : ContDiff ℝ ∞ (d i) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hFirst (i : Fin n) : (fun y => fderiv ℝ (fun z => f (t • z)) y
      (EuclideanSpace.single i 1)) = fun y => t • d i (t • y) :=
    funext fun y => coordinateDerivative_comp_smul f hf t y i
  rw [laplacian_eq_sum_second_coordinate _ hComp, laplacian_eq_sum_second_coordinate _ hf,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hdi : DifferentiableAt ℝ (fun y : Domain n => d i (t • y)) x :=
    ((hd i).comp (contDiff_id.const_smul t)).differentiable (by simp) x
  rw [hFirst i]
  change (fderiv ℝ (t • (fun y : Domain n => d i (t • y))) x) (EuclideanSpace.single i 1) = _
  rw [fderiv_const_smul hdi t]
  change t • fderiv ℝ (fun y => d i (t • y)) x (EuclideanSpace.single i 1) = _
  rw [coordinateDerivative_comp_smul (d i) (hd i), smul_smul, pow_two]

/-- Actual raw L2 harmonic solenoidal data have one smooth harmonic solenoidal approximation on neighborhoods of the closed unit ball, converging on the whole original ball. -/
theorem exists_solenoidal_harmonic_L2_approximation_unitBall {n q : ℕ}
    (F : Domain n → Gradient n q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hDiv : HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) F (fun _ => 0))
    (hHarm : ∀ (i : Fin n) (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Domain n) 1 →
      (∫ x in ball (0 : Domain n) 1, inner ℝ (F x i) (Laplacian.laplacian ψ x)) = 0) :
    ∃ (G : ℕ → Domain n → Gradient n q) (ρ : ℕ → ℝ),
      (∀ k, 1 < ρ k) ∧
      (∀ k i, ContDiff ℝ ∞ (fun x => G k x i)) ∧
      (∀ k x, x ∈ ball (0 : Domain n) (ρ k) →
        (∑ i : Fin n, fderiv ℝ (fun y => G k y i) x (EuclideanSpace.single i 1)) = 0) ∧
      (∀ k i x, x ∈ ball (0 : Domain n) (ρ k) →
        Laplacian.laplacian (fun y => G k y i) x = 0) ∧
      ∀ i, Tendsto (fun k => eLpNorm (fun x => G k x i-F x i) 2
        (volume.restrict (ball (0 : Domain n) 1))) atTop (𝓝 0) := by
  let Ω := ballDomain (0 : Domain n) 1
  let μ := volume.restrict Ω.val
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hI (i : Fin n) : IntegrableOn (fun x => F x i) Ω.val volume :=
    (show MemLp (fun x => F x i) 2 μ from hF i).integrable (by norm_num)
  have hScalar (i : Fin n) (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η)
      (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ Ω.val) :
      (∫ x in Ω.val, Laplacian.laplacian η x • F x i) = 0 :=
    (scalar_vector_laplacian_of_vector_tests Ω (fun x => F x i) (hI i)
      (hHarm i) η hη hcη hsη).2
  let u (k : ℕ) : ℝ := (1/2 : ℝ)*(1/((k : ℝ)+1))
  have hupos (k : ℕ) : 0 < u k := by dsimp only [u]; positivity
  have hule (k : ℕ) : u k ≤ (1/2 : ℝ) := by
    have H := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1)
      (le_add_of_nonneg_left (Nat.cast_nonneg k) : (1 : ℝ)≤(k : ℝ)+1)
    have HH := mul_le_mul_of_nonneg_left H (by norm_num : (0 : ℝ)≤1/2)
    simpa only [u, one_div_one, mul_one] using HH
  have hu : Tendsto u atTop (𝓝 (0 : ℝ)) := by
    simpa only [u, mul_zero] using
      (tendsto_const_nhds (x := (1/2 : ℝ))).mul tendsto_one_div_add_atTop_nhds_zero_nat
  let t (k : ℕ) : ℝ := 1-u k
  have htpos (k : ℕ) : 0 < t k := by dsimp only [t]; linarith only [hule k]
  have htlt (k : ℕ) : t k < 1 := by dsimp only [t]; linarith only [hupos k]
  have ht : Tendsto t atTop (𝓝 (1 : ℝ)) := by
    simpa only [t, sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hu
  let ε (k : ℕ) : PositiveRadius := ⟨u k, hupos k⟩
  have hε : Tendsto (fun k => (ε k).val) atTop (𝓝 (0 : ℝ)) := hu
  let ρ (k : ℕ) : ℝ := (1+t k)/(2*t k)
  have hρ (k : ℕ) : 1 < ρ k := by
    apply (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ)<2) (htpos k))).mpr
    linarith only [htlt k]
  have hmargin (k : ℕ) : t k*ρ k+(ε k).val/2=1 := by
    dsimp only [ρ, ε]
    calc
      _ = (1+t k)/2+u k/2 := by field_simp [(htpos k).ne']
      _ = 1 := by dsimp only [t]; ring
  let m (k : ℕ) (x : Domain n) (i : Fin n) :=
    ∫ z, scaledMollifierKernel n (ε k) z • zeroExtensionOn Ω (fun y => F y i) (x-z)
  let G (k : ℕ) (x : Domain n) (i : Fin n) := m k (t k • x) i
  have hm (k : ℕ) (i : Fin n) : ContDiff ℝ ∞ (fun x => m k x i) :=
    kernelConvolution_contDiff Ω (fun y => F y i) (hI i)
      (scaledMollifierKernel_contDiff n (ε k)) (scaledMollifierKernel_hasCompactSupport n (ε k))
  have hG (k : ℕ) (i : Fin n) : ContDiff ℝ ∞ (fun x => G k x i) :=
    (hm k i).comp (contDiff_id.const_smul (t k))
  have hSample (k : ℕ) (x : Domain n) (hx : x ∈ ball (0 : Domain n) (ρ k)) :
      ∀ y ∈ tsupport (scaledMollifierKernel n (ε k)), t k • x-y ∈ Ω.val := by
    apply scaledMollifierKernel_sampling_ball (ε k) (0 : Domain n) _ 1
    have H := mul_lt_mul_of_pos_left (show ‖x‖ < ρ k by simpa only [mem_ball, dist_zero_right] using hx)
      (htpos k)
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (htpos k).le]
    linarith only [H, hmargin k]
  refine ⟨G, ρ, hρ, hG, ?_, ?_, ?_⟩
  · intro k x hx
    have H := kernelConvolution_solenoidal F hF hDiv (scaledMollifierKernel_contDiff n (ε k))
      (scaledMollifierKernel_hasCompactSupport n (ε k)) (t k • x) (hSample k x hx)
    change (∑ i : Fin n, fderiv ℝ (fun y => m k y i) (t k • x)
      (EuclideanSpace.single i 1)) = 0 at H
    have hDG (i : Fin n) : fderiv ℝ (fun y => G k y i) x (EuclideanSpace.single i 1) =
        t k • fderiv ℝ (fun y => m k y i) (t k • x) (EuclideanSpace.single i 1) :=
      coordinateDerivative_comp_smul (fun y => m k y i) (hm k i) (t k) x i
    simp only [hDG, ← Finset.smul_sum, H, smul_zero]
  · intro k i x hx
    have H := distribution_harmonic_kernelConvolution Ω (fun y => F y i) (hI i) (hScalar i)
      (scaledMollifierKernel_contDiff n (ε k)) (scaledMollifierKernel_hasCompactSupport n (ε k))
      (t k • x) (hSample k x hx)
    change Laplacian.laplacian (fun y => m k (t k • y) i) x = 0
    rw [smooth_vector_laplacian_comp_smul (fun y => m k y i) (hm k i), H, smul_zero]
  · intro i
    let f := zeroExtensionOn Ω (fun x => F x i)
    have hf : Integrable f volume := zeroExtensionOn_integrable Ω (fun x => F x i) (hI i)
    have hf₂ : MemLp f 2 volume := (memLp_indicator_iff_restrict Ω.property.measurableSet).mpr (hF i)
    have H := (tendsto_eLpNorm_mollification_centeredDilation_sub f hf hf₂ (0 : Domain n)
      t ht (fun k => (htpos k).ne') ε hε).2
    simp only [sub_zero, zero_add] at H
    have heq (k : ℕ) : (fun x => G k x i-F x i) =ᵐ[μ] (fun x => G k x i-f x) := by
      filter_upwards [ae_restrict_mem Ω.property.measurableSet] with x hx
      simp only [f, zeroExtensionOn, indicator_of_mem hx]
    have hle (k : ℕ) : eLpNorm (fun x => G k x i-F x i) 2 μ ≤
        eLpNorm (fun x => G k x i-f x) 2 volume := by
      rw [eLpNorm_congr_ae (heq k)]
      exact eLpNorm_mono_measure _ Measure.restrict_le_self
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds H (fun _ => bot_le) hle

end StationaryHarmonicMaps.Analysis

end
