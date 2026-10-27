module

public import HarmonicMaps.Frozen.OuterVariation
public import HarmonicMaps.Analysis.SobolevMollificationGradient
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Function.L2Space
public import HarmonicMaps.Analysis.MollificationEnergy
public import HarmonicMaps.Analysis.UniformSmoothingBounds
public import HarmonicMaps.Analysis.FiniteEnergySobolev

public section
open MeasureTheory Filter Set
open scoped ContDiff Convolution Topology
namespace HarmonicMaps.Providers.UniformSmoothing
noncomputable section

private theorem laplacian_columns {n q : ℕ} (f : Domain n → Ambient q)
    (hf : ContDiff ℝ ∞ f) (x : Domain n) :
    Laplacian.laplacian f x = ∑ i : Fin n,
      fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) Set.univ :=
    hf.contDiffOn.fderiv_of_isOpen isOpen_univ (by simp)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hDf.contDiffAt (isOpen_univ.mem_nhds (Set.mem_univ x))).differentiableAt (by simp)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
    fderiv_clm_apply hdiff (differentiableAt_const _)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

private theorem kernelConvolution_fderiv {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (x v : Domain n) :
    fderiv ℝ (fun x => ∫ z, χ z • zeroExtensionOn Ω u (x - z)) x v =
      ∫ z, fderiv ℝ χ (x - z) v • zeroExtensionOn Ω u z := by
  let L : ℝ →L[ℝ] Ambient q →L[ℝ] Ambient q := ContinuousLinearMap.lsmul ℝ ℝ
  have hzero := (zeroExtensionOn_integrable Ω u hu).locallyIntegrable
  have hderiv := hcχ.hasFDerivAt_convolution_right L.flip hzero
    (hχ.of_le (by simp)) x
  rw [convolution_flip] at hderiv
  change fderiv ℝ (χ ⋆[L, volume] zeroExtensionOn Ω u) x v = _
  rw [hderiv.fderiv,
    convolution_precompR_apply L.flip hzero (hcχ.fderiv ℝ)
      (hχ.continuous_fderiv (by simp)) x v]
  rfl

private theorem mollification_laplacian_gradient {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    Laplacian.laplacian (zeroExtendedMollification u hu.integrable_unitBall h) x =
      ∑ i : Fin n, ∫ z in Metric.ball (0 : Domain n) 1,
        fderiv ℝ (scaledMollifierKernel n h) (x - z)
          (EuclideanSpace.single i 1) • Du z i := by
  rw [laplacian_columns _ (zeroExtendedMollification_contDiff u hu.integrable_unitBall h)]
  apply Finset.sum_congr rfl
  intro i _
  have hlocal : (fun z => fderiv ℝ (zeroExtendedMollification u hu.integrable_unitBall h) z
      (EuclideanSpace.single i 1)) =ᶠ[𝓝 x]
      (fun z => ∫ y, scaledMollifierKernel n h y •
        zeroExtensionOn (ballDomain (0 : Domain n) 1) (fun z => Du z i) (z - y)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact hu.1.kernelConvolution_coordinateDerivative hu.integrable_unitBall
      (scaledMollifierKernel_contDiff n h) (scaledMollifierKernel_hasCompactSupport n h)
      z (scaledMollifierKernel_sampling_unitBall h hh hz) i
  rw [hlocal.fderiv_eq, kernelConvolution_fderiv _ _ (hu.column_integrable_ball i)
    (scaledMollifierKernel_contDiff n h) (scaledMollifierKernel_hasCompactSupport n h)]
  simp only [zeroExtensionOn, ← indicator_smul]
  exact integral_indicator measurableSet_ball

private theorem mollification_laplacian_weakEquation {n q : ℕ}
    {u F : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (hF : IntegrableOn F (Metric.ball (0 : Domain n) 1))
    (hEq : ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball (0 : Domain n) 1 →
      (∫ z in Metric.ball (0 : Domain n) 1, ∑ i : Fin n,
        inner ℝ (Du z i) (fderiv ℝ ψ z (EuclideanSpace.single i 1))) =
        -(∫ z in Metric.ball (0 : Domain n) 1, inner ℝ (F z) (ψ z)))
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    Laplacian.laplacian (zeroExtendedMollification u hu.integrable_unitBall h) x =
      ∫ z in Metric.ball (0 : Domain n) 1,
        scaledMollifierKernel n h (x - z) • F z := by
  let χ := scaledMollifierKernel n h
  have hχ : ContDiff ℝ ∞ χ := scaledMollifierKernel_contDiff n h
  have hcχ : HasCompactSupport χ := scaledMollifierKernel_hasCompactSupport n h
  have hsample := scaledMollifierKernel_sampling_unitBall h hh hx
  have hI' : ∀ i : Fin n, IntegrableOn (fun z =>
      fderiv ℝ χ (x - z) (EuclideanSpace.single i 1) • Du z i)
      (Metric.ball (0 : Domain n) 1) := by
    intro i
    have hdc : Continuous (fun z => fderiv ℝ χ (x - z) (EuclideanSpace.single i 1)) :=
      ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).comp
        (continuous_const.sub continuous_id)
    have hcc : HasCompactSupport (fun z => fderiv ℝ χ (x - z) (EuclideanSpace.single i 1)) :=
      (hcχ.fderiv_apply ℝ (EuclideanSpace.single i 1)).comp_homeomorph (Homeomorph.subLeft x)
    exact (hu.column_integrable_ball i).smul_of_top_right
      (hdc.memLp_top_of_hasCompactSupport hcc _)
  have hsumI := integrable_finsetSum Finset.univ (fun i _ => hI' i)
  have hψ : ContDiff ℝ ∞ (translatedKernelTest χ x) := translatedKernelTest_contDiff hχ x
  have hcψ := translatedKernelTest_hasCompactSupport hcχ x
  have hsψ := translatedKernelTest_tsupport_subset (ballDomain (0 : Domain n) 1) x hsample
  have hFI : IntegrableOn (fun z => χ (x - z) • F z)
      (Metric.ball (0 : Domain n) 1) :=
    hF.smul_of_top_right (hψ.continuous.memLp_top_of_hasCompactSupport hcψ _)
  rw [mollification_laplacian_gradient hu h hh hx, ← integral_finsetSum _ (fun i _ => hI' i)]
  apply ext_inner_left ℝ
  intro v
  let ψ : Domain n → Ambient q := fun z => translatedKernelTest χ x z • v
  have hψv : ContDiff ℝ ∞ ψ := hψ.smul contDiff_const
  have hcψv : HasCompactSupport ψ := hcψ.smul_right
  have hsψv : tsupport ψ ⊆ Metric.ball (0 : Domain n) 1 :=
    (tsupport_smul_subset_left _ _).trans hsψ
  have hdψ : ∀ z i, fderiv ℝ ψ z (EuclideanSpace.single i 1) =
      -(fderiv ℝ χ (x - z) (EuclideanSpace.single i 1)) • v := by
    intro z i
    rw [fderiv_smul_const (hψ.differentiable (by simp)).differentiableAt v]
    simp only [ContinuousLinearMap.smulRight_apply]
    exact congrArg (fun a : ℝ => a • v) (translatedKernelTest_coordinateDerivative hχ x z i)
  have htest : ∀ z, (∑ i : Fin n,
      inner ℝ (Du z i) (fderiv ℝ ψ z (EuclideanSpace.single i 1))) =
      -inner ℝ v (∑ i : Fin n,
        fderiv ℝ χ (x - z) (EuclideanSpace.single i 1) • Du z i) := by
    intro z
    simp only [hdψ, inner_smul_right, inner_sum, inner_smul_right, neg_mul,
      Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm]
  have htestF : ∀ z, inner ℝ (F z) (ψ z) = inner ℝ v (χ (x - z) • F z) := by
    intro z
    simp only [ψ, translatedKernelTest, inner_smul_right, real_inner_comm]
  have heq := hEq ψ hψv hcψv hsψv
  simp_rw [htest, htestF] at heq
  rw [integral_neg, integral_inner hsumI v, integral_inner hFI v] at heq
  exact neg_injective heq

/-- The same source forcing term from the weak outer-variation equation commutes with
literal fixed-kernel smoothing on the whole proved interior neighborhood. -/
private theorem sourceMollification_laplacian (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
  let S : Set ℝ := {k | ∃ p : N.Carrier, ∃ hp : p.val ∈ tubularTube q N,
    k = ‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖}
  ∀ (n : ℕ) (hn : 2 ≤ n) (u : Domain n → Ambient q)
    (Du : Domain n → Gradient n q),
    MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
    TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
    IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du →
    dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ →
    ∃ F : Domain n → Ambient q,
      LocallyIntegrableOn F (Metric.ball (0 : Domain n) 1) volume ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
        ∃ hx : u x ∈ tubularTube q N,
          F x = ∑ i : Fin n,
            tubularProjectionSecondDerivative q N ⟨u x, hx⟩ (Du x i) (Du x i) ∧
          ‖F x‖ ≤ sSup S * hsNormSq (Du x)) ∧
      (∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
        HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball (0 : Domain n) 1 →
        IntegrableOn (fun x => ∑ i : Fin n,
          inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))
          (Metric.ball (0 : Domain n) 1) ∧
        IntegrableOn (fun x => inner ℝ (F x) (ψ x)) (Metric.ball (0 : Domain n) 1) ∧
        (∫ x in Metric.ball (0 : Domain n) 1, ∑ i : Fin n,
          inner ℝ (Du x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
          -(∫ x in Metric.ball (0 : Domain n) 1, inner ℝ (F x) (ψ x))) ∧
      IntegrableOn F (Metric.ball (0 : Domain n) 1) ∧
      ∀ (h : PositiveRadius), h.val ≤ 1 / 4 →
        ∀ x ∈ Metric.ball (0 : Domain n) (3 / 4),
          IntegrableOn (fun y => fixedMollifierKernel n y • F (x - h.val • y))
            (Metric.ball (0 : Domain n) 1) ∧
          Laplacian.laplacian (fun z : Domain n =>
            ∫ y in Metric.ball (0 : Domain n) 1,
              fixedMollifierKernel n y • u (z - h.val • y)) x =
            ∫ y in Metric.ball (0 : Domain n) 1,
              fixedMollifierKernel n y • F (x - h.val • y) := by
  intro S n hn u Du hu hN hmin hE
  obtain ⟨F, hFlocal, hFformula, hWeak⟩ :=
    outerVariation_weakEquation q N n hn (ballDomain (0 : Domain n) 1) u Du hu hN hmin
  have hW := hu.memW12_unitBall_of_finiteEnergy N hN hE
  have hbound : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      ‖F x‖ ≤ sSup S * hsNormSq (Du x) := by
    filter_upwards [hFformula] with x hx
    exact hx.choose_spec.2
  have hF : IntegrableOn F (Metric.ball (0 : Domain n) 1) :=
    (hW.integrable_hsNormSq.const_mul (sSup S)).mono' hFlocal.aestronglyMeasurable hbound
  refine ⟨F, hFlocal, hFformula, hWeak, hF, ?_⟩
  intro h hh x hx
  refine ⟨sourceMollification_integrableOn F hF h hh x hx, ?_⟩
  have hlocal : (fun z : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (z - h.val • y)) =ᶠ[𝓝 x]
      zeroExtendedMollification u hW.integrable_unitBall h := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact sourceMollification_eq_zeroExtended u hW.integrable_unitBall h hh z hz
  rw [(InnerProductSpace.laplacian_congr_nhds hlocal).eq_of_nhds]
  rw [mollification_laplacian_weakEquation hW hF (fun ψ hψ hcψ hsψ =>
    (hWeak ψ hψ hcψ hsψ).2.2) h hh hx]
  calc
    _ = ∫ z, scaledMollifierKernel n h (x - z) • unitBallZeroExtension F z := by
      simp only [unitBallZeroExtension, ← indicator_smul]
      exact (integral_indicator measurableSet_ball).symm
    _ = ∫ z, scaledMollifierKernel n h z • unitBallZeroExtension F (x - z) := by
      rw [← integral_sub_left_eq_self
        (fun z => scaledMollifierKernel n h z • unitBallZeroExtension F (x - z)) volume x]
      simp only [sub_sub_cancel]
    _ = ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • F (x - h.val • y) :=
      (sourceMollification_eq_zeroExtended F hF h hh x hx).symm


private theorem averageNorm_integrable {n q : ℕ} (F : Domain n → Ambient q)
    (hF : IntegrableOn F (Metric.ball (0 : Domain n) 1)) (h : PositiveRadius) :
    Integrable (fun x => ‖∫ y, fixedMollifierKernel n y •
      unitBallZeroExtension F (x - h.val • y)‖) volume := by
  have hzero := unitBallZeroExtension_integrable F hF
  have hJoint := weighted_shift_joint_integrable hzero.norm h
  have hm : AEStronglyMeasurable (fun x => ‖∫ y, fixedMollifierKernel n y •
      unitBallZeroExtension F (x - h.val • y)‖) volume := by
    simp_rw [fixedMollifierKernel_integral_zeroExtension_eq F hF h]
    exact (zeroExtendedMollification_contDiff F hF h).continuous.norm.aestronglyMeasurable
  apply hJoint.integral_prod_left.mono' hm
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    simpa only [norm_smul, Real.norm_of_nonneg (fixedMollifierKernel_nonneg n _)]
      using norm_integral_le_integral_norm (fun y => fixedMollifierKernel n y •
        unitBallZeroExtension F (x - h.val • y))

private theorem averageNorm_integral_le {n q : ℕ} (F : Domain n → Ambient q)
    (hF : IntegrableOn F (Metric.ball (0 : Domain n) 1)) (h : PositiveRadius) :
    (∫ x, ‖∫ y, fixedMollifierKernel n y •
      unitBallZeroExtension F (x - h.val • y)‖) ≤
      ∫ z in Metric.ball (0 : Domain n) 1, ‖F z‖ := by
  have hzero := unitBallZeroExtension_integrable F hF
  have hJoint := weighted_shift_joint_integrable hzero.norm h
  calc
    _ ≤ ∫ x, ∫ y, fixedMollifierKernel n y *
        ‖unitBallZeroExtension F (x - h.val • y)‖ := by
      apply integral_mono (averageNorm_integrable F hF h) hJoint.integral_prod_left
      intro x
      simpa only [norm_smul, Real.norm_of_nonneg (fixedMollifierKernel_nonneg n _)]
        using norm_integral_le_integral_norm (fun y => fixedMollifierKernel n y •
          unitBallZeroExtension F (x - h.val • y))
    _ = ∫ y, ∫ x, fixedMollifierKernel n y *
        ‖unitBallZeroExtension F (x - h.val • y)‖ := integral_integral_swap hJoint
    _ = ∫ y, fixedMollifierKernel n y * ∫ z, ‖unitBallZeroExtension F z‖ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        dsimp only
        rw [integral_const_mul,
          integral_sub_right_eq_self (fun z => ‖unitBallZeroExtension F z‖) (h.val • y)]
    _ = ∫ z, ‖unitBallZeroExtension F z‖ := by
      rw [integral_mul_const, fixedMollifierKernel_integral, one_mul]
    _ = ∫ z in Metric.ball (0 : Domain n) 1, ‖F z‖ := by
      have heq : (fun z => ‖unitBallZeroExtension F z‖) =
          (Metric.ball (0 : Domain n) 1).indicator (fun z => ‖F z‖) := by
        funext z
        by_cases hz : z ∈ Metric.ball (0 : Domain n) 1
        · simp only [unitBallZeroExtension, Set.indicator_of_mem hz]
        · simp only [unitBallZeroExtension, Set.indicator_of_notMem hz, norm_zero]
      rw [heq, integral_indicator measurableSet_ball]

private theorem sourceAverageNorm_energy_le {n q : ℕ} (F : Domain n → Ambient q)
    (hF : IntegrableOn F (Metric.ball (0 : Domain n) 1))
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    IntegrableOn (fun x => ‖∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • F (x - h.val • y)‖)
      (Metric.ball (0 : Domain n) (1 / 2)) ∧
    (∫ x in Metric.ball (0 : Domain n) (1 / 2),
      ‖∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • F (x - h.val • y)‖) ≤
      ∫ z in Metric.ball (0 : Domain n) 1, ‖F z‖ := by
  have heq : EqOn (fun x => ‖∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • F (x - h.val • y)‖)
      (fun x => ‖∫ y, fixedMollifierKernel n y •
        unitBallZeroExtension F (x - h.val • y)‖)
      (Metric.ball (0 : Domain n) (1 / 2)) := by
    intro x hx
    dsimp only
    have hx' := Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hx
    rw [sourceMollification_eq_zeroExtended F hF h hh x hx',
      fixedMollifierKernel_integral_zeroExtension_eq F hF h]
  refine ⟨((averageNorm_integrable F hF h).integrableOn).congr_fun heq.symm
    measurableSet_ball, ?_⟩
  calc
    _ = ∫ x in Metric.ball (0 : Domain n) (1 / 2), ‖∫ y,
        fixedMollifierKernel n y • unitBallZeroExtension F (x - h.val • y)‖ :=
      setIntegral_congr_fun measurableSet_ball heq
    _ ≤ ∫ x, ‖∫ y, fixedMollifierKernel n y •
        unitBallZeroExtension F (x - h.val • y)‖ :=
      setIntegral_le_integral (averageNorm_integrable F hF h)
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ _ := averageNorm_integral_le F hF h
private theorem sourceGradient_energy_le {n q : ℕ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    let m : Domain n → Ambient q := fun x => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (x - h.val • y)
    IntegrableOn (fun x => hsNormSq (fun i =>
      fderiv ℝ m x (EuclideanSpace.single i 1)))
      (Metric.ball (0 : Domain n) (1 / 2)) ∧
    (∫ x in Metric.ball (0 : Domain n) (1 / 2),
      hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1))) ≤
      (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
  dsimp only
  have heq : EqOn (fun x => hsNormSq (fun i =>
      fderiv ℝ (fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - h.val • y)) x (EuclideanSpace.single i 1)))
      (fun x => hsNormSq (fun i => ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • Du (x - h.val • y) i))
      (Metric.ball (0 : Domain n) (1 / 2)) := by
    intro x hx
    apply congrArg hsNormSq
    funext i
    exact hu.sourceMollification_coordinateDerivative h hh
      (Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hx) i
  refine ⟨(sourceMollifiedGradient_integrable_hsNormSq hu.2.2 h hh).congr_fun
    heq.symm measurableSet_ball, ?_⟩
  have hInput : IntegrableOn (fun x => hsNormSq (Du x))
      (Metric.ball (0 : Domain n) 1) := hu.integrable_hsNormSq
  rw [setIntegral_congr_fun measurableSet_ball heq, dirichletEnergy_toReal hInput]
  exact sourceMollifiedGradient_energy_le hu.2.2 h hh

private theorem sourceF_integrable_energy_le {n q : ℕ} {Du : Domain n → Gradient n q}
    (hDu : IntegrableOn (fun x => hsNormSq (Du x)) (Metric.ball (0 : Domain n) 1))
    (F : Domain n → Ambient q)
    (hF : LocallyIntegrableOn F (Metric.ball (0 : Domain n) 1) volume)
    (K : ℝ) (hbound : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      ‖F x‖ ≤ K * hsNormSq (Du x)) :
    IntegrableOn F (Metric.ball (0 : Domain n) 1) ∧
    (∫ x in Metric.ball (0 : Domain n) 1, ‖F x‖) ≤
      K * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
  have hi : IntegrableOn F (Metric.ball (0 : Domain n) 1) :=
    (hDu.const_mul K).mono' hF.aestronglyMeasurable hbound
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x in Metric.ball (0 : Domain n) 1, K * hsNormSq (Du x) :=
      integral_mono_ae hi.norm (hDu.const_mul K) hbound
    _ = K * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
      rw [integral_const_mul, dirichletEnergy_toReal hDu]


/-- All four source smoothing estimates for the same literal fixed-radius integral. -/
theorem result (n : ℕ) (hn : 2 ≤ n) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (q : ℕ) (N : CompactSmoothEmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
    MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
    TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
    IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du →
    dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ →
    let S : Set ℝ := {k | ∃ p : N.Carrier, ∃ hp : p.val ∈ tubularTube q N,
      k = ‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖}
    ∀ (h : PositiveRadius), h.val ≤ 1 / 4 →
    let m : Domain n → Ambient q := fun x =>
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - h.val • y)
    ContDiffOn ℝ ∞ m (Metric.ball (0 : Domain n) (3 / 4)) ∧
    (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2),
      Metric.infDist (m x) N.carrierSet ^ 2 ≤
        C₀ * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal ∧
      hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1)) ≤
        C₀ * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal *
          h.val ^ (-2 : ℤ)) ∧
    IntegrableOn (fun x => hsNormSq (fun i =>
      fderiv ℝ m x (EuclideanSpace.single i 1)))
      (Metric.ball (0 : Domain n) (1 / 2)) ∧
    (∫ x in Metric.ball (0 : Domain n) (1 / 2),
      hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1))) ≤
      (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal ∧
    IntegrableOn (fun x => ‖Laplacian.laplacian m x‖)
      (Metric.ball (0 : Domain n) (1 / 2)) ∧
    (∫ x in Metric.ball (0 : Domain n) (1 / 2), ‖Laplacian.laplacian m x‖) ≤
      sSup S * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
  obtain ⟨C₀, hC₀, hpoint⟩ := uniformSmoothing_distance_gradient n hn
  refine ⟨C₀, hC₀, ?_⟩
  intro q N u Du hu hN hmin hE S h hh m
  have hW := hu.memW12_unitBall_of_finiteEnergy N hN hE
  obtain ⟨F, hFlocal, hFformula, _, hF, hLap⟩ :=
    sourceMollification_laplacian q N n hn u Du hu hN hmin hE
  have hbound : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      ‖F x‖ ≤ sSup S * hsNormSq (Du x) := by
    filter_upwards [hFformula] with x hx
    exact hx.choose_spec.2
  have hInput : IntegrableOn (fun x => hsNormSq (Du x))
      (Metric.ball (0 : Domain n) 1) := hW.integrable_hsNormSq
  have hFEnergy := (sourceF_integrable_energy_le hInput F hFlocal (sSup S) hbound).2
  have hAverage := sourceAverageNorm_energy_le F hF h hh
  have hLapEq : EqOn (fun x => ‖Laplacian.laplacian m x‖)
      (fun x => ‖∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • F (x - h.val • y)‖)
      (Metric.ball (0 : Domain n) (1 / 2)) := by
    intro x hx
    exact congrArg norm (hLap h hh x
      (Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hx)).2
  have hGradient := sourceGradient_energy_le hW h hh
  refine ⟨sourceMollification_contDiffOn u hW.integrable_unitBall h hh,
    hpoint q N u Du hu hN hmin hE h hh, hGradient.1, hGradient.2,
    hAverage.1.congr_fun hLapEq.symm measurableSet_ball, ?_⟩
  calc
    _ = ∫ x in Metric.ball (0 : Domain n) (1 / 2),
        ‖∫ y in Metric.ball (0 : Domain n) 1,
          fixedMollifierKernel n y • F (x - h.val • y)‖ :=
      setIntegral_congr_fun measurableSet_ball hLapEq
    _ ≤ ∫ x in Metric.ball (0 : Domain n) 1, ‖F x‖ := hAverage.2
    _ ≤ _ := hFEnergy

end
end HarmonicMaps.Providers.UniformSmoothing
end
