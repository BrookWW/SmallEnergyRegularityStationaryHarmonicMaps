module

public import StationaryHarmonicMaps.Analysis.CurlFreeGradientApproximation
public import StationaryHarmonicMaps.Analysis.CurlFreeConvolution
public import HarmonicMaps.Analysis.InteriorSobolevApproximation
public import HarmonicMaps.Analysis.L2AffineContinuity
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Actual L² convergence of contracted smooth convolutions

The original fixed-kernel approximation and the true Jacobian formula for
centered dilations give strong L² convergence of the same contracted
convolutions. The original field is assumed only integrable and L²;
no weak gradient or Sobolev zero extension is used.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The same smooth mollifications contracted by actual near-identity dilations converge in genuine global L². -/
theorem tendsto_eLpNorm_mollification_centeredDilation_sub {n q : ℕ}
    (f : Domain n → Ambient q) (hf : Integrable f volume) (hf₂ : MemLp f 2 volume)
    (a : Domain n) (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 1)) (htne : ∀ k, t k ≠ 0)
    (ε : ℕ → PositiveRadius) (hε : Tendsto (fun k => (ε k).val) atTop (𝓝 (0 : ℝ))) :
    (∀ k, MemLp (fun x => ∫ z, scaledMollifierKernel n (ε k) z •
      f (a+t k • (x-a)-z)) 2 volume) ∧
    Tendsto (fun k => eLpNorm (fun x => (∫ z, scaledMollifierKernel n (ε k) z •
      f (a+t k • (x-a)-z))-f x) 2 volume) atTop (𝓝 0) := by
  let m (k : ℕ) (x : Domain n) := ∫ z, scaledMollifierKernel n (ε k) z • f (x-z)
  have hm (k : ℕ) : MemLp (m k) 2 volume := by
    have H := fixedKernelAverage_memLp hf hf₂ (ε k)
    simpa only [fixedKernelAverage_eq_scaledConvolution] using H
  have heFilter : Tendsto ε atTop (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) :=
    tendsto_comap_iff.mpr hε
  have hmconv : Tendsto (fun k => eLpNorm (m k-f) 2 volume) atTop (𝓝 0) := by
    have H := (tendsto_eLpNorm_fixedKernelAverage_sub hf hf₂).comp heFilter
    have Hraw : Tendsto (fun k => eLpNorm (fun x => m k x-f x) 2 volume) atTop (𝓝 0) := by
      simpa only [Function.comp_def,m,fixedKernelAverage_eq_scaledConvolution] using H
    apply Hraw.congr
    intro k
    congr 1
  let c (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (abs (s^n)⁻¹) ^ (1/2 : ℝ)
  have hc : Tendsto (fun k => c (t k)) atTop (𝓝 1) := by
    have hi : ContinuousAt (fun s : ℝ => (s^n)⁻¹) 1 :=
      (continuousAt_id.pow n).inv₀ (by simp)
    have H := (ENNReal.continuous_rpow_const (y := (1/2 : ℝ))).continuousAt.comp
      (ENNReal.continuous_ofReal.continuousAt.comp hi.abs)
    have H₁ : Tendsto c (𝓝 1) (𝓝 1) := by
      simpa only [ContinuousAt,Function.comp_def,c,one_pow,inv_one,abs_one,
        ENNReal.ofReal_one,ENNReal.one_rpow] using H
    exact H₁.comp ht
  have hfirst : Tendsto (fun k => c (t k)*eLpNorm (m k-f) 2 volume) atTop (𝓝 0) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul hc (Or.inl (by norm_num)) hmconv (Or.inr (by norm_num))
  have hsecond := (tendsto_eLpNorm_centeredDilation_sub hf₂ a).comp ht
  have hsum : Tendsto (fun k => c (t k)*eLpNorm (m k-f) 2 volume+
      eLpNorm (fun x => f (a+t k • (x-a))-f x) 2 volume) atTop (𝓝 0) := by
    simpa only [Function.comp_def,add_zero] using hfirst.add hsecond
  refine ⟨fun k => memLp_comp_centeredDilation (hm k) a (htne k),?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
  intro k
  have hfirstLp := memLp_comp_centeredDilation ((hm k).sub hf₂) a (htne k)
  have hsecondLp := (memLp_comp_centeredDilation hf₂ a (htne k)).sub hf₂
  have heq : (fun x => m k (a+t k • (x-a))-f x) =
      (fun x => (m k-f) (a+t k • (x-a)))+(fun x => f (a+t k • (x-a))-f x) := by
    funext x
    simp only [Pi.add_apply,Pi.sub_apply]
    abel
  change eLpNorm (fun x => m k (a+t k • (x-a))-f x) 2 volume ≤ _
  rw [heq]
  exact (eLpNorm_add_le hfirstLp.aestronglyMeasurable hsecondLp.aestronglyMeasurable (by norm_num)).trans_eq
    (congrArg (fun z => z+eLpNorm (fun x => f (a+t k • (x-a))-f x) 2 volume)
      (eLpNorm_comp_centeredDilation ((hm k).sub hf₂) a (htne k)))

/-- Original planar L² weak curl-free data admit actual native smooth-gradient approximations on the same whole ball. -/
theorem exists_planar_curl_free_gradient_L2_approximation {q : ℕ}
    (a : Domain 2) (R : ℝ) (hR : 0<R) (F : Domain 2 → Gradient 2 q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a R)))
    (hcurl : HolderToCK.WeakPoissonOn (ballDomain a R)
      (fun x i => -(![-F x 1,F x 0] : Gradient 2 q) i) (fun _ => 0)) :
    ∃ (φ : ℕ → Domain 2 → Ambient q) (Dφ : ℕ → Domain 2 → Gradient 2 q),
      (∀ k, MemW12 (ballDomain a R) (φ k) (Dφ k)) ∧
      (∀ k i, ContDiff ℝ ∞ (fun x => Dφ k x i)) ∧
      (∀ k, ∃ s : ℝ, R<s ∧ ContDiffOn ℝ ∞ (φ k) (Metric.ball a s)) ∧
      ∀ i : Fin 2, Tendsto (fun k => eLpNorm
        (fun x => Dφ k x i-F x i) 2 (volume.restrict (Metric.ball a R))) atTop (𝓝 0) := by
  classical
  let Ω := ballDomain a R
  let μ := volume.restrict Ω.val
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hI (i : Fin 2) : IntegrableOn (fun x => F x i) Ω.val volume :=
    (show MemLp (fun x => F x i) 2 μ from hF i).integrable (by norm_num)
  let u (k : ℕ) : ℝ := (1/2 : ℝ)*(1/((k : ℝ)+1))
  have hupos (k : ℕ) : 0<u k := by dsimp only [u]; positivity
  have hule (k : ℕ) : u k ≤ (1/2 : ℝ) := by
    have H := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1)
      (le_add_of_nonneg_left (Nat.cast_nonneg k) : (1 : ℝ)≤(k : ℝ)+1)
    have HH := mul_le_mul_of_nonneg_left H (by norm_num : (0 : ℝ)≤1/2)
    simpa only [u,one_div_one,mul_one] using HH
  have hu : Tendsto u atTop (𝓝 (0 : ℝ)) := by
    simpa only [u,mul_zero] using
      (tendsto_const_nhds (x := (1/2 : ℝ))).mul tendsto_one_div_add_atTop_nhds_zero_nat
  let t (k : ℕ) : ℝ := 1-u k
  have htpos (k : ℕ) : 0<t k := by dsimp only [t];linarith only [hule k]
  have htlt (k : ℕ) : t k<1 := by dsimp only [t];linarith only [hupos k]
  have ht : Tendsto t atTop (𝓝 (1 : ℝ)) := by
    simpa only [t,sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hu
  let ε (k : ℕ) : PositiveRadius := ⟨R*u k,mul_pos hR (hupos k)⟩
  have hε : Tendsto (fun k => (ε k).val) atTop (𝓝 (0 : ℝ)) := by
    simpa only [ε,mul_zero] using (tendsto_const_nhds (x := R)).mul hu
  let ρ (k : ℕ) : ℝ := R*(1+t k)/(2*t k)
  have hρ (k : ℕ) : R<ρ k := by
    apply (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ)<2) (htpos k))).mpr
    have H := mul_lt_mul_of_pos_left (show 2*t k<1+t k by linarith only [htlt k]) hR
    nlinarith only [H]
  have hmargin (k : ℕ) : t k*ρ k+(ε k).val/2=R := by
    dsimp only [ρ,ε]
    calc
      _ = R*(1+t k)/2+R*u k/2 := by field_simp [(htpos k).ne']
      _ = R := by dsimp only [t];ring
  let m (k : ℕ) (x : Domain 2) (i : Fin 2) :=
    ∫ z, scaledMollifierKernel 2 (ε k) z • zeroExtensionOn Ω (fun y => F y i) (x-z)
  let G (k : ℕ) (x : Domain 2) (i : Fin 2) := m k (a+t k • (x-a)) i
  have hm (k : ℕ) (i : Fin 2) : ContDiff ℝ ∞ (fun x => m k x i) :=
    kernelConvolution_contDiff Ω (fun y => F y i) (hI i)
      (scaledMollifierKernel_contDiff 2 (ε k)) (scaledMollifierKernel_hasCompactSupport 2 (ε k))
  have hAffine (k : ℕ) : ContDiff ℝ ∞ (fun x : Domain 2 => a+t k • (x-a)) := by
    let A : Domain 2 →L[ℝ] Domain 2 := (t k) • ContinuousLinearMap.id ℝ (Domain 2)
    have H : ContDiff ℝ ∞ ((fun _ : Domain 2 => a)+(A ∘ (fun x : Domain 2 => x-a))) :=
      (contDiff_const (c := a)).add (A.contDiff.comp (contDiff_id.sub (contDiff_const (c := a))))
    convert H using 1
    funext x
    rfl
  have hG (k : ℕ) (i : Fin 2) : ContDiff ℝ ∞ (fun x => G k x i) :=
    (hm k i).comp (hAffine k)
  have hDG (k : ℕ) (x : Domain 2) (i j : Fin 2) :
      fderiv ℝ (fun y => G k y j) x (EuclideanSpace.single i 1) =
        t k • fderiv ℝ (fun y => m k y j) (a+t k • (x-a)) (EuclideanSpace.single i 1) := by
    have hAff : HasFDerivAt (fun y : Domain 2 => a+t k • (y-a))
        ((t k) • ContinuousLinearMap.id ℝ (Domain 2)) x :=
      (((hasFDerivAt_id (𝕜 := ℝ) x).sub_const a).const_smul (t k)).const_add a
    have H := ((hm k j).differentiable (by simp) (a+t k • (x-a))).hasFDerivAt.comp x hAff
    change fderiv ℝ ((fun y => m k y j) ∘ (fun y => a+t k • (y-a))) x
      (EuclideanSpace.single i 1) = _
    rw [H.fderiv]
    simp only [ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul]
  have hGcurl (k : ℕ) (x : Domain 2) (hx : x ∈ Metric.ball a (ρ k)) (i j : Fin 2) :
      fderiv ℝ (fun y => G k y j) x (EuclideanSpace.single i 1) =
        fderiv ℝ (fun y => G k y i) x (EuclideanSpace.single j 1) := by
    have hdist : dist (a+t k • (x-a)) a=t k*dist x a := by
      simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (htpos k)]
    have hSample : ∀ y ∈ tsupport (scaledMollifierKernel 2 (ε k)),
        a+t k • (x-a)-y ∈ Metric.ball a R := by
      apply scaledMollifierKernel_sampling_ball (ε k) a _ R
      have H := mul_lt_mul_of_pos_left (show dist x a<ρ k from hx) (htpos k)
      rw [hdist]
      linarith only [H,hmargin k]
    have Hcurl := (planar_kernelConvolution_curl_free a R F hF hcurl
      (scaledMollifierKernel_contDiff 2 (ε k)) (scaledMollifierKernel_hasCompactSupport 2 (ε k))
      (a+t k • (x-a)) hSample).2
    rw [hDG,hDG]
    fin_cases i <;> fin_cases j
    · rfl
    · exact congrArg (fun z : Ambient q => t k • z) Hcurl
    · exact congrArg (fun z : Ambient q => t k • z) Hcurl.symm
    · rfl
  have hPrimitive (k : ℕ) := exists_primitive_of_smooth_curl_free_ball a (ρ k) (G k) (hG k) (hGcurl k)
  choose φ hφSmooth hφColumns hφNative using hPrimitive
  refine ⟨φ,G,(fun k => hφNative k R (hρ k)),hG,
    (fun k => ⟨ρ k,hρ k,hφSmooth k⟩),?_⟩
  intro i
  let f := zeroExtensionOn Ω (fun x => F x i)
  have hf : Integrable f volume := zeroExtensionOn_integrable Ω (fun x => F x i) (hI i)
  have hf₂ : MemLp f 2 volume := (memLp_indicator_iff_restrict Ω.property.measurableSet).mpr (hF i)
  have H := (tendsto_eLpNorm_mollification_centeredDilation_sub f hf hf₂ a t ht
    (fun k => (htpos k).ne') ε hε).2
  have heq (k : ℕ) : (fun x => G k x i-F x i) =ᵐ[μ] (fun x => G k x i-f x) := by
    filter_upwards [ae_restrict_mem Ω.property.measurableSet] with x hx
    simp only [f,zeroExtensionOn,indicator_of_mem hx]
  have hle (k : ℕ) : eLpNorm (fun x => G k x i-F x i) 2 μ ≤
      eLpNorm (fun x => G k x i-f x) 2 volume := by
    rw [eLpNorm_congr_ae (heq k)]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds H (fun _ => bot_le) hle

end StationaryHarmonicMaps.Analysis

end
