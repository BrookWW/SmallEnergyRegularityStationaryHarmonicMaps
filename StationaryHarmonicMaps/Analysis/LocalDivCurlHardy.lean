module

public import StationaryHarmonicMaps.Analysis.OneFormBallExtension
public import StationaryHarmonicMaps.Analysis.ZeroBoundaryZeroExtension
public import StationaryHarmonicMaps.Analysis.SmoothGrandMaximalMeasurability

/-!
# Actual local div--curl Hardy estimate

The original solenoidal field is extended by the genuine Kelvin producer,
and the original native W0 graph by literal zero. Their whole-space
contraction is the zero extension of the original scalar contraction.
The actual measurable grand kernel supremum therefore has finite L1
norm with the original bilinear energy bound. The factor sqrt(2) comes
from the proved Kelvin squared-energy estimate.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original ball-solenoidal L2 and genuine W0 data produce the same scalar zero-extension's actual measurable Hardy grand supremum and its bilinear L1 bound. -/
theorem exists_local_divcurl_measurable_grand_kernel_bound_explicit (n : ℕ) (hn : 2≤n) :
    ∃ K : ℝ,0<K ∧ K=(divcurlGrandKernelMajorant n:ℝ) ∧ ∀ (q : ℕ) (a : Domain n) (r : ℝ),0<r →
      ∀ (Z : Domain n → Gradient n q),
        (∀ i,MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball a r))) →
        HolderToCK.WeakPoissonOn (ballDomain a r) Z (fun _ => (0 : Ambient q)) →
        ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
          HasZeroBoundaryValues (ballDomain a r) w Dw →
          let f := (Metric.ball a r).indicator
            (fun x => ∑ i : Fin n,inner ℝ (Z x i) (Dw x i))
          let J := fun b => ⨆ s : PositiveRadius, ⨆ κ : Domain n → ℝ,
            ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
            ⨆ (_ : tsupport κ⊆Metric.ball b s.val),
            ⨆ (_ : ∀ x∈Metric.ball b s.val,∀ i : Fin n,
              |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤s.val^(-(n : ℝ)-1)),
              ENNReal.ofReal |∫ x,κ x*f x|
          Integrable f volume ∧ (∫ x,f x)=0 ∧
            LowerSemicontinuous J ∧ Measurable J ∧
            (∫⁻ b,J b)≤ENNReal.ofReal (K*Real.sqrt 2*
              Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Z x))*
              Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Dw x))) ∧
            (∫⁻ b,J b)<(∞ : ℝ≥0∞) ∧ (∀ᵐ b ∂volume,J b≠(∞ : ℝ≥0∞)) ∧
            Integrable (fun b => (J b).toReal) volume ∧
            (∫ b,(J b).toReal)≤K*Real.sqrt 2*
              Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Z x))*
              Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Dw x)) := by
  obtain ⟨K,hK,hKEq,H⟩ := exists_divcurl_measurable_grand_kernel_bound_explicit n hn
  refine ⟨K,hK,hKEq,?_⟩
  intro q a r hr Z hZ hdiv w Dw hw f J
  let B := Metric.ball a r
  let v : Domain n → Ambient q := B.indicator w
  let Dv : Domain n → Gradient n q := fun x i => B.indicator (fun y => Dw y i) x
  obtain ⟨G,hG,hInside,hEnergyG,hDivG⟩ := exists_solenoidal_oneForm_L2_extension_ball hn a r hr Z hZ hdiv
  obtain ⟨hv,_hMapEnergy,hGradEnergy⟩ := zeroBoundary_zeroExtension_univ (ballDomain a r) w Dw hw
  change (∫ x,hsNormSq (Dv x))=(∫ x in B,hsNormSq (Dw x)) at hGradEnergy
  have hvLoc : MemW12Loc (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv := hv.1.to_memW12Loc
  have hDv (i : Fin n) : MemLp (fun x => Dv x i) 2 volume := by
    have HH := hv.1.2.2 i
    change MemLp (fun x => Dv x i) 2 (volume.restrict univ) at HH
    simpa only [Measure.restrict_univ] using HH
  have hInside' : ∀ᵐ x ∂volume,x∈B → G x=Z x :=
    (ae_restrict_iff' measurableSet_ball).mp hInside
  have hScalar : (fun x => ∑ i : Fin n,inner ℝ (G x i) (Dv x i))=ᵐ[volume] f := by
    filter_upwards [hInside'] with x hx
    by_cases hxB : x∈B
    · simp only [Dv,indicator_of_mem hxB]
      change (∑ i : Fin n,inner ℝ (G x i) (Dw x i))=B.indicator
        (fun x => ∑ i : Fin n,inner ℝ (Z x i) (Dw x i)) x
      rw [indicator_of_mem hxB,hx hxB]
    · change (∑ i : Fin n,inner ℝ (G x i) (B.indicator (fun y => Dw y i) x))=
        B.indicator (fun x => ∑ i : Fin n,inner ℝ (Z x i) (Dw x i)) x
      simp only [indicator_of_notMem hxB,inner_zero_right,Finset.sum_const_zero]
  have hPair (κ : Domain n → ℝ) :
      (∫ x,κ x*(∑ i : Fin n,inner ℝ (G x i) (Dv x i)))=(∫ x,κ x*f x) :=
    integral_congr_ae (hScalar.mono fun x hx => congrArg (fun z => κ x*z) hx)
  obtain ⟨hLS,hMeas,hBound,hFinite,hAE⟩ := H q G hG hDivG v Dv hvLoc hDv
  have hGrand : (fun b => ⨆ s : PositiveRadius, ⨆ κ : Domain n → ℝ,
      ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
      ⨆ (_ : tsupport κ⊆Metric.ball b s.val),
      ⨆ (_ : ∀ x∈Metric.ball b s.val,∀ i : Fin n,
        |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤s.val^(-(n : ℝ)-1)),
        ENNReal.ofReal |∫ x,κ x*∑ i : Fin n,inner ℝ (G x i) (Dv x i)|)=J := by
    funext b
    simp only [J,hPair]
  rw [hGrand] at hLS hMeas hBound hFinite hAE
  have hEG : 0≤∫ x,hsNormSq (G x) := integral_nonneg fun x => hsNormSq_nonneg (G x)
  have hED : 0≤∫ x,hsNormSq (Dv x) := integral_nonneg fun x => hsNormSq_nonneg (Dv x)
  have hRoot : Real.sqrt (∫ x,hsNormSq (G x)) ≤
      Real.sqrt 2*Real.sqrt (∫ x in B,hsNormSq (Z x)) := by
    calc
      _ ≤ Real.sqrt (2*(∫ x in B,hsNormSq (Z x))) := Real.sqrt_le_sqrt hEnergyG
      _ = _ := Real.sqrt_mul (by norm_num : (0 : ℝ)≤2) _
  have hRHS : ENNReal.ofReal K *
      (ENNReal.ofReal (∫ x,hsNormSq (G x)))^((1 : ℝ)/2)*
      (ENNReal.ofReal (∫ x,hsNormSq (Dv x)))^((1 : ℝ)/2)=
      ENNReal.ofReal (K*Real.sqrt (∫ x,hsNormSq (G x))*Real.sqrt (∫ x,hsNormSq (Dv x))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hEG (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg hED (by norm_num),← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow,
      ← ENNReal.ofReal_mul hK.le,← ENNReal.ofReal_mul (mul_nonneg hK.le (Real.sqrt_nonneg _))]
  rw [hRHS] at hBound
  have hRealRHS : K*Real.sqrt (∫ x,hsNormSq (G x))*Real.sqrt (∫ x,hsNormSq (Dv x))≤
      K*Real.sqrt 2*Real.sqrt (∫ x in B,hsNormSq (Z x))*Real.sqrt (∫ x in B,hsNormSq (Dw x)) := by
    rw [hGradEnergy]
    have HH := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRoot hK.le) (Real.sqrt_nonneg (∫ x in B,hsNormSq (Dw x)))
    simpa only [mul_assoc] using HH
  have hFinal : (∫⁻ b,J b)≤ENNReal.ofReal (K*Real.sqrt 2*
      Real.sqrt (∫ x in B,hsNormSq (Z x))*Real.sqrt (∫ x in B,hsNormSq (Dw x))) :=
    hBound.trans (ENNReal.ofReal_le_ofReal hRealRHS)
  have hFData := divergence_free_zeroBoundary_test (ballDomain a r) Z hZ hdiv hw
  have hf : Integrable f volume := (integrable_indicator_iff measurableSet_ball).mpr hFData.1
  have hfZero : (∫ x,f x)=0 := by
    rw [integral_indicator measurableSet_ball]
    exact hFData.2
  have hInt : Integrable (fun b => (J b).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top hMeas.aemeasurable hFinite.ne
  refine ⟨hf,hfZero,hLS,hMeas,hFinal,hFinite,hAE,hInt,?_⟩
  rw [integral_toReal hMeas.aemeasurable (hAE.mono fun _ hx => lt_top_iff_ne_top.mpr hx)]
  have HH := ENNReal.toReal_mono ENNReal.ofReal_ne_top hFinal
  rw [ENNReal.toReal_ofReal] at HH
  · exact HH
  · exact mul_nonneg (mul_nonneg (mul_nonneg hK.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)

theorem exists_local_divcurl_measurable_grand_kernel_bound (n : ℕ) (hn : 2≤n) :
    ∃ K : ℝ,0<K ∧ ∀ (q : ℕ) (a : Domain n) (r : ℝ),0<r →
      ∀ (Z : Domain n → Gradient n q),
        (∀ i,MemLp (fun x => Z x i) 2 (volume.restrict (Metric.ball a r))) →
        HolderToCK.WeakPoissonOn (ballDomain a r) Z (fun _ => (0 : Ambient q)) →
        ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
          HasZeroBoundaryValues (ballDomain a r) w Dw →
          let f := (Metric.ball a r).indicator
            (fun x => ∑ i : Fin n,inner ℝ (Z x i) (Dw x i))
          let J := fun b => ⨆ s : PositiveRadius, ⨆ κ : Domain n → ℝ,
            ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
            ⨆ (_ : tsupport κ⊆Metric.ball b s.val),
            ⨆ (_ : ∀ x∈Metric.ball b s.val,∀ i : Fin n,
              |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤s.val^(-(n : ℝ)-1)),
              ENNReal.ofReal |∫ x,κ x*f x|
          Integrable f volume ∧ (∫ x,f x)=0 ∧
            LowerSemicontinuous J ∧ Measurable J ∧
            (∫⁻ b,J b)≤ENNReal.ofReal (K*Real.sqrt 2*
              Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Z x))*
              Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Dw x))) ∧
            (∫⁻ b,J b)<(∞ : ℝ≥0∞) ∧ (∀ᵐ b ∂volume,J b≠(∞ : ℝ≥0∞)) ∧
            Integrable (fun b => (J b).toReal) volume ∧
            (∫ b,(J b).toReal)≤K*Real.sqrt 2*
              Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Z x))*
              Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Dw x)) := by
  obtain ⟨K,hK,_hKEq,H⟩ := exists_local_divcurl_measurable_grand_kernel_bound_explicit n hn
  exact ⟨K,hK,H⟩

end StationaryHarmonicMaps.Analysis

end
