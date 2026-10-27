module

public import StationaryHarmonicMaps.Analysis.GrandCalderonZygmund
public import StationaryHarmonicMaps.Analysis.GrandLevelIntegralLimits

/-!
# Genuine two-ended L1 limits of the original CZ good family

One good function is chosen from the actual reconstruction at every
positive level. Its genuine cap and tail estimates consume the proved
original grand-integral level limits. The same family converges to zero
in L1 at small levels and to the original function in L1 at large levels.
Extended grand values are never replaced by a real fallback.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem tendsto_integral_abs_of_lintegral_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (v : ℕ → X → ℝ) (hI : ∀ k,Integrable (v k) μ)
    (hT : Tendsto (fun k=>∫⁻ x,ENNReal.ofReal |v k x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k=>∫ x,|v k x| ∂μ) atTop (𝓝 (0 : ℝ)) := by
  have hReal (k : ℕ) : (∫⁻ x,ENNReal.ofReal |v k x| ∂μ).toReal=(∫ x,|v k x| ∂μ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hI k).abs (Eventually.of_forall fun _=>abs_nonneg _)]
    exact ENNReal.toReal_ofReal (integral_nonneg fun _=>abs_nonneg _)
  have H := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT
  change Tendsto (fun k=>(∫⁻ x,ENNReal.ofReal |v k x| ∂μ).toReal) atTop (𝓝 (0 : ℝ)) at H
  simpa only [hReal] using H

/-- Original finite literal grand data produce one actual good family, preserving the original integral and converging strongly in L1 at both ends of the positive level range. -/
theorem exists_grand_cz_good_family_L1_limits (n : ℕ) (hn : 0<n) :
    ∃ A : ℝ,0<A ∧ ∀ (f : Domain n → ℝ),Integrable f volume →
      let J := fun a => ⨆ r : PositiveRadius, ⨆ κ : Domain n → ℝ,
        ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
        ⨆ (_ : tsupport κ⊆Metric.ball a r.val),
        ⨆ (_ : ∀ x∈Metric.ball a r.val,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤r.val^(-(n : ℝ)-1)),
          ENNReal.ofReal |∫ x,κ x*f x|
      (∫⁻ x,J x)<(∞ : ℝ≥0∞) → ∃ G : PositiveRadius → Domain n → ℝ,
        (∀ L,Integrable (G L) volume ∧ (∫ x,G L x)=(∫ x,f x) ∧
          (∀ x,J x≤ENNReal.ofReal L.val → G L x=f x) ∧
          (∀ᵐ x ∂volume,ENNReal.ofReal |G L x|≤ENNReal.ofReal A*min (J x) (ENNReal.ofReal L.val)) ∧
          (∀ᵐ x ∂volume,ENNReal.ofReal |f x-G L x|≤ENNReal.ofReal (2*A)*
            ({y | ENNReal.ofReal L.val<J y}.indicator J x))) ∧
        (∀ t : ℕ → PositiveRadius,Tendsto (fun k=>(t k).val) atTop (𝓝 (0 : ℝ)) →
          Tendsto (fun k=>∫ x,|G (t k) x|) atTop (𝓝 (0 : ℝ))) ∧
        (∀ t : ℕ → PositiveRadius,Tendsto (fun k=>(t k).val) atTop atTop →
          Tendsto (fun k=>∫ x,|f x-G (t k) x|) atTop (𝓝 (0 : ℝ))) := by
  classical
  obtain ⟨A,hA,Hcz⟩ := exists_grand_calderon_zygmund_reconstruction n hn
  refine ⟨A,hA,?_⟩
  intro f hf J hJ
  have hExists (L : PositiveRadius) : ∃ g : Domain n → ℝ,Integrable g volume ∧
      (∫ x,g x)=(∫ x,f x) ∧ (∀ x,J x≤ENNReal.ofReal L.val → g x=f x) ∧
      (∀ᵐ x ∂volume,ENNReal.ofReal |g x|≤ENNReal.ofReal A*min (J x) (ENNReal.ofReal L.val)) ∧
      (∀ᵐ x ∂volume,ENNReal.ofReal |f x-g x|≤ENNReal.ofReal (2*A)*
        ({y | ENNReal.ofReal L.val<J y}.indicator J x)) := by
    obtain ⟨U,_hCount,θ,_hθ,_hFinite,_hBounds,_hPart,_hPieces,_hAbsI,_hSumI,_hSumZero,hgI,hgMean,
      _hInside,hOutside,_hRecon,hCap,hError⟩ := Hcz f hf hJ L.val L.property
    refine ⟨_,hgI,hgMean,?_,hCap,hError⟩
    intro x hx
    exact hOutside x (not_lt.mpr hx)
  choose G hGI hMean hOutside hCap hError using hExists
  obtain ⟨_hLS,hMeas⟩ := lowerSemicontinuous_measurable_smooth_grand_kernel f
  refine ⟨G,fun L=>⟨hGI L,hMean L,hOutside L,hCap L,hError L⟩,?_,?_⟩
  · intro t ht
    apply tendsto_integral_abs_of_lintegral_zero volume (fun k=>G (t k)) (fun k=>hGI (t k))
    have hLevel := tendsto_lintegral_min_ofReal_zero volume J hMeas hJ.ne (fun k=>(t k).val) ht
    have hUpper : Tendsto (fun k=>ENNReal.ofReal A*∫⁻ x,min (J x) (ENNReal.ofReal (t k).val)) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hLevel (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper (fun _=>zero_le)
    intro k
    exact (lintegral_mono_ae (hCap (t k))).trans_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
  · intro t ht
    apply tendsto_integral_abs_of_lintegral_zero volume (fun k x=>f x-G (t k) x) (fun k=>hf.sub (hGI (t k)))
    have hLevel := tendsto_lintegral_upper_level_tail_zero volume J hMeas hJ.ne (fun k=>(t k).val) ht
    have hUpper : Tendsto (fun k=>ENNReal.ofReal (2*A)*∫⁻ x,if ENNReal.ofReal (t k).val<J x then J x else 0)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hLevel (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper (fun _=>zero_le)
    intro k
    exact (lintegral_mono_ae (hError (t k))).trans_eq (by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp only [indicator_apply,mem_setOf_eq])

/-- The original integrable function with a finite literal smooth grand maximal integral has actual zero integral, produced from the true small-level L1 limit. -/
theorem integral_eq_zero_of_finite_smooth_grand_kernel (n : ℕ) (hn : 0<n)
    (f : Domain n → ℝ) (hf : Integrable f volume) :
    let J := fun a => ⨆ r : PositiveRadius, ⨆ κ : Domain n → ℝ,
      ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
      ⨆ (_ : tsupport κ⊆Metric.ball a r.val),
      ⨆ (_ : ∀ x∈Metric.ball a r.val,∀ i : Fin n,
        |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤r.val^(-(n : ℝ)-1)),
        ENNReal.ofReal |∫ x,κ x*f x|
    (∫⁻ x,J x)<(∞ : ℝ≥0∞) → (∫ x,f x)=0 := by
  intro J hJ
  obtain ⟨A,_hA,H⟩ := exists_grand_cz_good_family_L1_limits n hn
  obtain ⟨G,hG,hLow,_hHigh⟩ := H f hf hJ
  let t : ℕ → PositiveRadius := fun k=>⟨1/((k : ℝ)+1),by positivity⟩
  have ht : Tendsto (fun k=>(t k).val) atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hBound (k : ℕ) : |∫ x,f x|≤∫ x,|G (t k) x| := by
    rw [← (hG (t k)).2.1]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (G (t k))
  have hZero : |∫ x,f x|≤0 := ge_of_tendsto (hLow t ht) (Eventually.of_forall hBound)
  exact abs_eq_zero.mp (le_antisymm hZero (abs_nonneg _))

end StationaryHarmonicMaps.Analysis

end
