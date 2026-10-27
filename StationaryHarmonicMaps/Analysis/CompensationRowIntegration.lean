module

public import StationaryHarmonicMaps.Analysis.AbsolutelyIntegrableSeries

/-!
# Actual integral cancellation of each compensation row

The original high bad series is pointwise finite with a genuine
integrable absolute sum. Tonelli gives its true finite absolute
integral series. Multiplication by the original bounded low cutoff
preserves this estimate. Every original mass-normalized correction has
absolute integral equal to the absolute original numerator, so both
actual row series converge in L1 and their original integrals agree.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Original absolutely integrable high pieces, an actual bounded low cutoff and original positive high masses produce genuine row integrability and exact compensation of the original row integrals. -/
theorem integrable_compensation_row_and_integral_eq {X I : Type*} [MeasurableSpace X] [Countable I]
    (μ : Measure X) (F ψ : I → X → ℝ)
    (hF : ∀ j,Integrable (F j) μ) (hFinite : ∀ x,Function.HasFiniteSupport (fun j=>F j x))
    (hAbsI : Integrable (fun x=>∑' j,|F j x|) μ)
    (hψ : ∀ j,Integrable (ψ j) μ) (hNonneg : ∀ j x,0≤ψ j x)
    (hMass : ∀ j,0<(∫ x,ψ j x ∂μ))
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ μ) (hBound : ∀ x,|φ x|≤1) :
    let P := fun j x=>φ x*F j x
    let d := fun j=>(∫ x,P j x ∂μ)/(∫ x,ψ j x ∂μ)
    let Q := fun j x=>d j*ψ j x
    (∀ j,Integrable (P j) μ ∧ Integrable (Q j) μ) ∧
      Integrable (fun x=>∑' j,|P j x|) μ ∧ Integrable (fun x=>∑' j,P j x) μ ∧
      Integrable (fun x=>∑' j,|Q j x|) μ ∧ Integrable (fun x=>∑' j,Q j x) μ ∧
      (∫ x,(∑' j,P j x) ∂μ)=(∫ x,(∑' j,Q j x) ∂μ) := by
  intro P d Q
  have hFMeas (j : I) : AEMeasurable (fun x=>ENNReal.ofReal |F j x|) μ :=
    (hF j).abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hAbsFinite (x : X) : Function.HasFiniteSupport (fun j=>|F j x|) := (hFinite x).subset (by
    intro j hj
    by_contra hn
    have H : F j x=0 := not_not.mp hn
    exact hj (by change |F j x|=0;rw [H,abs_zero]))
  have hRNonneg (x : X) : 0≤∑' j,|F j x| := tsum_nonneg (fun _=>abs_nonneg _)
  have hRFinite : (∫⁻ x,ENNReal.ofReal (∑' j,|F j x|) ∂μ)<∞ := by
    have H := hAbsI.hasFiniteIntegral
    change (∫⁻ x,‖∑' j,|F j x|‖ₑ ∂μ)<∞ at H
    simpa only [Real.enorm_eq_ofReal (hRNonneg _)] using H
  have hFIntegralSum : (∑' j,∫⁻ x,ENNReal.ofReal |F j x| ∂μ)<∞ := by
    rw [← lintegral_tsum hFMeas]
    have hEq (x : X) : (∑' j,ENNReal.ofReal |F j x|)=ENNReal.ofReal (∑' j,|F j x|) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun _=>abs_nonneg _) (summable_of_hasFiniteSupport (hAbsFinite x))).symm
    simp_rw [hEq]
    exact hRFinite
  have hPI (j : I) : Integrable (P j) μ := (hF j).bdd_mul hφ (Eventually.of_forall fun x=>by
    simpa only [Real.norm_eq_abs] using hBound x)
  have hPNorm (j : I) : (∫⁻ x,ENNReal.ofReal |P j x| ∂μ)≤∫⁻ x,ENNReal.ofReal |F j x| ∂μ := by
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    change |φ x*F j x|≤|F j x|
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hBound x) (abs_nonneg _)).trans_eq (one_mul _)
  have hPFinite : (∑' j,∫⁻ x,ENNReal.ofReal |P j x| ∂μ)<∞ :=
    (ENNReal.tsum_le_tsum hPNorm).trans_lt hFIntegralSum
  have hQI (j : I) : Integrable (Q j) μ := (hψ j).const_mul (d j)
  have hQIntegral (j : I) : (∫ x,Q j x ∂μ)=(∫ x,P j x ∂μ) := by
    rw [integral_const_mul]
    exact div_mul_cancel₀ _ (hMass j).ne'
  have hQNormEq (j : I) : (∫⁻ x,ENNReal.ofReal |Q j x| ∂μ)=ENNReal.ofReal |∫ x,P j x ∂μ| := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hQI j).abs (Eventually.of_forall fun _=>abs_nonneg _)]
    congr 1
    dsimp only [Q]
    simp_rw [abs_mul,abs_of_nonneg (hNonneg j _)]
    rw [integral_const_mul]
    dsimp only [d]
    rw [abs_div,abs_of_pos (hMass j)]
    exact div_mul_cancel₀ _ (hMass j).ne'
  have hQNorm (j : I) : (∫⁻ x,ENNReal.ofReal |Q j x| ∂μ)≤∫⁻ x,ENNReal.ofReal |P j x| ∂μ := by
    rw [hQNormEq]
    have H := ENNReal.ofReal_le_ofReal (show |∫ x,P j x ∂μ|≤∫ x,|P j x| ∂μ from by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (P j))
    rw [ofReal_integral_eq_lintegral_ofReal (hPI j).abs (Eventually.of_forall fun _=>abs_nonneg _)] at H
    exact H
  have hQFinite : (∑' j,∫⁻ x,ENNReal.ofReal |Q j x| ∂μ)<∞ :=
    (ENNReal.tsum_le_tsum hQNorm).trans_lt hPFinite
  obtain ⟨_hPAE,hPAbsI,hPSumI,hPInt⟩ := integrable_tsum_of_finite_lintegral_abs_sum μ P hPI hPFinite
  obtain ⟨_hQAE,hQAbsI,hQSumI,hQInt⟩ := integrable_tsum_of_finite_lintegral_abs_sum μ Q hQI hQFinite
  refine ⟨fun j=>⟨hPI j,hQI j⟩,hPAbsI,hPSumI,hQAbsI,hQSumI,?_⟩
  exact hPInt.trans ((tsum_congr fun j=>(hQIntegral j).symm).trans hQInt.symm)

end StationaryHarmonicMaps.Analysis

end
