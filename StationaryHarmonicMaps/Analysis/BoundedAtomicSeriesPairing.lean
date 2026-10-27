module

public import StationaryHarmonicMaps.Analysis.AbsolutelyIntegrableSeries

/-!
# Actual bounded pairings of an absolutely summable atomic series

The original L1 atom bounds and the original coefficient sum supply
genuine absolute integrability of the paired series. A bounded test
therefore pairs with the same original reconstructed function, and
the original atom pairing bounds control the actual integral.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace StationaryHarmonicMaps.Analysis

/-- A bounded test pairs with the actual original L1 atomic series, with a bound from the original atom pairings and coefficient sum. -/
theorem bounded_atomic_series_pairing {X I : Type*} [MeasurableSpace X] [Countable I]
    (μ : Measure X) (a : I → X → ℝ) (ha : ∀ i,Integrable (a i) μ)
    (haNorm : ∀ i,(∫ x,|a i x| ∂μ)≤1)
    (c : I → ℝ) (hc : Summable (fun i=>|c i|))
    (f b : X → ℝ) (hRecon : f=ᵐ[μ](fun x=>∑' i,c i*a i x))
    (hb : AEStronglyMeasurable b μ) (M : ℝ) (hM : 0≤M)
    (hBound : ∀ᵐ x ∂μ,|b x|≤M)
    (B : ℝ) (hAtomPair : ∀ i,|∫ x,a i x*b x ∂μ|≤B) :
    Integrable (fun x=>f x*b x) μ ∧
      Summable (fun i=>c i*(∫ x,a i x*b x ∂μ)) ∧
      (∫ x,f x*b x ∂μ)=∑' i,c i*(∫ x,a i x*b x ∂μ) ∧
      |∫ x,f x*b x ∂μ|≤B*(∑' i,|c i|) := by
  let F := fun i x=>c i*a i x*b x
  have hBnorm : ∀ᵐ x ∂μ,‖b x‖≤M := by simpa only [Real.norm_eq_abs] using hBound
  have hAB (i : I) : Integrable (fun x=>a i x*b x) μ := by
    convert (ha i).bdd_mul hb hBnorm using 1
    funext x
    exact mul_comm _ _
  have hFI (i : I) : Integrable (F i) μ := by
    simpa only [F,mul_assoc] using (hAB i).const_mul (c i)
  have hNorm (i : I) : (∫ x,|F i x| ∂μ)≤|c i| *M := by
    calc
      _ ≤ ∫ x,(|c i| *M)*|a i x| ∂μ := integral_mono_ae (hFI i).abs
        ((ha i).abs.const_mul _) (by
          filter_upwards [hBound] with x hx
          change |c i*a i x*b x|≤(|c i| *M)*|a i x|
          rw [abs_mul,abs_mul]
          nlinarith only [mul_le_mul_of_nonneg_left hx (mul_nonneg (abs_nonneg (c i)) (abs_nonneg (a i x)))])
      _ = (|c i| *M)*(∫ x,|a i x| ∂μ) := integral_const_mul _ _
      _ ≤ |c i| *M := mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) hM) (haNorm i)
  have hFinite : (∑' i,∫⁻ x,ENNReal.ofReal |F i x| ∂μ)<∞ := by
    calc
      _ ≤ ∑' i,ENNReal.ofReal (|c i| *M) := ENNReal.tsum_le_tsum fun i=>by
        rw [← ofReal_integral_eq_lintegral_ofReal (hFI i).abs
          (Eventually.of_forall fun _=>abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hNorm i)
      _ = ENNReal.ofReal (∑' i,|c i| *M) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i=>mul_nonneg (abs_nonneg _) hM) (hc.mul_right M)).symm
      _ < _ := ENNReal.ofReal_lt_top
  obtain ⟨_hAE,_hAbsI,hSumI,hInterchange⟩ :=
    integrable_tsum_of_finite_lintegral_abs_sum μ F hFI hFinite
  have hCA : ∀ᵐ x ∂μ,Summable (fun i=>c i*a i x) := by
    have hCAI (i : I) : Integrable (fun x=>c i*a i x) μ := (ha i).const_mul _
    have hCAFin : (∑' i,∫⁻ x,ENNReal.ofReal |c i*a i x| ∂μ)<∞ := by
      calc
        _ ≤ ∑' i,ENNReal.ofReal |c i| := ENNReal.tsum_le_tsum fun i=>by
          rw [← ofReal_integral_eq_lintegral_ofReal (hCAI i).abs
            (Eventually.of_forall fun _=>abs_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          simp_rw [abs_mul]
          rw [integral_const_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (haNorm i)
        _ = ENNReal.ofReal (∑' i,|c i|) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun i=>abs_nonneg _) hc).symm
        _ < _ := ENNReal.ofReal_lt_top
    exact (integrable_tsum_of_finite_lintegral_abs_sum μ _ hCAI hCAFin).1.mono fun _ h=>h.2
  have hEq : (fun x=>f x*b x)=ᵐ[μ](fun x=>∑' i,F i x) := by
    filter_upwards [hRecon,hCA] with x hx _hCAx
    rw [hx,tsum_mul_right]
  have hPairI : Integrable (fun x=>f x*b x) μ := hSumI.congr hEq.symm
  have hTermIntegral (i : I) : (∫ x,F i x ∂μ)=c i*(∫ x,a i x*b x ∂μ) := by
    simpa only [F,mul_assoc] using integral_const_mul (c i) (fun x=>a i x*b x)
  have hPairEq : (∫ x,f x*b x ∂μ)=∑' i,c i*(∫ x,a i x*b x ∂μ) := by
    rw [integral_congr_ae hEq,hInterchange]
    simp_rw [hTermIntegral]
  have hPairNorm : Summable (fun i=>‖c i*(∫ x,a i x*b x ∂μ)‖) := by
    apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>?_) (hc.mul_right B)
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left (hAtomPair i) (abs_nonneg _)
  refine ⟨hPairI,hPairNorm.of_norm,hPairEq,?_⟩
  rw [hPairEq]
  calc
    _ ≤ ∑' i,|c i*(∫ x,a i x*b x ∂μ)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hPairNorm
    _ ≤ ∑' i,|c i| *B := Summable.tsum_le_tsum
      (fun i=>by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hAtomPair i) (abs_nonneg _))
      (by simpa only [Real.norm_eq_abs] using hPairNorm) (hc.mul_right B)
    _ = B*(∑' i,|c i|) := by rw [tsum_mul_right,mul_comm]

end StationaryHarmonicMaps.Analysis

end
