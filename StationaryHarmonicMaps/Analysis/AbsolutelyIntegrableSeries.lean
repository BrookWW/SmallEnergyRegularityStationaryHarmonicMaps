module

public import StationaryHarmonicMaps.Analysis.PartitionCancellationSum
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Genuine convergence and integration of absolutely integrable series

The actual extended sum of the original absolute integrals gives a
finite integral of the original pointwise norm series by Tonelli.
Consequently the real original series is genuinely absolutely summable
almost everywhere, both original sums are integrable, and the original
integrals commute with the series.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The true finite sum of the original absolute integrals produces genuine AE convergence, integrability and integral interchange for the same original scalar series. -/
theorem integrable_tsum_of_finite_lintegral_abs_sum {X I : Type*} [MeasurableSpace X] [Countable I]
    (μ : Measure X) (F : I → X → ℝ) (hF : ∀ i,Integrable (F i) μ)
    (hFinite : (∑' i,∫⁻ x,ENNReal.ofReal |F i x| ∂μ)<∞) :
    (∀ᵐ x ∂μ,Summable (fun i=>|F i x|) ∧ Summable (fun i=>F i x)) ∧
      Integrable (fun x=>∑' i,|F i x|) μ ∧ Integrable (fun x=>∑' i,F i x) μ ∧
      (∫ x,(∑' i,F i x) ∂μ)=∑' i,∫ x,F i x ∂μ := by
  have hMeas (i : I) : AEMeasurable (fun x=>ENNReal.ofReal |F i x|) μ :=
    (hF i).abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hNormIntegral : (∫⁻ x,∑' i,ENNReal.ofReal |F i x| ∂μ)<∞ := by
    rw [lintegral_tsum hMeas]
    exact hFinite
  have hAE : ∀ᵐ x ∂μ,Summable (fun i=>|F i x|) ∧ Summable (fun i=>F i x) := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hMeas) hNormIntegral.ne] with x hx
    have hNorm : Summable (fun i=>‖F i x‖) := tsum_enorm_ne_top_iff_summable_norm.mp (by
      simpa only [Real.enorm_eq_ofReal_abs] using hx.ne)
    exact ⟨by simpa only [Real.norm_eq_abs] using hNorm,hNorm.of_norm⟩
  let R := fun x=>∑' i,|F i x|
  have hRMeas : AEStronglyMeasurable R μ :=
    (AEMeasurable.tsum (fun i=>(hF i).abs.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hRNonneg (x : X) : 0≤R x := tsum_nonneg (fun _=>abs_nonneg _)
  have hREq : (fun x=>ENNReal.ofReal (R x))=ᵐ[μ](fun x=>∑' i,ENNReal.ofReal |F i x|) := by
    filter_upwards [hAE] with x hx
    exact ENNReal.ofReal_tsum_of_nonneg (fun _=>abs_nonneg _) hx.1
  have hRI : Integrable R μ := by
    refine ⟨hRMeas,?_⟩
    change (∫⁻ x,‖R x‖ₑ ∂μ)<∞
    simp_rw [Real.enorm_eq_ofReal (hRNonneg _)]
    rw [lintegral_congr_ae hREq]
    exact hNormIntegral
  have hSumMeas : AEStronglyMeasurable (fun x=>∑' i,F i x) μ :=
    (AEMeasurable.tsum (fun i=>(hF i).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hSumI : Integrable (fun x=>∑' i,F i x) μ := hRI.mono' hSumMeas (by
    filter_upwards [hAE] with x hx
    have H := norm_tsum_le_tsum_norm (show Summable (fun i=>‖F i x‖) from by simpa only [Real.norm_eq_abs] using hx.1)
    simpa only [Real.norm_eq_abs] using H)
  refine ⟨hAE,hRI,hSumI,?_⟩
  apply integral_tsum (fun i=>(hF i).aestronglyMeasurable)
  simpa only [Real.enorm_eq_ofReal_abs] using hFinite.ne

end StationaryHarmonicMaps.Analysis

end
