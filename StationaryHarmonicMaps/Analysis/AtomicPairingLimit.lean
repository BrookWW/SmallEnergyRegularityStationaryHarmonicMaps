module

public import StationaryHarmonicMaps.Analysis.BoundedAtomicSeriesPairing
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Genuine limits of bounded atomic pairings

Original atom bounds, an actual summable coefficient family and actual
reconstruction identify each bounded pairing with its true scalar
series. Uniform bounds on the original atom pairings permit dominated
convergence of that series and give a genuine same-function limit.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual bounded approximants with uniformly controlled atom pairings have a genuine original-function pairing limit controlled by the original coefficient sum. -/
theorem atomic_pairing_limit_of_bounded_approximants {X I : Type*}
    [MeasurableSpace X] [Countable I]
    (μ : Measure X) (a : I → X → ℝ) (ha : ∀ i,Integrable (a i) μ)
    (haNorm : ∀ i,(∫ x,|a i x| ∂μ)≤1)
    (c : I → ℝ) (hc : Summable (fun i=>|c i|))
    (f : X → ℝ) (hRecon : f=ᵐ[μ](fun x=>∑' i,c i*a i x))
    (b : ℕ → X → ℝ) (hb : ∀ k,AEStronglyMeasurable (b k) μ)
    (M : ℕ → ℝ) (hM : ∀ k,0≤M k)
    (hBound : ∀ k,∀ᵐ x ∂μ,|b k x|≤M k)
    (B : ℝ) (hAtomPair : ∀ k i,|∫ x,a i x*b k x ∂μ|≤B)
    (l : I → ℝ)
    (hLimit : ∀ i,Tendsto (fun k=>∫ x,a i x*b k x ∂μ) atTop (𝓝 (l i))) :
    Summable (fun i=>c i*l i) ∧
      (∀ k,Integrable (fun x=>f x*b k x) μ) ∧
      Tendsto (fun k=>∫ x,f x*b k x ∂μ) atTop (𝓝 (∑' i,c i*l i)) ∧
      |∑' i,c i*l i|≤B*(∑' i,|c i|) := by
  have hLBound (i : I) : |l i|≤B :=
    le_of_tendsto (hLimit i).abs (Eventually.of_forall fun k=>hAtomPair k i)
  have hNormSum : Summable (fun i=>‖c i*l i‖) := by
    apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>?_) (hc.mul_right B)
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left (hLBound i) (abs_nonneg _)
  have hPair (k : ℕ) := bounded_atomic_series_pairing μ a ha haNorm c hc f (b k)
    hRecon (hb k) (M k) (hM k) (hBound k) B (hAtomPair k)
  have hSeriesLimit : Tendsto (fun k=>∑' i,c i*(∫ x,a i x*b k x ∂μ)) atTop
      (𝓝 (∑' i,c i*l i)) := by
    apply tendsto_tsum_of_dominated_convergence (hc.mul_right B)
      (fun i=>(hLimit i).const_mul (c i))
    exact Eventually.of_forall fun k i=>by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (hAtomPair k i) (abs_nonneg _)
  refine ⟨hNormSum.of_norm,fun k=>(hPair k).1,?_,?_⟩
  · exact hSeriesLimit.congr' (Eventually.of_forall fun k=>(hPair k).2.2.1.symm)
  · calc
      _ ≤ ∑' i,|c i*l i| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hNormSum
      _ ≤ ∑' i,|c i| *B := Summable.tsum_le_tsum
        (fun i=>by rw [abs_mul];exact mul_le_mul_of_nonneg_left (hLBound i) (abs_nonneg _))
        (by simpa only [Real.norm_eq_abs] using hNormSum) (hc.mul_right B)
      _ = _ := by rw [tsum_mul_right,mul_comm]

end StationaryHarmonicMaps.Analysis

end
