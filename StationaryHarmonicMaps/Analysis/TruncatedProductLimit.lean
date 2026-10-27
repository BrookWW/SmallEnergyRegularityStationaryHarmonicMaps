module

public import StationaryHarmonicMaps.Analysis.MeanOscillationTruncation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual integral limits for symmetric truncation products

The literal truncations are bounded by the original value and eventually
equal it at each point. A genuine integrable original product therefore
dominates the same truncated products and supplies their true integral
limit on the original measure.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Genuine original product integrability gives the actual dominated limit of the same symmetric-truncation integrals. -/
theorem tendsto_integral_product_symmetric_truncation {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (a b : X → ℝ)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hab : Integrable (fun x=>a x*b x) μ) :
    (∀ k : ℕ,Integrable (fun x=>a x*min (k : ℝ) (max (-(k : ℝ)) (b x))) μ) ∧
      Tendsto (fun k : ℕ=>∫ x,a x*min (k : ℝ) (max (-(k : ℝ)) (b x)) ∂μ)
        atTop (𝓝 (∫ x,a x*b x ∂μ)) := by
  let F := fun (k : ℕ) (x : X)=>a x*min (k : ℝ) (max (-(k : ℝ)) (b x))
  have hMeas (k : ℕ) : AEStronglyMeasurable (F k) μ := ha.mul
    ((symmetric_truncation_lipschitz_bounds (k : ℝ) (Nat.cast_nonneg k)).1.continuous.comp_aestronglyMeasurable hb)
  have hBound (k : ℕ) (x : X) : ‖F k x‖≤|a x*b x| := by
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    exact mul_le_mul_of_nonneg_left
      ((symmetric_truncation_lipschitz_bounds (k : ℝ) (Nat.cast_nonneg k)).2 (b x)).2 (abs_nonneg _)
  have hI (k : ℕ) : Integrable (F k) μ := hab.abs.mono' (hMeas k) (Eventually.of_forall (hBound k))
  refine ⟨hI,?_⟩
  apply tendsto_integral_of_dominated_convergence (fun x=>|a x*b x|) hMeas hab.abs
    (fun k=>Eventually.of_forall (hBound k))
  exact Eventually.of_forall fun x=>tendsto_const_nhds.congr'
    ((eventually_symmetric_truncation_eq atTop (fun k : ℕ=>(k : ℝ))
      tendsto_natCast_atTop_atTop (b x)).mono fun k hk=>by
        change a x*b x=F k x
        dsimp only [F]
        rw [hk])

end StationaryHarmonicMaps.Analysis

end
