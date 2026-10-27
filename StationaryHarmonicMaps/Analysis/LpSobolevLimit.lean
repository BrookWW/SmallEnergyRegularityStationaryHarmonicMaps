module

public import StationaryHarmonicMaps.Analysis.L1SobolevLimit
public import StationaryHarmonicMaps.Analysis.LpL1Bound
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Lower norm-power integrals under actual L2 approximation

Finite-measure exponent comparison transfers the original L2 convergence
to every exponent between one and two. Continuity of the actual Lp norm
then gives convergence of the literal power integrals, including the
original centered representatives.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Actual L2 convergence on finite measure implies convergence at every smaller positive exponent. -/
theorem tendsto_eLpNorm_real_of_L2 {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} [IsFiniteMeasure μ] {f : ℕ → X → E} {u : X → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k-u) 2 μ) atTop (𝓝 0))
    {p : ℝ} (hp : 0 < p) (hp₂ : p ≤ 2) :
    Tendsto (fun k => eLpNorm (f k-u) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
  have hpower : 0 ≤ 1 / p - 1 / (2 : ℝ) :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hp hp₂)
  have hb := ENNReal.Tendsto.mul_const hconv
    (Or.inr (ENNReal.rpow_ne_top_of_nonneg hpower (measure_ne_top μ univ)))
  simp only [zero_mul] at hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => zero_le)
  intro k
  have H := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show ENNReal.ofReal p ≤ 2 by simpa using ENNReal.ofReal_le_ofReal hp₂)
    ((hf k).sub hu).aestronglyMeasurable
  simpa only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofNat] using H

/-- The literal real norm-power integral is continuous under the original L2 approximation. -/
theorem tendsto_integral_norm_rpow_of_L2 {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℕ → X → E} {u : X → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k-u) 2 μ) atTop (𝓝 0))
    {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    Tendsto (fun k => ∫ x, ‖f k x‖ ^ p ∂μ) atTop (𝓝 (∫ x, ‖u x‖ ^ p ∂μ)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  have hfp (k : ℕ) : MemLp (f k) (ENNReal.ofReal p) μ :=
    memLp_real_of_memL2 (f k) hp₂ (hf k)
  have hup : MemLp u (ENNReal.ofReal p) μ := memLp_real_of_memL2 u hp₂ hu
  have hlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hfp u hup).mpr
    (tendsto_eLpNorm_real_of_L2 hf hu hconv hp0 hp₂)
  have hnorm := hlim.norm
  have heq (v : X → E) (hv : MemLp v (ENNReal.ofReal p) μ) :
      ‖hv.toLp v‖ ^ p = ∫ x, ‖v x‖ ^ p ∂μ := by
    rw [Lp.norm_toLp, hv.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hp0).ne'
      ENNReal.ofReal_ne_top]
    rw [ENNReal.toReal_ofReal (by positivity)]
    simp only [ENNReal.toReal_ofReal hp0.le]
    exact Real.rpow_inv_rpow (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) hp0.ne'
  have H := hnorm.rpow_const (Or.inr hp0.le : ‖hup.toLp u‖ ≠ 0 ∨ 0 ≤ p)
  simpa only [heq] using H

/-- Subtracting the actual convergent averages preserves the power-integral limit. -/
theorem tendsto_integral_centered_rpow_of_L2 {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} [IsFiniteMeasure μ] {f : ℕ → X → E} {u : X → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k-u) 2 μ) atTop (𝓝 0))
    {p : ℝ} (hp : 1 ≤ p) (hp₂ : p ≤ 2) :
    Tendsto (fun k => ∫ x, ‖f k x-(⨍ y, f k y ∂μ)‖ ^ p ∂μ) atTop
      (𝓝 (∫ x, ‖u x-(⨍ y, u y ∂μ)‖ ^ p ∂μ)) :=
  tendsto_integral_norm_rpow_of_L2 (fun k => (hf k).sub (memLp_const _))
    (hu.sub (memLp_const _)) (tendsto_centered_eLpNorm_two_of_L2 hf hu hconv) hp hp₂

end StationaryHarmonicMaps.Analysis

end
