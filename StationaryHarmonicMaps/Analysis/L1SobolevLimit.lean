module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Integral and mean-oscillation limits under L2 approximation

On a finite measure space, L2 convergence implies L1 convergence with the
actual measure factor. Norm integrals and averages therefore converge.
Subtracting the convergent averages preserves L2 convergence, giving the
limit of the centered norm integrals without a mean-oscillation assumption.
-/

public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps

/-- Finite-measure L2 convergence implies L1 convergence. -/
theorem tendsto_eLpNorm_one_zero_of_L2 {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → E} {u : α → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (f k - u) 1 μ) atTop (𝓝 0) := by
  have hb : Tendsto (fun k => eLpNorm (f k - u) 2 μ *
      μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)) atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hconv
      (Or.inr (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => zero_le)
  intro k
  exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ((hf k).sub hu).aestronglyMeasurable

/-- The integral of the norm is continuous under actual L2 approximation. -/
theorem tendsto_integral_norm_of_L2 {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → E} {u : α → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖f k x‖ ∂μ) atTop (𝓝 (∫ x, ‖u x‖ ∂μ)) := by
  have hnorm : Tendsto (fun k => eLpNorm
      ((fun x => ‖f k x‖) - (fun x => ‖u x‖)) 2 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun _ => zero_le)
    intro k
    apply eLpNorm_mono_ae
    filter_upwards [] with x
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using abs_norm_sub_norm_le (f k x) (u x)
  have hL1 := tendsto_eLpNorm_one_zero_of_L2 (fun k => (hf k).norm) hu.norm hnorm
  exact tendsto_integral_of_L1' (fun x => ‖u x‖) hu.aestronglyMeasurable.norm
    (Eventually.of_forall fun k => ((hf k).integrable (by norm_num)).norm) hL1

/-- The vector integral is continuous under finite-measure L2 approximation. -/
theorem tendsto_integral_of_L2 {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → E} {u : α → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, f k x ∂μ) atTop (𝓝 (∫ x, u x ∂μ)) := by
  exact tendsto_integral_of_L1' u hu.aestronglyMeasurable
    (Eventually.of_forall fun k => (hf k).integrable (by norm_num))
    (tendsto_eLpNorm_one_zero_of_L2 hf hu hconv)

/-- Averages converge without a probability or nonzero-measure assumption. -/
theorem tendsto_average_of_L2 {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → E} {u : α → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ⨍ x, f k x ∂μ) atTop (𝓝 (⨍ x, u x ∂μ)) := by
  simpa only [average_eq] using
    (tendsto_integral_of_L2 hf hu hconv).const_smul ((μ.real univ)⁻¹)

/-- Subtracting the actual averages preserves L2 convergence. -/
theorem tendsto_centered_eLpNorm_two_of_L2 {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → E} {u : α → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm
      ((fun x => f k x - ⨍ y, f k y ∂μ) - (fun x => u x - ⨍ y, u y ∂μ)) 2 μ)
      atTop (𝓝 0) := by
  have ha := tendsto_average_of_L2 hf hu hconv
  have hn : Tendsto (fun k => ‖(⨍ y, f k y ∂μ) - (⨍ y, u y ∂μ)‖ₑ) atTop (𝓝 0) := by
    simpa only [sub_self, enorm_zero] using
      (ha.sub (tendsto_const_nhds (x := (⨍ y, u y ∂μ)))).enorm
  have hc : Tendsto (fun k => eLpNorm
      (fun _ : α => (⨍ y, f k y ∂μ) - (⨍ y, u y ∂μ)) 2 μ) atTop (𝓝 0) := by
    simp_rw [eLpNorm_const' (p := (2 : ℝ≥0∞)) (μ := μ) _ (by norm_num) (by norm_num)]
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hn
      (Or.inr (by finiteness))
  have hsum : Tendsto (fun k => eLpNorm (f k - u) 2 μ + eLpNorm
      (fun _ : α => (⨍ y, f k y ∂μ) - (⨍ y, u y ∂μ)) 2 μ) atTop (𝓝 0) := by
    simpa only [add_zero] using hconv.add hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le)
  intro k
  have heq : ((fun x => f k x - ⨍ y, f k y ∂μ) -
      (fun x => u x - ⨍ y, u y ∂μ)) =
      (f k - u) - (fun _ : α => (⨍ y, f k y ∂μ) - (⨍ y, u y ∂μ)) := by
    funext x
    simp only [Pi.sub_apply]
    abel
  dsimp only
  rw [heq]
  exact eLpNorm_sub_le ((hf k).sub hu).aestronglyMeasurable aestronglyMeasurable_const
    (by norm_num)

/-- Centered norm integrals converge from the original L2 approximation data. -/
theorem tendsto_integral_centered_norm_of_L2 {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → E} {u : α → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖f k x - ⨍ y, f k y ∂μ‖ ∂μ) atTop
      (𝓝 (∫ x, ‖u x - ⨍ y, u y ∂μ‖ ∂μ)) := by
  exact tendsto_integral_norm_of_L2
    (fun k => (hf k).sub (memLp_const _)) (hu.sub (memLp_const _))
    (tendsto_centered_eLpNorm_two_of_L2 hf hu hconv)

end StationaryHarmonicMaps

end
