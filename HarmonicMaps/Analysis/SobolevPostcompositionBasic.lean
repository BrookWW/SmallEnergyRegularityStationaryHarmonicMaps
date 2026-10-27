module

public import HarmonicMaps.Sobolev
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# L2 estimates for smooth target postcomposition

A global bound on the derivative gives a Lipschitz estimate for the target
map, including its constant value at zero. The displayed derivative applied
to an L2 column remains L2. Dominated convergence controls the derivative
coefficient error against a fixed L2 column.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace HarmonicMaps

/-- A bounded derivative controls differences of the target map. -/
theorem postcomposition_norm_sub_le {q k : ℕ}
    {F : Ambient q → Ambient k} (hF : ContDiff ℝ ∞ F)
    {L : ℝ} (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) (z w : Ambient q) :
    ‖F z - F w‖ ≤ L * ‖z - w‖ := by
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (hF.differentiable (by simp)).differentiableAt)
    (fun x _ => hDF x) convex_univ (mem_univ w) (mem_univ z)

/-- Smooth postcomposition preserves L2 on a finite measure space. -/
theorem memLp_postcomposition {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {q k : ℕ}
    {u : α → Ambient q} (hu : MemLp u 2 μ)
    {F : Ambient q → Ambient k} (hF : ContDiff ℝ ∞ F)
    {L : ℝ} (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) : MemLp (F ∘ u) 2 μ := by
  have hmeas : AEStronglyMeasurable (F ∘ u) μ :=
    hF.continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable
  apply ((hu.norm.const_mul L).add (memLp_const ‖F 0‖)).mono' hmeas
  filter_upwards [] with x
  have hb := postcomposition_norm_sub_le hF hDF (u x) 0
  simp only [sub_zero] at hb
  calc
    ‖F (u x)‖ ≤ ‖F (u x) - F 0‖ + ‖F 0‖ := norm_le_norm_sub_add _ _
    _ ≤ L * ‖u x‖ + ‖F 0‖ := by gcongr

/-- The actual derivative applied to an L2 column is L2. -/
theorem memLp_postcomposition_column {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {q k : ℕ} {u v : α → Ambient q}
    (hu : AEStronglyMeasurable u μ) (hv : MemLp v 2 μ)
    {F : Ambient q → Ambient k} (hF : ContDiff ℝ ∞ F)
    {L : ℝ} (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) :
    MemLp (fun x => fderiv ℝ F (u x) (v x)) 2 μ := by
  have hmeas : AEStronglyMeasurable (fun x => fderiv ℝ F (u x) (v x)) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (((hF.continuous_fderiv (by simp)).comp_aestronglyMeasurable hu).prodMk
        hv.aestronglyMeasurable)
  apply hv.of_le_mul hmeas
  filter_upwards [] with x
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hDF (u x)) (norm_nonneg (v x)))

/-- L2 convergence follows from a fixed L2 majorant and a.e. convergence to zero. -/
theorem tendsto_eLpNorm_two_zero_of_dominated {α E G : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup G]
    {μ : Measure α} {f : ℕ → α → E} {g : α → G}
    (hf : ∀ j, AEStronglyMeasurable (f j) μ) (hg : MemLp g 2 μ)
    {C : ℝ}
    (hb : ∀ j, ∀ᵐ x ∂μ, ‖f j x‖ ≤ C * ‖g x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (f j) 2 μ) atTop (𝓝 0) := by
  have hm : ∀ j, MemLp (f j) 2 μ := fun j => hg.of_le_mul (hf j) (hb j)
  have hbound : Integrable (fun x => C ^ 2 * ‖g x‖ ^ 2) μ :=
    (hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _
  have hint : Tendsto (fun j => ∫ x, ‖f j x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have H := tendsto_integral_of_dominated_convergence
      (bound := fun x => C ^ 2 * ‖g x‖ ^ 2)
      (fun j => (hf j).norm.pow 2) hbound
      (fun j => (hb j).mono fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hx 2)
      (hlim.mono fun x hx => by simpa using hx.norm.pow 2)
    simpa only [integral_zero, Pi.pow_apply] using H
  have hof : Tendsto (fun j => ENNReal.ofReal (∫ x, ‖f j x‖ ^ 2 ∂μ))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.tendsto 0 |>.comp hint
  have H := (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).tendsto 0 |>.comp hof
  have heq (j : ℕ) : eLpNorm (f j) 2 μ =
      ENNReal.ofReal (∫ x, ‖f j x‖ ^ 2 ∂μ) ^ ((2 : ℝ)⁻¹) := by
    rw [(hm j).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    norm_num
    exact (ENNReal.ofReal_rpow_of_nonneg
      (integral_nonneg fun x => sq_nonneg _) (by norm_num)).symm
  simpa only [Function.comp_def, ← heq, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (by norm_num :
    (0 : ℝ) < (2 : ℝ)⁻¹)] using H

end HarmonicMaps
