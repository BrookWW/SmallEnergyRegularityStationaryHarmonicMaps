module

public import HarmonicMaps.Analysis.SobolevPostcompositionBasic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# L² estimates for C¹ target postcomposition

A global bound on the derivative gives a Lipschitz estimate for the target
map, including its constant value at zero. The displayed derivative applied
to an L2 column remains L2. Dominated convergence controls the derivative
coefficient error against a fixed L2 column.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

open HarmonicMaps

/-- A bounded derivative controls differences of the target map. -/
theorem postcomposition_c1_norm_sub_le {q k : ℕ}
    {F : Ambient q → Ambient k} (hF : ContDiff ℝ 1 F)
    {L : ℝ} (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) (z w : Ambient q) :
    ‖F z - F w‖ ≤ L * ‖z - w‖ := by
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (hF.differentiable (by simp)).differentiableAt)
    (fun x _ => hDF x) convex_univ (mem_univ w) (mem_univ z)

/-- C¹ postcomposition preserves L2 on a finite measure space. -/
theorem memLp_postcomposition_c1 {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {q k : ℕ}
    {u : α → Ambient q} (hu : MemLp u 2 μ)
    {F : Ambient q → Ambient k} (hF : ContDiff ℝ 1 F)
    {L : ℝ} (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) : MemLp (F ∘ u) 2 μ := by
  have hmeas : AEStronglyMeasurable (F ∘ u) μ :=
    hF.continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable
  apply ((hu.norm.const_mul L).add (memLp_const ‖F 0‖)).mono' hmeas
  filter_upwards [] with x
  have hb := postcomposition_c1_norm_sub_le hF hDF (u x) 0
  simp only [sub_zero] at hb
  calc
    ‖F (u x)‖ ≤ ‖F (u x) - F 0‖ + ‖F 0‖ := norm_le_norm_sub_add _ _
    _ ≤ L * ‖u x‖ + ‖F 0‖ := by gcongr

/-- The actual derivative applied to an L2 column is L2. -/
theorem memLp_postcomposition_c1_column {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {q k : ℕ} {u v : α → Ambient q}
    (hu : AEStronglyMeasurable u μ) (hv : MemLp v 2 μ)
    {F : Ambient q → Ambient k} (hF : ContDiff ℝ 1 F)
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

end StationaryHarmonicMaps.Analysis

end
