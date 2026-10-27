module

public import StationaryHarmonicMaps.Analysis.C1PostcompositionBasic

/-!
# L² limits of postcomposed derivative columns

Continuous bounded derivative coefficients converge against a fixed L²
column by dominated convergence. The variable-column error is controlled
by the same uniform derivative bound.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Actual C¹ postcomposition preserves strong L² column limits along a.e. convergent maps. -/
theorem tendsto_postcomposition_column_l2 {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {q k : ℕ} {m v : ℕ → α → Ambient q} {u w : α → Ambient q}
    (hm : ∀ j, AEStronglyMeasurable (m j) μ) (hu : AEStronglyMeasurable u μ)
    (hv : ∀ j, MemLp (v j) 2 μ) (hw : MemLp w 2 μ)
    (hmae : ∀ᵐ x ∂μ, Tendsto (fun j => m j x) atTop (𝓝 (u x)))
    (hconv : Tendsto (fun j => eLpNorm (v j - w) 2 μ) atTop (𝓝 0))
    {F : Ambient q → Ambient k} (hF : ContDiff ℝ 1 F)
    {L : ℝ} (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) :
    Tendsto (fun j => eLpNorm
      (fun x => fderiv ℝ F (m j x) (v j x) - fderiv ℝ F (u x) (w x)) 2 μ)
      atTop (𝓝 0) := by
  let A : ℕ → α → Ambient k := fun j x => fderiv ℝ F (m j x) (v j x - w x)
  let B : ℕ → α → Ambient k := fun j x =>
    (fderiv ℝ F (m j x) - fderiv ℝ F (u x)) (w x)
  have hA : ∀ j, MemLp (A j) 2 μ := fun j =>
    memLp_postcomposition_c1_column (hm j) ((hv j).sub hw) hF hDF
  have hB : ∀ j, AEStronglyMeasurable (B j) μ := fun j =>
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((((hF.continuous_fderiv (by simp)).comp_aestronglyMeasurable (hm j)).sub
        ((hF.continuous_fderiv (by simp)).comp_aestronglyMeasurable hu)).prodMk
          hw.aestronglyMeasurable)
  have hbB : ∀ j, ∀ᵐ x ∂μ, ‖B j x‖ ≤ (2 * L) * ‖w x‖ := by
    intro j
    filter_upwards [] with x
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith only [hDF (m j x), hDF (u x)])
  have hlimB : Tendsto (fun j => eLpNorm (B j) 2 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_zero_of_dominated hB hw hbB
    filter_upwards [hmae] with x hx
    have hd := (hF.continuous_fderiv (by simp)).continuousAt.tendsto.comp hx
    have hzero : Tendsto (fun j => fderiv ℝ F (m j x) - fderiv ℝ F (u x))
        atTop (𝓝 0) := by
      simpa only [sub_self, Function.comp_def] using
        hd.sub (tendsto_const_nhds (x := fderiv ℝ F (u x)))
    have he := (ContinuousLinearMap.apply ℝ (Ambient k) (w x)).continuous.tendsto 0
      |>.comp hzero
    simpa only [B, Function.comp_def, ContinuousLinearMap.apply_apply,
      zero_apply] using he
  have hlimA : Tendsto (fun j => eLpNorm (A j) 2 μ) atTop (𝓝 0) := by
    have H := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal L) hconv
      (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using H) (fun _ => zero_le)
    intro j
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (p := 2)
    filter_upwards [] with x
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hDF (m j x)) (norm_nonneg _))
  have hsplit (j : ℕ) :
      (fun x => fderiv ℝ F (m j x) (v j x) - fderiv ℝ F (u x) (w x)) = A j + B j := by
    funext x
    simp only [A, B, Pi.add_apply, map_sub, sub_apply]
    abel
  have H := hlimA.add hlimB
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using H) (fun _ => zero_le)
  intro j
  dsimp only
  rw [hsplit]
  exact eLpNorm_add_le (hA j).aestronglyMeasurable (hB j) (by norm_num)

end StationaryHarmonicMaps.Analysis

end
