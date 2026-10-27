module

public import StationaryHarmonicMaps.Analysis.WeakL2Subsequence

/-!
# Genuine weak-strong pairings

A common eventual norm bound controls the varying test error. The fixed
test uses the original weak limit. The L2 instance retains the actual
Euclidean fields, their true integrals, and the original uniform energy.
-/

public section

open HarmonicMaps MeasureTheory Filter
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- An actually weak sequence pairs continuously with a genuinely strong sequence of tests. -/
theorem tendsto_inner_of_weak_and_strong {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (u w : ℕ → H) (v z : H)
    (hweak : ∀ b : H, Tendsto (fun k => inner ℝ (u k) b) atTop (𝓝 (inner ℝ v b)))
    (hstrong : Tendsto w atTop (𝓝 z))
    {M : ℝ} (hbound : ∀ᶠ k in atTop, ‖u k‖ ≤ M) :
    Tendsto (fun k => inner ℝ (u k) (w k)) atTop (𝓝 (inner ℝ v z)) := by
  have hsmall : Tendsto (fun k => M * ‖w k - z‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using ((hstrong.sub_const z).norm.const_mul M)
  have herror : Tendsto (fun k => inner ℝ (u k) (w k - z)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hsmall
    filter_upwards [hbound] with k hk
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hk (norm_nonneg _))
  have heq (k : ℕ) : inner ℝ (u k) z + inner ℝ (u k) (w k - z) =
      inner ℝ (u k) (w k) := by
    rw [inner_sub_right]
    ring
  simpa only [heq, add_zero] using (hweak z).add herror

/-- Actual weak L2 fields and actual strong L2 tests give convergence of their true pairings. -/
theorem tendsto_integral_inner_of_weak_and_strong_L2 {n q : ℕ} (μ : Measure (Domain n))
    (f g : ℕ → Domain n → Ambient q) (v w : Domain n → Ambient q)
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : ∀ k, MemLp (g k) 2 μ)
    (hv : MemLp v 2 μ) (hw : MemLp w 2 μ)
    (hweak : ∀ b : Domain n → Ambient q, MemLp b 2 μ →
      Tendsto (fun k => ∫ x, inner ℝ (f k x) (b x) ∂μ) atTop
        (𝓝 (∫ x, inner ℝ (v x) (b x) ∂μ)))
    (hstrong : Tendsto (fun k => eLpNorm (g k - w) 2 μ) atTop (𝓝 0))
    {M : ℝ} (henergy : ∀ k, (∫ x, ‖f k x‖ ^ 2 ∂μ) ≤ M) :
    Tendsto (fun k => ∫ x, inner ℝ (f k x) (g k x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (v x) (w x) ∂μ)) := by
  let F (k : ℕ) : Lp (Ambient q) 2 μ := (hf k).toLp (f k)
  let G (k : ℕ) : Lp (Ambient q) 2 μ := (hg k).toLp (g k)
  have hF (k : ℕ) : ‖F k‖ ≤ Real.sqrt M := by
    have heq : (∫ x, ‖f k x‖ ^ 2 ∂μ) = ‖F k‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simpa only [real_inner_self_eq_norm_sq] using
        HolderToCK.integral_inner_eq_L2_inner (hf k) (hf k)
    have H := Real.sqrt_le_sqrt (henergy k)
    rw [heq, Real.sqrt_sq (norm_nonneg _)] at H
    exact H
  have hweakLp (b : Lp (Ambient q) 2 μ) :
      Tendsto (fun k => inner ℝ (F k) b) atTop (𝓝 (inner ℝ (hv.toLp v) b)) := by
    have H := hweak b (Lp.memLp b)
    simpa only [HolderToCK.integral_inner_eq_L2_inner (hf _) (Lp.memLp b),
      HolderToCK.integral_inner_eq_L2_inner hv (Lp.memLp b), Lp.toLp_coeFn] using H
  have hstrongLp : Tendsto G atTop (𝓝 (hw.toLp w)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg w hw).mpr hstrong
  have H := tendsto_inner_of_weak_and_strong F G (hv.toLp v) (hw.toLp w)
    hweakLp hstrongLp (Eventually.of_forall hF)
  simp_rw [HolderToCK.integral_inner_eq_L2_inner (hf _) (hg _),
    HolderToCK.integral_inner_eq_L2_inner hv hw]
  exact H

end StationaryHarmonicMaps.Analysis

end
