module

public import HarmonicMaps.Analysis.SmoothPoincare
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Passage to the L2 limit in the ball Poincare estimate

A sequence of smooth maps with convergence of the maps and their classical
coordinate derivatives carries the smooth estimate to its Sobolev limit.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff BigOperators

namespace HarmonicMaps

private theorem integral_norm_sq_eq_norm_toLp_sq {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖hf.toLp f‖ ^ 2 := by
  calc
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ∫ x, inner ℝ ((hf.toLp f) x) ((hf.toLp f) x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx, real_inner_self_eq_norm_sq]
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := (L2.inner_def _ _).symm
    _ = ‖hf.toLp f‖ ^ 2 := real_inner_self_eq_norm_sq _

private theorem tendsto_integral_norm_sq_of_L2 {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure α} {f : ℕ → α → E} {u : α → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖f k x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x, ‖u x‖ ^ 2 ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hconv
  have hn := hLp.norm.pow 2
  simpa only [← integral_norm_sq_eq_norm_toLp_sq] using hn

private theorem tendsto_average_of_L2 {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → E} {u : α → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ⨍ x, f k x ∂μ) atTop (𝓝 (⨍ x, u x ∂μ)) := by
  have hb : Tendsto (fun k => eLpNorm (f k - u) 2 μ *
      μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)) atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hconv
      (Or.inr (by norm_num))
  have hL1 : Tendsto (fun k => eLpNorm (f k - u) 1 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun _ => zero_le)
    intro k
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      ((hf k).sub hu).aestronglyMeasurable
  have hi := tendsto_integral_of_L1' u hu.aestronglyMeasurable
    (Eventually.of_forall fun k => (hf k).integrable (by norm_num)) hL1
  simpa only [average_eq] using hi.const_smul ((μ.real univ)⁻¹)

private theorem tendsto_centered_L2 {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → E} {u : α → E}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm
      ((fun x => f k x - ⨍ y, f k y ∂μ) - (fun x => u x - ⨍ y, u y ∂μ)) 2 μ)
      atTop (𝓝 0) := by
  have ha := tendsto_average_of_L2 hf hu hconv
  have hn : Tendsto (fun k => ‖(⨍ y, f k y ∂μ) - (⨍ y, u y ∂μ)‖ₑ) atTop (𝓝 0) := by
    simpa only [sub_self, enorm_zero] using (ha.sub (tendsto_const_nhds (x := (⨍ y, u y ∂μ)))).enorm
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

/-- The smooth ball Poincare estimate is closed under convergence of the map and
all classical coordinate derivatives in L2. The approximation data are explicit. -/
theorem poincare_ball_of_smooth_L2_approximation {n q : ℕ} (a : Domain n)
    {r : ℝ} (hr : 0 < r) {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemLp u 2 (volume.restrict (Metric.ball a r)))
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict (Metric.ball a r)))
    (f : ℕ → Domain n → Ambient q)
    (hsmooth : ∀ k, ContDiffOn ℝ ∞ (f k) (Metric.ball a r))
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict (Metric.ball a r)))
    (hDf : ∀ k (i : Fin n), MemLp
      (fun x => fderiv ℝ (f k) x (EuclideanSpace.single i 1)) 2
      (volume.restrict (Metric.ball a r)))
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2
      (volume.restrict (Metric.ball a r))) atTop (𝓝 0))
    (hDconv : ∀ i : Fin n, Tendsto (fun k => eLpNorm
      (fun x => fderiv ℝ (f k) x (EuclideanSpace.single i 1) - Du x i) 2
      (volume.restrict (Metric.ball a r))) atTop (𝓝 0)) :
    (∫ x in Metric.ball a r, ‖u x - ⨍ y in Metric.ball a r, u y‖ ^ 2) ≤
      (2 : ℝ) ^ (n + 1) * r ^ 2 * ∫ x in Metric.ball a r, hsNormSq (Du x) := by
  classical
  let μ := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hcenter := tendsto_centered_L2 hf hu hconv
  have hfc (k : ℕ) : MemLp (fun x => f k x - ⨍ y, f k y ∂μ) 2 μ :=
    (hf k).sub (memLp_const _)
  have huc : MemLp (fun x => u x - ⨍ y, u y ∂μ) 2 μ :=
    hu.sub (memLp_const _)
  have hvariance := tendsto_integral_norm_sq_of_L2 hfc huc hcenter
  have hcolumns (i : Fin n) :
      Tendsto (fun k => ∫ x, ‖fderiv ℝ (f k) x (EuclideanSpace.single i 1)‖ ^ 2 ∂μ)
        atTop (𝓝 (∫ x, ‖Du x i‖ ^ 2 ∂μ)) :=
    tendsto_integral_norm_sq_of_L2 (fun k => hDf k i) (hDu i) (hDconv i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hcolumns i)
  have hfkHS (k : ℕ) :
      (∫ x, hsNormSq (fun i => fderiv ℝ (f k) x (EuclideanSpace.single i 1)) ∂μ) =
        ∑ i : Fin n, ∫ x, ‖fderiv ℝ (f k) x (EuclideanSpace.single i 1)‖ ^ 2 ∂μ :=
    integral_finsetSum Finset.univ (fun i _ => (hDf k i).integrable_norm_pow (by decide))
  have huHS : (∫ x, hsNormSq (Du x) ∂μ) = ∑ i : Fin n, ∫ x, ‖Du x i‖ ^ 2 ∂μ :=
    integral_finsetSum Finset.univ (fun i _ => (hDu i).integrable_norm_pow (by decide))
  have hHS : Tendsto (fun k =>
      ∫ x, hsNormSq (fun i => fderiv ℝ (f k) x (EuclideanSpace.single i 1)) ∂μ)
      atTop (𝓝 (∫ x, hsNormSq (Du x) ∂μ)) := by
    simpa only [hfkHS, huHS] using hsum
  exact le_of_tendsto_of_tendsto hvariance
    (hHS.const_mul ((2 : ℝ) ^ (n + 1) * r ^ 2))
    (Eventually.of_forall fun k => smoothPoincare_ball a hr (hsmooth k) (hf k) (hDf k))

end HarmonicMaps
