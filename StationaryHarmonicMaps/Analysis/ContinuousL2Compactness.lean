module

public import HarmonicMaps.Sobolev
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.Sequences

/-!
# L2 precompactness of genuinely bounded Lipschitz families

Arzela-Ascoli applies on the compact closed ball. Finite uniform covers
have centers in the actual family, and the finite-measure L2 estimate
transfers them to covers of the original ambient functions' L2 classes.
No extension of a Sobolev function or unproved compactness input is used.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace StationaryHarmonicMaps.Analysis

private theorem totallyBounded_range_of_dist_bound {I : Type*} {X Y : Type}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (f : I → X) (g : I → Y)
    (hf : TotallyBounded (range f)) {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ i j, dist (g i) (g j) ≤ C * dist (f i) (f j)) :
    TotallyBounded (range g) := by
  classical
  apply Metric.totallyBounded_of_finite_discretization
  intro ε hε
  let δ : ℝ := ε / (2 * (C + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨t, _htsub, htfinite, htcover⟩ := Metric.finite_approx_of_totallyBounded hf δ hδ
  have hchoice (i : I) : ∃ y : t, dist (f i) y.val < δ := by
    obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (htcover (mem_range_self i))
    exact ⟨⟨y, hyt⟩, hy⟩
  choose c hc using hchoice
  letI : Fintype t := htfinite.fintype
  refine ⟨↥t, inferInstance, (fun z => c z.property.choose), ?_⟩
  intro x y hxy
  let i : I := x.property.choose
  let j : I := y.property.choose
  have hxi : g i = x.val := x.property.choose_spec
  have hyj : g j = y.val := y.property.choose_spec
  have hcenter : (c i).val = (c j).val := congrArg Subtype.val hxy
  have hdist : dist (f i) (f j) < 2 * δ := by
    calc
      _ ≤ dist (f i) (c i).val + dist (c i).val (f j) := dist_triangle _ _ _
      _ = dist (f i) (c i).val + dist (f j) (c j).val := by
        rw [hcenter, dist_comm (c j).val (f j)]
      _ < δ + δ := add_lt_add (hc i) (hc j)
      _ = _ := by ring
  rw [← hxi, ← hyj]
  calc
    _ ≤ C * dist (f i) (f j) := hfg i j
    _ ≤ (C + 1) * dist (f i) (f j) := by
      exact mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < (C + 1) * (2 * δ) := mul_lt_mul_of_pos_left hdist (by positivity)
    _ = ε := by dsimp only [δ]; field_simp

/-- Actual closed-ball uniform bounds and Lipschitz bounds make the ambient L2 family precompact. -/
theorem continuous_lipschitz_family_L2_totallyBounded {I : Type*} {n q : ℕ}
    (a : Domain n) (r : ℝ) (f : I → Domain n → Ambient q)
    (hf : ∀ i, ContinuousOn (f i) (Metric.closedBall a r))
    {B L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ i x, x ∈ Metric.closedBall a r → ‖f i x‖ ≤ B)
    (hlip : ∀ i x, x ∈ Metric.closedBall a r →
      ∀ y, y ∈ Metric.closedBall a r → dist (f i x) (f i y) ≤ L * dist x y) :
    ∃ hm : ∀ i, MemLp (f i) 2 (volume.restrict (Metric.ball a r)),
      TotallyBounded (range (fun i => (hm i).toLp (f i))) := by
  classical
  let K := Metric.closedBall a r
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall a r)
  let μ := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hm (i : I) : MemLp (f i) 2 μ := by
    apply MemLp.of_bound
      ((hf i).aestronglyMeasurable_of_subset_isCompact
        (isCompact_closedBall a r) measurableSet_ball Metric.ball_subset_closedBall) B
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hbound i x (Metric.ball_subset_closedBall hx)
  let F (i : I) : K →ᵇ Ambient q := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => f i x.val, (hf i).restrict⟩
  have hFL (i : I) : LipschitzWith ⟨L, hL⟩ (F i) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hlip i x.val x.property y.val y.property
  have hEq : Equicontinuous (fun g : range F => (g.val : K → Ambient q)) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ ⟨L, hL⟩
    intro g
    obtain ⟨i, hi⟩ := g.property
    rw [← hi]
    exact hFL i
  have hcompact : IsCompact (closure (range F)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : Ambient q) B)
      (isCompact_closedBall _ _) (range F)
      (fun g x hg => by
        obtain ⟨i, rfl⟩ := hg
        change dist (f i x.val) 0 ≤ B
        rw [dist_zero_right]
        exact hbound i x.val x.property) hEq
  let C : ℝ := (measureUnivNNReal μ : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹
  have hC : 0 ≤ C := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  refine ⟨hm, totallyBounded_range_of_dist_bound F (fun i => (hm i).toLp (f i))
    (hcompact.totallyBounded.subset subset_closure) hC ?_⟩
  intro i j
  have H : ‖((hm i).sub (hm j)).toLp (f i - f j)‖ ≤ C * dist (F i) (F j) := by
    apply Lp.norm_le_of_ae_bound dist_nonneg
    filter_upwards [((hm i).sub (hm j)).coeFn_toLp, ae_restrict_mem measurableSet_ball]
      with x hx hxball
    rw [hx]
    change ‖f i x - f j x‖ ≤ dist (F i) (F j)
    exact BoundedContinuousFunction.dist_coe_le_dist
      (f := F i) (g := F j) ⟨x, Metric.ball_subset_closedBall hxball⟩
  rw [MemLp.toLp_sub] at H
  simpa only [dist_eq_norm] using H

end StationaryHarmonicMaps.Analysis

end
