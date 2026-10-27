module

public import HarmonicMaps.SobolevLemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Closure of the weak Sobolev graph in L2

On a finite-measure open domain, convergence of the maps and each displayed
weak-gradient column in L2 preserves the weak derivative identities. In
particular, this applies to every Euclidean ball without a positivity condition
on its radius.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace HarmonicMaps

private theorem tendsto_integral_smul_of_L2 {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} [IsFiniteMeasure μ] {f : ℕ → α → E} {u : α → E}
    {φ : α → ℝ} (hφ : MemLp φ ∞ μ)
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, φ x • f k x ∂μ) atTop (𝓝 (∫ x, φ x • u x ∂μ)) := by
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
  have hm : Tendsto (fun k => eLpNorm φ ∞ μ * eLpNorm (f k - u) 1 μ)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hL1
      (Or.inr hφ.eLpNorm_lt_top.ne)
  have hpair : Tendsto (fun k => eLpNorm
      ((fun x => φ x • f k x) - (fun x => φ x • u x)) 1 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm
      (fun _ => zero_le)
    intro k
    have heq : ((fun x => φ x • f k x) - (fun x => φ x • u x)) = φ • (f k - u) := by
      funext x
      exact (smul_sub (φ x) (f k x) (u x)).symm
    dsimp only
    rw [heq]
    exact eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 1
        ((hf k).sub hu).aestronglyMeasurable φ
  exact tendsto_integral_of_L1' _ (hφ.aestronglyMeasurable.smul hu.aestronglyMeasurable)
    (Eventually.of_forall fun k => ((hf k).integrable (by norm_num)).smul_of_top_right hφ)
    hpair

/-- The weak Sobolev graph is closed under L2 convergence on a finite-measure
open domain. All derivative limits are the columns of the same displayed `Du`. -/
theorem MemW12.of_L2_limit {n q : ℕ} {Ω : OpenDomain n}
    [IsFiniteMeasure (volume.restrict Ω.val)]
    {f : ℕ → Domain n → Ambient q} {Df : ℕ → Domain n → Gradient n q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hf : ∀ k, MemW12 Ω (f k) (Df k))
    (hu : MemLp u 2 (volume.restrict Ω.val))
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict Ω.val))
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 (volume.restrict Ω.val))
      atTop (𝓝 0))
    (hDconv : ∀ i : Fin n, Tendsto (fun k => eLpNorm
      (fun x => Df k x i - Du x i) 2 (volume.restrict Ω.val)) atTop (𝓝 0)) :
    MemW12 Ω u Du := by
  refine ⟨⟨IntegrableOn.locallyIntegrableOn (hu.integrable (by norm_num)),
    (fun i => IntegrableOn.locallyIntegrableOn ((hDu i).integrable (by norm_num))), ?_⟩, hu, hDu⟩
  intro i φ hφ hcompact hsupport
  have htest : MemLp φ ∞ (volume.restrict Ω.val) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hcompact _
  have hderiv_cont : Continuous (coordinateDerivative φ hφ i) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hderiv_compact : HasCompactSupport (coordinateDerivative φ hφ i) :=
    hcompact.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hderiv := hderiv_cont.memLp_top_of_hasCompactSupport hderiv_compact
    (volume.restrict Ω.val)
  have hl := tendsto_integral_smul_of_L2 hderiv (fun k => (hf k).2.1) hu hconv
  have hr := (tendsto_integral_smul_of_L2 htest (fun k => (hf k).2.2 i)
    (hDu i) (hDconv i)).neg
  exact tendsto_nhds_unique hl (hr.congr fun k => ((hf k).1.2.2 i φ hφ hcompact hsupport).symm)

/-- Ball specialization of weak Sobolev graph closure in L2. -/
theorem MemW12.of_L2_limit_ball {n q : ℕ} (a : Domain n) (r : ℝ)
    {f : ℕ → Domain n → Ambient q} {Df : ℕ → Domain n → Gradient n q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hf : ∀ k, MemW12 (ballDomain a r) (f k) (Df k))
    (hu : MemLp u 2 (volume.restrict (Metric.ball a r)))
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict (Metric.ball a r)))
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 (volume.restrict (Metric.ball a r)))
      atTop (𝓝 0))
    (hDconv : ∀ i : Fin n, Tendsto (fun k => eLpNorm
      (fun x => Df k x i - Du x i) 2 (volume.restrict (Metric.ball a r))) atTop (𝓝 0)) :
    MemW12 (ballDomain a r) u Du := by
  letI : IsFiniteMeasure (volume.restrict (ballDomain a r).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  exact MemW12.of_L2_limit hf hu hDu hconv hDconv

end HarmonicMaps
