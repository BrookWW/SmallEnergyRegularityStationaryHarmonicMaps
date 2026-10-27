module

public import StationaryHarmonicMaps.Analysis.BoundedSobolevL2Approximation
public import StationaryHarmonicMaps.Analysis.ContinuousL2Compactness
public import StationaryHarmonicMaps.Analysis.MetricApproximationCompactness
public import HolderToCK.Analysis.L2PairingContinuity
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Actual whole-ball L2 compactness of bounded Sobolev sequences

A common almost-everywhere value bound controls the actual boundary layer.
Together with the displayed weak-gradient energy bound it produces genuine
whole-ball uniform smooth approximations. The original L2 classes are
totally bounded, and completeness gives an increasing convergent subsequence
represented by an actual L2 map on the whole unit ball.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem toLp_dist_lt_of_integral_sq_lt {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {ε : ℝ} (hε : 0 < ε) (herror : (∫ x, ‖f x - g x‖ ^ 2 ∂μ) < ε ^ 2) :
    dist (hf.toLp f) (hg.toLp g) < ε := by
  have hnorm : (∫ x, ‖f x - g x‖ ^ 2 ∂μ) = ‖((hf.sub hg).toLp (f - g))‖ ^ 2 := by
    simpa only [Pi.sub_apply, real_inner_self_eq_norm_sq] using
      HolderToCK.integral_inner_eq_L2_inner (hf.sub hg) (hf.sub hg)
  rw [MemLp.toLp_sub hf hg] at hnorm
  apply (sq_lt_sq₀ dist_nonneg hε.le).mp
  rw [dist_eq_norm, ← hnorm]
  exact herror

/-- Actual AE boundedness and same-gradient energy give compactness on the whole unit ball. -/
theorem bounded_sobolev_L2_compactness_unitBall {n q : ℕ}
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (hu : ∀ k, MemW12 (ballDomain (0 : Domain n) 1) (u k) (Du k))
    (B Mgrad : ℝ) (hB : 0 ≤ B) (hMgrad : 0 ≤ Mgrad)
    (hbound : ∀ k, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1), ‖u k x‖ ≤ B)
    (hgrad : ∀ k, (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du k x)) ≤ Mgrad) :
    ∃ hMap : ∀ k, MemLp (u k) 2 (volume.restrict (Metric.ball (0 : Domain n) 1)),
      TotallyBounded (range (fun k => (hMap k).toLp (u k))) ∧
      ∃ v : Domain n → Ambient q, MemLp v 2 (volume.restrict (Metric.ball (0 : Domain n) 1)) ∧
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          Tendsto (fun k => eLpNorm (u (σ k) - v) 2
            (volume.restrict (Metric.ball (0 : Domain n) 1))) atTop (𝓝 0) := by
  let μ : Measure (Domain n) := volume.restrict (Metric.ball (0 : Domain n) 1)
  have hMap (k : ℕ) : MemLp (u k) 2 μ := (hu k).2.1
  let U : ℕ → Lp (Ambient q) 2 μ := fun k => (hMap k).toLp (u k)
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ g : ℕ → Lp (Ambient q) 2 μ,
      TotallyBounded (range g) ∧ ∀ k, dist (U k) (g k) < ε := by
    intro ε hε
    obtain ⟨m, L, hL, hsmooth, _hglobal, hvalue, hlip, herror⟩ :=
      exists_bounded_sobolev_uniform_L2_approximation u Du hu B Mgrad hB hMgrad hbound hgrad ε hε
    obtain ⟨hm, hTB⟩ := continuous_lipschitz_family_L2_totallyBounded (0 : Domain n) 1 m
      (fun k => (hsmooth k).continuous.continuousOn) hL
      (fun k x _ => hvalue k x) (fun k x _ y _ => hlip k x y)
    refine ⟨fun k => (hm k).toLp (m k), hTB, ?_⟩
    intro k
    rw [dist_comm]
    exact toLp_dist_lt_of_integral_sq_lt (hm k) (hMap k) hε (herror k)
  have hTB : TotallyBounded (range U) := totallyBounded_range_of_uniform_approximation U happrox
  obtain ⟨vClass, σ, hσ, hlim⟩ := exists_subsequence_limit_of_uniform_approximation U happrox
  let v : Domain n → Ambient q := vClass
  have hv : MemLp v 2 μ := Lp.memLp vClass
  have hlim' : Tendsto (fun k => (hMap (σ k)).toLp (u (σ k))) atTop (𝓝 (hv.toLp v)) := by
    rw [Lp.toLp_coeFn]
    exact hlim
  have hconv : Tendsto (fun k => eLpNorm (u (σ k) - v) 2 μ) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k => u (σ k))
      (fun k => hMap (σ k)) v hv).mp hlim'
  exact ⟨hMap, hTB, v, hv, σ, hσ, hconv⟩

end StationaryHarmonicMaps.Analysis

end
