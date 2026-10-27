module

public import HarmonicMaps.Analysis.SobolevL2Closure
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Closure of the native zero-boundary Sobolev space

One diagonal compactly supported smooth sequence approximates the limit map
and every column of its actual weak gradient. The finite coordinate set permits
simultaneous choices; the L2 triangle inequality supplies graph convergence.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace HolderToCK

theorem hasZeroBoundaryValues_of_L2_limit {n q : ℕ} {Ω : OpenDomain n}
    [IsFiniteMeasure (volume.restrict Ω.val)]
    {f : ℕ → Domain n → Ambient q} {Df : ℕ → Domain n → Gradient n q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hf : ∀ k, HasZeroBoundaryValues Ω (f k) (Df k))
    (hu : MemLp u 2 (volume.restrict Ω.val))
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict Ω.val))
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 (volume.restrict Ω.val))
      atTop (𝓝 0))
    (hDconv : ∀ i : Fin n, Tendsto (fun k => eLpNorm
      (fun x => Df k x i - Du x i) 2 (volume.restrict Ω.val)) atTop (𝓝 0)) :
    HasZeroBoundaryValues Ω u Du := by
  classical
  have hW : MemW12 Ω u Du :=
    MemW12.of_L2_limit (fun k => (hf k).1) hu hDu hconv hDconv
  choose m hm hc hmc hDc using fun k => (hf k).2
  let ε : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (1 / ((k : ℝ) + 1))
  have hε (k : ℕ) : 0 < ε k := by dsimp only [ε]; positivity
  have hindex (k : ℕ) : ∃ j : ℕ,
      eLpNorm (m k j - f k) 2 (volume.restrict Ω.val) ≤ ε k ∧
      ∀ i : Fin n, eLpNorm (fun x => coordinateDerivative (m k j) (hm k j) i x - Df k x i)
        2 (volume.restrict Ω.val) ≤ ε k := by
    have hmap : ∀ᶠ j in atTop,
        eLpNorm (m k j - f k) 2 (volume.restrict Ω.val) < ε k :=
      (hmc k).eventually (gt_mem_nhds (hε k))
    have hgrad : ∀ᶠ j in atTop, ∀ i : Fin n,
        eLpNorm (fun x => coordinateDerivative (m k j) (hm k j) i x - Df k x i)
          2 (volume.restrict Ω.val) < ε k :=
      eventually_all.mpr (fun i => (hDc k i).eventually (gt_mem_nhds (hε k)))
    obtain ⟨j, hjmap, hjgrad⟩ := (hmap.and hgrad).exists
    exact ⟨j, hjmap.le, fun i => (hjgrad i).le⟩
  choose J hJ hDJ using hindex
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨hW, (fun k => m k (J k)), (fun k => hm k (J k)),
    (fun k => hc k (J k)), ?_, ?_⟩
  · have hlim : Tendsto (fun k => ε k + eLpNorm (f k - u) 2 (volume.restrict Ω.val))
        atTop (𝓝 0) := by
      simpa only [zero_add] using hεlim.add hconv
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le)
    intro k
    dsimp only
    have heq : m k (J k) - u = (m k (J k) - f k) + (f k - u) := by
      funext x
      simp only [Pi.sub_apply, Pi.add_apply]
      abel
    rw [heq]
    exact (eLpNorm_add_le
      ((hm k (J k)).continuous.aestronglyMeasurable.sub (hf k).1.2.1.aestronglyMeasurable)
      ((hf k).1.2.1.aestronglyMeasurable.sub hu.aestronglyMeasurable)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add (hJ k) le_rfl)
  · intro i
    have hlim : Tendsto (fun k => ε k + eLpNorm
        (fun x => Df k x i - Du x i) 2 (volume.restrict Ω.val)) atTop (𝓝 0) := by
      simpa only [zero_add] using hεlim.add (hDconv i)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le)
    intro k
    dsimp only
    have heq : (fun x => coordinateDerivative (m k (J k)) (hm k (J k)) i x - Du x i) =
        (fun x => coordinateDerivative (m k (J k)) (hm k (J k)) i x - Df k x i) +
          (fun x => Df k x i - Du x i) := by
      funext x
      simp only [Pi.add_apply]
      abel
    rw [heq]
    have hdm : Continuous (coordinateDerivative (m k (J k)) (hm k (J k)) i) :=
      ((hm k (J k)).continuous_fderiv (by simp)).clm_apply continuous_const
    exact (eLpNorm_add_le
      (hdm.aestronglyMeasurable.sub ((hf k).1.2.2 i).aestronglyMeasurable)
      (((hf k).1.2.2 i).aestronglyMeasurable.sub (hDu i).aestronglyMeasurable)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add (hDJ k i) le_rfl)

theorem hasZeroBoundaryValues_of_L2_limit_ball {n q : ℕ} (a : Domain n) (r : ℝ)
    {f : ℕ → Domain n → Ambient q} {Df : ℕ → Domain n → Gradient n q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hf : ∀ k, HasZeroBoundaryValues (ballDomain a r) (f k) (Df k))
    (hu : MemLp u 2 (volume.restrict (Metric.ball a r)))
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict (Metric.ball a r)))
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 (volume.restrict (Metric.ball a r)))
      atTop (𝓝 0))
    (hDconv : ∀ i : Fin n, Tendsto (fun k => eLpNorm
      (fun x => Df k x i - Du x i) 2 (volume.restrict (Metric.ball a r))) atTop (𝓝 0)) :
    HasZeroBoundaryValues (ballDomain a r) u Du := by
  letI : IsFiniteMeasure (volume.restrict (ballDomain a r).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  exact hasZeroBoundaryValues_of_L2_limit hf hu hDu hconv hDconv

end HolderToCK
end
