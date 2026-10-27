module

public import HarmonicMaps.Analysis.SmoothInverseSobolevBasic
public import HarmonicMaps.Analysis.SobolevL2Closure

/-!
# Sobolev composition by smooth inverse coordinates

Whole-ball smooth density and L2 graph closure prove the weak chain rule for
the genuine inverse-coordinate pullback. Every transformed gradient column
is the finite sum of the original columns evaluated at the same inverse.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace HarmonicMaps

private theorem tendsto_eLpNorm_sum_L2 {α E ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [Fintype ι] {μ : Measure α} {v : ι → ℕ → α → E}
    (hv : ∀ j k, AEStronglyMeasurable (v j k) μ)
    (hlim : ∀ j, Tendsto (fun k => eLpNorm (v j k) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x => ∑ j, v j k x) 2 μ) atTop (𝓝 0) := by
  have hs : Tendsto (fun k => ∑ j, eLpNorm (v j k) 2 μ) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hlim j)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
    (fun _ => zero_le)
  intro k
  have heq : (fun x => ∑ j, v j k x) = ∑ j, v j k := by
    funext x
    simp only [Finset.sum_apply]
  dsimp only
  rw [heq]
  exact eLpNorm_sum_le (fun j (_ : j ∈ Finset.univ) => hv j k)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)

/-- A finite Sobolev map pulls back by smooth inverse coordinates with the
actual weak chain-rule columns and no assumed transformed weak identity. -/
theorem MemW12.comp_smooth_inverse_ball {n q : ℕ} {a : Domain n} {R : ℝ}
    (hR : 0 < R) {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du)
    {f g : Domain n → Domain n} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfg : Function.RightInverse g f) (hgf : Function.LeftInverse g f)
    (hfball : MapsTo f (Metric.ball a R) (Metric.ball a R))
    (hgball : MapsTo g (Metric.ball a R) (Metric.ball a R)) :
    MemW12 (ballDomain a R) (u ∘ g)
      (fun x i => ∑ j : Fin n, (fderiv ℝ g x (EuclideanSpace.single i 1)) j • Du (g x) j) := by
  let μ := volume.restrict (Metric.ball a R)
  let A : Fin n → Fin n → Domain n → ℝ :=
    fun i j x => (fderiv ℝ g x (EuclideanSpace.single i 1)) j
  have hA (i j : Fin n) : MemLp (A i j) ∞ μ :=
    smooth_inverse_coefficient_memLp_top hg a R i j
  have hsumL (V : Domain n → Gradient n q)
      (hV : ∀ j, MemLp (fun x => V x j) 2 μ) (i : Fin n) :
      MemLp (fun x => ∑ j : Fin n, A i j x • V (g x) j) 2 μ := by
    have hterm (j : Fin n) : MemLp (fun x => A i j x • V (g x) j) 2 μ :=
      (memLp_comp_smooth_inverse_ball (hV j) hf hg.continuous hfg hgf hfball hgball).smul
        (r := (2 : ℝ≥0∞)) (hA i j)
    simpa only [Finset.sum_apply] using memLp_finsetSum Finset.univ (fun j _ => hterm j)
  obtain ⟨m, hm, hmL, hmDL, hmconv, hmDconv⟩ := hu.smoothDensity_ball hR
  have hchain (k : ℕ) (i : Fin n) :
      coordinateDerivative (m k ∘ g) ((hm k).comp hg) i =
        (fun x => ∑ j : Fin n, A i j x • coordinateDerivative (m k) (hm k) j (g x)) := by
    funext x
    exact coordinateDerivative_comp_smooth (hm k) hg i x
  have hmW (k : ℕ) : MemW12 (ballDomain a R) (m k ∘ g)
      (fun x i => coordinateDerivative (m k ∘ g) ((hm k).comp hg) i x) := by
    apply memW12_of_contDiff (ballDomain a R) ((hm k).comp hg)
    · exact memLp_comp_smooth_inverse_ball (hmL k) hf hg.continuous hfg hgf hfball hgball
    · intro i
      rw [hchain k i]
      exact hsumL (fun x j => coordinateDerivative (m k) (hm k) j x) (hmDL k) i
  apply MemW12.of_L2_limit_ball a R hmW
    (memLp_comp_smooth_inverse_ball hu.2.1 hf hg.continuous hfg hgf hfball hgball)
    (hsumL Du hu.2.2)
  · have hlim := tendsto_eLpNorm_comp_smooth_inverse_ball
      (fun k => (hmL k).sub hu.2.1) hmconv hf hg.continuous hfg hgf hfball hgball
    exact hlim
  · intro i
    let v : Fin n → ℕ → Domain n → Ambient q := fun j k x =>
      A i j x • (coordinateDerivative (m k) (hm k) j (g x) - Du (g x) j)
    have hv (j : Fin n) (k : ℕ) : MemLp (v j k) 2 μ :=
      (memLp_comp_smooth_inverse_ball ((hmDL k j).sub (hu.2.2 j))
        hf hg.continuous hfg hgf hfball hgball).smul (r := (2 : ℝ≥0∞)) (hA i j)
    have hvlim (j : Fin n) : Tendsto (fun k => eLpNorm (v j k) 2 μ) atTop (𝓝 0) := by
      have hcomp := tendsto_eLpNorm_comp_smooth_inverse_ball
        (fun k => (hmDL k j).sub (hu.2.2 j)) (hmDconv j)
        hf hg.continuous hfg hgf hfball hgball
      exact tendsto_eLpNorm_smul_of_top (hA i j)
        (fun k => (memLp_comp_smooth_inverse_ball ((hmDL k j).sub (hu.2.2 j))
          hf hg.continuous hfg hgf hfball hgball).aestronglyMeasurable) hcomp
    have hlim := tendsto_eLpNorm_sum_L2 (fun j k => (hv j k).aestronglyMeasurable) hvlim
    have heq (k : ℕ) :
        (fun x => coordinateDerivative (m k ∘ g) ((hm k).comp hg) i x -
          ∑ j : Fin n, (fderiv ℝ g x (EuclideanSpace.single i 1)) j • Du (g x) j) =
          (fun x => ∑ j : Fin n, v j k x) := by
      funext x
      rw [hchain k i]
      dsimp only [v, A]
      simp only [smul_sub, Finset.sum_sub_distrib]
    exact hlim.congr (fun k => congrArg (fun w => eLpNorm w 2 μ) (heq k).symm)

end HarmonicMaps
