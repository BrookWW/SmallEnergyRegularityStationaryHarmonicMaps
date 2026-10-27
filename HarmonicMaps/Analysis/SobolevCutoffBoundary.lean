module

public import HarmonicMaps.Analysis.SobolevCutoff
public import HarmonicMaps.Analysis.SobolevSmoothDensity

/-!
# Zero boundary values of compact smooth cutoffs

Multiplying whole-ball smooth approximants by a fixed compact smooth cutoff
gives compactly supported graph-norm approximants. Both error terms in the
product gradient converge in L2 to zero.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace HarmonicMaps

/-- A fixed essentially bounded scalar multiplier preserves Lp convergence to zero. -/
theorem tendsto_eLpNorm_smul_of_top {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {p : ℝ≥0∞}
    {v : ℕ → α → E} {χ : α → ℝ} (hχ : MemLp χ ∞ μ)
    (hv : ∀ k, AEStronglyMeasurable (v k) μ)
    (hlim : Tendsto (fun k => eLpNorm (v k) p μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x => χ x • v k x) p μ) atTop (𝓝 0) := by
  have hb : Tendsto (fun k => eLpNorm χ ∞ μ * eLpNorm (v k) p μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr hχ.eLpNorm_lt_top.ne)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => zero_le) (fun k => eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm p (hv k) χ)

/-- The classical coordinate derivative of a smooth scalar-vector product. -/
theorem coordinateDerivative_smul {n q : ℕ} {χ : Domain n → ℝ}
    {f : Domain n → Ambient q} (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (i : Fin n) (x : Domain n) :
    coordinateDerivative (fun y => χ y • f y) (hχ.smul hf) i x =
      coordinateDerivative χ hχ i x • f x + χ x • coordinateDerivative f hf i x := by
  simp only [coordinateDerivative, fderiv_fun_smul (hχ.differentiable (by simp) x)
    (hf.differentiable (by simp) x), add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, add_comm]

/-- A cutoff supported strictly inside a ball has zero boundary values in the
literal smooth graph-norm closure, with the product's actual weak gradient. -/
theorem MemW12.smoothCutoff_zeroBoundary_ball {n q : ℕ} {a : Domain n} {R : ℝ}
    (hR : 0 < R) {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) {χ : Domain n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Metric.ball a R) :
    HasZeroBoundaryValues (ballDomain a R) (fun x => χ x • u x)
      (fun x i => coordinateDerivative χ hχ i x • u x + χ x • Du x i) := by
  let μ := volume.restrict (Metric.ball a R)
  obtain ⟨m, hm, hmL, hmDL, hmconv, hmDconv⟩ := hu.smoothDensity_ball hR
  have hχL : MemLp χ ∞ μ := hχ.continuous.memLp_top_of_hasCompactSupport hcχ μ
  have hdχL (i : Fin n) : MemLp (coordinateDerivative χ hχ i) ∞ μ :=
    ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hcχ.fderiv_apply ℝ (EuclideanSpace.single i 1)) μ
  refine ⟨hu.smoothCutoff_ball hχ hcχ, (fun k x => χ x • m k x),
    (fun k => hχ.smul (hm k)), ?_, ?_, ?_⟩
  · intro k
    exact ⟨hcχ.smul_right, (tsupport_smul_subset_left χ (m k)).trans hsχ⟩
  · have hl := tendsto_eLpNorm_smul_of_top hχL
      (fun k => ((hmL k).sub hu.2.1).aestronglyMeasurable) hmconv
    change Tendsto (fun k => eLpNorm (fun x => χ x • m k x - χ x • u x) 2 μ) atTop (𝓝 0)
    simpa only [Pi.sub_apply, smul_sub] using hl
  · intro i
    have huerr (k : ℕ) : MemLp (fun x => coordinateDerivative χ hχ i x • (m k x - u x)) 2 μ :=
      ((hmL k).sub hu.2.1).smul (hdχL i)
    have hDerr (k : ℕ) : MemLp
        (fun x => χ x • (coordinateDerivative (m k) (hm k) i x - Du x i)) 2 μ :=
      ((hmDL k i).sub (hu.2.2 i)).smul hχL
    have hlimu := tendsto_eLpNorm_smul_of_top (hdχL i)
      (fun k => ((hmL k).sub hu.2.1).aestronglyMeasurable) hmconv
    have hlimD := tendsto_eLpNorm_smul_of_top hχL
      (fun k => ((hmDL k i).sub (hu.2.2 i)).aestronglyMeasurable) (hmDconv i)
    have hsum : Tendsto (fun k =>
        eLpNorm (fun x => coordinateDerivative χ hχ i x • (m k x - u x)) 2 μ +
        eLpNorm (fun x => χ x • (coordinateDerivative (m k) (hm k) i x - Du x i)) 2 μ)
        atTop (𝓝 0) := by
      simpa only [zero_add, Pi.sub_apply] using hlimu.add hlimD
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le)
    intro k
    have heq : (fun x => coordinateDerivative (fun y => χ y • m k y) (hχ.smul (hm k)) i x -
        (coordinateDerivative χ hχ i x • u x + χ x • Du x i)) =
        (fun x => coordinateDerivative χ hχ i x • (m k x - u x)) +
        (fun x => χ x • (coordinateDerivative (m k) (hm k) i x - Du x i)) := by
      funext x
      rw [coordinateDerivative_smul hχ (hm k)]
      simp only [Pi.add_apply, smul_sub]
      abel
    change eLpNorm (fun x => coordinateDerivative (fun y => χ y • m k y) (hχ.smul (hm k)) i x -
      (coordinateDerivative χ hχ i x • u x + χ x • Du x i)) 2 μ ≤ _
    rw [heq]
    exact eLpNorm_add_le (huerr k).aestronglyMeasurable (hDerr k).aestronglyMeasurable
      (by norm_num)

end HarmonicMaps
