module

public import HarmonicMaps.Analysis.AffineSobolevApproximation
public import HarmonicMaps.Analysis.InteriorSobolevApproximation
public import HarmonicMaps.Analysis.SmoothWeakGradient
public import HarmonicMaps.SobolevRestriction
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Euclidean smooth density on a whole ball

An inward affine pullback is defined on a larger ball. Interior mollification
of that pullback gives smooth maps on the whole original ball. The affine and
mollification errors are combined for the map and the same weak-gradient
columns, and a sequence of vanishing tolerances gives simultaneous L2 density.
The approximants take values in the Euclidean ambient space.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace HarmonicMaps

noncomputable section

/-- Simultaneous approximation on the whole ball, including its boundary layer. -/
theorem MemW12.exists_smooth_approximation_ball {n q : ℕ}
    {a : Domain n} {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ m : Domain n → Ambient q, ∃ hm : ContDiff ℝ ∞ m,
      MemLp m 2 (volume.restrict (Metric.ball a R)) ∧
      (∀ i : Fin n, MemLp (coordinateDerivative m hm i) 2
        (volume.restrict (Metric.ball a R))) ∧
      eLpNorm (m - u) 2 (volume.restrict (Metric.ball a R)) ≤ ε ∧
      ∀ i : Fin n, eLpNorm (fun x => coordinateDerivative m hm i x - Du x i)
        2 (volume.restrict (Metric.ball a R)) ≤ ε := by
  let δ : ℝ≥0∞ := ε / 2
  have hδ : 0 < δ := ENNReal.div_pos hε.ne' (by norm_num)
  have hsum : δ + δ = ε := by
    rw [← two_mul]
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  obtain ⟨t, ht, ht1, hv, hvMap, hvGrad⟩ :=
    hu.exists_inward_affine_approximation_ball δ hδ
  have hLarge : R < R / t := (lt_div_iff₀ ht).mpr (by nlinarith)
  have hvOriginal : MemW12 (ballDomain a R) (fun x => u (ballAffine a t x))
      (fun x i => t • Du (ballAffine a t x) i) :=
    hv.to_memW12Loc.memW12_ball (Metric.closedBall_subset_ball hLarge)
  obtain ⟨m, hm, hmL, hmDL, hmError, hmDError⟩ :=
    hv.exists_smooth_approximation_inner_ball hLarge δ hδ
  refine ⟨m, hm, hmL, hmDL, ?_, ?_⟩
  · have hsplit : m - u =
        (m - (fun x => u (ballAffine a t x))) +
          ((fun x => u (ballAffine a t x)) - u) := by
      funext x
      simp only [Pi.add_apply, Pi.sub_apply]
      abel
    rw [hsplit]
    calc
      eLpNorm ((m - (fun x => u (ballAffine a t x))) +
          ((fun x => u (ballAffine a t x)) - u)) 2
          (volume.restrict (Metric.ball a R)) ≤
          eLpNorm (m - (fun x => u (ballAffine a t x))) 2
            (volume.restrict (Metric.ball a R)) +
          eLpNorm ((fun x => u (ballAffine a t x)) - u) 2
            (volume.restrict (Metric.ball a R)) :=
        eLpNorm_add_le (hmL.sub hvOriginal.2.1).aestronglyMeasurable
          (hvOriginal.2.1.sub hu.2.1).aestronglyMeasurable (by norm_num)
      _ ≤ δ + δ := add_le_add hmError hvMap
      _ = ε := hsum
  · intro i
    have hsplit : (fun x => coordinateDerivative m hm i x - Du x i) =
        (fun x => coordinateDerivative m hm i x - t • Du (ballAffine a t x) i) +
          (fun x => t • Du (ballAffine a t x) i - Du x i) := by
      funext x
      simp only [Pi.add_apply]
      abel
    rw [hsplit]
    calc
      eLpNorm ((fun x => coordinateDerivative m hm i x - t • Du (ballAffine a t x) i) +
          (fun x => t • Du (ballAffine a t x) i - Du x i)) 2
          (volume.restrict (Metric.ball a R)) ≤
          eLpNorm (fun x => coordinateDerivative m hm i x - t • Du (ballAffine a t x) i)
            2 (volume.restrict (Metric.ball a R)) +
          eLpNorm (fun x => t • Du (ballAffine a t x) i - Du x i) 2
            (volume.restrict (Metric.ball a R)) :=
        eLpNorm_add_le ((hmDL i).sub (hvOriginal.2.2 i)).aestronglyMeasurable
          ((hvOriginal.2.2 i).sub (hu.2.2 i)).aestronglyMeasurable (by norm_num)
      _ ≤ δ + δ := add_le_add (hmDError i) (hvGrad i)
      _ = ε := hsum

/-- Smooth Euclidean maps and their classical gradient columns are dense in
the finite W1,2 graph norm on any positive-radius ball. -/
theorem MemW12.smoothDensity_ball {n q : ℕ} {a : Domain n} {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) :
    ∃ m : ℕ → Domain n → Ambient q, ∃ hm : ∀ k, ContDiff ℝ ∞ (m k),
      (∀ k, MemLp (m k) 2 (volume.restrict (Metric.ball a R))) ∧
      (∀ k (i : Fin n), MemLp (coordinateDerivative (m k) (hm k) i) 2
        (volume.restrict (Metric.ball a R))) ∧
      Tendsto (fun k => eLpNorm (m k - u) 2 (volume.restrict (Metric.ball a R)))
        atTop (𝓝 0) ∧
      ∀ i : Fin n, Tendsto (fun k => eLpNorm
        (fun x => coordinateDerivative (m k) (hm k) i x - Du x i) 2
        (volume.restrict (Metric.ball a R))) atTop (𝓝 0) := by
  have hε (k : ℕ) : 0 < ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by positivity
  choose m hm hmL hmDL hmError hmDError using
    fun k : ℕ => hu.exists_smooth_approximation_ball hR _ (hε k)
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨m, hm, hmL, hmDL, ?_, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) hmError
  · intro i
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) (fun k => hmDError k i)

/-- The approximating maps belong to the literal finite Sobolev space, with
their genuine classical derivatives as weak gradients. -/
theorem MemW12.smoothDensity_memW12_ball {n q : ℕ} {a : Domain n} {R : ℝ}
    (hR : 0 < R) {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) :
    ∃ m : ℕ → Domain n → Ambient q, ∃ hm : ∀ k, ContDiff ℝ ∞ (m k),
      (∀ k, MemW12 (ballDomain a R) (m k)
        (fun x i => coordinateDerivative (m k) (hm k) i x)) ∧
      Tendsto (fun k => eLpNorm (m k - u) 2 (volume.restrict (Metric.ball a R)))
        atTop (𝓝 0) ∧
      ∀ i : Fin n, Tendsto (fun k => eLpNorm
        (fun x => coordinateDerivative (m k) (hm k) i x - Du x i) 2
        (volume.restrict (Metric.ball a R))) atTop (𝓝 0) := by
  obtain ⟨m, hm, hmL, hmDL, hconv, hDconv⟩ := hu.smoothDensity_ball hR
  exact ⟨m, hm, (fun k => memW12_of_contDiff (ballDomain a R) (hm k) (hmL k)
    (hmDL k)), hconv, hDconv⟩

end
end HarmonicMaps
