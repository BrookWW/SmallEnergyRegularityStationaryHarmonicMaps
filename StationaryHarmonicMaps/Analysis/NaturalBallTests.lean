module

public import StationaryHarmonicMaps.Analysis.NaturalCoulombTests

/-!
# Actual all-native natural tests on arbitrary balls

Whole-ball smooth graph density preserves the original L2 flux pairing
against every native gradient. The test graph has arbitrary boundary
values; the actual ball center and radius are retained.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual smooth natural tests on a positive-radius ball imply every native W1,2 gradient test there. -/
theorem native_ball_tests_of_all_smooth_tests {n q : ℕ}
    (a : Domain n) {r : ℝ} (hr : 0 < r)
    (F : Domain n → Gradient n q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a r)))
    (hzero : ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
      (∫ x in Metric.ball a r,
        ∑ i : Fin n, inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) = 0)
    (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
    (hψ : MemW12 (ballDomain a r) ψ Dψ) :
    IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (F x i) (Dψ x i))
      (Metric.ball a r) volume ∧
    (∫ x in Metric.ball a r, ∑ i : Fin n, inner ℝ (F x i) (Dψ x i)) = 0 := by
  let μ := volume.restrict (Metric.ball a r)
  have hI := integrable_column_pairing μ F Dψ hF hψ.2.2
  obtain ⟨m, hm, _hmL, hmD, _hconv, hDconv⟩ := hψ.smoothDensity_ball hr
  have hlim (i : Fin n) : Tendsto (fun k => ∫ x, inner ℝ (F x i)
      (coordinateDerivative (m k) (hm k) i x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (F x i) (Dψ x i) ∂μ)) := by
    apply HolderToCK.tendsto_integral_inner_of_L2 (fun k => hmD k i) (hψ.2.2 i) (hF i)
    exact hDconv i
  have hsum : Tendsto (fun k => ∑ i : Fin n, ∫ x, inner ℝ (F x i)
      (coordinateDerivative (m k) (hm k) i x) ∂μ) atTop
      (𝓝 (∑ i : Fin n, ∫ x, inner ℝ (F x i) (Dψ x i) ∂μ)) :=
    tendsto_finsetSum _ fun i _ => hlim i
  have hmzero (k : ℕ) : (∑ i : Fin n, ∫ x, inner ℝ (F x i)
      (coordinateDerivative (m k) (hm k) i x) ∂μ) = 0 := by
    rw [← integral_finsetSum _ (fun i _ =>
      HolderToCK.integrable_inner_of_memLp_two (hF i) (hmD k i))]
    exact hzero (m k) (hm k)
  have hfun : (fun k => ∑ i : Fin n, ∫ x, inner ℝ (F x i)
      (coordinateDerivative (m k) (hm k) i x) ∂μ) = (fun _ : ℕ => (0 : ℝ)) :=
    funext hmzero
  rw [hfun] at hsum
  have H := tendsto_nhds_unique hsum tendsto_const_nhds
  refine ⟨hI, ?_⟩
  rw [integral_finsetSum _ (fun i _ =>
    HolderToCK.integrable_inner_of_memLp_two (hF i) (hψ.2.2 i))]
  exact H

end StationaryHarmonicMaps.Analysis

end
