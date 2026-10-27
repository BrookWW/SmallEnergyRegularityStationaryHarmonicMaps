module
public import HarmonicMaps.Analysis.UniformSmoothingBounds
public import HarmonicMaps.Frozen.OuterVariation
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import HarmonicMaps.Providers.UniformSmoothing

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace HarmonicMaps

theorem uniformSmoothing_complete (n : ℕ) (hn : 2 ≤ n) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (q : ℕ) (N : CompactSmoothEmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
    MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
    TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
    IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du →
    dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ →
    let S : Set ℝ := {k | ∃ p : N.Carrier, ∃ hp : p.val ∈ tubularTube q N,
      k = ‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖}
    ∀ (h : PositiveRadius), h.val ≤ 1 / 4 →
    let m : Domain n → Ambient q := fun x =>
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - h.val • y)
    ContDiffOn ℝ ∞ m (Metric.ball (0 : Domain n) (3 / 4)) ∧
    (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2),
      Metric.infDist (m x) N.carrierSet ^ 2 ≤
        C₀ * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal ∧
      hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1)) ≤
        C₀ * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal *
          h.val ^ (-2 : ℤ)) ∧
    IntegrableOn (fun x => hsNormSq (fun i =>
      fderiv ℝ m x (EuclideanSpace.single i 1)))
      (Metric.ball (0 : Domain n) (1 / 2)) ∧
    (∫ x in Metric.ball (0 : Domain n) (1 / 2),
      hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1))) ≤
      (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal ∧
    IntegrableOn (fun x => ‖Laplacian.laplacian m x‖)
      (Metric.ball (0 : Domain n) (1 / 2)) ∧
    (∫ x in Metric.ball (0 : Domain n) (1 / 2), ‖Laplacian.laplacian m x‖) ≤
      sSup S * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HarmonicMaps.Providers.UniformSmoothing.result n hn
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HarmonicMaps
end
-- FROZEN_ANCHOR_SUFFIX_END
