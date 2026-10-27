module

public import HarmonicMaps.Analysis.MollificationDistance
public import HarmonicMaps.Analysis.MollificationPointwise

/-!
# Joint uniform distance and pointwise gradient bounds

One positive constant, chosen before every target and map, controls both
source smoothing estimates. The original displayed weak gradient and the
literal fixed-radius integral are retained.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps

/-- Both source pointwise smoothing estimates share one dimension-only constant. -/
theorem uniformSmoothing_distance_gradient (n : ℕ) (hn : 2 ≤ n) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (q : ℕ) (N : CompactSmoothEmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
    MemW12Loc (ballDomain (0 : Domain n) 1) u Du →
    TakesValuesIn N (ballDomain (0 : Domain n) 1) u →
    IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du →
    dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤ →
    ∀ (h : PositiveRadius), h.val ≤ 1 / 4 →
    let m : Domain n → Ambient q := fun x =>
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • u (x - h.val • y)
    ∀ (x : Domain n), x ∈ Metric.ball (0 : Domain n) (1 / 2) →
      Metric.infDist (m x) N.carrierSet ^ 2 ≤
        C₀ * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal ∧
      hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1)) ≤
        C₀ * (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal *
          h.val ^ (-2 : ℤ) := by
  have hKpos := fixedMollifierKernelBound_pos n
  refine ⟨fixedMollifierKernelBound n * (2 : ℝ) ^ (n + 1) * 2 ^ (n - 2),
    by positivity, ?_⟩
  intro q N u Du hu hN hmin hE h hh
  dsimp only
  intro x hx
  refine ⟨hmin.sourceMollification_distance_bound hn N u Du hu hN hE h hh x hx, ?_⟩
  have hg := hmin.sourceMollification_pointwise_gradient_bound hn N u Du hu hN hE h hh x hx
  have hcp : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hcoeff : fixedMollifierKernelBound n * (2 : ℝ) ^ (n - 2) ≤
      fixedMollifierKernelBound n * (2 : ℝ) ^ (n + 1) * 2 ^ (n - 2) := by
    calc
      _ ≤ (fixedMollifierKernelBound n * (2 : ℝ) ^ (n - 2)) * 2 ^ (n + 1) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hcp
          (mul_nonneg hKpos.le (pow_nonneg (by norm_num) _))
      _ = _ := by ring
  exact hg.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff ENNReal.toReal_nonneg)
    (zpow_nonneg h.property.le _))

end HarmonicMaps
