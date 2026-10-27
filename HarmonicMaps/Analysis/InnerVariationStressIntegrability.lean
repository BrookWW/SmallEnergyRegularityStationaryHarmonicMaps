module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integrability of the actual inner-variation stress

The products of two displayed gradient columns are L1 by the L2 inner-product
estimate. Smooth derivative coefficients are bounded on the closed ball,
so every term of the source stationarity integrand is genuinely integrable.
-/

public section

open MeasureTheory Set
open scoped ContDiff BigOperators

namespace HarmonicMaps

private theorem integrable_inner_memLp {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

/-- Every actual Sobolev inner-variation stress integrand is L1 on its ball. -/
theorem MemW12.integrable_innerVariation_stress {n q : ℕ} {a : Domain n} {R : ℝ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) {ζ : Domain n → Domain n}
    (hζ : ContDiff ℝ ∞ ζ) :
    IntegrableOn (fun x => hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i 1)) i) -
      2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (Du x i) (Du x j) *
          (fderiv ℝ ζ x (EuclideanSpace.single i 1)) j) (Metric.ball a R) := by
  have hc (i j : Fin n) : Continuous (fun x => (fderiv ℝ ζ x (EuclideanSpace.single i 1)) j) :=
    (EuclideanSpace.proj j).continuous.comp
      ((hζ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdiv : Continuous (fun x => ∑ i : Fin n,
      (fderiv ℝ ζ x (EuclideanSpace.single i 1)) i) :=
    continuous_finsetSum Finset.univ (fun i _ => hc i i)
  have he : IntegrableOn (fun x => hsNormSq (Du x) *
      (∑ i : Fin n, (fderiv ℝ ζ x (EuclideanSpace.single i 1)) i)) (Metric.ball a R) :=
    IntegrableOn.mul_continuousOn_of_subset hu.integrable_hsNormSq hdiv.continuousOn
      measurableSet_ball (isCompact_closedBall a R) Metric.ball_subset_closedBall
  have hterm (i j : Fin n) : IntegrableOn (fun x =>
      inner ℝ (Du x i) (Du x j) * (fderiv ℝ ζ x (EuclideanSpace.single i 1)) j)
      (Metric.ball a R) :=
    IntegrableOn.mul_continuousOn_of_subset
      (integrable_inner_memLp (hu.2.2 i) (hu.2.2 j)) (hc i j).continuousOn
      measurableSet_ball (isCompact_closedBall a R) Metric.ball_subset_closedBall
  exact he.sub ((integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hterm i j))).const_mul 2)

end HarmonicMaps
