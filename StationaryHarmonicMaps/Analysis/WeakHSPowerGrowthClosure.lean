module

public import StationaryHarmonicMaps.Analysis.WeakHSMorreyClosure

/-!
# Truncated power growth of the actual weak HS limit

Indicator L2 tests restrict the original full weak convergence to each
truncated ball. The actual HS weak energy bound then preserves the original
uniform real-power estimate for the same limit, without local lower
semicontinuity or integral convergence as additional premises.
-/

public section

open HarmonicMaps MeasureTheory Set Filter Metric
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

private theorem integral_inner_indicator_restrict {n q : ℕ}
    (D S : Set (Domain n)) (hS : MeasurableSet S) (hSub : S ⊆ D)
    (f g : Domain n → Ambient q) :
    (∫ x in D, inner ℝ (f x) (S.indicator g x)) =
      ∫ x in S, inner ℝ (f x) (g x) := by
  have hEq : (fun x => inner ℝ (f x) (S.indicator g x)) =
      S.indicator (fun x => inner ℝ (f x) (g x)) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, inner_zero_right]
  rw [hEq, integral_indicator hS, Measure.restrict_restrict hS,
    inter_eq_left.mpr hSub]

/-- Full actual weak L2 column convergence preserves every original
truncated-ball power bound of the same HS field. -/
theorem power_growth_bound_of_weak_L2_limit {n q : ℕ}
    (D : Set (Domain n)) (hD : MeasurableSet D)
    (F : ℕ → Domain n → Gradient n q) (G : Domain n → Gradient n q)
    (hF : ∀ k i, MemLp (fun x => F k x i) 2 (volume.restrict D))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict D))
    (hWeak : ∀ (i : Fin n) (g : Domain n → Ambient q),
      MemLp g 2 (volume.restrict D) →
      Tendsto (fun k => ∫ x in D, inner ℝ (F k x i) (g x)) atTop
        (𝓝 (∫ x in D, inner ℝ (G x i) (g x))))
    (ν K : ℝ) (hK : 0 ≤ K)
    (hGrowth : ∀ k a, a ∈ D → ∀ r : ℝ, 0 < r →
      (∫ x in ball a r ∩ D, hsNormSq (F k x)) ≤ K * r ^ ν) :
    ∀ a, a ∈ D → ∀ r : ℝ, 0 < r →
      IntegrableOn (fun x => hsNormSq (G x)) (ball a r ∩ D) volume ∧
      (∫ x in ball a r ∩ D, hsNormSq (G x)) ≤ K * r ^ ν := by
  intro a ha r hr
  let S := ball a r ∩ D
  have hS : MeasurableSet S := measurableSet_ball.inter hD
  have hSub : S ⊆ D := inter_subset_right
  have hFS (k : ℕ) (i : Fin n) : MemLp (fun x => F k x i) 2 (volume.restrict S) :=
    (hF k i).mono_measure (Measure.restrict_mono_set volume hSub)
  have hGS (i : Fin n) : MemLp (fun x => G x i) 2 (volume.restrict S) :=
    (hG i).mono_measure (Measure.restrict_mono_set volume hSub)
  have hLocal (i : Fin n) (g : Domain n → Ambient q)
      (hg : MemLp g 2 (volume.restrict S)) :
      Tendsto (fun k => ∫ x in S, inner ℝ (F k x i) (g x)) atTop
        (𝓝 (∫ x in S, inner ℝ (G x i) (g x))) := by
    have hIndicator : MemLp (S.indicator g) 2 (volume.restrict D) := by
      apply (memLp_indicator_iff_restrict hS).mpr
      simpa only [Measure.restrict_restrict hS, inter_eq_left.mpr hSub] using hg
    have H := hWeak i (S.indicator g) hIndicator
    simpa only [integral_inner_indicator_restrict D S hS hSub] using H
  refine ⟨integrable_hsNormSq_of_columns G hGS, ?_⟩
  exact integral_hsNormSq_weak_limit_le (volume.restrict S) F G hFS hGS hLocal
    (mul_nonneg hK (Real.rpow_nonneg hr.le ν)) (fun k => hGrowth k a ha r hr)

end StationaryHarmonicMaps.Analysis

end
