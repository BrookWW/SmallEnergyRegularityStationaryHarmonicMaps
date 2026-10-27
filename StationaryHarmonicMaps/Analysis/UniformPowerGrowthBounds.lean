module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds

/-! # External-center bounds from actual uniform power growth

A ball meeting the original set lies, on that set, in a doubled ball
centered at an actual original point. The fields are genuine L2 columns.
-/

public section

open HarmonicMaps MeasureTheory Filter Set

namespace StationaryHarmonicMaps.Analysis

/-- Original all-radius truncated energy growth controls every external center with its exact doubled-radius factor. -/
theorem integral_hsNormSq_inter_le_of_uniform_power_growth {n q : ℕ}
    (F : Domain n → Gradient n q) (D : Set (Domain n))
    (hF : ∀ i,MemLp (fun x => F x i) 2 (volume.restrict D))
    (K ν : ℝ) (hK : 0≤K)
    (hGrowth : ∀ (x : Domain n),x∈D → ∀ r : ℝ,0<r →
      (∫ y in Metric.ball x r∩D,hsNormSq (F y))≤K*r^ν)
    (a : Domain n) {r : ℝ} (hr : 0<r) :
    (∫ y in Metric.ball a r∩D,hsNormSq (F y))≤(2 : ℝ)^ν*K*r^ν := by
  let S := Metric.ball a r∩D
  by_cases hEmpty : S=∅
  · change (∫ y in S,hsNormSq (F y))≤_
    rw [hEmpty,setIntegral_empty]
    positivity
  · obtain ⟨x,hx⟩ := nonempty_iff_ne_empty.mpr hEmpty
    have hSub : S⊆Metric.ball x (2*r)∩D := by
      intro y hy
      refine ⟨?_,hy.2⟩
      have H := dist_triangle y a x
      have Hx : dist x a<r := hx.1
      have Hy : dist y a<r := hy.1
      rw [dist_comm a x] at H
      exact Metric.mem_ball.mpr (by linarith only [H,Hx,Hy])
    have hFullI : IntegrableOn (fun y => hsNormSq (F y)) D volume := integrable_hsNormSq_of_columns F hF
    have hFI : IntegrableOn (fun y => hsNormSq (F y)) (Metric.ball x (2*r)∩D) volume :=
      hFullI.mono_set inter_subset_right
    calc
      _ ≤ ∫ y in Metric.ball x (2*r)∩D,hsNormSq (F y) :=
        setIntegral_mono_set hFI (Eventually.of_forall fun _ => hsNormSq_nonneg _)
          (Eventually.of_forall fun _ hy => hSub hy)
      _ ≤ K*(2*r)^ν := hGrowth x hx.2 (2*r) (by positivity)
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤2) hr.le];ring

end StationaryHarmonicMaps.Analysis
end
