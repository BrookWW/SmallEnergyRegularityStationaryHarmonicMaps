module

public import StationaryHarmonicMaps.Analysis.GrandKernelCutoffAverage

/-!
# Actual radius caps inside a finite-volume set

In positive dimension the true volume of every contained ball grows
with its radius. A finite original volume therefore gives one global
radius cap and forces the complement to be nonempty. No boundedness
of the original set is assumed.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original finite volume in positive dimension produces a global contained-ball radius cap and a genuine point outside the set. -/
theorem exists_ball_radius_cap_of_finite_volume (n : ℕ) (hn : 0<n)
    (S : Set (Domain n)) (hS : volume S≠∞) :
    ∃ R : ℝ,0<R ∧ (∀ (a : Domain n) (r : ℝ),0<r → Metric.ball a r⊆S → r≤R) ∧ Sᶜ.Nonempty := by
  let V : ℝ := volume.real (Metric.ball (0 : Domain n) 1)
  have hV : 0<V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume (0 : Domain n) (by norm_num : (0 : ℝ)<1)).ne' measure_ball_ne_top
  let R := 1+volume.real S/V
  have hR : 0<R := by dsimp only [R];positivity
  have hCap (a : Domain n) (r : ℝ) (hr : 0<r) (hs : Metric.ball a r⊆S) : r≤R := by
    by_contra hnot
    have hRr : R<r := lt_of_not_ge hnot
    have hOne : 1≤r := by
      have H : 0≤volume.real S/V := div_nonneg ENNReal.toReal_nonneg hV.le
      dsimp only [R] at hRr
      linarith only [H,hRr]
    have hMass : volume.real (Metric.ball a r)≤volume.real S := ENNReal.toReal_mono hS (measure_mono hs)
    rw [HolderToCK.ball_volume_real a hr] at hMass
    have hPow : r≤r^n := le_self_pow₀ hOne hn.ne'
    have hLinear : r*V≤volume.real S :=
      (mul_le_mul_of_nonneg_right hPow hV.le).trans hMass
    have H : r≤volume.real S/V := (le_div_iff₀ hV).mpr hLinear
    dsimp only [R] at hRr
    linarith only [H,hRr]
  have hComp : Sᶜ.Nonempty := by
    by_contra hnone
    have hAll (x : Domain n) : x∈S := by
      by_contra hx
      exact hnone ⟨x,hx⟩
    have H := hCap (0 : Domain n) (R+1) (by linarith) (fun x _=>hAll x)
    linarith only [H]
  exact ⟨R,hR,hCap,hComp⟩

end StationaryHarmonicMaps.Analysis

end
