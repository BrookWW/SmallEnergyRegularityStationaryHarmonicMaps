module

public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Group.Measure

/-! # Actual restricted L2 bounds under interior translations -/

public section

open HarmonicMaps MeasureTheory Set Metric

namespace StationaryHarmonicMaps.Analysis

/-- A translation within the actual radius margin stays in the outer ball. -/
theorem add_mem_ball_of_norm_le_margin {n : ℕ} {a x h : Domain n} {r R : ℝ}
    (hx : x ∈ Metric.ball a r) (hh : ‖h‖ ≤ R - r) : x + h ∈ Metric.ball a R := by
  have hshift : dist (x + h) x = ‖h‖ := by rw [dist_eq_norm, add_sub_cancel_left]
  change dist (x + h) a < R
  calc
    _ ≤ dist (x + h) x + dist x a := dist_triangle _ _ _
    _ = ‖h‖ + dist x a := by rw [hshift]
    _ < ‖h‖ + r := by
      have hdist : dist x a < r := hx
      linarith
    _ ≤ R := by linarith

/-- Restricted L2 data give actual translated L2 data and the same seminorm bound. -/
theorem inner_translate_memLp_and_eLpNorm_le {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : Domain n → E) (a h : Domain n) {r R : ℝ}
    (hh : ‖h‖ ≤ R - r) (hf : MemLp f 2 (volume.restrict (Metric.ball a R))) :
    MemLp (fun x => f (x + h)) 2 (volume.restrict (Metric.ball a r)) ∧
      eLpNorm (fun x => f (x + h)) 2 (volume.restrict (Metric.ball a r)) ≤
        eLpNorm f 2 (volume.restrict (Metric.ball a R)) := by
  classical
  let F : Domain n → E := (Metric.ball a R).indicator f
  have hF : MemLp F 2 volume := (memLp_indicator_iff_restrict measurableSet_ball).mpr hf
  have hMP : MeasurePreserving (fun x : Domain n => x + h) volume volume :=
    measurePreserving_add_right volume h
  have hshift : MemLp (fun x => F (x + h)) 2 volume := hF.comp_measurePreserving hMP
  have heq : (fun x => F (x + h)) =ᵐ[volume.restrict (Metric.ball a r)]
      (fun x => f (x + h)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact indicator_of_mem (add_mem_ball_of_norm_le_margin hx hh) f
  have hrestricted : MemLp (fun x => F (x + h)) 2 (volume.restrict (Metric.ball a r)) :=
    hshift.mono_measure Measure.restrict_le_self
  have hnormShift : eLpNorm (fun x => F (x + h)) 2 volume = eLpNorm F 2 volume := by
    exact eLpNorm_comp_measurePreserving (g := F) (f := fun x : Domain n => x + h)
      (p := 2) (μ := volume) (ν := volume) hF.aestronglyMeasurable hMP
  have hnormF : eLpNorm F 2 volume = eLpNorm f 2 (volume.restrict (Metric.ball a R)) := by
    exact eLpNorm_indicator_eq_eLpNorm_restrict (f := f) (p := 2) (μ := volume)
      measurableSet_ball
  refine ⟨(memLp_congr_ae heq).mp hrestricted, ?_⟩
  calc
    _ = eLpNorm (fun x => F (x + h)) 2 (volume.restrict (Metric.ball a r)) :=
      eLpNorm_congr_ae heq.symm
    _ ≤ eLpNorm (fun x => F (x + h)) 2 volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm F 2 volume := hnormShift
    _ = _ := hnormF

end StationaryHarmonicMaps.Analysis

end
