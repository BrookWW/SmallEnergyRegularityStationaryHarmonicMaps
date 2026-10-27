module

public import HolderToCK.Foundation.HolderBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Continuity from the literal Holder estimate -/

public section

open HarmonicMaps Filter
open scoped Topology

namespace HolderToCK

theorem HolderBoundOn.continuousOn {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {s : Set (Domain n)} {f : Domain n → E} {α H : ℝ}
    (h : HolderBoundOn s f α H) (hα : 0 < α) : ContinuousOn f s := by
  intro x hx
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  have hAt : ContinuousAt (fun y : Domain n => H * Real.rpow (dist y x) α) x :=
    continuousAt_const.mul ((continuousAt_id.dist continuousAt_const).rpow_const (Or.inr hα.le))
  have hlim : Tendsto (fun y : Domain n => H * Real.rpow (dist y x) α) (𝓝 x) (𝓝 0) := by
    simpa only [dist_self, Real.rpow_eq_pow, Real.zero_rpow hα.ne', mul_zero] using hAt.tendsto
  obtain ⟨δ, hδ, hsmall⟩ := Metric.eventually_nhds_iff.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨δ, hδ, ?_⟩
  intro y hy hxy
  rw [dist_eq_norm]
  exact (h y hy x hx).trans_lt (hsmall hxy)

theorem LocallyHolderOn.continuousOn {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {Ω : OpenDomain n} {f : Domain n → E} (h : LocallyHolderOn Ω f) :
    ContinuousOn f Ω.val := by
  intro x hx
  obtain ⟨r, _, α, H, hα, _, _, hbound⟩ := h x hx
  exact ((hbound.continuousOn hα).continuousAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self r.property))).continuousWithinAt

end HolderToCK
end
