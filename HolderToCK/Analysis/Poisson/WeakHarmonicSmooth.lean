module

public import HolderToCK.Analysis.Poisson.WeakHarmonicMean
public import HolderToCK.Analysis.Harmonic.RadialMollifier
public import HarmonicMaps.SobolevRestriction

/-! # Smoothness of the same continuous weak harmonic map

Spherical means identify the continuous weak solution with a fixed smooth
radial convolution near each interior point. This gives its classical
smoothness and its pointwise zero Laplacian, with no new representative.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace HolderToCK

theorem WeakPoissonOn.harmonic_mollification_eq_on_inner_ball
    {n q : ℕ} (hn : 2 ≤ n) (a : Domain n) (R : PositiveRadius)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R.val) u Du)
    (hcont : ContinuousOn u (Metric.ball a R.val))
    (hEq : WeakPoissonOn (ballDomain a R.val) Du (fun _ => 0)) :
    EqOn (euclideanMollification (ballDomain a R.val) u hu.integrable_ball
      ⟨R.val / 8, div_pos R.property (by norm_num)⟩) u (Metric.ball a (R.val / 8)) := by
  let h : PositiveRadius := ⟨R.val / 8, div_pos R.property (by norm_num)⟩
  intro y hy
  have hyR : dist y a < R.val / 8 := hy
  have hclosedY : Metric.closedBall y (R.val / 2) ⊆ Metric.ball a R.val := by
    intro z hz
    have hzy : dist z y ≤ R.val / 2 := hz
    change dist z a < R.val
    exact lt_of_le_of_lt (dist_triangle z y a)
      (by linarith only [hzy, hyR, R.property])
  have hsubY : (ballDomain y (R.val / 2)).val ⊆ (ballDomain a R.val).val :=
    Metric.ball_subset_closedBall.trans hclosedY
  have huY := hu.to_memW12Loc.memW12_ball hclosedY
  have hEqY := hEq.mono hsubY
  have hcontY := hcont.mono hsubY
  have hclosedh : Metric.closedBall y h.val ⊆ Metric.ball a R.val :=
    (Metric.closedBall_subset_closedBall
      (show h.val ≤ R.val / 2 by dsimp only [h]; linarith only [R.property])).trans hclosedY
  have hmean : ∀ r ∈ Ioo (0 : ℝ) h.val,
      (∫ θ : Metric.sphere (0 : Domain n) 1, u (y + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) =
      (volume : Measure (Domain n)).toSphere.real univ • u y := by
    intro r hr
    exact hEqY.harmonic_sphere_integral_eq_of_continuous hn y huY hcontY ⟨r, hr.1⟩
      (by dsimp only [h] at hr; linarith only [hr.2, R.property])
  exact euclideanMollification_eq_of_sphereMean (by omega : 0 < n)
    (ballDomain a R.val) y h u hu.integrable_ball
    (Metric.ball_subset_closedBall.trans hclosedh) (hcont.mono hclosedh) hmean

theorem WeakPoissonOn.contDiffOn_of_continuous_weak_harmonic
    {n q : ℕ} (hn : 2 ≤ n) (Ω : OpenDomain n)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du) (hcont : ContinuousOn u Ω.val)
    (hEq : WeakPoissonOn Ω Du (fun _ => 0)) :
    ContDiffOn ℝ ∞ u Ω.val ∧ ∀ x ∈ Ω.val, Laplacian.laplacian u x = 0 := by
  have hlocal (x : Domain n) (hx : x ∈ Ω.val) :
      ContDiffAt ℝ ∞ u x ∧ Laplacian.laplacian u x = 0 := by
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (Ω.property.mem_nhds hx)
    let R : PositiveRadius := ⟨ρ / 2, half_pos hρ⟩
    have hclosed : Metric.closedBall x R.val ⊆ Ω.val :=
      (Metric.closedBall_subset_ball (half_lt_self hρ)).trans hball
    have hsub : (ballDomain x R.val).val ⊆ Ω.val :=
      Metric.ball_subset_closedBall.trans hclosed
    have huB := hu.memW12_ball hclosed
    have hEqB := hEq.mono hsub
    let h : PositiveRadius := ⟨R.val / 8, div_pos R.property (by norm_num)⟩
    let M := euclideanMollification (ballDomain x R.val) u huB.integrable_ball h
    have hsame := hEqB.harmonic_mollification_eq_on_inner_ball hn x R huB (hcont.mono hsub)
    have hnhds : M =ᶠ[𝓝 x] u := by
      filter_upwards [Metric.ball_mem_nhds x (by positivity : 0 < R.val / 8)] with y hy
      exact hsame hy
    have hM := euclideanMollification_contDiff (ballDomain x R.val) u huB.integrable_ball h
    have hLap := hEqB.mollification_laplacian_ball huB 0
      (Eventually.of_forall fun y => by simp only [norm_zero, zero_mul, le_refl]) h
      (show R.val / 8 + h.val / 2 ≤ R.val by dsimp only [h]; linarith only [R.property])
    refine ⟨hM.contDiffAt.congr_of_eventuallyEq hnhds.symm, ?_⟩
    rw [← (InnerProductSpace.laplacian_congr_nhds hnhds).eq_of_nhds]
    simpa only [smul_zero, integral_zero] using
      hLap.2 x (Metric.mem_ball_self (by positivity : 0 < R.val / 8))
  refine ⟨?_, fun x hx => (hlocal x hx).2⟩
  intro x hx
  exact (hlocal x hx).1.contDiffWithinAt

end HolderToCK
end
