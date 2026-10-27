module

public import HolderToCK.Analysis.ClassicalPoisson
public import HolderToCK.Analysis.WeakPoissonLocality
public import HolderToCK.Analysis.Harmonic.WeakEnergyOrthogonality
public import HarmonicMaps.Analysis.PoissonSourceDirichlet
public import HarmonicMaps.Analysis.HarmonicMaximumDifference
public import HarmonicMaps.Analysis.HarmonicEnergyOrthogonality

/-! # Smooth boundary replacements and their contraction estimates

The actual Poisson solution of each smooth datum has its native zero-boundary
difference. Uniqueness on the closed ball gives the maximum estimate for any
smooth harmonic solution with those boundary values. Energy orthogonality for
the difference of two solutions gives contraction of the displayed gradients.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace HolderToCK

theorem smooth_harmonic_replacement_exists {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (m : Domain n → Ambient q) (hm : ContDiff ℝ ∞ m) :
    ∃ w : Domain n → Ambient q,
      ContDiffOn ℝ ∞ w (Metric.closedBall (0 : Domain n) R.val) ∧
      (∀ x ∈ Metric.sphere (0 : Domain n) R.val, w x = m x) ∧
      (∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian w x = 0) ∧
      MemW12 (ballDomain (0 : Domain n) R.val) w
        (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
      HasZeroBoundaryValues (ballDomain (0 : Domain n) R.val) (m - w)
        (fun x i => fderiv ℝ m x (EuclideanSpace.single i 1) -
          fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
      WeakPoissonOn (ballDomain (0 : Domain n) R.val)
        (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) (fun _ => 0) := by
  obtain ⟨v, _, hb, w, hwv, hws, hwh, _, hwW, hzero, _, _⟩ :=
    poisson_source_closedData_dirichlet_assembly hn R univ isOpen_univ
      (subset_univ _) m hm.contDiffOn
  have hEq := weakPoissonOn_of_contDiffOn_two (ballDomain (0 : Domain n) R.val)
    ((hws.mono Metric.ball_subset_closedBall).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))
  refine ⟨w, hws, ?_, hwh, hwW, hzero, ?_⟩
  · intro x hx
    exact (hwv ⟨x, Metric.sphere_subset_closedBall hx⟩).trans (hb ⟨x, hx⟩)
  · apply hEq.congr (EventuallyEq.refl _ _)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hwh x hx

theorem smooth_harmonic_norm_sub_le_boundary {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (m w : Domain n → Ambient q) (hm : ContDiff ℝ ∞ m)
    (hw : ContDiffOn ℝ ∞ w (Metric.closedBall (0 : Domain n) R.val))
    (hboundary : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, w x = m x)
    (hHarmonic : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian w x = 0)
    (c : Ambient q) (M : ℝ)
    (hbound : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, ‖m x - c‖ ≤ M) :
    ∀ x ∈ Metric.closedBall (0 : Domain n) R.val, ‖w x - c‖ ≤ M := by
  obtain ⟨v, _, _, z, _, hzs, hzh, hformula, _, _, huniq, _⟩ :=
    poisson_source_closedData_dirichlet_assembly hn R univ isOpen_univ
      (subset_univ _) m hm.contDiffOn
  have hsame := huniq w hw hboundary hHarmonic
  rw [← poisson_scaledPolar_eq_euclideanSphereArea hn R] at hformula
  have hinner : ∀ x ∈ Metric.ball (0 : Domain n) R.val, ‖w x - c‖ ≤ M := by
    intro x hx
    rw [hsame (Metric.ball_subset_closedBall hx), hformula x hx]
    exact poisson_scaledPolar_norm_sub_le_boundary hn R univ isOpen_univ
      (subset_univ _) m hm.contDiffOn c M hbound x hx
  have hcont : ContinuousOn (fun x : Domain n => ‖w x - c‖)
      (closure (Metric.ball (0 : Domain n) R.val)) := by
    rw [closure_ball 0 R.property.ne']
    exact (hw.continuousOn.sub continuousOn_const).norm
  intro x hx
  apply le_on_closure hinner hcont continuousOn_const
  rwa [closure_ball 0 R.property.ne']

theorem smooth_harmonic_replacements_sup_contraction {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (m₁ m₂ w₁ w₂ : Domain n → Ambient q)
    (hm₁ : ContDiff ℝ ∞ m₁) (hm₂ : ContDiff ℝ ∞ m₂)
    (hw₁ : ContDiffOn ℝ ∞ w₁ (Metric.closedBall (0 : Domain n) R.val))
    (hw₂ : ContDiffOn ℝ ∞ w₂ (Metric.closedBall (0 : Domain n) R.val))
    (hb₁ : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, w₁ x = m₁ x)
    (hb₂ : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, w₂ x = m₂ x)
    (hh₁ : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian w₁ x = 0)
    (hh₂ : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian w₂ x = 0)
    (M : ℝ) (hbound : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, ‖m₁ x - m₂ x‖ ≤ M) :
    ∀ x ∈ Metric.closedBall (0 : Domain n) R.val, ‖w₁ x - w₂ x‖ ≤ M := by
  have hh : ∀ x ∈ Metric.ball (0 : Domain n) R.val,
      Laplacian.laplacian (w₁ - w₂) x = 0 := by
    intro x hx
    have h₁ := (hw₁.mono Metric.ball_subset_closedBall).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)
    have h₂ := (hw₂.mono Metric.ball_subset_closedBall).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)
    rw [(h₁.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).laplacian_sub
      (h₂.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))), hh₁ x hx,
      hh₂ x hx, sub_self]
  simpa only [Pi.sub_apply, sub_zero] using
    smooth_harmonic_norm_sub_le_boundary hn R (m₁ - m₂) (w₁ - w₂)
      (hm₁.sub hm₂) (hw₁.sub hw₂)
      (fun x hx => by simp only [Pi.sub_apply, hb₁ x hx, hb₂ x hx]) hh 0 M
      (by simpa only [Pi.sub_apply, sub_zero] using hbound)

theorem smooth_harmonic_replacements_gradient_contraction {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (m₁ m₂ w₁ w₂ : Domain n → Ambient q)
    (hm₁ : ContDiff ℝ ∞ m₁) (hm₂ : ContDiff ℝ ∞ m₂)
    (hw₁ : ContDiffOn ℝ ∞ w₁ (Metric.closedBall (0 : Domain n) R.val))
    (hw₂ : ContDiffOn ℝ ∞ w₂ (Metric.closedBall (0 : Domain n) R.val))
    (hb₁ : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, w₁ x = m₁ x)
    (hb₂ : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, w₂ x = m₂ x)
    (hh₁ : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian w₁ x = 0)
    (hh₂ : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian w₂ x = 0) :
    (∫ x in Metric.ball (0 : Domain n) R.val,
      hsNormSq (fun i => fderiv ℝ w₁ x (EuclideanSpace.single i 1) -
        fderiv ℝ w₂ x (EuclideanSpace.single i 1))) ≤
      ∫ x in Metric.ball (0 : Domain n) R.val,
        hsNormSq (fun i => fderiv ℝ m₁ x (EuclideanSpace.single i 1) -
          fderiv ℝ m₂ x (EuclideanSpace.single i 1)) := by
  let m := m₁ - m₂
  let w := w₁ - w₂
  have hms : ContDiff ℝ ∞ m := hm₁.sub hm₂
  have hws : ContDiffOn ℝ ∞ w (Metric.closedBall (0 : Domain n) R.val) := hw₁.sub hw₂
  have hboundary : ∀ x ∈ Metric.sphere (0 : Domain n) R.val, m x = w x := by
    intro x hx
    simp only [m, w, Pi.sub_apply, hb₁ x hx, hb₂ x hx]
  have hzero := closed_smooth_zeroBoundaryDifference hn R m w
    hms.contDiffOn hws hboundary
  have hwh : ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian w x = 0 := by
    intro x hx
    have h₁ := (hw₁.mono Metric.ball_subset_closedBall).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)
    have h₂ := (hw₂.mono Metric.ball_subset_closedBall).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)
    rw [(h₁.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).laplacian_sub
      (h₂.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))), hh₁ x hx,
      hh₂ x hx, sub_self]
  have horth := closedBall_harmonic_energy_orthogonality R univ isOpen_univ
    (subset_univ _) m w hms.contDiffOn hws hwh hzero
  have hid := horth.1
  dsimp only at hid
  simp only [Pi.sub_apply] at hid
  have hnonneg : 0 ≤ ∫ x in Metric.ball (0 : Domain n) R.val,
      hsNormSq ((fun i => fderiv ℝ m x (EuclideanSpace.single i 1)) -
        (fun i => fderiv ℝ w x (EuclideanSpace.single i 1))) :=
    integral_nonneg (fun _ => hsNormSq_nonneg _)
  have hle : (∫ x in Metric.ball (0 : Domain n) R.val,
      hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1))) ≤
      ∫ x in Metric.ball (0 : Domain n) R.val,
        hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1)) := by
    linarith only [hid, hnonneg]
  have hmder (x : Domain n) : fderiv ℝ m x = fderiv ℝ m₁ x - fderiv ℝ m₂ x :=
    fderiv_sub ((hm₁.differentiable (by simp)).differentiableAt)
      ((hm₂.differentiable (by simp)).differentiableAt)
  have hwder (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
      fderiv ℝ w x = fderiv ℝ w₁ x - fderiv ℝ w₂ x :=
    fderiv_sub (((hw₁.mono Metric.ball_subset_closedBall).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
      (((hw₂.mono Metric.ball_subset_closedBall).contDiffAt
        (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp))
  convert hle using 1
  · apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    simp only [hwder x hx, sub_apply]
  · apply setIntegral_congr_fun measurableSet_ball
    intro x _
    simp only [hmder x, sub_apply]

end HolderToCK
end
