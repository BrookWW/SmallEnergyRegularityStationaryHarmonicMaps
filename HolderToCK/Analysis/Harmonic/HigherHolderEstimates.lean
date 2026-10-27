module

public import HolderToCK.Analysis.Harmonic.DerivativeEstimates
public import HolderToCK.Analysis.Bootstrap.FirstDerivativeHolder

/-! # Derivative bounds on arbitrary nested harmonic balls

Interior derivative estimates apply in the ball centered at each evaluation
point with radius equal to the domain margin. One more derivative controls
the full Holder exponent on the convex inner ball.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK

theorem harmonic_iteratedFDeriv_inner_sup_bound (n k : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (R : PositiveRadius)
      (s : ℝ) (f : Domain n → Ambient q) (M : ℝ),
      s < R.val →
      ContDiffOn ℝ ∞ f (Metric.ball a R.val) →
      (∀ z ∈ Metric.ball a R.val, Laplacian.laplacian f z = 0) →
      (∀ z ∈ Metric.ball a R.val, ‖f z‖ ≤ M) →
      ∀ x ∈ Metric.ball a s,
        ‖iteratedFDeriv ℝ k f x‖ ≤ C * ((R.val - s) ^ k)⁻¹ * M := by
  obtain ⟨C, hC, hbound⟩ := harmonic_iteratedFDeriv_sup_bound n k hn
  refine ⟨C, hC, ?_⟩
  intro q a R s f M hs hf hh hM x hx
  let d : PositiveRadius := ⟨R.val - s, sub_pos.mpr hs⟩
  have hsub : Metric.ball x d.val ⊆ Metric.ball a R.val := by
    intro z hz
    have hzx : dist z x < R.val - s := hz
    have hxa : dist x a < s := hx
    change dist z a < R.val
    exact lt_of_le_of_lt (dist_triangle z x a) (by linarith only [hzx, hxa])
  exact hbound q x d f M (hf.mono hsub) (fun z hz => hh z (hsub hz))
    (fun z hz => hM z (hsub hz)) x
    (Metric.mem_ball_self (half_pos d.property))

theorem harmonic_iteratedFDeriv_inner_holderBound (n k : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (R : PositiveRadius)
      (s γ M : ℝ) (f : Domain n → Ambient q),
      0 < s → s < R.val → 0 ≤ γ → γ ≤ 1 → 0 ≤ M →
      ContDiffOn ℝ ∞ f (Metric.ball a R.val) →
      (∀ z ∈ Metric.ball a R.val, Laplacian.laplacian f z = 0) →
      (∀ z ∈ Metric.ball a R.val, ‖f z‖ ≤ M) →
      HolderBoundOn (Metric.ball a s) (iteratedFDeriv ℝ k f) γ
        (C * ((R.val - s) ^ (k + 1))⁻¹ * M * (2 * s) ^ (1 - γ)) := by
  obtain ⟨C, hC, hbound⟩ := harmonic_iteratedFDeriv_inner_sup_bound n (k + 1) hn
  refine ⟨C, hC, ?_⟩
  intro q a R s γ M f hs hsR hγ hγOne hM hf hh hnorm
  let B : ℝ := C * ((R.val - s) ^ (k + 1))⁻¹ * M
  have hB : 0 ≤ B := by
    exact mul_nonneg (mul_nonneg hC.le (inv_nonneg.mpr
      (pow_nonneg (sub_pos.mpr hsR).le _))) hM
  have hD (z : Domain n) (hz : z ∈ Metric.ball a s) :
      DifferentiableAt ℝ (iteratedFDeriv ℝ k f) z := by
    have hzR := Metric.ball_subset_ball hsR.le hz
    have hlocal := hf.contDiffAt (Metric.isOpen_ball.mem_nhds hzR)
    exact (hlocal.iteratedFDeriv_right (m := 1)
      (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) + (k : ℕ∞) ≤ ⊤ from le_top))).differentiableAt
      one_ne_zero
  have hDBound (z : Domain n) (hz : z ∈ Metric.ball a s) :
      ‖fderiv ℝ (iteratedFDeriv ℝ k f) z‖ ≤ B := by
    rw [norm_fderiv_iteratedFDeriv]
    exact hbound q a R s f M hsR hf hh hnorm z hz
  intro x hx y hy
  have hLip := Convex.norm_image_sub_le_of_norm_fderiv_le
    hD hDBound (convex_ball a s) hy hx
  have hdiameter : dist x y ≤ 2 * s := by
    have hxa : dist x a < s := hx
    have hay : dist a y < s := by simpa only [Metric.mem_ball, dist_comm] using hy
    exact (dist_triangle x a y).trans (by linarith only [hxa, hay])
  have hpower := dist_le_diameter_factor_rpow x y hdiameter hγ hγOne
  calc
    _ ≤ B * dist x y := by simpa only [dist_eq_norm] using hLip
    _ ≤ B * ((2 * s) ^ (1 - γ) * (dist x y) ^ γ) :=
      mul_le_mul_of_nonneg_left hpower hB
    _ = _ := by
      simp only [Real.rpow_eq_pow]
      exact (mul_assoc _ _ _).symm

end HolderToCK
end
