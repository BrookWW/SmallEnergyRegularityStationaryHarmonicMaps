module

public import HolderToCK.Analysis.SegmentDerivativeIdentity
public import HolderToCK.Analysis.GradientLinearAlgebra
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # The L1 segment estimate for Sobolev Poincare arguments

The coordinate-column sum controls the actual classical derivative. The
fundamental theorem on a segment therefore gives an L1 gradient bound,
without replacing the gradient by its L2 average.
-/

public section

open HarmonicMaps HolderToCK MeasureTheory Set
open scoped BigOperators ContDiff

namespace StationaryHarmonicMaps

/-- The Hilbert--Schmidt norm is bounded by the sum of the column norms. -/
theorem sqrt_hsNormSq_le_sum_norm {n q : ℕ} (A : Gradient n q) :
    Real.sqrt (hsNormSq A) ≤ ∑ i : Fin n, ‖A i‖ := by
  have hsum : 0 ≤ ∑ i : Fin n, ‖A i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hsq : hsNormSq A ≤ (∑ i : Fin n, ‖A i‖) ^ 2 := by
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg (A i))
  exact (Real.sqrt_le_iff).mpr ⟨hsum, hsq⟩

/-- The operator norm estimate uses the actual coordinate columns. -/
theorem norm_linearMap_le_sum_column_norm {n q : ℕ}
    (L : Domain n →L[ℝ] Ambient q) :
    ‖L‖ ≤ ∑ i : Fin n, ‖L (EuclideanSpace.single i 1)‖ :=
  (norm_linearMap_le_sqrt_hsNormSq L).trans (sqrt_hsNormSq_le_sum_norm _)

/-- Endpoint differences are controlled by the integral of column norms. -/
theorem segment_norm_le_integral_column_norm {n q : ℕ}
    {f : Domain n → Ambient q} {a x y : Domain n} {r : ℝ}
    (hf : ContDiffOn ℝ 1 f (Metric.ball a r))
    (hx : x ∈ Metric.ball a r) (hy : y ∈ Metric.ball a r) :
    ‖f x - f y‖ ≤ ‖y - x‖ * ∫ t in (0 : ℝ)..1,
      ∑ i : Fin n, ‖fderiv ℝ f ((1 - t) • x + t • y) (EuclideanSpace.single i 1)‖ := by
  let γ : ℝ → Domain n := fun t => x + t • (y - x)
  have hγeq (t : ℝ) : γ t = (1 - t) • x + t • y := by
    dsimp only [γ]
    simp only [smul_sub, sub_smul, one_smul]
    abel
  have hγmem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Metric.ball a r := by
    intro t ht
    rw [hγeq]
    exact segmentPoint_mem_ball hx hy ht
  have hline := c1_segment_integral (ballDomain a r) hf x y hγmem
  have hfd : ContinuousOn (fun t : ℝ => fderiv ℝ f (γ t)) (Icc (0 : ℝ) 1) :=
    (hf.continuousOn_fderiv_of_isOpen Metric.isOpen_ball le_rfl).comp
      (by dsimp only [γ]; fun_prop) hγmem
  have hcolumn (i : Fin n) : ContinuousOn
      (fun t : ℝ => ‖fderiv ℝ f (γ t) (EuclideanSpace.single i 1)‖)
      (Icc (0 : ℝ) 1) :=
    (hfd.clm_apply continuousOn_const).norm
  have hsum : ContinuousOn (fun t : ℝ =>
      ∑ i : Fin n, ‖fderiv ℝ f (γ t) (EuclideanSpace.single i 1)‖)
      (Icc (0 : ℝ) 1) :=
    continuousOn_finsetSum Finset.univ (fun i _ => hcolumn i)
  have hderivInt : IntervalIntegrable
      (fun t : ℝ => ‖fderiv ℝ f (γ t) (y - x)‖) volume 0 1 :=
    (hfd.clm_apply continuousOn_const).norm.intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)
  have hsumInt : IntervalIntegrable (fun t : ℝ =>
      ∑ i : Fin n, ‖fderiv ℝ f (γ t) (EuclideanSpace.single i 1)‖) volume 0 1 :=
    hsum.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hnorm : ‖f x - f y‖ ≤ ∫ t in (0 : ℝ)..1, ‖fderiv ℝ f (γ t) (y - x)‖ := by
    have h := intervalIntegral.norm_integral_le_integral_norm
      (f := fun t : ℝ => fderiv ℝ f (γ t) (y - x)) (μ := volume)
      (by norm_num : (0 : ℝ) ≤ 1)
    rw [← hline] at h
    simpa only [norm_sub_rev] using h
  have hbound := intervalIntegral.integral_mono_on
    (by norm_num : (0 : ℝ) ≤ 1) hderivInt (hsumInt.const_mul ‖y - x‖)
    (fun t _ => (ContinuousLinearMap.le_opNorm _ _).trans
      (by
        simpa only [mul_comm] using
          (mul_le_mul_of_nonneg_right (norm_linearMap_le_sum_column_norm (fderiv ℝ f (γ t)))
            (norm_nonneg (y - x)))))
  rw [intervalIntegral.integral_const_mul] at hbound
  have hrewrite : (fun t : ℝ =>
      ∑ i : Fin n, ‖fderiv ℝ f (γ t) (EuclideanSpace.single i 1)‖) =
      (fun t : ℝ =>
        ∑ i : Fin n, ‖fderiv ℝ f ((1 - t) • x + t • y) (EuclideanSpace.single i 1)‖) := by
    funext t
    rw [hγeq]
  rw [hrewrite] at hbound
  exact hnorm.trans hbound

/-- The ball diameter gives a uniform segment constant. -/
theorem ball_segment_norm_le_integral_column_norm {n q : ℕ}
    {f : Domain n → Ambient q} {a x y : Domain n} {r : ℝ}
    (hf : ContDiffOn ℝ 1 f (Metric.ball a r))
    (hx : x ∈ Metric.ball a r) (hy : y ∈ Metric.ball a r) (_hr : 0 < r) :
    ‖f x - f y‖ ≤ 2 * r * ∫ t in Icc (0 : ℝ) 1,
      ∑ i : Fin n, ‖fderiv ℝ f ((1 - t) • x + t • y) (EuclideanSpace.single i 1)‖ := by
  have hdist : ‖y - x‖ ≤ 2 * r := by
    have ht := dist_triangle y a x
    have hy' : dist y a < r := hy
    have hx' : dist a x < r := by simpa only [Metric.mem_ball, dist_comm] using hx
    rw [dist_eq_norm] at ht
    linarith only [ht, hy', hx']
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..1,
      ∑ i : Fin n, ‖fderiv ℝ f ((1 - t) • x + t • y) (EuclideanSpace.single i 1)‖ :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have h := (segment_norm_le_integral_column_norm hf hx hy).trans
    (mul_le_mul_of_nonneg_right hdist hnonneg)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc] at h
  exact h

end StationaryHarmonicMaps

end
