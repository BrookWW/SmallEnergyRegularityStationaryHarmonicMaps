module

public import HarmonicMaps.Analysis.HarmonicBallMeanValue
public import HarmonicMaps.Analysis.HarmonicDerivative
public import HarmonicMaps.EnergyLemmas
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Interior Hilbert--Schmidt gradient estimate

The ball mean of each harmonic derivative column and Jensen's inequality
bound the actual squared gradient by its energy on the half-unit ball.
The coefficient is the reciprocal volume of the quarter-unit ball.
-/

public section

open MeasureTheory Set
open scoped ContDiff BigOperators

namespace HarmonicMaps

/-- The square norm of a smooth harmonic map is bounded by its ball mean. -/
theorem harmonic_norm_sq_le_ballAverage {n q : ℕ} (hn : 2 ≤ n)
    (a : Domain n) (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall a R.val ⊆ U)
    (f : Domain n → Ambient q) (hf : ContDiffOn ℝ ∞ f U)
    (hharm : ∀ x ∈ Metric.ball a R.val, Laplacian.laplacian f x = 0) :
    ‖f a‖ ^ 2 ≤ ((volume : Measure (Domain n)).real (Metric.ball a R.val))⁻¹ *
      ∫ x in Metric.ball a R.val, ‖f x‖ ^ 2 := by
  have hfi : IntegrableOn f (Metric.ball a R.val) volume :=
    ((hf.continuousOn.mono hclosed).integrableOn_compact
      (isCompact_closedBall a R.val)).mono_set Metric.ball_subset_closedBall
  have hf2 : IntegrableOn (fun x => ‖f x‖ ^ 2) (Metric.ball a R.val) volume :=
    (((hf.continuousOn.mono hclosed).norm.pow 2).integrableOn_compact
      (isCompact_closedBall a R.val)).mono_set Metric.ball_subset_closedBall
  have hc : ConvexOn ℝ univ (fun v : Ambient q => ‖v‖ ^ 2) :=
    (convexOn_univ_norm (E := Ambient q)).pow (fun _ _ => norm_nonneg _) 2
  have hj := hc.map_set_average_le (continuous_norm.pow 2).continuousOn
    isClosed_univ (Metric.measure_ball_pos volume a R.property).ne'
    measure_ball_ne_top (Filter.Eventually.of_forall fun _ => mem_univ _) hfi hf2
  rw [harmonic_ball_meanValue hn a R U hU hclosed f hf hharm]
  simpa only [setAverage_eq, smul_eq_mul] using hj

/-- One dimension-only coefficient bounds the native HS gradient at every
point of the quarter-unit ball by the actual half-ball gradient energy. -/
theorem harmonic_interiorGradient {n q : ℕ} (hn : 2 ≤ n)
    (w : Domain n → Ambient q)
    (hw : ContDiffOn ℝ ∞ w (Metric.ball (0 : Domain n) (1 / 2 : ℝ)))
    (hh : ∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ),
      Laplacian.laplacian w x = 0)
    (hE : IntegrableOn (fun x => hsNormSq (fun i =>
      fderiv ℝ w x (EuclideanSpace.single i 1)))
      (Metric.ball (0 : Domain n) (1 / 2 : ℝ)) volume)
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) (1 / 4 : ℝ)) :
    hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1)) ≤
      ((volume : Measure (Domain n)).real
        (Metric.ball (0 : Domain n) (1 / 4 : ℝ)))⁻¹ *
      ∫ y in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
        hsNormSq (fun i => fderiv ℝ w y (EuclideanSpace.single i 1)) := by
  let B : Set (Domain n) := Metric.ball x (1 / 4 : ℝ)
  let c : ℝ := ((volume : Measure (Domain n)).real B)⁻¹
  have hclosed : Metric.closedBall x (1 / 4 : ℝ) ⊆
      Metric.ball (0 : Domain n) (1 / 2 : ℝ) := by
    intro y hy
    have hyx : dist y x ≤ (1 / 4 : ℝ) := hy
    have hx0 : dist x 0 < (1 / 4 : ℝ) := hx
    change dist y 0 < (1 / 2 : ℝ)
    exact lt_of_le_of_lt (dist_triangle y x 0) (by linarith only [hyx, hx0])
  have hcol (i : Fin n) :
      ContDiffOn ℝ ∞ (fun z => fderiv ℝ w z (EuclideanSpace.single i 1))
        (Metric.ball (0 : Domain n) (1 / 2 : ℝ)) ∧
      ∀ y ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ),
        Laplacian.laplacian (fun z => fderiv ℝ w z (EuclideanSpace.single i 1)) y = 0 :=
    harmonic_fderiv_column (Metric.ball (0 : Domain n) (1 / 2 : ℝ))
      Metric.isOpen_ball w hw hh i
  have hInt (i : Fin n) : IntegrableOn (fun y =>
      ‖fderiv ℝ w y (EuclideanSpace.single i 1)‖ ^ 2) B volume :=
    (((hcol i).1.continuousOn.mono hclosed).norm.pow 2).integrableOn_compact
      (isCompact_closedBall x (1 / 4 : ℝ)) |>.mono_set Metric.ball_subset_closedBall
  have hpoint (i : Fin n) : ‖fderiv ℝ w x (EuclideanSpace.single i 1)‖ ^ 2 ≤
      c * ∫ y in B, ‖fderiv ℝ w y (EuclideanSpace.single i 1)‖ ^ 2 :=
    harmonic_norm_sq_le_ballAverage (n := n) (q := q) hn x ⟨1 / 4, by norm_num⟩
      (Metric.ball (0 : Domain n) (1 / 2 : ℝ))
      Metric.isOpen_ball hclosed (fun z => fderiv ℝ w z (EuclideanSpace.single i 1))
      (hcol i).1
      (fun y hy => (hcol i).2 y (hclosed (Metric.ball_subset_closedBall hy)))
  have hsum : hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1)) ≤
      c * ∫ y in B, hsNormSq (fun i =>
        fderiv ℝ w y (EuclideanSpace.single i 1)) := by
    unfold hsNormSq
    rw [integral_finsetSum _ (fun i _ => hInt i), Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hpoint i)
  have hsub : B ⊆ Metric.ball (0 : Domain n) (1 / 2 : ℝ) :=
    Metric.ball_subset_closedBall.trans hclosed
  have henergy : (∫ y in B, hsNormSq (fun i =>
      fderiv ℝ w y (EuclideanSpace.single i 1))) ≤
      ∫ y in Metric.ball (0 : Domain n) (1 / 2 : ℝ), hsNormSq (fun i =>
        fderiv ℝ w y (EuclideanSpace.single i 1)) :=
    setIntegral_mono_set hE (Filter.Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Filter.Eventually.of_forall fun y hy => hsub hy)
  have hc : c = ((volume : Measure (Domain n)).real
      (Metric.ball (0 : Domain n) (1 / 4 : ℝ)))⁻¹ := by
    dsimp only [c, B]
    rw [measureReal_def, measureReal_def, Measure.addHaar_ball_center volume]
  have hfinal := hsum.trans (mul_le_mul_of_nonneg_left henergy
    (show 0 ≤ c from inv_nonneg.mpr ENNReal.toReal_nonneg))
  rw [hc] at hfinal
  exact hfinal

end HarmonicMaps
end
