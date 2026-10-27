module

public import HolderToCK.Foundation.BallVolume
public import HarmonicMaps.Analysis.HarmonicInteriorGradient

/-! # Harmonic gradient energy on arbitrary concentric balls

The ball mean of each classical gradient column controls its value by the
original Hilbert--Schmidt energy. Integration on a smaller ball gives the
exact dimension factor `2^n * theta^n`.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK

theorem harmonic_gradient_sq_le_ball_energy {n q : ℕ} (hn : 2 ≤ n)
    (a : Domain n) (R : PositiveRadius) (w : Domain n → Ambient q)
    (hw : ContDiffOn ℝ ∞ w (Metric.ball a R.val))
    (hh : ∀ z ∈ Metric.ball a R.val, Laplacian.laplacian w z = 0)
    (hE : IntegrableOn (fun z => hsNormSq (fun i =>
      fderiv ℝ w z (EuclideanSpace.single i 1))) (Metric.ball a R.val))
    {x : Domain n} (hx : x ∈ Metric.ball a (R.val / 2)) :
    hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1)) ≤
      (volume.real (Metric.ball (0 : Domain n) (R.val / 2)))⁻¹ *
        ∫ z in Metric.ball a R.val,
          hsNormSq (fun i => fderiv ℝ w z (EuclideanSpace.single i 1)) := by
  let B := Metric.ball x (R.val / 2)
  let c := (volume.real B)⁻¹
  have hclosed : Metric.closedBall x (R.val / 2) ⊆ Metric.ball a R.val := by
    intro z hz
    have hzx : dist z x ≤ R.val / 2 := hz
    have hxa : dist x a < R.val / 2 := hx
    change dist z a < R.val
    exact lt_of_le_of_lt (dist_triangle z x a) (by linarith only [hzx, hxa])
  have hcolumn (i : Fin n) :=
    harmonic_fderiv_column (Metric.ball a R.val) Metric.isOpen_ball w hw hh i
  have hInt (i : Fin n) : IntegrableOn (fun z =>
      ‖fderiv ℝ w z (EuclideanSpace.single i 1)‖ ^ 2) B :=
    ((((hcolumn i).1.continuousOn.mono hclosed).norm.pow 2).integrableOn_compact
      (isCompact_closedBall x (R.val / 2))).mono_set Metric.ball_subset_closedBall
  have hpoint (i : Fin n) : ‖fderiv ℝ w x (EuclideanSpace.single i 1)‖ ^ 2 ≤
      c * ∫ z in B, ‖fderiv ℝ w z (EuclideanSpace.single i 1)‖ ^ 2 :=
    harmonic_norm_sq_le_ballAverage hn x ⟨R.val / 2, half_pos R.property⟩
      (Metric.ball a R.val) Metric.isOpen_ball hclosed
      (fun z => fderiv ℝ w z (EuclideanSpace.single i 1)) (hcolumn i).1
      (fun z hz => (hcolumn i).2 z (hclosed (Metric.ball_subset_closedBall hz)))
  have hsum : hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1)) ≤
      c * ∫ z in B, hsNormSq (fun i => fderiv ℝ w z (EuclideanSpace.single i 1)) := by
    unfold hsNormSq
    rw [integral_finsetSum _ (fun i _ => hInt i), Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hpoint i)
  have henergy : (∫ z in B, hsNormSq (fun i =>
      fderiv ℝ w z (EuclideanSpace.single i 1))) ≤
      ∫ z in Metric.ball a R.val, hsNormSq (fun i =>
        fderiv ℝ w z (EuclideanSpace.single i 1)) :=
    setIntegral_mono_set hE (Filter.Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Filter.Eventually.of_forall fun z hz => hclosed (Metric.ball_subset_closedBall hz))
  have hc : c = (volume.real (Metric.ball (0 : Domain n) (R.val / 2)))⁻¹ := by
    dsimp only [c, B]
    rw [measureReal_def, measureReal_def, Measure.addHaar_ball_center volume]
  have hfinal := hsum.trans (mul_le_mul_of_nonneg_left henergy
    (show 0 ≤ c from inv_nonneg.mpr ENNReal.toReal_nonneg))
  rw [hc] at hfinal
  exact hfinal

theorem harmonic_energy_decay {n q : ℕ} (hn : 2 ≤ n)
    (a : Domain n) (R : PositiveRadius) (w : Domain n → Ambient q)
    (hw : ContDiffOn ℝ ∞ w (Metric.ball a R.val))
    (hh : ∀ z ∈ Metric.ball a R.val, Laplacian.laplacian w z = 0)
    (hE : IntegrableOn (fun z => hsNormSq (fun i =>
      fderiv ℝ w z (EuclideanSpace.single i 1))) (Metric.ball a R.val))
    {θ : ℝ} (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2) :
    (∫ z in Metric.ball a (θ * R.val),
      hsNormSq (fun i => fderiv ℝ w z (EuclideanSpace.single i 1))) ≤
      (2 : ℝ) ^ n * θ ^ n *
        ∫ z in Metric.ball a R.val,
          hsNormSq (fun i => fderiv ℝ w z (EuclideanSpace.single i 1)) := by
  have hsub : Metric.ball a (θ * R.val) ⊆ Metric.ball a (R.val / 2) := by
    apply Metric.ball_subset_ball
    nlinarith only [hθhalf, R.property]
  have hsubR : Metric.ball a (θ * R.val) ⊆ Metric.ball a R.val :=
    hsub.trans (Metric.ball_subset_ball (by linarith only [R.property]))
  have hpoint : ∀ z ∈ Metric.ball a (θ * R.val),
      hsNormSq (fun i => fderiv ℝ w z (EuclideanSpace.single i 1)) ≤
      (volume.real (Metric.ball (0 : Domain n) (R.val / 2)))⁻¹ *
        ∫ y in Metric.ball a R.val,
          hsNormSq (fun i => fderiv ℝ w y (EuclideanSpace.single i 1)) := by
    intro z hz
    exact harmonic_gradient_sq_le_ball_energy hn a R w hw hh hE (hsub hz)
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a (θ * R.val))) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hbound := setIntegral_mono_on (hE.mono_set hsubR) (integrable_const _)
    measurableSet_ball hpoint
  rw [setIntegral_const, smul_eq_mul, ← mul_assoc,
    ball_volume_ratio_half a R.property hθ] at hbound
  exact hbound

end HolderToCK
end
