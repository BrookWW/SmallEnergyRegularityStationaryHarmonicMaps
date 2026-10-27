module

public import HolderToCK.Analysis.Harmonic.OscillationDecay
public import HolderToCK.Analysis.Harmonic.EnergyDecay

/-! # Harmonic gradient excess on concentric balls

The ball mean of a harmonic field equals its central value. Quantitative
Lipschitz oscillation therefore yields the exact `theta^(n+2)` decay for each
harmonic gradient column, summed in the native Hilbert--Schmidt norm.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK

noncomputable section

@[expose] def classicalGradientBallMean {n q : ℕ}
    (f : Domain n → Ambient q) (a : Domain n) (r : ℝ) : Gradient n q :=
  fun i => ⨍ z in Metric.ball a r, fderiv ℝ f z (EuclideanSpace.single i 1)

theorem harmonic_field_excess_decay (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (R : PositiveRadius)
      (f : Domain n → Ambient q),
      ContDiffOn ℝ ∞ f (Metric.ball a R.val) →
      (∀ z ∈ Metric.ball a R.val, Laplacian.laplacian f z = 0) →
      IntegrableOn (fun z => ‖f z‖ ^ 2) (Metric.ball a R.val) →
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
        (∫ z in Metric.ball a (θ * R.val),
          ‖f z - ⨍ y in Metric.ball a (θ * R.val), f y‖ ^ 2) ≤
        C * θ ^ (n + 2) * ∫ z in Metric.ball a R.val,
          ‖f z - ⨍ y in Metric.ball a R.val, f y‖ ^ 2 := by
  obtain ⟨C, hC, hdecay⟩ := harmonic_ball_oscillation_decay n hn
  refine ⟨C, hC, ?_⟩
  intro q a R f hf hh hE θ hθ hθhalf
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a R.val)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hfLp : MemLp f 2 (volume.restrict (Metric.ball a R.val)) :=
    (memLp_two_iff_integrable_sq_norm
      (hf.continuousOn.aestronglyMeasurable measurableSet_ball)).mpr hE
  have hEcenter : IntegrableOn
      (fun z => ‖f z - ⨍ y in Metric.ball a R.val, f y‖ ^ 2) (Metric.ball a R.val) :=
    (hfLp.sub (memLp_const _)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hclosed : Metric.closedBall a (θ * R.val) ⊆ Metric.ball a R.val :=
    Metric.closedBall_subset_ball (by nlinarith only [hθhalf, R.property])
  have hmean : (⨍ y in Metric.ball a (θ * R.val), f y) = f a := by
    rw [setAverage_eq]
    exact (harmonic_ball_meanValue hn a ⟨θ * R.val, mul_pos hθ R.property⟩
      (Metric.ball a R.val) Metric.isOpen_ball hclosed f hf
      (fun z hz => hh z (hclosed (Metric.ball_subset_closedBall hz)))).symm
  rw [hmean]
  exact hdecay q a R f (⨍ y in Metric.ball a R.val, f y) hf hh hEcenter θ hθ hθhalf

theorem harmonic_gradient_excess_decay (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (R : PositiveRadius)
      (f : Domain n → Ambient q),
      ContDiffOn ℝ ∞ f (Metric.ball a R.val) →
      (∀ z ∈ Metric.ball a R.val, Laplacian.laplacian f z = 0) →
      IntegrableOn (fun z => hsNormSq (fun i =>
        fderiv ℝ f z (EuclideanSpace.single i 1))) (Metric.ball a R.val) →
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
        (∫ z in Metric.ball a (θ * R.val), hsNormSq (fun i =>
          fderiv ℝ f z (EuclideanSpace.single i 1) -
            classicalGradientBallMean f a (θ * R.val) i)) ≤
        C * θ ^ (n + 2) * ∫ z in Metric.ball a R.val, hsNormSq (fun i =>
          fderiv ℝ f z (EuclideanSpace.single i 1) -
            classicalGradientBallMean f a R.val i) := by
  obtain ⟨C, hC, hdecay⟩ := harmonic_field_excess_decay n hn
  refine ⟨C, hC, ?_⟩
  intro q a R f hf hh hE θ hθ hθhalf
  let F : Fin n → Domain n → Ambient q := fun i z =>
    fderiv ℝ f z (EuclideanSpace.single i 1)
  have hcol (i : Fin n) := harmonic_fderiv_column
    (Metric.ball a R.val) Metric.isOpen_ball f hf hh i
  have hFi (i : Fin n) : IntegrableOn (fun z => ‖F i z‖ ^ 2) (Metric.ball a R.val) := by
    apply hE.mono' (((hcol i).1.continuousOn.norm.pow 2).aestronglyMeasurable measurableSet_ball)
    apply Filter.Eventually.of_forall
    intro z
    change ‖‖F i z‖ ^ 2‖ ≤ hsNormSq (fun j => F j z)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖F j z‖) (Finset.mem_univ i)
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a R.val)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hLp (i : Fin n) : MemLp (F i) 2 (volume.restrict (Metric.ball a R.val)) :=
    (memLp_two_iff_integrable_sq_norm
      ((hcol i).1.continuousOn.aestronglyMeasurable measurableSet_ball)).mpr (hFi i)
  have hlarge (i : Fin n) : IntegrableOn
      (fun z => ‖F i z - classicalGradientBallMean f a R.val i‖ ^ 2)
      (Metric.ball a R.val) :=
    ((hLp i).sub (memLp_const _)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hclosed : Metric.closedBall a (θ * R.val) ⊆ Metric.ball a R.val :=
    Metric.closedBall_subset_ball (by nlinarith only [hθhalf, R.property])
  have hsmall (i : Fin n) : IntegrableOn
      (fun z => ‖F i z - classicalGradientBallMean f a (θ * R.val) i‖ ^ 2)
      (Metric.ball a (θ * R.val)) :=
    ((((hcol i).1.continuousOn.mono hclosed).sub continuousOn_const).norm.pow 2).integrableOn_compact (isCompact_closedBall a (θ * R.val)) |>.mono_set
      Metric.ball_subset_closedBall
  change (∫ z in Metric.ball a (θ * R.val), ∑ i : Fin n,
      ‖F i z - classicalGradientBallMean f a (θ * R.val) i‖ ^ 2) ≤
    C * θ ^ (n + 2) * ∫ z in Metric.ball a R.val, ∑ i : Fin n,
      ‖F i z - classicalGradientBallMean f a R.val i‖ ^ 2
  rw [integral_finsetSum _ (fun i _ => hsmall i),
    integral_finsetSum _ (fun i _ => hlarge i), Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ =>
    hdecay q a R (F i) (hcol i).1 (hcol i).2 (hFi i) θ hθ hθhalf)

end
end HolderToCK
end
