module

public import StationaryHarmonicMaps.Analysis.DistributionHarmonicRepresentative
public import StationaryHarmonicMaps.Analysis.HarmonicLpDecay
public import StationaryHarmonicMaps.Analysis.LpL1Bound
public import StationaryHarmonicMaps.Analysis.VectorDistributionTests

/-!
# Lp decay of the original distribution-harmonic L² field

Forward finite-measure exponent comparison gives genuine Lp membership.
The actual smooth representative supplies harmonic decay, and its a.e.
equality transfers both integrals back to the same original field.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Every 1<=p<=2 has genuine Lp integrability and the harmonic decay bound for the original raw field. -/
theorem distribution_harmonic_lp_decay {n q : ℕ} (hn : 2 ≤ n) {p : ℝ}
    (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2) (a : Domain n) (R : PositiveRadius)
    (u : Domain n → Ambient q) (hu : MemLp u 2 (volume.restrict (Metric.ball a R.val)))
    (hharm : ∀ (η : Domain n → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Metric.ball a R.val →
        (∫ z in Metric.ball a R.val, Laplacian.laplacian η z • u z) = 0) :
    MemLp u (ENNReal.ofReal p) (volume.restrict (Metric.ball a R.val)) ∧
    IntegrableOn (fun x => ‖u x‖ ^ p) (Metric.ball a R.val) volume ∧
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      IntegrableOn (fun x => ‖u x‖ ^ p) (Metric.ball a (θ * R.val)) volume ∧
      (∫ x in Metric.ball a (θ * R.val), ‖u x‖ ^ p) ≤
        (2 : ℝ) ^ n * θ ^ n * ∫ x in Metric.ball a R.val, ‖u x‖ ^ p := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a R.val)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hup : MemLp u (ENNReal.ofReal p) (volume.restrict (Metric.ball a R.val)) :=
    memLp_real_of_memL2 u hp₂ hu
  have hIp : IntegrableOn (fun x => ‖u x‖ ^ p) (Metric.ball a R.val) volume :=
    integrable_norm_rpow_of_memLp_real u (zero_le_one.trans hp₁) hup
  obtain ⟨v, hv, hAE, hΔ⟩ :=
    memLp_two_distribution_harmonic_smooth_representative_ball hn a R.val u hu hharm
  have hvp : IntegrableOn (fun x => ‖v x‖ ^ p) (Metric.ball a R.val) volume :=
    hIp.congr (hAE.mono fun _ hx => by dsimp only; rw [hx])
  refine ⟨hup, hIp, ?_⟩
  intro θ hθ hθhalf
  have hsub : Metric.ball a (θ * R.val) ⊆ Metric.ball a R.val := by
    apply Metric.ball_subset_ball
    nlinarith only [hθhalf, R.property]
  have H := harmonic_lp_decay hn hp₁ a R v hv hΔ hvp hθ hθhalf
  have hinner := ae_restrict_of_ae_restrict_of_subset hsub hAE
  refine ⟨hIp.mono_set hsub, ?_⟩
  calc
    _ = ∫ x in Metric.ball a (θ * R.val), ‖v x‖ ^ p :=
      integral_congr_ae (hinner.mono fun _ hx => by dsimp only; rw [hx])
    _ ≤ _ := H
    _ = _ := congrArg (fun z => (2 : ℝ) ^ n * θ ^ n * z)
      (integral_congr_ae (hAE.mono fun _ hx => by dsimp only; rw [hx]))


/-- The original L² one-form and its actual column-vector distribution tests have full HS Lp decay. -/
theorem distribution_harmonic_oneForm_lp_decay {n q : ℕ} (hn : 2 ≤ n) {p : ℝ}
    (hp₁ : 1 ≤ p) (hp₂ : p ≤ 2) (a : Domain n) (R : PositiveRadius)
    (F : Domain n → Gradient n q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a R.val)))
    (hvector : ∀ (i : Fin n) (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball a R.val →
        (∫ x in Metric.ball a R.val, inner ℝ (F x i) (Laplacian.laplacian ψ x)) = 0) :
    MemLp (fun x => Real.sqrt (hsNormSq (F x))) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball a R.val)) ∧
    IntegrableOn (fun x => (Real.sqrt (hsNormSq (F x))) ^ p) (Metric.ball a R.val) volume ∧
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      IntegrableOn (fun x => (Real.sqrt (hsNormSq (F x))) ^ p) (Metric.ball a (θ * R.val)) volume ∧
      (∫ x in Metric.ball a (θ * R.val), (Real.sqrt (hsNormSq (F x))) ^ p) ≤
        (2 : ℝ) ^ n * θ ^ n * ∫ x in Metric.ball a R.val, (Real.sqrt (hsNormSq (F x))) ^ p := by
  let E := fun x => WithLp.toLp 2 (fun j : Fin (n * q) =>
    F x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
  have hE : MemLp E 2 (volume.restrict (Metric.ball a R.val)) := memLp_hs_flatten F hF
  have hdist (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
      (hsη : tsupport η ⊆ Metric.ball a R.val) :
      (∫ z in Metric.ball a R.val, Laplacian.laplacian η z • E z) = 0 :=
    (hs_flatten_laplacian_of_column_vector_tests a R.val F hF hvector η hη hcη hsη).2
  have hnorm (x : Domain n) : ‖E x‖ = Real.sqrt (hsNormSq (F x)) := by
    calc
      _ = Real.sqrt (‖E x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = _ := congrArg Real.sqrt (hs_flatten_norm_sq (F x))
  have H := distribution_harmonic_lp_decay hn hp₁ hp₂ a R E hE hdist
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hnorm] using H.1.norm
  · simpa only [hnorm] using H.2.1
  · intro θ hθ hθhalf
    simpa only [hnorm] using H.2.2 θ hθ hθhalf

end StationaryHarmonicMaps.Analysis

end
