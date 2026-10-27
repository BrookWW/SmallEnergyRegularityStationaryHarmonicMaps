module

public import StationaryHarmonicMaps.Foundation.CriticalGradientMorrey
import HarmonicMaps.Analysis.AffineEnergyScaling

/-!
# Affine invariance of the full critical Morrey supremum

Positive affine transport preserves every normalized truncated-ball energy.
The energy field is arbitrary; no Sobolev or finite-energy hypothesis is used.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ENNReal

namespace StationaryHarmonicMaps

/-- Zero extension of an energy field gives the exact truncated energy. -/
theorem dirichletEnergy_indicator_eq_inter {n q : ℕ}
    (F : Domain n → Gradient n q) {D : Set (Domain n)} (hD : MeasurableSet D)
    (U : Set (Domain n)) :
    dirichletEnergy (D.indicator F) U = dirichletEnergy F (U ∩ D) := by
  classical
  have hind : (fun x => ENNReal.ofReal (hsNormSq (D.indicator F x))) =
      D.indicator (fun x => ENNReal.ofReal (hsNormSq (F x))) := by
    funext x
    by_cases hx : x ∈ D
    · simp only [indicator_of_mem hx]
    · simp [indicator_of_notMem hx, hsNormSq]
  unfold dirichletEnergy
  rw [hind, lintegral_indicator hD, Measure.restrict_restrict hD, inter_comm D U]

/-- Positive affine transport commutes with zero extension between the two balls. -/
theorem affineBall_indicator_field {n q : ℕ} (a b : Domain n) {t : ℝ}
    (ht : 0 < t) (R : ℝ) (F : Domain n → Gradient n q) :
    (fun z i => t • (Metric.ball a R).indicator F (a + t • (z - b)) i) =
      (Metric.ball b (R / t)).indicator (fun z i => t • F (a + t • (z - b)) i) := by
  classical
  funext z i
  by_cases hz : z ∈ Metric.ball b (R / t)
  · simp only [indicator_of_mem hz,
      indicator_of_mem ((affineBall_mem_ball_iff a b ht R z).mpr hz)]
  · simp only [indicator_of_notMem hz,
      indicator_of_notMem (mt (affineBall_mem_ball_iff a b ht R z).mp hz), Pi.zero_apply,
      smul_zero]

/-- The exact extended energy identity includes boundary-truncated balls. -/
theorem dirichletEnergy_affineBall_inter {n q : ℕ} (a b x : Domain n) {t : ℝ}
    (ht : 0 < t) (R r : ℝ) (F : Domain n → Gradient n q) :
    dirichletEnergy (fun z i => t • F (a + t • (z - b)) i)
        (Metric.ball x r ∩ Metric.ball b (R / t)) =
      ENNReal.ofReal (t ^ (2 - (n : ℤ))) *
        dirichletEnergy F (Metric.ball (a + t • (x - b)) (t * r) ∩ Metric.ball a R) := by
  have h := dirichletEnergy_affineBall (a + t • (x - b)) x ht (t * r)
    ((Metric.ball a R).indicator F)
  have heq : (fun z i => t • (Metric.ball a R).indicator F
      (a + t • (x - b) + t • (z - x)) i) =
      (fun z i => t • (Metric.ball a R).indicator F (a + t • (z - b)) i) := by
    funext z i
    congr 2
    simp only [smul_sub]
    abel_nf
  rw [mul_div_cancel_left₀ _ ht.ne', heq, affineBall_indicator_field a b ht R F,
    dirichletEnergy_indicator_eq_inter _ measurableSet_ball,
    dirichletEnergy_indicator_eq_inter _ measurableSet_ball] at h
  exact h

/-- The normalization cancels the affine energy factor without converting extended energy. -/
theorem normalized_truncated_energy_affineBall {n q : ℕ} (a b x : Domain n) {t r : ℝ}
    (ht : 0 < t) (hr : 0 < r) (R : ℝ) (F : Domain n → Gradient n q) :
    ENNReal.ofReal (r ^ (2 - (n : ℤ))) *
        dirichletEnergy (fun z i => t • F (a + t • (z - b)) i)
          (Metric.ball x r ∩ Metric.ball b (R / t)) =
      ENNReal.ofReal ((t * r) ^ (2 - (n : ℤ))) *
        dirichletEnergy F (Metric.ball (a + t • (x - b)) (t * r) ∩ Metric.ball a R) := by
  rw [dirichletEnergy_affineBall_inter a b x ht R r F, ← mul_assoc,
    ← ENNReal.ofReal_mul (zpow_nonneg hr.le _), ← mul_zpow, mul_comm r t]

/-- The literal double supremum is invariant under positive affine transport. -/
theorem criticalGradientMorreySquare_affineBall {n q : ℕ}
    (a b : Domain n) {t : ℝ} (ht : 0 < t) (R : ℝ)
    (F : Domain n → Gradient n q) :
    criticalGradientMorreySquare (fun z i => t • F (a + t • (z - b)) i)
        (Metric.ball b (R / t)) =
      criticalGradientMorreySquare F (Metric.ball a R) := by
  classical
  unfold criticalGradientMorreySquare
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun r => ?_
    rw [normalized_truncated_energy_affineBall a b x.val ht r.property R F]
    exact le_iSup_of_le
      (⟨a + t • (x.val - b), (affineBall_mem_ball_iff a b ht R x.val).mpr x.property⟩ :
        Metric.ball a R)
      (le_iSup_of_le (⟨t * r.val, mul_pos ht r.property⟩ : PositiveRadius) le_rfl)
  · refine iSup_le fun x => iSup_le fun r => ?_
    let y : Domain n := b + t⁻¹ • (x.val - a)
    have hy : a + t • (y - b) = x.val := by
      dsimp only [y]
      simp [smul_smul, ht.ne']
    have hyD : y ∈ Metric.ball b (R / t) := by
      apply (affineBall_mem_ball_iff a b ht R y).mp
      rw [hy]
      exact x.property
    have hterm := normalized_truncated_energy_affineBall a b y ht
      (div_pos r.property ht) R F
    rw [hy, mul_div_cancel₀ _ ht.ne'] at hterm
    rw [← hterm]
    exact le_iSup_of_le (⟨y, hyD⟩ : Metric.ball b (R / t))
      (le_iSup_of_le (⟨r.val / t, div_pos r.property ht⟩ : PositiveRadius) le_rfl)

/-- Rescaling a positive-radius ball to the unit ball preserves its full critical supremum. -/
theorem criticalGradientMorreySquare_unitBall {n q : ℕ}
    (a : Domain n) (R : PositiveRadius) (F : Domain n → Gradient n q) :
    criticalGradientMorreySquare (fun z i => R.val • F (a + R.val • z) i)
        (Metric.ball (0 : Domain n) 1) =
      criticalGradientMorreySquare F (Metric.ball a R.val) := by
  simpa only [div_self R.property.ne', sub_zero] using
    criticalGradientMorreySquare_affineBall a (0 : Domain n) R.property R.val F

/-- Continuous linear coefficient encoding commutes with the transported matrix one-form. -/
theorem criticalGradientMorreySquare_affineBall_encoded_operator {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q))
    (A : Domain n → Fin n → Ambient q →L[ℝ] Ambient q)
    (a b : Domain n) {t : ℝ} (ht : 0 < t) (R : ℝ) :
    criticalGradientMorreySquare (fun z i => E (t • A (a + t • (z - b)) i))
        (Metric.ball b (R / t)) =
      criticalGradientMorreySquare (fun x i => E (A x i)) (Metric.ball a R) := by
  simpa only [map_smul] using
    criticalGradientMorreySquare_affineBall a b ht R (fun x i => E (A x i))

end StationaryHarmonicMaps

end
