module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyMeanOscillation
public import StationaryHarmonicMaps.Foundation.C2Target
public import HarmonicMaps.Analysis.SobolevPoincare
public import HarmonicMaps.Analysis.ContinuousRepresentativeLocality

/-!
# Genuine zero-energy representatives

The actual Sobolev Poincaré estimate forces equality with the ball mean
almost everywhere. On an interior half-ball the constant representative
has the actual closed target range and is unique among continuous a.e.
representatives. No stationarity or weak harmonic equation is needed.
-/

public section

open HarmonicMaps MeasureTheory Filter

namespace StationaryHarmonicMaps.Analysis

/-- Zero actual HS gradient energy forces equality with the actual ball mean a.e. -/
theorem ae_eq_ballMean_of_zero_energy {n q : ℕ} (a : Domain n) {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du)
    (henergy : (∫ x in Metric.ball a R, hsNormSq (Du x)) = 0) :
    u =ᵐ[volume.restrict (Metric.ball a R)] (fun _ => ⨍ y in Metric.ball a R, u y) := by
  letI : IsFiniteMeasure (volume.restrict (ballDomain a R).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let c := ⨍ y in Metric.ball a R, u y
  have hconst : MemLp (fun _ : Domain n => c) 2 (volume.restrict (ballDomain a R).val) := memLp_const c
  have hsub := hu.2.1.sub hconst
  have hp := hu.poincare_ball hR
  rw [henergy, mul_zero] at hp
  have hnorm : (∫ x in Metric.ball a R, ‖u x - c‖ ^ 2) = 0 :=
    le_antisymm hp (integral_nonneg fun _ => sq_nonneg _)
  have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖u x - c‖)
    (hsub.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))).mp hnorm
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hx))

/-- The literal critical Morrey quantity zero gives the same a.e. constant map. -/
theorem ae_eq_ballMean_of_zero_criticalMorrey {n q : ℕ} (a : Domain n) {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du)
    (hzero : criticalGradientMorreySquare Du (Metric.ball a R) ≤ 0) :
    u =ᵐ[volume.restrict (Metric.ball a R)] (fun _ => ⨍ y in Metric.ball a R, u y) := by
  have hbound : normalizedEnergy Du a ⟨R, hR⟩ ≤ ENNReal.ofReal 0 := by
    simpa only [ENNReal.ofReal_zero] using
      (normalizedEnergy_le_criticalMorrey_of_ball_subset Du hR (Set.Subset.refl _)).trans hzero
  have hI := integral_hsNormSq_le_of_normalizedEnergy_bound a hR (by norm_num) hu hbound
  rw [zero_mul] at hI
  exact ae_eq_ballMean_of_zero_energy a hR hu
    (le_antisymm hI (integral_nonneg fun x => hsNormSq_nonneg (Du x)))

/-- Zero normalized energy already gives the target-valued unique half-ball representative. -/
theorem exists_target_representative_of_zero_normalizedEnergy {n q : ℕ}
    (N : CompactC2EmbeddedTarget q) {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (hN : ∀ᵐ x ∂volume.restrict Ω.val, u x ∈ N.carrierSet)
    (a : Domain n) (R : PositiveRadius) (hclosed : Metric.closedBall a R.val ⊆ Ω.val)
    (hzero : normalizedEnergy Du a R = 0) :
    ∃ w : Metric.ball a (R.val / 2) → Ambient q,
      IsContinuousRepresentative (ballDomain a (R.val / 2)) u w ∧
      (∀ x, w x ∈ N.carrierSet) ∧ (∀ x y, ‖w x - w y‖ = 0) ∧
      ∀ v : Metric.ball a (R.val / 2) → Ambient q,
        IsContinuousRepresentative (ballDomain a (R.val / 2)) u v → v = w := by
  have hW := hu.memW12_ball hclosed
  have hbound : normalizedEnergy Du a R ≤ ENNReal.ofReal 0 := by
    rw [hzero, ENNReal.ofReal_zero]
  have hI := integral_hsNormSq_le_of_normalizedEnergy_bound a R.property (by norm_num) hW hbound
  rw [zero_mul] at hI
  have hEq := ae_eq_ballMean_of_zero_energy a R.property hW
    (le_antisymm hI (integral_nonneg fun x => hsNormSq_nonneg (Du x)))
  have hhalf : Metric.ball a (R.val / 2) ⊆ Metric.ball a R.val :=
    Metric.ball_subset_ball (by linarith only [R.property])
  have hEqHalf := ae_restrict_of_ae_restrict_of_subset hhalf hEq
  let w : Metric.ball a (R.val / 2) → Ambient q := fun _ => ⨍ y in Metric.ball a R.val, u y
  have hw : IsContinuousRepresentative (ballDomain a (R.val / 2)) u w := by
    refine ⟨continuous_const, ?_⟩
    filter_upwards [hEqHalf] with x hx _hx
    exact hx.symm
  have hNhalf := ae_restrict_of_ae_restrict_of_subset
    (hhalf.trans (Metric.ball_subset_closedBall.trans hclosed)) hN
  refine ⟨w, hw, hw.mem_closed_of_ae N.carrierSet N.isCompact.isClosed hNhalf, ?_, ?_⟩
  · intro x y
    simp only [w, sub_self, norm_zero]
  · intro v hv
    exact hv.unique hw

end StationaryHarmonicMaps.Analysis

end
