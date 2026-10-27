module

public import StationaryHarmonicMaps.Foundation.CriticalGradientMorrey
public import StationaryHarmonicMaps.Analysis.LpMorreyRepresentative
public import HarmonicMaps.SobolevRestriction
public import HarmonicMaps.EnergyLemmas

/-!
# Critical Morrey control of the actual contained-ball mean oscillation

Finite Sobolev data restrict under open-set inclusion, including equality of
the inner and outer balls. The literal critical supremum controls each
contained ball's normalized HS energy. The actual L1 Poincare inequality
then gives a radius-independent mean-oscillation bound.
-/

public section

open HarmonicMaps MeasureTheory Set Metric
open scoped ENNReal

namespace StationaryHarmonicMaps

/-- Finite Sobolev membership restricts to any smaller open domain. -/
theorem memW12_of_openDomain_subset {n q : ℕ} {Ω Ω' : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (hsub : Ω'.val ⊆ Ω.val) : MemW12 Ω' u Du := by
  refine ⟨hu.1.mono hsub, ?_, ?_⟩
  · exact MemLp.mono_measure (Measure.restrict_mono_set volume hsub) hu.2.1
  · intro i
    exact MemLp.mono_measure (Measure.restrict_mono_set volume hsub) (hu.2.2 i)

/-- Every positive-radius contained ball is one term of the literal critical supremum. -/
theorem normalizedEnergy_le_criticalMorrey_of_ball_subset {n q : ℕ}
    (Du : Domain n → Gradient n q) {D : Set (Domain n)} {x : Domain n} {r : ℝ}
    (hr : 0 < r) (hsub : Metric.ball x r ⊆ D) :
    normalizedEnergy Du x ⟨r, hr⟩ ≤ criticalGradientMorreySquare Du D := by
  have hxD : x ∈ D := hsub (Metric.mem_ball_self hr)
  have hterm : ENNReal.ofReal (r ^ (2 - (n : ℤ))) *
      dirichletEnergy Du (Metric.ball x r ∩ D) ≤ criticalGradientMorreySquare Du D :=
    le_iSup_of_le (⟨x, hxD⟩ : D) (le_iSup_of_le (⟨r, hr⟩ : PositiveRadius) le_rfl)
  simpa only [normalizedEnergy, inter_eq_left.mpr hsub] using hterm

/-- A finite normalized-energy bound gives the exact real HS integral growth. -/
theorem integral_hsNormSq_le_of_normalizedEnergy_bound {n q : ℕ}
    (x : Domain n) {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain x r) u Du)
    (hbound : normalizedEnergy Du x ⟨r, hr⟩ ≤ ENNReal.ofReal M) :
    (∫ y in Metric.ball x r, hsNormSq (Du y)) ≤ M * r ^ ((n : ℝ) - 2) := by
  have hreal := normalizedEnergy_toReal_le_of_le_ofReal hM hbound
  rw [normalizedEnergy_toReal hu.integrable_hsNormSq] at hreal
  have hcancel : r ^ ((n : ℝ) - 2) * r ^ (2 - (n : ℤ)) = 1 := by
    rw [← Real.rpow_intCast, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
      ← Real.rpow_add hr]
    norm_num
  calc
    _ = r ^ ((n : ℝ) - 2) *
        (r ^ (2 - (n : ℤ)) * ∫ y in Metric.ball x r, hsNormSq (Du y)) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ r ^ ((n : ℝ) - 2) * M :=
      mul_le_mul_of_nonneg_left hreal (Real.rpow_nonneg hr.le _)
    _ = _ := mul_comm _ _

/-- A single actual normalized-energy bound controls that ball's mean oscillation. -/
theorem meanOscillation_le_of_normalizedEnergy_bound {n q : ℕ}
    (x : Domain n) {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain x r) u Du)
    (hbound : normalizedEnergy Du x ⟨r, hr⟩ ≤ ENNReal.ofReal M) :
    (⨍ y in Metric.ball x r, ‖u y - (⨍ z in Metric.ball x r, u z)‖) ≤
      (((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) *
        (volume.real (Metric.ball (0 : Domain n) 1)) ^ (-(1 / (2 : ℝ)))) * Real.sqrt M := by
  have hI := integral_hsNormSq_le_of_normalizedEnergy_bound x hr hM hu hbound
  have hsquare (y : Domain n) : (Real.sqrt (hsNormSq (Du y))) ^ 2 = hsNormSq (Du y) :=
    Real.sq_sqrt (hsNormSq_nonneg _)
  have hgrowth : (∫ y in Metric.ball x r, (Real.sqrt (hsNormSq (Du y))) ^ (2 : ℝ)) ≤
      (Real.sqrt M) ^ (2 : ℝ) * r ^ ((n : ℝ) - 2 + 2 * (0 : ℝ)) := by
    simpa only [Real.rpow_two, hsquare, Real.sq_sqrt hM, mul_zero, add_zero] using hI
  have h := sobolev_meanOscillation_of_lp_growth (p := 2) (α := 0)
    x hr (by norm_num) (by norm_num) (Real.sqrt_nonneg M) hu hgrowth
  simpa only [Real.rpow_zero, mul_one] using h

/-- One squared critical Morrey bound controls every contained ball's actual mean oscillation. -/
theorem contained_ball_meanOscillation_le_of_criticalMorrey_bound
    (n : ℕ) (_hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (R M : ℝ)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      0 < R → MemW12 (ballDomain a R) u Du → 0 ≤ M →
      criticalGradientMorreySquare Du (Metric.ball a R) ≤ ENNReal.ofReal M →
      ∀ (x : Domain n) (r : ℝ), 0 < r → Metric.ball x r ⊆ Metric.ball a R →
        (⨍ y in Metric.ball x r, ‖u y - (⨍ z in Metric.ball x r, u z)‖) ≤ C * Real.sqrt M := by
  let C₀ : ℝ := ((2 : ℝ) ^ (n + 1) * Real.sqrt (n : ℝ)) *
    (volume.real (Metric.ball (0 : Domain n) 1)) ^ (-(1 / (2 : ℝ)))
  let C : ℝ := 1 + C₀
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hle : C₀ ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro q a R M u Du _hR hu hM hcritical x r hr hsub
  have hW : MemW12 (ballDomain x r) u Du := memW12_of_openDomain_subset hu hsub
  have hbound : normalizedEnergy Du x ⟨r, hr⟩ ≤ ENNReal.ofReal M :=
    (normalizedEnergy_le_criticalMorrey_of_ball_subset Du hr hsub).trans hcritical
  exact (meanOscillation_le_of_normalizedEnergy_bound x hr hM hW hbound).trans
    (mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg M))

end StationaryHarmonicMaps

end
