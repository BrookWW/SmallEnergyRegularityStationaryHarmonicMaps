module

public import StationaryHarmonicMaps.Foundation.CriticalGradientMorrey
public import StationaryHarmonicMaps.Analysis.LpL1Bound
public import HarmonicMaps.EnergyLemmas

/-!
# Actual local integral bounds from the complete critical supremum

The field consists of genuine Euclidean HS columns. Its L² membership gives
actual integrability before the extended critical bound is converted to real
energy. No potential map or finite total energy on the full domain is needed.
-/

public section

open HarmonicMaps MeasureTheory Set

namespace StationaryHarmonicMaps.Analysis

/-- L² columns give the actual integrability of their full HS square. -/
theorem integrable_hsNormSq_of_columns {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {n q : ℕ} (F : X → Gradient n q) (hF : ∀ i, MemLp (fun x => F x i) 2 μ) :
    Integrable (fun x => hsNormSq (F x)) μ :=
  integrable_finsetSum _ (fun i _ => (hF i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))

/-- Every actual L² subregion of a truncated ball has the scale-correct real HS energy bound. -/
theorem integral_hsNormSq_le_of_criticalMorrey {n q : ℕ}
    (F : Domain n → Gradient n q) {D S : Set (Domain n)} {x : Domain n} {r M : ℝ}
    (hx : x ∈ D) (hr : 0 < r) (hM : 0 ≤ M)
    (hsub : S ⊆ Metric.ball x r ∩ D)
    (hF : ∀ i, MemLp (fun y => F y i) 2 (volume.restrict S))
    (hcritical : criticalGradientMorreySquare F D ≤ ENNReal.ofReal M) :
    (∫ y in S, hsNormSq (F y)) ≤ M * r ^ ((n : ℝ) - 2) := by
  have hInt := integrable_hsNormSq_of_columns F hF
  have hI : 0 ≤ ∫ y in S, hsNormSq (F y) := integral_nonneg fun y => hsNormSq_nonneg (F y)
  have hc : 0 < r ^ (2 - (n : ℤ)) := zpow_pos hr _
  have hEnergy : dirichletEnergy F S ≤ dirichletEnergy F (Metric.ball x r ∩ D) :=
    lintegral_mono_set hsub
  have hle : ENNReal.ofReal (r ^ (2 - (n : ℤ))) *
      dirichletEnergy F (Metric.ball x r ∩ D) ≤ criticalGradientMorreySquare F D :=
    le_iSup_of_le (⟨x, hx⟩ : D)
      (le_iSup_of_le (⟨r, hr⟩ : PositiveRadius) le_rfl)
  have hterm := hle.trans hcritical
  have hbound := (mul_le_mul_right hEnergy (ENNReal.ofReal (r ^ (2 - (n : ℤ))))).trans hterm
  rw [dirichletEnergy_eq_ofReal_integral hInt, ← ENNReal.ofReal_mul hc.le] at hbound
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal (mul_nonneg hc.le hI), ENNReal.toReal_ofReal hM] at hreal
  have hcancel : r ^ ((n : ℝ) - 2) * r ^ (2 - (n : ℤ)) = 1 := by
    rw [← Real.rpow_intCast, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
      ← Real.rpow_add hr]
    norm_num
  calc
    _ = r ^ ((n : ℝ) - 2) * (r ^ (2 - (n : ℤ)) * ∫ y in S, hsNormSq (F y)) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ r ^ ((n : ℝ) - 2) * M := mul_le_mul_of_nonneg_left hreal (Real.rpow_nonneg hr.le _)
    _ = _ := mul_comm _ _

/-- The corresponding actual L² energy root has the exponent n/2-1. -/
theorem sqrt_integral_hsNormSq_le_of_criticalMorrey {n q : ℕ}
    (F : Domain n → Gradient n q) {D S : Set (Domain n)} {x : Domain n} {r M : ℝ}
    (hx : x ∈ D) (hr : 0 < r) (hM : 0 ≤ M)
    (hsub : S ⊆ Metric.ball x r ∩ D)
    (hF : ∀ i, MemLp (fun y => F y i) 2 (volume.restrict S))
    (hcritical : criticalGradientMorreySquare F D ≤ ENNReal.ofReal M) :
    Real.sqrt (∫ y in S, hsNormSq (F y)) ≤ Real.sqrt M * r ^ ((n : ℝ) / 2 - 1) := by
  have h := Real.sqrt_le_sqrt (integral_hsNormSq_le_of_criticalMorrey F hx hr hM hsub hF hcritical)
  have hpower : Real.sqrt (r ^ ((n : ℝ) - 2)) = r ^ ((n : ℝ) / 2 - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le]
    congr 1
    ring
  exact h.trans_eq (by rw [Real.sqrt_mul hM, hpower])

end StationaryHarmonicMaps.Analysis

end
