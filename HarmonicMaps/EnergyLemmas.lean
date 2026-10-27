module

public import HarmonicMaps.Energy
import HarmonicMaps.SobolevLemmas

/-! # Finiteness and real-valued formulas for Dirichlet energy

Coordinatewise L2 membership implies integrability of the Hilbert--Schmidt
density. The extended energy can then be converted to its real Bochner integral.
Finite thresholds also rule out infinite normalized energy; positive radii
ensure that this finiteness passes to the unnormalized energy.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace HarmonicMaps

variable {n q : ℕ}

/-- The HS density is nonnegative, including when there are no gradient columns. -/
theorem hsNormSq_nonneg (A : Gradient n q) : 0 ≤ hsNormSq A :=
  Finset.sum_nonneg fun i _ => sq_nonneg ‖A i‖

/-- The HS norm is the sum of squares of all entries, not the Pi maximum norm. -/
theorem hsNormSq_eq_sum_entries (A : Gradient n q) :
    hsNormSq A = ∑ i : Fin n, ∑ j : Fin q, (A i j) ^ 2 := by
  exact Finset.sum_congr rfl fun i _ => EuclideanSpace.real_norm_sq_eq (A i)

/-- L2 membership of each column gives integrability of the HS density. -/
theorem integrable_hsNormSq_of_memLp_columns
    {Du : Domain n → Gradient n q} {μ : Measure (Domain n)}
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 μ) :
    Integrable (fun x => hsNormSq (Du x)) μ := by
  exact integrable_finsetSum Finset.univ fun i _ =>
    (hDu i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)

/-- W1,2 membership on the whole domain gives an integrable HS density there. -/
theorem MemW12.integrable_hsNormSq
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (h : MemW12 Ω u Du) : IntegrableOn (fun x => hsNormSq (Du x)) Ω.val volume :=
  integrable_hsNormSq_of_memLp_columns h.2.2

/-- Local W1,2 membership gives integrability on a closed ball inside the domain. -/
theorem MemW12Loc.integrable_hsNormSq_closedBall
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (h : MemW12Loc Ω u Du) {a : Domain n} {r : ℝ}
    (hball : Metric.closedBall a r ⊆ Ω.val) :
    IntegrableOn (fun x => hsNormSq (Du x)) (Metric.closedBall a r) volume :=
  integrable_hsNormSq_of_memLp_columns fun i =>
    h.2.2 i (Metric.closedBall a r) (isCompact_closedBall a r) hball

/-- Local W1,2 membership gives integrability on an open ball with its closure in the domain. -/
theorem MemW12Loc.integrable_hsNormSq_ball
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (h : MemW12Loc Ω u Du) {a : Domain n} {r : ℝ}
    (hball : Metric.closedBall a r ⊆ Ω.val) :
    IntegrableOn (fun x => hsNormSq (Du x)) (Metric.ball a r) volume :=
  (h.integrable_hsNormSq_closedBall hball).mono_set Metric.ball_subset_closedBall

/-- Genuine integrability of the HS density rules out infinite extended energy. -/
theorem dirichletEnergy_ne_top_of_integrable
    {Du : Domain n → Gradient n q} {U : Set (Domain n)}
    (h : IntegrableOn (fun x => hsNormSq (Du x)) U volume) :
    dirichletEnergy Du U ≠ ⊤ := by
  exact (lintegral_ofReal_ne_top_iff_integrable h.aestronglyMeasurable
    (Eventually.of_forall fun x => hsNormSq_nonneg (Du x))).mpr h

/-- W1,2 membership makes the extended energy of the entire domain finite. -/
theorem MemW12.dirichletEnergy_ne_top
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (h : MemW12 Ω u Du) : dirichletEnergy Du Ω.val ≠ ⊤ :=
  dirichletEnergy_ne_top_of_integrable h.integrable_hsNormSq

/-- Local W1,2 membership makes energy finite on compactly contained balls. -/
theorem MemW12Loc.dirichletEnergy_ne_top_ball
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (h : MemW12Loc Ω u Du) {a : Domain n} {r : ℝ}
    (hball : Metric.closedBall a r ⊆ Ω.val) :
    dirichletEnergy Du (Metric.ball a r) ≠ ⊤ :=
  dirichletEnergy_ne_top_of_integrable (h.integrable_hsNormSq_ball hball)

/-- The finite extended energy is the real integral, viewed in the extended nonnegative reals. -/
theorem dirichletEnergy_eq_ofReal_integral
    {Du : Domain n → Gradient n q} {U : Set (Domain n)}
    (h : IntegrableOn (fun x => hsNormSq (Du x)) U volume) :
    dirichletEnergy Du U = ENNReal.ofReal (∫ x in U, hsNormSq (Du x)) :=
  (ofReal_integral_eq_lintegral_ofReal h
    (Eventually.of_forall fun x => hsNormSq_nonneg (Du x))).symm

/-- With actual integrability, taking `toReal` recovers the real energy integral. -/
theorem dirichletEnergy_toReal
    {Du : Domain n → Gradient n q} {U : Set (Domain n)}
    (h : IntegrableOn (fun x => hsNormSq (Du x)) U volume) :
    (dirichletEnergy Du U).toReal = ∫ x in U, hsNormSq (Du x) :=
  (integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => hsNormSq_nonneg (Du x)) h.aestronglyMeasurable).symm

/-- The normalization factor is strictly positive because the radius is positive. -/
theorem normalizationFactor_ne_zero (r : PositiveRadius) :
    ENNReal.ofReal (r.val ^ (2 - (n : ℤ))) ≠ 0 :=
  ENNReal.ofReal_ne_zero_iff.mpr (zpow_pos r.property _)

/-- Finite unnormalized energy gives finite normalized energy. -/
theorem normalizedEnergy_ne_top_of_dirichletEnergy_ne_top
    {Du : Domain n → Gradient n q} {a : Domain n} {r : PositiveRadius}
    (h : dirichletEnergy Du (Metric.ball a r.val) ≠ ⊤) :
    normalizedEnergy Du a r ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top h

/-- Positive radii ensure that finite normalized energy implies finite energy. -/
theorem dirichletEnergy_ne_top_of_normalizedEnergy_ne_top
    {Du : Domain n → Gradient n q} {a : Domain n} {r : PositiveRadius}
    (h : normalizedEnergy Du a r ≠ ⊤) :
    dirichletEnergy Du (Metric.ball a r.val) ≠ ⊤ :=
  (ENNReal.lt_top_of_mul_ne_top_right h (normalizationFactor_ne_zero (n := n) r)).ne

/-- A real threshold cannot bound infinite normalized energy. -/
theorem normalizedEnergy_ne_top_of_le_ofReal
    {Du : Domain n → Gradient n q} {a : Domain n} {r : PositiveRadius} {ε : ℝ}
    (h : normalizedEnergy Du a r ≤ ENNReal.ofReal ε) :
    normalizedEnergy Du a r ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

/-- A small normalized-energy hypothesis also makes the underlying ball energy finite. -/
theorem dirichletEnergy_ne_top_of_normalizedEnergy_le_ofReal
    {Du : Domain n → Gradient n q} {a : Domain n} {r : PositiveRadius} {ε : ℝ}
    (h : normalizedEnergy Du a r ≤ ENNReal.ofReal ε) :
    dirichletEnergy Du (Metric.ball a r.val) ≠ ⊤ :=
  dirichletEnergy_ne_top_of_normalizedEnergy_ne_top
    (normalizedEnergy_ne_top_of_le_ofReal h)

/-- Under integrability, the normalized real energy has the manuscript's exact factor. -/
theorem normalizedEnergy_toReal
    {Du : Domain n → Gradient n q} {a : Domain n} {r : PositiveRadius}
    (h : IntegrableOn (fun x => hsNormSq (Du x)) (Metric.ball a r.val) volume) :
    (normalizedEnergy Du a r).toReal =
      r.val ^ (2 - (n : ℤ)) * ∫ x in Metric.ball a r.val, hsNormSq (Du x) := by
  rw [normalizedEnergy, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (le_of_lt (zpow_pos r.property _)), dirichletEnergy_toReal h]

/-- A nonnegative real threshold also bounds the real value of normalized energy. -/
theorem normalizedEnergy_toReal_le_of_le_ofReal
    {Du : Domain n → Gradient n q} {a : Domain n} {r : PositiveRadius} {ε : ℝ}
    (hε : 0 ≤ ε) (h : normalizedEnergy Du a r ≤ ENNReal.ofReal ε) :
    (normalizedEnergy Du a r).toReal ≤ ε := by
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  exact hreal.trans_eq (ENNReal.toReal_ofReal hε)

/-- Almost-everywhere equality of gradient fields preserves extended energy, even if infinite. -/
theorem dirichletEnergy_congr_ae
    {Du Dv : Domain n → Gradient n q} {U : Set (Domain n)}
    (h : Du =ᵐ[volume.restrict U] Dv) :
    dirichletEnergy Du U = dirichletEnergy Dv U :=
  lintegral_congr_ae (h.fun_comp fun A => ENNReal.ofReal (hsNormSq A))

/-- The Dirichlet energy is independent of the chosen weak gradient of a fixed map. -/
theorem HasWeakGradient.dirichletEnergy_eq
    {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du Dv : Domain n → Gradient n q}
    (hDu : HasWeakGradient Ω u Du) (hDv : HasWeakGradient Ω u Dv)
    {U : Set (Domain n)} (hU : U ⊆ Ω.val) :
    dirichletEnergy Du U = dirichletEnergy Dv U :=
  dirichletEnergy_congr_ae
    (ae_restrict_of_ae_restrict_of_subset hU (hDu.ae_eq hDv))

/-- Normalized ball energy is also independent of the chosen weak gradient. -/
theorem HasWeakGradient.normalizedEnergy_eq
    {Ω : OpenDomain n} {u : Domain n → Ambient q}
    {Du Dv : Domain n → Gradient n q}
    (hDu : HasWeakGradient Ω u Du) (hDv : HasWeakGradient Ω u Dv)
    {a : Domain n} {r : PositiveRadius} (hball : Metric.ball a r.val ⊆ Ω.val) :
    normalizedEnergy Du a r = normalizedEnergy Dv a r := by
  unfold normalizedEnergy
  rw [hDu.dirichletEnergy_eq hDv hball]

end HarmonicMaps

end
