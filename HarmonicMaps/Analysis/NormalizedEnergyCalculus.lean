module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Calculus of normalized energy on positive radius intervals

An absolutely continuous energy primitive and its a.e. radius boundary
identity yield the exact normalized increment, including the outer endpoint.
The integer exponent is the one in the existing normalized energy definition.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace HarmonicMaps

/-- Integer powers are continuously differentiable on an interval bounded
away from zero, including the zero exponent. -/
theorem contDiffOn_zpow_positive_interval (k : ℤ) {s r : ℝ} (hs : 0 < s) :
    ContDiffOn ℝ 1 (fun t : ℝ => t ^ k) (Icc s r) := by
  cases k with
  | ofNat m =>
    simpa only [zpow_natCast, id_eq] using! (contDiffOn_id.pow m : ContDiffOn ℝ 1
      (fun t : ℝ => t ^ m) (Icc s r))
  | negSucc m =>
    have hi : ContDiffOn ℝ 1 (fun t : ℝ => (t ^ (m + 1))⁻¹) (Icc s r) :=
      (contDiffOn_id.pow (m + 1)).inv (fun t ht => pow_ne_zero _ (ne_of_gt (hs.trans_le ht.1)))
    simpa only [zpow_negSucc] using hi

/-- The radius boundary identity gives the exact normalized derivative at
every positive point where the original energy is differentiable. -/
theorem normalized_energy_hasDerivAt (n : ℕ) {e : ℝ → ℝ} {p g t : ℝ}
    (ht : 0 < t) (he : HasDerivAt e p t)
    (hboundary : ((n : ℝ) - 2) * e t - t * p = -2 * t * g) :
    HasDerivAt (fun z : ℝ => z ^ (2 - (n : ℤ)) * e z)
      (2 * t ^ (2 - (n : ℤ)) * g) t := by
  have hshift : t ^ (2 - (n : ℤ) - 1) * t = t ^ (2 - (n : ℤ)) := by
    calc
      _ = t ^ (2 - (n : ℤ) - 1) * t ^ (1 : ℤ) := by rw [zpow_one]
      _ = t ^ (2 - (n : ℤ) - 1 + 1) := (zpow_add₀ ht.ne' _ _).symm
      _ = _ := by congr 1; omega
  have hlin : (2 - (n : ℝ)) * e t + t * p = 2 * t * g := by
    linarith only [hboundary]
  have h := (hasDerivAt_zpow (2 - (n : ℤ)) t (Or.inl ht.ne')).mul he
  convert! h using 1
  simp only [Int.cast_sub, Int.cast_ofNat, Int.cast_natCast]
  calc
    2 * t ^ (2 - (n : ℤ)) * g =
        t ^ (2 - (n : ℤ) - 1) * (2 * t * g) := by rw [← hshift]; ring
    _ = t ^ (2 - (n : ℤ) - 1) * ((2 - (n : ℝ)) * e t + t * p) := by rw [hlin]
    _ = _ := by rw [← hshift]; ring

/-- Absolute continuity, the exact a.e. normalized derivative, weighted L1,
and the exact increment follow from the genuine one-dimensional energy
primitive. The upper radius may equal the full outer endpoint. -/
theorem normalized_energy_increment (n : ℕ) {e p g : ℝ → ℝ} {s r R : ℝ}
    (hs : 0 < s) (hsr : s < r) (hrR : r ≤ R)
    (he : AbsolutelyContinuousOnInterval e 0 R)
    (hder : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R), HasDerivAt e (p t) t)
    (hboundary : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R),
      ((n : ℝ) - 2) * e t - t * p t = -2 * t * g t)
    (hg : IntegrableOn g (Ioo (0 : ℝ) R) volume) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => t ^ (2 - (n : ℤ)) * e t) s r ∧
    (∀ᵐ t ∂volume.restrict (Ioo s r), HasDerivAt
      (fun z : ℝ => z ^ (2 - (n : ℤ)) * e z) (2 * t ^ (2 - (n : ℤ)) * g t) t) ∧
    IntervalIntegrable (fun t : ℝ => t ^ (2 - (n : ℤ)) * g t) volume s r ∧
    r ^ (2 - (n : ℤ)) * e r - s ^ (2 - (n : ℤ)) * e s =
      2 * ∫ t in s..r, t ^ (2 - (n : ℤ)) * g t := by
  have hR : 0 < R := (hs.trans hsr).trans_le hrR
  have hsub : Ioo s r ⊆ Ioo (0 : ℝ) R := by
    intro t ht
    exact ⟨hs.trans ht.1, ht.2.trans_le hrR⟩
  have he' : AbsolutelyContinuousOnInterval e s r := he.mono (by
    rw [uIcc_of_le hsr.le, uIcc_of_le hR.le]
    intro t ht
    exact ⟨hs.le.trans ht.1, ht.2.trans hrR⟩)
  have hpow := contDiffOn_zpow_positive_interval (2 - (n : ℤ)) (r := r) hs
  have hpac : AbsolutelyContinuousOnInterval (fun t : ℝ => t ^ (2 - (n : ℤ))) s r := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hsr.le] using hpow
  have hac : AbsolutelyContinuousOnInterval (fun t : ℝ => t ^ (2 - (n : ℤ)) * e t) s r :=
    hpac.mul he'
  have hd : ∀ᵐ t ∂volume.restrict (Ioo s r), HasDerivAt
      (fun z : ℝ => z ^ (2 - (n : ℤ)) * e z) (2 * t ^ (2 - (n : ℤ)) * g t) t := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hder,
      ae_restrict_of_ae_restrict_of_subset hsub hboundary,
      ae_restrict_mem measurableSet_Ioo] with t hdt hbt ht
    exact normalized_energy_hasDerivAt n (hs.trans ht.1) hdt hbt
  have hweighted : IntegrableOn (fun t : ℝ => t ^ (2 - (n : ℤ)) * g t) (Ioo s r) volume :=
    IntegrableOn.continuousOn_mul_of_subset hpow.continuousOn (hg.mono_set hsub)
      isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self
  have hI : IntervalIntegrable (fun t : ℝ => t ^ (2 - (n : ℤ)) * g t) volume s r :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hsr.le).mpr hweighted
  refine ⟨hac, hd, hI, ?_⟩
  rw [← hac.integral_deriv_eq_sub]
  have hdEq : (fun t => deriv (fun z : ℝ => z ^ (2 - (n : ℤ)) * e z) t) =ᵐ[
      volume.restrict (Ioo s r)] (fun t => 2 * t ^ (2 - (n : ℤ)) * g t) :=
    hd.mono (fun _ h => h.deriv)
  have heq : (∫ t in s..r, deriv (fun z : ℝ => z ^ (2 - (n : ℤ)) * e z) t) =
      ∫ t in s..r, 2 * t ^ (2 - (n : ℤ)) * g t := by
    apply intervalIntegral.integral_congr_ae_restrict
    simpa only [uIoc_of_le hsr.le, ← restrict_Ioo_eq_restrict_Ioc] using hdEq
  rw [heq]
  simp only [mul_assoc, intervalIntegral.integral_const_mul]

end HarmonicMaps
