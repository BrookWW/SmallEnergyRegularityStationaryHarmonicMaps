module

public import StationaryHarmonicMaps.Geometry.GaugedEnergyAlgebra

/-! # The actual HS pairing with the skew part of an operator -/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps

/-- Transposition is self-adjoint for the actual full HS coordinate inner product. -/
theorem encoded_inner_star_right_eq_star_left {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (Z T : Ambient q →L[ℝ] Ambient q) :
    inner ℝ (E Z) (E (star T)) = inner ℝ (E (star Z)) (E T) := by
  let e (j : Fin q) : Ambient q := EuclideanSpace.single j 1
  have hc (A : Ambient q →L[ℝ] Ambient q) (j k : Fin q) :
      (star A (e j)) k = (A (e k)) j := by
    have H := ContinuousLinearMap.adjoint_inner_left A (e k) (e j)
    simpa only [ContinuousLinearMap.star_eq_adjoint, e,
      EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
      conj_trivial, one_mul] using H
  rw [encoded_inner_eq_sum_columns E hE, encoded_inner_eq_sum_columns E hE]
  change (∑ j : Fin q, inner ℝ (Z (e j)) (star T (e j))) =
    ∑ j : Fin q, inner ℝ (star Z (e j)) (T (e j))
  simp_rw [PiLp.inner_apply, Real.inner_apply, hc]
  rw [Finset.sum_comm]

/-- Against an actual skew operator, taking the genuine skew part of the test preserves the HS pairing. -/
theorem encoded_inner_skew_part_eq {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (Z T : Ambient q →L[ℝ] Ambient q) (hZ : star Z = -Z) :
    inner ℝ (E Z) (E ((1 / 2 : ℝ) • (T - star T))) = inner ℝ (E Z) (E T) := by
  have H : inner ℝ (E Z) (E (star T)) = - inner ℝ (E Z) (E T) := by
    rw [encoded_inner_star_right_eq_star_left E hE, hZ, map_neg, inner_neg_left]
  rw [map_smul, map_sub, real_inner_smul_right, inner_sub_right, H]
  ring

end StationaryHarmonicMaps

end
