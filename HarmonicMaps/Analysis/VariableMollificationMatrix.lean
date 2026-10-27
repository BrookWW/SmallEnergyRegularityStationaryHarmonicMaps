module

public import HarmonicMaps.EnergyLemmas
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Sharp right-composition estimate for gradient columns

The Hilbert--Schmidt density of arbitrary gradient columns composed on the
right with a domain endomorphism is bounded by its squared operator norm.
The proof applies the adjoint to each target-coordinate row.
-/

public section

open scoped BigOperators

namespace HarmonicMaps

private theorem right_comp_entry_eq_adjoint {n q : ℕ}
    (A : Gradient n q) (B : Domain n →L[ℝ] Domain n) (k : Fin q) (i : Fin n) :
    (∑ j : Fin n, (B (EuclideanSpace.single i 1)) j * A j k) =
      (ContinuousLinearMap.adjoint B (WithLp.toLp 2 (fun j : Fin n => A j k))) i := by
  have h := B.adjoint_inner_left (EuclideanSpace.single i 1)
    (WithLp.toLp 2 (fun j : Fin n => A j k))
  rw [EuclideanSpace.inner_single_right] at h
  simp only [starRingEnd_apply, star_trivial, one_mul, PiLp.inner_apply,
    RCLike.inner_apply] at h
  simpa only [mul_comm] using h.symm

/-- Right composition costs exactly the squared operator norm, without a
dimension factor. Both domain and target dimensions may be zero. -/
theorem hsNormSq_right_comp_le {n q : ℕ} (A : Gradient n q)
    (B : Domain n →L[ℝ] Domain n) :
    hsNormSq (fun i => ∑ j : Fin n, (B (EuclideanSpace.single i 1)) j • A j) ≤
      ‖B‖ ^ 2 * hsNormSq A := by
  classical
  rw [hsNormSq_eq_sum_entries, hsNormSq_eq_sum_entries, Finset.sum_comm]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  conv_rhs => rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  let a : Domain n := WithLp.toLp 2 (fun j : Fin n => A j k)
  have hnorm : ‖ContinuousLinearMap.adjoint B a‖ ≤ ‖B‖ * ‖a‖ := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using
      (ContinuousLinearMap.adjoint B).le_opNorm a
  have hsquare := sq_le_sq₀ (norm_nonneg (ContinuousLinearMap.adjoint B a))
    (mul_nonneg (norm_nonneg B) (norm_nonneg a)) |>.mpr hnorm
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hsquare
  simpa only [a, right_comp_entry_eq_adjoint, Finset.mul_sum] using hsquare

/-- A nonnegative operator-norm majorant gives the same sharp HS bound. -/
theorem hsNormSq_right_comp_le_of_norm_le {n q : ℕ} (A : Gradient n q)
    (B : Domain n →L[ℝ] Domain n) {K : ℝ} (hB : ‖B‖ ≤ K) :
    hsNormSq (fun i => ∑ j : Fin n, (B (EuclideanSpace.single i 1)) j • A j) ≤
      K ^ 2 * hsNormSq A := by
  exact (hsNormSq_right_comp_le A B).trans
    (mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg B) ((norm_nonneg B).trans hB)).mpr hB)
      (hsNormSq_nonneg A))

end HarmonicMaps
