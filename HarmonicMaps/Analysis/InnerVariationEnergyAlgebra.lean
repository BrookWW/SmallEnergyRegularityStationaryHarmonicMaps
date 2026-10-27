module

public import HarmonicMaps.Analysis.InnerVariationEnergyAlgebraBasic

/-!
# First variation of the actual inner-coordinate energy density

The inverse columns use Mathlib's ring inverse. The imported operator
certificates prove that this is the genuine inverse throughout the
norm-small parameter interval. The exact energy derivative retains the
original Hilbert--Schmidt normalization and the same input gradient columns.
-/

public section

open Set Filter
open scoped ContDiff Topology BigOperators

namespace HarmonicMaps

set_option backward.isDefEq.respectTransparency false in
/-- At zero parameter the inverse-coordinate gradient is the original gradient. -/
theorem innerVariation_inverse_column_zero {n q : ℕ}
    (B : Domain n →L[ℝ] Domain n) (A : Gradient n q) (i : Fin n) :
    (∑ j : Fin n, (Ring.inverse (1 + (0 : ℝ) • B) (EuclideanSpace.single i 1)) j • A j) = A i := by
  have hzero : ((1 : Domain n →L[ℝ] Domain n) + (0 : ℝ) • B) = 1 := by
    ext x j
    simp
  rw [hzero]
  simp only [Ring.inverse_one, one_apply_eq_self, PiLp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, one_smul]
  · intro j _ hji
    simp only [if_neg hji, zero_smul]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

set_option backward.isDefEq.respectTransparency false in
/-- The inverse-coordinate gradient column has its actual parameter derivative. -/
theorem innerVariation_inverse_column_hasDerivAt {n q : ℕ}
    (B : Domain n →L[ℝ] Domain n) (A : Gradient n q) (i : Fin n) :
    HasDerivAt (fun t : ℝ => ∑ j : Fin n,
      (Ring.inverse (1 + t • B) (EuclideanSpace.single i 1)) j • A j)
      (-(∑ j : Fin n, (B (EuclideanSpace.single i 1)) j • A j)) 0 := by
  have hinv := innerVariation_operator_inverse_hasDerivAt B
  have hvec := hinv.clm_apply (hasDerivAt_const (0 : ℝ) (EuclideanSpace.single i 1))
  have hcoord (j : Fin n) : HasDerivAt
      (fun t : ℝ => (Ring.inverse (1 + t • B) (EuclideanSpace.single i 1)) j)
      (-(B (EuclideanSpace.single i 1)) j) 0 := by
    have h := (EuclideanSpace.proj j).hasFDerivAt.comp_hasDerivAt 0 hvec
    simpa using! h
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (fun j (_ : j ∈ Finset.univ) => (hcoord j).smul_const (A j))
  simpa only [neg_smul, Finset.sum_neg_distrib, Finset.sum_fn] using hsum

/-- The squared Hilbert--Schmidt norm of the actual inverse-coordinate
gradient has the precise stress-contraction derivative. -/
theorem innerVariation_inverse_hs_hasDerivAt {n q : ℕ}
    (B : Domain n →L[ℝ] Domain n) (A : Gradient n q) :
    HasDerivAt (fun t : ℝ => hsNormSq (fun i => ∑ j : Fin n,
      (Ring.inverse (1 + t • B) (EuclideanSpace.single i 1)) j • A j))
      (-2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (A i) (A j) * (B (EuclideanSpace.single i 1)) j) 0 := by
  have hcol (i : Fin n) := (innerVariation_inverse_column_hasDerivAt B A i).norm_sq
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i (_ : i ∈ Finset.univ) => hcol i)
  have hcoeff : (∑ i : Fin n, 2 * inner ℝ
      (∑ j : Fin n, (Ring.inverse (1 + (0 : ℝ) • B) (EuclideanSpace.single i 1)) j • A j)
      (-(∑ j : Fin n, (B (EuclideanSpace.single i 1)) j • A j))) =
      -2 * ∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (A i) (A j) * (B (EuclideanSpace.single i 1)) j := by
    simp only [innerVariation_inverse_column_zero, inner_neg_right, inner_sum,
      real_inner_smul_right, mul_neg, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcoeff] at hsum
  simpa only [Finset.sum_fn, hsNormSq] using hsum

/-- The exact first variation of the genuine transformed HS energy density.
The determinant is the absolute Jacobian, and the coefficient has no factor
of one half. Both positive and negative parameters are used by `HasDerivAt`. -/
theorem innerVariation_energy_density_hasDerivAt {n q : ℕ}
    (B : Domain n →L[ℝ] Domain n) (A : Gradient n q) :
    HasDerivAt (fun t : ℝ => |(1 + t • B).det| *
      hsNormSq (fun i => ∑ j : Fin n,
        (Ring.inverse (1 + t • B) (EuclideanSpace.single i 1)) j • A j))
      (hsNormSq A * (∑ i : Fin n, (B (EuclideanSpace.single i 1)) i) -
        2 * ∑ i : Fin n, ∑ j : Fin n,
          inner ℝ (A i) (A j) * (B (EuclideanSpace.single i 1)) j) 0 := by
  have h := (innerVariation_operator_abs_det_hasDerivAt B).mul
    (innerVariation_inverse_hs_hasDerivAt B A)
  have hz : hsNormSq (fun i => ∑ j : Fin n,
      (Ring.inverse (1 + (0 : ℝ) • B) (EuclideanSpace.single i 1)) j • A j) = hsNormSq A := by
    congr 1
    funext i
    exact innerVariation_inverse_column_zero B A i
  have hzero : ((1 : Domain n →L[ℝ] Domain n) + (0 : ℝ) • B) = 1 := by
    ext x j
    simp
  have hdetzero : |((1 : Domain n →L[ℝ] Domain n) + (0 : ℝ) • B).det| = 1 := by
    rw [hzero]
    simp [ContinuousLinearMap.det]
  simp only [hz, hdetzero, one_mul] at h
  convert! h using 1
  ring

end HarmonicMaps
