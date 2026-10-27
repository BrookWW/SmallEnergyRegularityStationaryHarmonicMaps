module

public import StationaryHarmonicMaps.Analysis.OrthogonalCoefficientBounds

/-!
# Actual Hilbert--Schmidt identities for the gauged energy

The full squared-norm identity of the actual coefficient encoder supplies
its inner product by polarization. A finite three-index expansion then
cancels the skew right-multiplication term. The adjoint moves left
multiplication across the same HS inner product, and an orthogonal left
factor preserves the actual encoded squared norm.
-/

public section

open HarmonicMaps

namespace StationaryHarmonicMaps

/-- Polarization of the genuine full HS norm gives the actual encoded inner product. -/
theorem encoded_inner_eq_sum_columns {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (A B : Ambient q →L[ℝ] Ambient q) :
    inner ℝ (E A) (E B) =
      ∑ j : Fin q, inner ℝ (A (EuclideanSpace.single j 1)) (B (EuclideanSpace.single j 1)) := by
  have H := hE (A + B)
  simp only [map_add, add_apply, norm_add_sq_real,
    Finset.sum_add_distrib, ← Finset.mul_sum] at H
  linarith only [H, hE A, hE B]

/-- The actual HS pairing of a matrix with its right product by a skew matrix vanishes. -/
theorem encoded_inner_mul_skew_right_eq_zero {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (B S : Ambient q →L[ℝ] Ambient q) (hS : star S = -S) :
    inner ℝ (E B) (E (B * S)) = 0 := by
  let e (j : Fin q) : Ambient q := EuclideanSpace.single j 1
  have hrepr (v : Ambient q) : (∑ k : Fin q, v k • e k) = v := by
    simpa only [e, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin q) ℝ).sum_repr v
  have hBS (j : Fin q) : (B * S) (e j) = ∑ k : Fin q, (S (e j)) k • B (e k) := by
    change B (S (e j)) = _
    conv_lhs => rw [← hrepr (S (e j)), map_sum]
    simp only [map_smul]
  have hcoeff (j k : Fin q) : (S (e j)) k = -(S (e k)) j := by
    have H := ContinuousLinearMap.adjoint_inner_left S (e j) (e k)
    have hSad : S.adjoint = -S := by
      simpa only [ContinuousLinearMap.star_eq_adjoint] using hS
    rw [hSad] at H
    simpa only [e, neg_apply, inner_neg_left,
      EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
      conj_trivial, one_mul] using H.symm
  let F (j k l : Fin q) : ℝ := (S (e j)) k * ((B (e j)) l * (B (e k)) l)
  have hF (j k l : Fin q) : F k j l = -F j k l := by
    dsimp only [F]
    rw [hcoeff k j]
    ring
  have hsum : (∑ j : Fin q, ∑ k : Fin q, ∑ l : Fin q, F j k l) =
      -(∑ j : Fin q, ∑ k : Fin q, ∑ l : Fin q, F j k l) := by
    calc
      _ = ∑ j : Fin q, ∑ k : Fin q, ∑ l : Fin q, F k j l := Finset.sum_comm
      _ = ∑ j : Fin q, ∑ k : Fin q, ∑ l : Fin q, -F j k l := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        exact Finset.sum_congr rfl fun l _ => hF j k l
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have hterm (j k : Fin q) :
      inner ℝ (B (e j)) ((S (e j)) k • B (e k)) = ∑ l : Fin q, F j k l := by
    rw [real_inner_smul_right, PiLp.inner_apply]
    simp only [Real.inner_apply, Finset.mul_sum, F]
  have hexpand : inner ℝ (E B) (E (B * S)) =
      ∑ j : Fin q, ∑ k : Fin q, ∑ l : Fin q, F j k l := by
    rw [encoded_inner_eq_sum_columns E hE]
    change (∑ j : Fin q, inner ℝ (B (e j)) ((B * S) (e j))) = _
    simp only [hBS, inner_sum, hterm]
  rw [hexpand]
  linarith only [hsum]

/-- The genuine adjoint moves a left factor across the actual encoded HS inner product. -/
theorem encoded_inner_mul_left_eq_adjoint {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (B P T : Ambient q →L[ℝ] Ambient q) :
    inner ℝ (E B) (E (P * T)) = inner ℝ (E (star P * B)) (E T) := by
  rw [encoded_inner_eq_sum_columns E hE, encoded_inner_eq_sum_columns E hE]
  apply Finset.sum_congr rfl
  intro j _
  exact (ContinuousLinearMap.adjoint_inner_left P (T (EuclideanSpace.single j 1))
    (B (EuclideanSpace.single j 1))).symm

/-- An actual orthogonal left factor preserves the genuine encoded HS square. -/
theorem encoded_norm_sq_mul_left_orthogonal {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q * q))
    (hE : ∀ T : Ambient q →L[ℝ] Ambient q,
      ‖E T‖ ^ 2 = ∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2)
    (P T : Ambient q →L[ℝ] Ambient q) (hP : star P * P = 1) :
    ‖E (P * T)‖ ^ 2 = ‖E T‖ ^ 2 := by
  simp only [hE, mul_apply_eq_comp, Analysis.norm_sq_apply_orthogonal P hP]

end StationaryHarmonicMaps

end
