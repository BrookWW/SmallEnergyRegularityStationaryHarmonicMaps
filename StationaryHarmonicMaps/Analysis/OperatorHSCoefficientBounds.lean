module

public import HarmonicMaps.Sobolev
public import StationaryHarmonicMaps.Geometry.ProjectionCommutator
public import StationaryHarmonicMaps.Analysis.LpL1Bound
public import Mathlib.Analysis.Real.Sqrt

/-!
# Operator bounds for the actual Hilbert--Schmidt coefficients

The square sum of all matrix entries is the square sum of the images of the
Euclidean unit columns. It is bounded by the ambient dimension times the
squared operator norm. Applying this bridge to commutators gives the matrix
one-form Hilbert--Schmidt bound with constant `2 * sqrt q * L`.
-/

public section

open HarmonicMaps MeasureTheory Filter
open scoped BigOperators

namespace StationaryHarmonicMaps.Analysis

/-- The column square sum is exactly the sum of squares of every real matrix entry. -/
theorem operator_column_sq_sum_eq_entries_sq_sum {q : ℕ}
    (T : Ambient q →L[ℝ] Ambient q) :
    (∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2) =
      ∑ j : Fin q, ∑ k : Fin q, (T (EuclideanSpace.single j 1) k) ^ 2 :=
  Finset.sum_congr rfl fun j _ =>
    EuclideanSpace.real_norm_sq_eq (T (EuclideanSpace.single j 1))

/-- The actual matrix Hilbert--Schmidt square sum is at most q times the operator norm squared. -/
theorem operator_column_sq_sum_le_dim_mul_opNorm_sq {q : ℕ}
    (T : Ambient q →L[ℝ] Ambient q) :
    (∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2) ≤ (q : ℝ) * ‖T‖ ^ 2 := by
  have hcolumn (j : Fin q) : ‖T (EuclideanSpace.single j 1)‖ ≤ ‖T‖ := by
    simpa only [PiLp.norm_single, norm_one, mul_one] using
      T.le_opNorm (EuclideanSpace.single j 1)
  calc
    (∑ j : Fin q, ‖T (EuclideanSpace.single j 1)‖ ^ 2) ≤
        ∑ _j : Fin q, ‖T‖ ^ 2 :=
      Finset.sum_le_sum fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hcolumn j) 2
    _ = (q : ℝ) * ‖T‖ ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The one-form column sum includes all three finite coefficient indices. -/
theorem commutator_hs_sq_eq_entries_sq_sum {n q : ℕ}
    (P : Ambient q →L[ℝ] Ambient q) (D : Fin n → Ambient q →L[ℝ] Ambient q) :
    (∑ i : Fin n, ∑ j : Fin q,
      ‖projectionCommutator P (D i) (EuclideanSpace.single j 1)‖ ^ 2) =
      ∑ i : Fin n, ∑ j : Fin q, ∑ k : Fin q,
        (projectionCommutator P (D i) (EuclideanSpace.single j 1) k) ^ 2 :=
  Finset.sum_congr rfl fun i _ =>
    operator_column_sq_sum_eq_entries_sq_sum (projectionCommutator P (D i))

/-- The coefficient square bound preserves every gradient column, including empty index sets. -/
theorem commutator_hs_sq_le {n q : ℕ}
    (P : Ambient q →L[ℝ] Ambient q) (D : Fin n → Ambient q →L[ℝ] Ambient q)
    (v : Fin n → Ambient q) {L : ℝ} (hP : ‖P‖ ≤ 1) (_hL : 0 ≤ L)
    (hD : ∀ i : Fin n, ‖D i‖ ≤ L * ‖v i‖) :
    (∑ i : Fin n, ∑ j : Fin q,
      ‖projectionCommutator P (D i) (EuclideanSpace.single j 1)‖ ^ 2) ≤
      (q : ℝ) * (2 * L) ^ 2 * ∑ i : Fin n, ‖v i‖ ^ 2 := by
  have hcomm (i : Fin n) : ‖projectionCommutator P (D i)‖ ≤ 2 * L * ‖v i‖ := by
    calc
      ‖projectionCommutator P (D i)‖ ≤ 2 * ‖P‖ * ‖D i‖ :=
        norm_projectionCommutator_le P (D i)
      _ ≤ 2 * 1 * ‖D i‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hP (by norm_num)) (norm_nonneg _)
      _ = 2 * ‖D i‖ := by ring
      _ ≤ 2 * (L * ‖v i‖) := mul_le_mul_of_nonneg_left (hD i) (by norm_num)
      _ = 2 * L * ‖v i‖ := by ring
  have hcolumn (i : Fin n) :
      (∑ j : Fin q, ‖projectionCommutator P (D i) (EuclideanSpace.single j 1)‖ ^ 2) ≤
        (q : ℝ) * (2 * L) ^ 2 * ‖v i‖ ^ 2 := by
    calc
      _ ≤ (q : ℝ) * ‖projectionCommutator P (D i)‖ ^ 2 :=
        operator_column_sq_sum_le_dim_mul_opNorm_sq _
      _ ≤ (q : ℝ) * (2 * L * ‖v i‖) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hcomm i) 2) (Nat.cast_nonneg q)
      _ = (q : ℝ) * (2 * L) ^ 2 * ‖v i‖ ^ 2 := by ring
  calc
    _ ≤ ∑ i : Fin n, (q : ℝ) * (2 * L) ^ 2 * ‖v i‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hcolumn i
    _ = (q : ℝ) * (2 * L) ^ 2 * ∑ i : Fin n, ‖v i‖ ^ 2 :=
      (Finset.mul_sum _ _ _).symm

/-- Taking square roots gives the genuine matrix one-form Hilbert--Schmidt norm bound. -/
theorem commutator_hsNorm_le {n q : ℕ}
    (P : Ambient q →L[ℝ] Ambient q) (D : Fin n → Ambient q →L[ℝ] Ambient q)
    (v : Fin n → Ambient q) {L : ℝ} (hP : ‖P‖ ≤ 1) (hL : 0 ≤ L)
    (hD : ∀ i : Fin n, ‖D i‖ ≤ L * ‖v i‖) :
    Real.sqrt (∑ i : Fin n, ∑ j : Fin q,
      ‖projectionCommutator P (D i) (EuclideanSpace.single j 1)‖ ^ 2) ≤
      (2 * Real.sqrt (q : ℝ) * L) * Real.sqrt (∑ i : Fin n, ‖v i‖ ^ 2) := by
  have hvnonneg : 0 ≤ ∑ i : Fin n, ‖v i‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hright : 0 ≤ (2 * Real.sqrt (q : ℝ) * L) *
      Real.sqrt (∑ i : Fin n, ‖v i‖ ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hL)
      (Real.sqrt_nonneg _)
  have hsq : ((2 * Real.sqrt (q : ℝ) * L) *
      Real.sqrt (∑ i : Fin n, ‖v i‖ ^ 2)) ^ 2 =
      (q : ℝ) * (2 * L) ^ 2 * ∑ i : Fin n, ‖v i‖ ^ 2 := by
    calc
      _ = 4 * (Real.sqrt (q : ℝ)) ^ 2 * L ^ 2 *
          (Real.sqrt (∑ i : Fin n, ‖v i‖ ^ 2)) ^ 2 := by ring
      _ = _ := by
        rw [Real.sq_sqrt (Nat.cast_nonneg q), Real.sq_sqrt hvnonneg]
        ring
  exact Real.sqrt_le_iff.mpr ⟨hright,
    (commutator_hs_sq_le P D v hP hL hD).trans_eq hsq.symm⟩

/-- Measurable operator coefficients and a genuine L² gradient bound give L² HS coefficients. -/
theorem memLp_commutator_hsNorm {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {n q : ℕ} (P : X → Ambient q →L[ℝ] Ambient q)
    (D : X → Fin n → Ambient q →L[ℝ] Ambient q) (v : X → Fin n → Ambient q)
    {L : ℝ} (hL : 0 ≤ L) (hPmeas : AEStronglyMeasurable P μ)
    (hDmeas : ∀ i : Fin n, AEStronglyMeasurable (fun x => D x i) μ)
    (hP : ∀ᵐ x ∂μ, ‖P x‖ ≤ 1)
    (hD : ∀ᵐ x ∂μ, ∀ i : Fin n, ‖D x i‖ ≤ L * ‖v x i‖)
    (hv : ∀ i : Fin n, MemLp (fun x => v x i) 2 μ) :
    MemLp (fun x => Real.sqrt (∑ i : Fin n, ∑ j : Fin q,
      ‖projectionCommutator (P x) (D x i) (EuclideanSpace.single j 1)‖ ^ 2)) 2 μ := by
  have hcomm (i : Fin n) : AEStronglyMeasurable
      (fun x => projectionCommutator (P x) (D x i)) μ := by
    have hfun : (P * (fun x => D x i) - (fun x => D x i) * P) =
        (fun x => projectionCommutator (P x) (D x i)) := rfl
    rw [← hfun]
    exact (hPmeas.mul (hDmeas i)).sub ((hDmeas i).mul hPmeas)
  have hcolumn (i : Fin n) (j : Fin q) : AEStronglyMeasurable
      (fun x => projectionCommutator (P x) (D x i) (EuclideanSpace.single j 1)) μ := by
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      ((ContinuousLinearMap.apply ℝ (Ambient q)
        (EuclideanSpace.single j (1 : ℝ))).continuous).comp_aestronglyMeasurable (hcomm i)
  have hsum : AEStronglyMeasurable (fun x => ∑ i : Fin n, ∑ j : Fin q,
      ‖projectionCommutator (P x) (D x i) (EuclideanSpace.single j 1)‖ ^ 2) μ :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hcolumn i j).norm.pow 2
  have hmeas := Real.continuous_sqrt.comp_aestronglyMeasurable hsum
  apply (memLp_sqrt_sum_norm_sq v hv).of_le_mul (c := 2 * Real.sqrt (q : ℝ) * L) hmeas
  filter_upwards [hP, hD] with x hxP hxD
  simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact commutator_hsNorm_le (P x) (D x) (v x) hxP hL hxD

end StationaryHarmonicMaps.Analysis

end
