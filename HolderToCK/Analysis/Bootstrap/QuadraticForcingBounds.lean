module

public import HolderToCK.Foundation.HolderBounds
public import HarmonicMaps.EnergyLemmas
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Quantitative bounds for the actual quadratic gradient forcing

The original HS density controls the displayed quadratic sum. Two positive
gradient factors give the squared small parameter in its norm and Holder
estimate. The single condition `delta <= 1` is independent of derivative order.
-/

public section

open HarmonicMaps Set

namespace HolderToCK

theorem norm_bilinear_apply_le {q : ℕ}
    (B : Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q) (v w : Ambient q) :
    ‖B v w‖ ≤ ‖B‖ * ‖v‖ * ‖w‖ := B.le_opNorm₂ v w

theorem norm_quadratic_forcing_le_hsNormSq {n q : ℕ}
    (B : Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q) (P : Gradient n q) :
    ‖∑ i : Fin n, B (P i) (P i)‖ ≤ ‖B‖ * hsNormSq P := by
  calc
    _ ≤ ∑ i : Fin n, ‖B (P i) (P i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ‖B‖ * ‖P i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [pow_two, mul_assoc] using norm_bilinear_apply_le B (P i) (P i)
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem norm_bilinear_diagonal_sub_le {q : ℕ}
    (B C : Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q) (v w : Ambient q) :
    ‖B v v - C w w‖ ≤
      ‖B - C‖ * ‖v‖ ^ 2 + ‖C‖ * (‖v‖ + ‖w‖) * ‖v - w‖ := by
  have heq : B v v - C w w =
      (B - C) v v + C (v - w) v + C w (v - w) := by
    simp only [sub_apply, map_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖(B - C) v v‖ + ‖C (v - w) v‖ + ‖C w (v - w)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖B - C‖ * ‖v‖ * ‖v‖ + ‖C‖ * ‖v - w‖ * ‖v‖ +
        ‖C‖ * ‖w‖ * ‖v - w‖ :=
      add_le_add (add_le_add (norm_bilinear_apply_le (B - C) v v)
        (norm_bilinear_apply_le C (v - w) v)) (norm_bilinear_apply_le C w (v - w))
    _ = _ := by ring

theorem quadratic_forcing_norm_bound {n q : ℕ} {s : Set (Domain n)}
    {u : Domain n → Ambient q} {P : Domain n → Gradient n q}
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    {a M δ : ℝ} (ha : 0 ≤ a) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hA : ∀ x ∈ s, ‖A (u x)‖ ≤ a)
    (hP : ∀ x ∈ s, ∀ i : Fin n, ‖P x i‖ ≤ M * δ) :
    ∀ x ∈ s, ‖∑ i : Fin n, A (u x) (P x i) (P x i)‖ ≤
      (n : ℝ) * a * M ^ 2 * δ ^ 2 := by
  intro x hx
  have hHS : hsNormSq (P x) ≤ (n : ℝ) * (M * δ) ^ 2 := by
    unfold hsNormSq
    calc
      _ ≤ ∑ _i : Fin n, (M * δ) ^ 2 :=
        Finset.sum_le_sum (fun i _ => (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM hδ)).mpr (hP x hx i))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ ≤ ‖A (u x)‖ * hsNormSq (P x) := norm_quadratic_forcing_le_hsNormSq _ _
    _ ≤ a * ((n : ℝ) * (M * δ) ^ 2) := mul_le_mul (hA x hx) hHS (hsNormSq_nonneg _) ha
    _ = _ := by ring

theorem quadratic_forcing_holder_bound {n q : ℕ} {s : Set (Domain n)}
    {u : Domain n → Ambient q} {P : Domain n → Gradient n q}
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    {γ a₀ a₁ L M H δ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (_hH : 0 ≤ H) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hA : ∀ x ∈ s, ‖A (u x)‖ ≤ a₀)
    (hALip : ∀ x ∈ s, ∀ y ∈ s, ‖A (u x) - A (u y)‖ ≤ a₁ * ‖u x - u y‖)
    (hu : HolderBoundOn s u γ (L * δ))
    (hP : ∀ x ∈ s, ∀ i : Fin n, ‖P x i‖ ≤ M * δ)
    (hPH : ∀ i : Fin n, HolderBoundOn s (fun x => P x i) γ (H * δ)) :
    HolderBoundOn s (fun x => ∑ i : Fin n, A (u x) (P x i) (P x i)) γ
      ((n : ℝ) * (a₁ * L * M ^ 2 + 2 * a₀ * M * H) * δ ^ 2) := by
  intro x hx y hy
  let r := Real.rpow (dist x y) γ
  have hr : 0 ≤ r := Real.rpow_nonneg dist_nonneg _
  have hcoef : ‖A (u x) - A (u y)‖ ≤ a₁ * (L * δ) * r := by
    simpa only [r, mul_assoc] using
      (hALip x hx y hy).trans (mul_le_mul_of_nonneg_left (hu x hx y hy) ha₁)
  have hδcube : δ ^ 3 ≤ δ ^ 2 := by
    calc
      δ ^ 3 = δ ^ 2 * δ := by ring
      _ ≤ δ ^ 2 * 1 := mul_le_mul_of_nonneg_left hδone (sq_nonneg δ)
      _ = _ := mul_one _
  have hcolumn (i : Fin n) :
      ‖A (u x) (P x i) (P x i) - A (u y) (P y i) (P y i)‖ ≤
        (a₁ * L * M ^ 2 + 2 * a₀ * M * H) * δ ^ 2 * r := by
    have hv := hP x hx i
    have hw := hP y hy i
    have hdiff := hPH i x hx y hy
    have hsq : ‖P x i‖ ^ 2 ≤ (M * δ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM hδ)).mpr hv
    have hsum : ‖P x i‖ + ‖P y i‖ ≤ 2 * M * δ := by
      calc
        _ ≤ M * δ + M * δ := add_le_add hv hw
        _ = _ := by ring
    calc
      _ ≤ ‖A (u x) - A (u y)‖ * ‖P x i‖ ^ 2 +
          ‖A (u y)‖ * (‖P x i‖ + ‖P y i‖) * ‖P x i - P y i‖ :=
        norm_bilinear_diagonal_sub_le _ _ _ _
      _ ≤ (a₁ * (L * δ) * r) * (M * δ) ^ 2 +
          a₀ * (2 * M * δ) * ((H * δ) * r) :=
        add_le_add (mul_le_mul hcoef hsq (sq_nonneg _) (by positivity))
          (mul_le_mul
            (mul_le_mul (hA y hy) hsum (add_nonneg (norm_nonneg _) (norm_nonneg _)) ha₀)
            hdiff (norm_nonneg _) (by positivity))
      _ = (a₁ * L * M ^ 2) * δ ^ 3 * r + (2 * a₀ * M * H) * δ ^ 2 * r := by ring
      _ ≤ (a₁ * L * M ^ 2) * δ ^ 2 * r + (2 * a₀ * M * H) * δ ^ 2 * r :=
        add_le_add (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hδcube (by positivity)) hr) le_rfl
      _ = _ := by ring
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin n, ‖A (u x) (P x i) (P x i) - A (u y) (P y i) (P y i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (a₁ * L * M ^ 2 + 2 * a₀ * M * H) * δ ^ 2 * r :=
      Finset.sum_le_sum (fun i _ => hcolumn i)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp only [r]
      ring

end HolderToCK
end
