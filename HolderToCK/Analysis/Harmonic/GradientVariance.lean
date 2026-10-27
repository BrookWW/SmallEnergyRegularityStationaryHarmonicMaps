module

public import HarmonicMaps.Analysis.BallVariance
public import HarmonicMaps.EnergyLemmas

/-! # Finite-measure gradient variance

The actual columnwise mean minimizes the Hilbert--Schmidt squared-distance
integral. Variance and difference estimates use the same displayed columns.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped InnerProductSpace

namespace HolderToCK

theorem integral_sq_norm_sub_average_decomposition
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → E}
    (hf : MemLp f 2 μ) (b : E) :
    (∫ x, ‖f x - b‖ ^ 2 ∂μ) =
      (∫ x, ‖f x - ⨍ y, f y ∂μ‖ ^ 2 ∂μ) +
        μ.real univ * ‖(⨍ y, f y ∂μ) - b‖ ^ 2 := by
  let m := ⨍ y, f y ∂μ
  let g : α → E := fun x => f x - m
  have hg : MemLp g 2 μ := hf.sub (memLp_const _)
  have hgi : Integrable g μ := hg.integrable (by norm_num)
  have hgsq : Integrable (fun x => ‖g x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hz : (∫ x, g x ∂μ) = 0 := integral_sub_average μ f
  have hi : Integrable (fun x => 2 * inner ℝ (m - b) (g x)) μ :=
    (hgi.const_inner _).const_mul 2
  have hsum : Integrable (fun x => ‖g x‖ ^ 2 + 2 * inner ℝ (m - b) (g x)) μ :=
    hgsq.add hi
  have heq (x : α) : f x - b = g x + (m - b) := by
    dsimp only [g]
    abel
  have hcomm (x : α) : inner ℝ (g x) (m - b) = inner ℝ (m - b) (g x) :=
    real_inner_comm _ _
  simp_rw [heq, norm_add_sq_real, hcomm]
  rw [integral_add hsum (integrable_const _), integral_add hgsq hi,
    integral_const_mul, integral_inner hgi, hz, inner_zero_right, mul_zero,
    add_zero, integral_const, smul_eq_mul]

theorem integral_sq_norm_sub_average_le
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → E}
    (hf : MemLp f 2 μ) (b : E) :
    (∫ x, ‖f x - ⨍ y, f y ∂μ‖ ^ 2 ∂μ) ≤ ∫ x, ‖f x - b‖ ^ 2 ∂μ := by
  rw [integral_sq_norm_sub_average_decomposition μ hf b]
  exact le_add_of_nonneg_right (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))

theorem hsNormSq_add_le {n q : ℕ} (A B : Gradient n q) :
    hsNormSq (A + B) ≤ 2 * hsNormSq A + 2 * hsNormSq B := by
  have hpoint (a b : Ambient q) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have htri := norm_add_le a b
    have hsq := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htri
    nlinarith only [hsq, sq_nonneg (‖a‖ - ‖b‖)]
  simp only [hsNormSq, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => hpoint (A i) (B i))

theorem gradient_variance_minimal {n q : ℕ}
    (μ : Measure (Domain n)) [IsFiniteMeasure μ]
    {D : Domain n → Gradient n q} (hD : ∀ i, MemLp (fun x => D x i) 2 μ)
    (B : Gradient n q) :
    (∫ x, hsNormSq (fun i => D x i - ⨍ y, D y i ∂μ) ∂μ) ≤
      ∫ x, hsNormSq (fun i => D x i - B i) ∂μ := by
  have hleft (i : Fin n) : Integrable
      (fun x => ‖D x i - ⨍ y, D y i ∂μ‖ ^ 2) μ :=
    ((hD i).sub (memLp_const _)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hright (i : Fin n) : Integrable (fun x => ‖D x i - B i‖ ^ 2) μ :=
    ((hD i).sub (memLp_const _)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  simp only [hsNormSq]
  rw [integral_finsetSum _ (fun i _ => hleft i),
    integral_finsetSum _ (fun i _ => hright i)]
  exact Finset.sum_le_sum (fun i _ => integral_sq_norm_sub_average_le μ (hD i) (B i))

theorem gradient_variance_difference_le {n q : ℕ}
    (μ : Measure (Domain n)) [IsFiniteMeasure μ]
    {D W : Domain n → Gradient n q}
    (hD : ∀ i, MemLp (fun x => D x i) 2 μ)
    (hW : ∀ i, MemLp (fun x => W x i) 2 μ) :
    (∫ x, hsNormSq (fun i => W x i - ⨍ y, W y i ∂μ) ∂μ) ≤
      2 * (∫ x, hsNormSq (fun i => D x i - ⨍ y, D y i ∂μ) ∂μ) +
        2 * ∫ x, hsNormSq (fun i => D x i - W x i) ∂μ := by
  let B : Gradient n q := fun i => ⨍ y, D y i ∂μ
  have hcenterD : Integrable (fun x => hsNormSq (fun i => D x i - B i)) μ :=
    HarmonicMaps.integrable_hsNormSq_of_memLp_columns (μ := μ)
    (fun i => (hD i).sub (memLp_const (B i)))
  have hcenterW : Integrable (fun x => hsNormSq (fun i => W x i - B i)) μ :=
    HarmonicMaps.integrable_hsNormSq_of_memLp_columns (μ := μ)
    (fun i => (hW i).sub (memLp_const (B i)))
  have hdiff : Integrable (fun x => hsNormSq (fun i => D x i - W x i)) μ :=
    HarmonicMaps.integrable_hsNormSq_of_memLp_columns (μ := μ)
    (fun i => (hD i).sub (hW i))
  calc
    _ ≤ ∫ x, hsNormSq (fun i => W x i - B i) ∂μ :=
      gradient_variance_minimal μ hW B
    _ ≤ ∫ x, 2 * hsNormSq (fun i => D x i - B i) +
        2 * hsNormSq (fun i => D x i - W x i) ∂μ := by
      apply integral_mono hcenterW ((hcenterD.const_mul 2).add (hdiff.const_mul 2))
      intro x
      change hsNormSq (fun i => W x i - B i) ≤
        2 * hsNormSq (fun i => D x i - B i) + 2 * hsNormSq (fun i => D x i - W x i)
      have heq : (fun i => W x i - B i) =
          (fun i => D x i - B i) + (fun i => W x i - D x i) := by
        ext i
        dsimp only [Pi.add_apply]
        abel_nf
      rw [heq]
      have h := hsNormSq_add_le (fun i => D x i - B i) (fun i => W x i - D x i)
      simpa only [hsNormSq, norm_sub_rev] using h
    _ = _ := by
      rw [integral_add (hcenterD.const_mul 2) (hdiff.const_mul 2), integral_const_mul,
        integral_const_mul]

theorem integral_hsNormSq_triangle_le {n q : ℕ}
    (μ : Measure (Domain n)) {D W : Domain n → Gradient n q}
    (hD : ∀ i, MemLp (fun x => D x i) 2 μ)
    (hW : ∀ i, MemLp (fun x => W x i) 2 μ) :
    (∫ x, hsNormSq (D x) ∂μ) ≤ 2 * (∫ x, hsNormSq (W x) ∂μ) +
      2 * ∫ x, hsNormSq (fun i => D x i - W x i) ∂μ := by
  have hDi := HarmonicMaps.integrable_hsNormSq_of_memLp_columns hD
  have hWi := HarmonicMaps.integrable_hsNormSq_of_memLp_columns hW
  have hdiff : Integrable (fun x => hsNormSq (fun i => D x i - W x i)) μ :=
    HarmonicMaps.integrable_hsNormSq_of_memLp_columns (fun i => (hD i).sub (hW i))
  calc
    _ ≤ ∫ x, 2 * hsNormSq (W x) + 2 * hsNormSq (fun i => D x i - W x i) ∂μ := by
      apply integral_mono hDi ((hWi.const_mul 2).add (hdiff.const_mul 2))
      intro x
      change hsNormSq (D x) ≤ 2 * hsNormSq (W x) +
        2 * hsNormSq (fun i => D x i - W x i)
      have heq : D x = W x + (fun i => D x i - W x i) := by
        ext i
        dsimp only [Pi.add_apply]
        abel_nf
      nth_rw 1 [heq]
      exact hsNormSq_add_le _ _
    _ = _ := by
      rw [integral_add (hWi.const_mul 2) (hdiff.const_mul 2), integral_const_mul,
        integral_const_mul]

end HolderToCK
end
