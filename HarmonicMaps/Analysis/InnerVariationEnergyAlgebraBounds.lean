module

public import HarmonicMaps.Analysis.InnerVariationEnergyAlgebra
public import HarmonicMaps.Analysis.RadialStressAlgebra
public import HarmonicMaps.EnergyLemmas
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Uniform bounds for the inner-variation energy difference

The finite array of inverse-Jacobian quadratic coefficients is smooth near
the identity. Its local Lipschitz bound is independent of the gradient. A
finite-sum estimate converts this to domination by the original HS density.
-/

public section

open Set Filter
open scoped ContDiff Topology BigOperators

namespace HarmonicMaps

set_option backward.isDefEq.respectTransparency false in
/-- The actual determinant on Euclidean operators is smooth. -/
theorem innerVariation_operator_det_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (fun M : Domain n →L[ℝ] Domain n => M.det) := by
  have hentry (i j : Fin n) : ContDiff ℝ ∞
      (fun M : Domain n →L[ℝ] Domain n => (M (EuclideanSpace.single i 1)) j) := by
    exact (EuclideanSpace.proj j : Domain n →L[ℝ] ℝ).contDiff.comp (contDiff_id.clm_apply contDiff_const)
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have heq (M : Domain n →L[ℝ] Domain n) :
      M.det = Matrix.det (fun i j : Fin n => (M (EuclideanSpace.single j 1)) i) := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
    congr 1
  simp_rw [heq, Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact hentry i (σ i)

set_option backward.isDefEq.respectTransparency false in
/-- The quadratic inverse-Jacobian coefficient array is locally Lipschitz
near the identity, with constants depending only on the domain dimension. -/
theorem innerVariation_coefficient_bound (n : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ M : Domain n →L[ℝ] Domain n, ‖M - 1‖ < δ →
      ∀ i j k : Fin n,
        |(|M.det| * (Ring.inverse M (EuclideanSpace.single i 1)) j *
          (Ring.inverse M (EuclideanSpace.single i 1)) k) -
          ((EuclideanSpace.single i (1 : ℝ)) j * (EuclideanSpace.single i (1 : ℝ)) k)| ≤
          K * ‖M - 1‖ := by
  let F : (Domain n →L[ℝ] Domain n) → Fin n → Fin n → Fin n → ℝ :=
    fun M i j k => |M.det| * (Ring.inverse M (EuclideanSpace.single i 1)) j *
      (Ring.inverse M (EuclideanSpace.single i 1)) k
  have hinv : ContDiffAt ℝ 1 (fun M : Domain n →L[ℝ] Domain n => Ring.inverse M) 1 := by
    simpa only [Units.val_one] using contDiffAt_ringInverse ℝ
      (n := (1 : WithTop ℕ∞)) (1 : (Domain n →L[ℝ] Domain n)ˣ)
  have hdet : ContDiffAt ℝ 1 (fun M : Domain n →L[ℝ] Domain n => |M.det|) 1 :=
    ((innerVariation_operator_det_contDiff n).of_le (by simp)).contDiffAt.abs
      (by simp [ContinuousLinearMap.det])
  have hF : ContDiffAt ℝ 1 F 1 := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    apply contDiffAt_pi.mpr
    intro k
    exact (hdet.mul ((EuclideanSpace.proj j : Domain n →L[ℝ] ℝ).contDiff.contDiffAt.comp 1
      (hinv.clm_apply contDiffAt_const))).mul
      ((EuclideanSpace.proj k : Domain n →L[ℝ] ℝ).contDiff.contDiffAt.comp 1 (hinv.clm_apply contDiffAt_const))
  obtain ⟨K, U, hU, hLip⟩ := hF.exists_lipschitzOnWith
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ, hδ, K, K.coe_nonneg, ?_⟩
  intro M hM i j k
  have hMb : M ∈ Metric.ball (1 : Domain n →L[ℝ] Domain n) δ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hM
  have h1b : (1 : Domain n →L[ℝ] Domain n) ∈ Metric.ball 1 δ := by
    simpa only [Metric.mem_ball, dist_self] using hδ
  have hbound := hLip.norm_sub_le (hδU hMb) (hδU h1b)
  have hcoord : ‖(F M - F 1) i j k‖ ≤ ‖F M - F 1‖ :=
    (norm_le_pi_norm ((F M - F 1) i j) k).trans
      ((norm_le_pi_norm ((F M - F 1) i) j).trans (norm_le_pi_norm (F M - F 1) i))
  have ht := hcoord.trans hbound
  have hdetone : ((1 : Domain n →L[ℝ] Domain n).det) = 1 := by
    change LinearMap.det (1 : Domain n →ₗ[ℝ] Domain n) = 1
    exact map_one LinearMap.det
  simpa only [F, Pi.sub_apply, hdetone, abs_one,
    Ring.inverse_one, one_apply_eq_self, one_mul, Real.norm_eq_abs] using ht

/-- Every pair of displayed gradient columns has inner product bounded by
the full original Hilbert--Schmidt density. -/
theorem innerVariation_abs_inner_le_hs {n q : ℕ} (A : Gradient n q) (i j : Fin n) :
    |inner ℝ (A i) (A j)| ≤ hsNormSq A := by
  have hi : ‖A i‖ ^ 2 ≤ hsNormSq A := by
    exact Finset.single_le_sum (fun k _ => sq_nonneg ‖A k‖) (Finset.mem_univ i)
  have hj : ‖A j‖ ^ 2 ≤ hsNormSq A := by
    exact Finset.single_le_sum (fun k _ => sq_nonneg ‖A k‖) (Finset.mem_univ j)
  have hp := norm_inner_le_norm (𝕜 := ℝ) (A i) (A j)
  rw [Real.norm_eq_abs] at hp
  nlinarith only [hp, hi, hj, sq_nonneg (‖A i‖ - ‖A j‖)]

/-- A gradient-independent local Lipschitz estimate for the literal transformed
energy density, with the original HS density as its only gradient factor. -/
theorem innerVariation_energy_density_local_bound (n : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) (M : Domain n →L[ℝ] Domain n) (A : Gradient n q), ‖M - 1‖ < δ →
        |(|M.det| * hsNormSq (fun i => ∑ j : Fin n,
          (Ring.inverse M (EuclideanSpace.single i 1)) j • A j)) - hsNormSq A| ≤
          C * ‖M - 1‖ * hsNormSq A := by
  obtain ⟨δ, hδ, K, hK, hcoeff⟩ := innerVariation_coefficient_bound n
  refine ⟨δ, hδ, (n : ℝ) ^ 3 * K, by positivity, ?_⟩
  intro q M A hM
  have hbase : hsNormSq A = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      ((EuclideanSpace.single i (1 : ℝ)) j * (EuclideanSpace.single i (1 : ℝ)) k) *
        inner ℝ (A j) (A k) := by
    have hcol (i : Fin n) : (∑ j : Fin n, (EuclideanSpace.single i (1 : ℝ)) j • A j) = A i := by
      simp [PiLp.single_apply]
    unfold hsNormSq
    apply Finset.sum_congr rfl
    intro i _
    rw [← hcol i, norm_sq_sum_smul]
  have heq : (|M.det| * hsNormSq (fun i => ∑ j : Fin n,
      (Ring.inverse M (EuclideanSpace.single i 1)) j • A j)) - hsNormSq A =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ((|M.det| * (Ring.inverse M (EuclideanSpace.single i 1)) j *
          (Ring.inverse M (EuclideanSpace.single i 1)) k) -
          ((EuclideanSpace.single i (1 : ℝ)) j * (EuclideanSpace.single i (1 : ℝ)) k)) *
          inner ℝ (A j) (A k) := by
    rw [hbase]
    simp only [hsNormSq, norm_sq_sum_smul, Finset.mul_sum, Finset.sum_sub_distrib, sub_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq]
  have hterm (i j k : Fin n) :
      |((|M.det| * (Ring.inverse M (EuclideanSpace.single i 1)) j *
        (Ring.inverse M (EuclideanSpace.single i 1)) k) -
        ((EuclideanSpace.single i (1 : ℝ)) j * (EuclideanSpace.single i (1 : ℝ)) k)) *
        inner ℝ (A j) (A k)| ≤ K * ‖M - 1‖ * hsNormSq A := by
    rw [abs_mul]
    exact mul_le_mul (hcoeff M hM i j k) (innerVariation_abs_inner_le_hs A j k)
      (abs_nonneg _) (mul_nonneg hK (norm_nonneg _))
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        |((|M.det| * (Ring.inverse M (EuclideanSpace.single i 1)) j *
          (Ring.inverse M (EuclideanSpace.single i 1)) k) -
          ((EuclideanSpace.single i (1 : ℝ)) j * (EuclideanSpace.single i (1 : ℝ)) k)) *
          inner ℝ (A j) (A k)| := by
      apply le_trans (Finset.abs_sum_le_sum_abs _ _)
      apply Finset.sum_le_sum
      intro i _
      apply le_trans (Finset.abs_sum_le_sum_abs _ _)
      apply Finset.sum_le_sum
      intro j _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ∑ _k : Fin n, K * ‖M - 1‖ * hsNormSq A :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        Finset.sum_le_sum (fun k _ => hterm i j k)))
    _ = (n : ℝ) ^ 3 * K * ‖M - 1‖ * hsNormSq A := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Uniform domination of both signed parameter difference quotients by the
original HS density. The witnesses depend only on dimension and the derivative
bound; actual inverses are certified for every parameter in the interval. -/
theorem innerVariation_energy_density_difference_quotient_bound (n : ℕ)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) (B : Domain n →L[ℝ] Domain n) (A : Gradient n q), ‖B‖ ≤ L →
      ∀ t : ℝ, |t| < ε → t ≠ 0 →
        IsUnit (1 + t • B) ∧
        |((|(1 + t • B).det| * hsNormSq (fun i => ∑ j : Fin n,
          (Ring.inverse (1 + t • B) (EuclideanSpace.single i 1)) j • A j)) - hsNormSq A) / t| ≤
          C * hsNormSq A := by
  obtain ⟨δ, hδ, K, hK, hbound⟩ := innerVariation_energy_density_local_bound n
  refine ⟨min δ 1 / (L + 1), div_pos (lt_min hδ zero_lt_one) (by linarith only [hL]),
    K * L, mul_nonneg hK hL, ?_⟩
  intro q B A hB t ht ht0
  have hsmall : |t| * ‖B‖ < min δ 1 := by
    have ht' := (lt_div_iff₀ (by linarith only [hL] : 0 < L + 1)).mp ht
    have hlt : |t| * ‖B‖ ≤ |t| * (L + 1) :=
      mul_le_mul_of_nonneg_left (hB.trans (by linarith)) (abs_nonneg t)
    exact hlt.trans_lt ht'
  have hunit : IsUnit (1 + t • B) := innerVariation_operator_isUnit B
    (hsmall.trans_le (min_le_right _ _))
  have hn : ‖(1 + t • B) - (1 : Domain n →L[ℝ] Domain n)‖ = |t| * ‖B‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  have hnorm : ‖(1 + t • B) - (1 : Domain n →L[ℝ] Domain n)‖ < δ := by
    rw [hn]
    exact hsmall.trans_le (min_le_left _ _)
  have hb := hbound q (1 + t • B) A hnorm
  rw [hn] at hb
  refine ⟨hunit, ?_⟩
  rw [abs_div, div_le_iff₀ (abs_pos.mpr ht0)]
  calc
    _ ≤ K * (|t| * ‖B‖) * hsNormSq A := hb
    _ ≤ K * (|t| * L) * hsNormSq A :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB (abs_nonneg t)) hK)
        (hsNormSq_nonneg A)
    _ = K * L * hsNormSq A * |t| := by ring

end HarmonicMaps
