module

public import HolderToCK.Analysis.Poisson.PotentialDerivatives

/-! # The trace of the actual potential Hessian -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators

namespace HolderToCK

theorem hessianKernelExpression_trace {n : ℕ} (z : Domain n) (hz : z ≠ 0) :
    (∑ i : Fin n, hessianKernelExpression i i z) = 0 := by
  have hp : ‖z‖ ^ (-(n : ℝ) - 2) * ‖z‖ ^ 2 = ‖z‖ ^ (-(n : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_add (norm_pos_iff.mpr hz)]
    congr 1
    ring
  simp only [hessianKernelExpression, ite_true, one_mul]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hprod : (∑ i : Fin n, (n : ℝ) * z i * z i * ‖z‖ ^ (-(n : ℝ) - 2)) =
      (n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 2) * ‖z‖ ^ 2 := by
    calc
      _ = (n : ℝ) * ‖z‖ ^ (-(n : ℝ) - 2) * ∑ i : Fin n, z i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [← EuclideanSpace.real_norm_sq_eq]
  rw [hprod, mul_assoc, hp, sub_self, mul_zero]

theorem potentialHessianExpression_trace {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (x : Domain n) :
    (∑ i : Fin n, potentialHessianExpression i i g x) = g x := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hnear (i : Fin n) :=
    hessianKernelExpression_holderDifference_integrableOn hn i i hη hH hHolder x (R := 1)
  have hfar (i : Fin n) := hessianKernelExpression_farHolder_integrableOn i i hη hHolder hcg x
  have hN : (∑ i : Fin n, ∫ z in Metric.ball (0 : Domain n) 1,
      hessianKernelExpression i i z • (g (x - z) - g x)) = 0 := by
    rw [← integral_finsetSum Finset.univ (fun i _ => hnear i)]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae ((volume : Measure (Domain n)).ae_ne 0)] with z hz
    rw [← Finset.sum_smul, hessianKernelExpression_trace z hz, zero_smul]
    rfl
  have hF : (∑ i : Fin n, ∫ z in (Metric.ball (0 : Domain n) 1)ᶜ,
      hessianKernelExpression i i z • g (x - z)) = 0 := by
    rw [← integral_finsetSum Finset.univ (fun i _ => hfar i)]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae ((volume : Measure (Domain n)).ae_ne 0)] with z hz
    rw [← Finset.sum_smul, hessianKernelExpression_trace z hz, zero_smul]
    rfl
  have hcoeff : (∑ _i : Fin n, (1 : ℝ) / (n : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [Nat.cast_ne_zero.mpr hn.ne']
  simp only [potentialHessianExpression, ite_true]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hN, hF, add_zero, add_zero,
    ← Finset.sum_smul, hcoeff, one_smul]

theorem newtonianPotential_laplacian {n q : ℕ}
    (hn : 2 ≤ n) {g : Domain n → Ambient q} {η H : ℝ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H) (x : Domain n) :
    Laplacian.laplacian (newtonianPotential hn g) x = g x := by
  rw [laplacian_eq_sum_coordinateDerivatives _ (newtonianPotential_contDiff hn hg hcg)]
  calc
    _ = ∑ i : Fin n, potentialHessianExpression i i g x := by
      apply Finset.sum_congr rfl
      intro i _
      exact newtonianPotential_mixedColumns_eq_hessian hn i i
        (hg.of_le (WithTop.coe_le_coe.mpr le_top)) hcg hη hH hHolder x
    _ = _ := potentialHessianExpression_trace (by omega : 0 < n) hη hH hHolder hcg x

end HolderToCK
end
