module

public import HolderToCK.Analysis.Poisson.PotentialRegularity
public import HolderToCK.Analysis.Poisson.PotentialBounds
public import HolderToCK.Analysis.Poisson.HessianTranslationHolder
public import HolderToCK.Analysis.Bootstrap.DerivativeProducts

/-! # Bounds for the actual first and second potential derivatives -/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace HolderToCK

theorem euclidean_sum_abs_le_sqrt_dimension_mul_norm {n : ℕ} (v : Domain n) :
    (∑ i : Fin n, |v i|) ≤ Real.sqrt (n : ℝ) * ‖v‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin n => |v i|) (fun _ => (1 : ℝ))
  have hcoords : (∑ i : Fin n, |v i| ^ 2) = ‖v‖ ^ 2 := by
    simpa only [sq_abs] using (EuclideanSpace.real_norm_sq_eq v).symm
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, hcoords] at hcs
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), mul_comm]
  exact hcs

theorem norm_euclideanLinearMap_le_of_columns_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Domain n →L[ℝ] E) {M : ℝ} (hM : 0 ≤ M)
    (hcolumns : ∀ i : Fin n, ‖L (EuclideanSpace.single i 1)‖ ≤ M) :
    ‖L‖ ≤ Real.sqrt (n : ℝ) * M := by
  apply L.opNorm_le_bound (mul_nonneg (Real.sqrt_nonneg _) hM)
  intro v
  have hrepr : (∑ i : Fin n, v i • EuclideanSpace.single i 1) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  calc
    ‖L v‖ = ‖L (∑ i : Fin n, v i • EuclideanSpace.single i 1)‖ :=
      congrArg (fun w => ‖L w‖) hrepr.symm
    _ = ‖∑ i : Fin n, v i • L (EuclideanSpace.single i 1)‖ := by
      rw [map_sum]
      simp only [map_smul]
    _ ≤ ∑ i : Fin n, ‖v i • L (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, |v i| * M := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hcolumns i) (abs_nonneg _)
    _ = (∑ i : Fin n, |v i|) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ (Real.sqrt (n : ℝ) * ‖v‖) * M :=
      mul_le_mul_of_nonneg_right (euclidean_sum_abs_le_sqrt_dimension_mul_norm v) hM
    _ = (Real.sqrt (n : ℝ) * M) * ‖v‖ := by ring

theorem fderiv_fderiv_coordinateColumn {n q : ℕ}
    (f : Domain n → Ambient q) (x : Domain n) (hf : ContDiffAt ℝ 2 f x) (i j : Fin n) :
    fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1) := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [fderiv_clm_apply hdiff (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]

theorem norm_iteratedFDeriv_two_le_of_mixedColumns {n q : ℕ}
    (f : Domain n → Ambient q) (x : Domain n) (hf : ContDiffAt ℝ 2 f x)
    {M : ℝ} (hM : 0 ≤ M)
    (hcolumns : ∀ i j : Fin n,
      ‖fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1)‖ ≤ M) :
    ‖iteratedFDeriv ℝ 2 f x‖ ≤ (n : ℝ) * M := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  have hcolumn (i : Fin n) :
      ‖fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1)‖ ≤
        Real.sqrt (n : ℝ) * M := by
    apply norm_linearMap_le_of_columns_bound _ hM
    intro j
    rw [fderiv_fderiv_coordinateColumn f x hf i j]
    exact hcolumns i j
  calc
    _ ≤ Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) * M) :=
      norm_euclideanLinearMap_le_of_columns_bound _
        (mul_nonneg (Real.sqrt_nonneg _) hM) hcolumn
    _ = _ := by rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]

theorem norm_iteratedFDeriv_two_sub_le_of_mixedColumns {n q : ℕ}
    (f : Domain n → Ambient q) (x y : Domain n)
    (hfx : ContDiffAt ℝ 2 f x) (hfy : ContDiffAt ℝ 2 f y)
    {M : ℝ} (hM : 0 ≤ M)
    (hcolumns : ∀ i j : Fin n,
      ‖fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1) -
        fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single j 1)) y
          (EuclideanSpace.single i 1)‖ ≤ M) :
    ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ (n : ℝ) * M := by
  rw [← norm_iteratedFDeriv_fderiv_sub f 1 x y,
    ← norm_iteratedFDeriv_fderiv_sub (fderiv ℝ f) 0 x y,
    norm_iteratedFDeriv_zero_sub]
  have hcolumn (i : Fin n) :
      ‖(fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) y)
        (EuclideanSpace.single i 1)‖ ≤ Real.sqrt (n : ℝ) * M := by
    apply norm_linearMap_le_of_columns_bound _ hM
    intro j
    rw [sub_apply, sub_apply, fderiv_fderiv_coordinateColumn f x hfx i j,
      fderiv_fderiv_coordinateColumn f y hfy i j]
    exact hcolumns i j
  calc
    _ ≤ Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) * M) :=
      norm_euclideanLinearMap_le_of_columns_bound _
        (mul_nonneg (Real.sqrt_nonneg _) hM) hcolumn
    _ = _ := by rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]

theorem iteratedFDeriv_two_holderBoundOn_of_mixedColumns {n q : ℕ}
    {f : Domain n → Ambient q} (hf : ContDiff ℝ 2 f) {K : Set (Domain n)} {η H : ℝ}
    (hH : 0 ≤ H)
    (hcolumns : ∀ i j : Fin n, HolderBoundOn K
      (fun x => fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1)) η H) :
    HolderBoundOn K (iteratedFDeriv ℝ 2 f) η ((n : ℝ) * H) := by
  intro x hx y hy
  have hM : 0 ≤ H * Real.rpow (dist x y) η :=
    mul_nonneg hH (Real.rpow_nonneg dist_nonneg _)
  simpa only [mul_assoc] using norm_iteratedFDeriv_two_sub_le_of_mixedColumns f x y
    hf.contDiffAt hf.contDiffAt hM (fun i j => hcolumns i j x hx y hy)

theorem newtonianPotential_holder_unitData_fderiv_norm_bound {n q : ℕ}
    (hn : 2 ≤ n) {g : Domain n → Ambient q} {η H M : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hHolder : HolderBoundOn univ g η H) (hcg : HasCompactSupport g)
    (hSupp : tsupport g ⊆ Metric.closedBall (0 : Domain n) 1)
    (hbound : ∀ y, ‖g y‖ ≤ M) {x : Domain n} (hx : ‖x‖ ≤ 1) :
    ‖fderiv ℝ (newtonianPotential hn g) x‖ ≤ 3 * Real.sqrt (n : ℝ) * M := by
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  apply (norm_linearMap_le_of_columns_bound _ (M := 3 * M)
    (mul_nonneg (by norm_num) hM) ?_).trans_eq
    (by ring)
  intro j
  rw [newtonianPotential_holder_column_eq_gradient hn j hη hH hHolder hcg]
  exact potentialGradientColumn_unitData_norm_bound (by omega) j hg hcg hSupp hM hbound hx

@[expose] noncomputable def potentialHessianSupConstant (n : ℕ) (η : ℝ) : ℝ :=
  1 / (n : ℝ) + ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ *
    volume.real (Metric.ball (0 : Domain n) 3) + ((n : ℝ) + 1) / η

theorem potentialHessianSupConstant_nonneg {n : ℕ} (hn : 0 < n) {η : ℝ}
    (hη : 0 < η) : 0 ≤ potentialHessianSupConstant n η := by
  exact add_nonneg (add_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg n))
    (mul_nonneg (mul_nonneg (by positivity) (inv_nonneg.mpr (euclideanSphereArea_pos hn).le))
      (measureReal_nonneg))) (div_nonneg (by positivity) hη.le)

theorem newtonianPotential_holder_unitData_secondDerivative_norm_bound {n q : ℕ}
    (hn : 2 ≤ n) {g : Domain n → Ambient q} {η H M : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hHolder : HolderBoundOn univ g η H) (hcg : HasCompactSupport g)
    (hSupp : tsupport g ⊆ Metric.closedBall (0 : Domain n) 1)
    (hbound : ∀ y, ‖g y‖ ≤ M) {x : Domain n} (hx : ‖x‖ ≤ 1) :
    ‖iteratedFDeriv ℝ 2 (newtonianPotential hn g) x‖ ≤
      ((n : ℝ) * potentialHessianSupConstant n η) * (M + H) := by
  have ha : 0 ≤ 1 / (n : ℝ) + ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ *
      volume.real (Metric.ball (0 : Domain n) 3) :=
    add_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg n))
      (mul_nonneg (mul_nonneg (by positivity)
        (inv_nonneg.mpr (euclideanSphereArea_pos (by omega : 0 < n)).le)) measureReal_nonneg)
  have hb : 0 ≤ ((n : ℝ) + 1) / η := div_nonneg (by positivity) hη.le
  have hC : 0 ≤ potentialHessianSupConstant n η * (M + H) :=
    mul_nonneg (potentialHessianSupConstant_nonneg (by omega) hη) (add_nonneg hM hH)
  apply (norm_iteratedFDeriv_two_le_of_mixedColumns _ x
    (newtonianPotential_holder_contDiff_two hn hη hH hHolder hcg).contDiffAt hC ?_).trans_eq
      (mul_assoc _ _ _).symm
  intro i j
  rw [newtonianPotential_holder_mixedColumns_eq_hessian hn i j hη hH hHolder hcg]
  apply (potentialHessianExpression_unitData_norm_bound (by omega) i j hη hH hM
    hHolder hcg hSupp hbound hx).trans
  rw [potentialHessianSupConstant]
  nlinarith only [mul_nonneg ha hH, mul_nonneg hb hM]

@[expose] noncomputable def potentialC2SupConstant (n : ℕ) (η : ℝ) : ℝ :=
  potentialValueConstant n + 3 * Real.sqrt (n : ℝ) +
    (n : ℝ) * potentialHessianSupConstant n η

theorem potentialC2SupConstant_nonneg {n : ℕ} (hn : 0 < n) {η : ℝ}
    (hη : 0 < η) : 0 ≤ potentialC2SupConstant n η := by
  exact add_nonneg (add_nonneg (potentialValueConstant_nonneg n)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
    (mul_nonneg (Nat.cast_nonneg n) (potentialHessianSupConstant_nonneg hn hη))

theorem newtonianPotential_holder_unitData_iteratedFDeriv_norm_bound {n q : ℕ}
    (hn : 2 ≤ n) {g : Domain n → Ambient q} {η H M : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hHolder : HolderBoundOn univ g η H) (hcg : HasCompactSupport g)
    (hSupp : tsupport g ⊆ Metric.closedBall (0 : Domain n) 1)
    (hbound : ∀ y, ‖g y‖ ≤ M) (k : ℕ) (hk : k ≤ 2)
    {x : Domain n} (hx : ‖x‖ ≤ 1) :
    ‖iteratedFDeriv ℝ k (newtonianPotential hn g) x‖ ≤
      potentialC2SupConstant n η * (M + H) := by
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  have h0 : 0 ≤ potentialValueConstant n := potentialValueConstant_nonneg n
  have h1 : 0 ≤ 3 * Real.sqrt (n : ℝ) := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have h2 : 0 ≤ (n : ℝ) * potentialHessianSupConstant n η :=
    mul_nonneg (Nat.cast_nonneg n) (potentialHessianSupConstant_nonneg (by omega) hη)
  have h0C : potentialValueConstant n ≤ potentialC2SupConstant n η := by
    rw [potentialC2SupConstant]
    linarith only [h1, h2]
  have h1C : 3 * Real.sqrt (n : ℝ) ≤ potentialC2SupConstant n η := by
    rw [potentialC2SupConstant]
    linarith only [h0, h2]
  have h2C : (n : ℝ) * potentialHessianSupConstant n η ≤ potentialC2SupConstant n η := by
    rw [potentialC2SupConstant]
    linarith only [h0, h1]
  have hkCases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hkCases with rfl | rfl | rfl
  · rw [norm_iteratedFDeriv_zero]
    calc
      _ ≤ potentialValueConstant n * M :=
        newtonianPotential_unitData_norm_bound hn hg hcg hSupp hM hbound hx
      _ ≤ potentialValueConstant n * (M + H) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hH) h0
      _ ≤ _ := mul_le_mul_of_nonneg_right h0C (add_nonneg hM hH)
  · rw [norm_iteratedFDeriv_one]
    calc
      _ ≤ (3 * Real.sqrt (n : ℝ)) * M :=
        newtonianPotential_holder_unitData_fderiv_norm_bound hn hη hH hM hHolder hcg hSupp hbound hx
      _ ≤ (3 * Real.sqrt (n : ℝ)) * (M + H) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hH) h1
      _ ≤ _ := mul_le_mul_of_nonneg_right h1C (add_nonneg hM hH)
  · exact (newtonianPotential_holder_unitData_secondDerivative_norm_bound hn hη hH hM
      hHolder hcg hSupp hbound hx).trans
        (mul_le_mul_of_nonneg_right h2C (add_nonneg hM hH))

theorem newtonianPotential_holder_iteratedHessian_holderBound {n q : ℕ}
    (hn : 2 ≤ n) {g : Domain n → Ambient q} {η H : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hH : 0 ≤ H)
    (hHolder : HolderBoundOn univ g η H) (hcg : HasCompactSupport g) :
    HolderBoundOn univ (iteratedFDeriv ℝ 2 (newtonianPotential hn g)) η
      (((n : ℝ) * potentialHessianHolderConstant n η) * H) := by
  have hconst : 0 ≤ potentialHessianHolderConstant n η * H :=
    mul_nonneg (potentialHessianHolderConstant_nonneg (by omega) hη hη1) hH
  have hcolumns (i j : Fin n) : HolderBoundOn univ
      (fun x => fderiv ℝ (fun z => fderiv ℝ (newtonianPotential hn g) z
        (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) η
      (potentialHessianHolderConstant n η * H) := by
    intro x hx y hy
    dsimp only
    rw [newtonianPotential_holder_mixedColumns_eq_hessian hn i j hη hH hHolder hcg,
      newtonianPotential_holder_mixedColumns_eq_hessian hn i j hη hH hHolder hcg]
    exact potentialHessianExpression_holderBound (by omega) i j hη hη1 hH hHolder hcg x hx y hy
  simpa only [mul_assoc] using iteratedFDeriv_two_holderBoundOn_of_mixedColumns
    (newtonianPotential_holder_contDiff_two hn hη hH hHolder hcg) hconst hcolumns

theorem newtonianPotential_holder_unitData_derivative_bounds {n q : ℕ}
    (hn : 2 ≤ n) {g : Domain n → Ambient q} {η H M : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hHolder : HolderBoundOn univ g η H) (hcg : HasCompactSupport g)
    (hSupp : tsupport g ⊆ Metric.closedBall (0 : Domain n) 1)
    (hbound : ∀ y, ‖g y‖ ≤ M) :
    (∀ k : ℕ, k ≤ 2 → ∀ x : Domain n, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ k (newtonianPotential hn g) x‖ ≤
        potentialC2SupConstant n η * (M + H)) ∧
    HolderBoundOn univ (iteratedFDeriv ℝ 2 (newtonianPotential hn g)) η
      (((n : ℝ) * potentialHessianHolderConstant n η) * H) := by
  exact ⟨fun k hk _ hx => newtonianPotential_holder_unitData_iteratedFDeriv_norm_bound hn
    hη hH hM hHolder hcg hSupp hbound k hk hx,
    newtonianPotential_holder_iteratedHessian_holderBound hn hη hη1 hH hHolder hcg⟩

end HolderToCK
end
