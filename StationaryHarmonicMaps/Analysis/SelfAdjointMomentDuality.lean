module

public import StationaryHarmonicMaps.Analysis.LpDualPowerTest
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Low moments from genuine self-adjoint high-moment control

The actual power-duality test is constructed from the original L2 response.
Finite measure supplies its L2 and conjugate-exponent membership. Genuine
L2 self-adjointness and ordinary Holder then give the quantitative low
moment estimate. The high-moment hypothesis belongs to this generic
functional-analytic lemma.
-/

public section

open MeasureTheory Filter

namespace StationaryHarmonicMaps.Analysis

/-- A real self-adjoint L2 operator with actual conjugate high-moment control has the corresponding low-p moment bound on every original L2 class. -/
theorem selfAdjoint_low_moment_bound_of_high_moment {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ) (hpOne : 1<p) (hpTwo : p<2)
    (C : ℝ) (hC : 0≤C) (T : Lp E 2 μ →L[ℝ] Lp E 2 μ) (hSelf : IsSelfAdjoint T)
    (hHigh : ∀ W : Lp E 2 μ,MemLp (fun x => W x) (ENNReal.ofReal (p/(p-1))) μ →
      MemLp (fun x => T W x) (ENNReal.ofReal (p/(p-1))) μ ∧
      (∫ x,‖T W x‖^(p/(p-1)) ∂μ)≤C*(∫ x,‖W x‖^(p/(p-1)) ∂μ))
    (Z : Lp E 2 μ) :
    MemLp (fun x => T Z x) (ENNReal.ofReal p) μ ∧
      (∫ x,‖T Z x‖^p ∂μ)≤C^(p-1)*(∫ x,‖Z x‖^p ∂μ) := by
  let r := p/(p-1)
  let Q := fun x => T Z x
  let G := fun x => ‖Q x‖^(p-2) • Q x
  have hp0 : 0<p := by linarith only [hpOne]
  have hpm : 0<p-1 := by linarith only [hpOne]
  have hr : 0<r := div_pos hp0 hpm
  have hpq : p.HolderConjugate r := Real.HolderConjugate.conjExponent hpOne
  have hQTwo : MemLp Q 2 μ := Lp.memLp (T Z)
  have hQp : MemLp Q (ENNReal.ofReal p) μ := memLp_real_of_memL2 Q hpTwo.le hQTwo
  have hZp : MemLp (fun x => Z x) (ENNReal.ofReal p) μ :=
    memLp_real_of_memL2 (fun x => Z x) hpTwo.le (Lp.memLp Z)
  obtain ⟨hGTwo,hGr⟩ := dual_power_test_memLp μ p hpOne hpTwo Q hQTwo
  let Y := hGTwo.toLp G
  have hYAE : (fun x => Y x) =ᵐ[μ] G := hGTwo.coeFn_toLp
  have hYr : MemLp (fun x => Y x) (ENNReal.ofReal r) μ := (memLp_congr_ae hYAE).mpr hGr
  obtain ⟨hTYr,hTYBound⟩ := hHigh Y hYr
  let A := ∫ x,‖Z x‖^p ∂μ
  let B := ∫ x,‖Q x‖^p ∂μ
  have hA : 0≤A := integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  have hB : 0≤B := integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  have hYMoment : (∫ x,‖Y x‖^r ∂μ)=B := by
    apply integral_congr_ae
    filter_upwards [hYAE] with x hx
    rw [hx]
    exact (dual_power_vector_identities p hpOne (Q x)).2.2
  have hPair : (∫ x,inner ℝ (T Z x) (Y x) ∂μ)=B := by
    apply integral_congr_ae
    filter_upwards [hYAE] with x hx
    rw [hx]
    exact (dual_power_vector_identities p hpOne (Q x)).2.1
  have hSym := hSelf.isSymmetric Z Y
  change inner ℝ (T Z) Y=inner ℝ Z (T Y) at hSym
  rw [L2.inner_def,L2.inner_def] at hSym
  have hProduct : MemLp (fun x => ‖Z x‖*‖T Y x‖) 1 μ :=
    (Lp.memLp (T Y)).norm.mul' (Lp.memLp Z).norm
  have hHolder : B≤A^(1/p)*(∫ x,‖T Y x‖^r ∂μ)^(1/r) := by
    calc
      _ = ∫ x,inner ℝ (Z x) (T Y x) ∂μ := hPair.symm.trans hSym
      _ ≤ ∫ x,‖Z x‖*‖T Y x‖ ∂μ :=
        integral_mono (L2.integrable_inner (𝕜 := ℝ) Z (T Y))
          (memLp_one_iff_integrable.mp hProduct) (fun x => real_inner_le_norm _ _)
      _ ≤ _ := integral_mul_norm_le_Lp_mul_Lq hpq hZp hTYr
  rw [hYMoment] at hTYBound
  refine ⟨hQp,?_⟩
  change B≤C^(p-1)*A
  by_cases hBZero : B=0
  · rw [hBZero]
    exact mul_nonneg (Real.rpow_nonneg hC _) hA
  have hBPos : 0<B := lt_of_le_of_ne hB (Ne.symm hBZero)
  have hInvSum : (1/p)+(1/r)=1 := by simpa only [one_div] using hpq.inv_add_inv_eq_one
  have hSplit : B=B^(1/p)*B^(1/r) := by rw [← Real.rpow_add hBPos,hInvSum,Real.rpow_one]
  have hMul : B^(1/p)*B^(1/r)≤(A^(1/p)*C^(1/r))*B^(1/r) := by
    calc
      _ = B := hSplit.symm
      _ ≤ A^(1/p)*(∫ x,‖T Y x‖^r ∂μ)^(1/r) := hHolder
      _ ≤ A^(1/p)*(C*B)^(1/r) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
          (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) hTYBound (one_div_nonneg.mpr hr.le))
          (Real.rpow_nonneg hA _)
      _ = _ := by rw [Real.mul_rpow hC hB];ring
  have hRoot : B^(1/p)≤A^(1/p)*C^(1/r) :=
    (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hBPos (1/r))).mp (by simpa only [mul_comm] using hMul)
  have hPow := Real.rpow_le_rpow (Real.rpow_nonneg hB _) hRoot hp0.le
  have hLeft : (B^(1/p))^p=B := by simpa only [one_div] using Real.rpow_inv_rpow hB hp0.ne'
  have hRight : (A^(1/p)*C^(1/r))^p=A*C^(p-1) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hA _) (Real.rpow_nonneg hC _)]
    have hARoot : (A^(1/p))^p=A := by simpa only [one_div] using Real.rpow_inv_rpow hA hp0.ne'
    rw [hARoot,← Real.rpow_mul hC]
    have hpr : (1/r)*p=p-1 := by
      simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hpq.div_conj_eq_sub_one
    rw [hpr]
  rw [hLeft,hRight] at hPow
  exact hPow.trans_eq (mul_comm _ _)

end StationaryHarmonicMaps.Analysis
end
