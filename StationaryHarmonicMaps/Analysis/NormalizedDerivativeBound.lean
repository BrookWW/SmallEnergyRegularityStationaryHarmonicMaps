module

public import StationaryHarmonicMaps.Analysis.LocallyFiniteSmoothSum
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Actual derivative bounds for finite local normalization

Local finiteness differentiates the original sum as one true finite
sum. Omitted topological supports give zero original derivatives. The
quotient is differentiated at the original positive denominator, and
the bounds use its actual value at least one and the original numerator
between zero and one.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The original locally finite sum has its actual derivative norm controlled by the genuine active finite set. -/
theorem norm_fderiv_locallyFinite_tsum_le {n : ℕ} {I : Type*}
    (η : I → Domain n → ℝ) (hη : ∀ i,ContDiff ℝ ∞ (η i)) (x : Domain n)
    (hLocal : ∃ V∈𝓝 x,{i | (Function.support (η i)∩V).Nonempty}.Finite)
    (A : Finset I) (hOutside : ∀ i∉A,x∉tsupport (η i))
    (B : ℝ) (hBound : ∀ i∈A,‖fderiv ℝ (η i) x‖≤B) :
    ‖fderiv ℝ (fun y=>∑' i,η i y) x‖≤A.card*B := by
  classical
  obtain ⟨F,hD,hZeroF⟩ := exists_hasFDerivAt_locallyFinite_tsum η hη x hLocal
  have hZeroA (i : I) (hi : i∉A) : fderiv ℝ (η i) x=0 := fderiv_of_notMem_tsupport ℝ (hOutside i hi)
  have hFA : (∑ i∈F,fderiv ℝ (η i) x)=∑ i∈A,fderiv ℝ (η i) x := by
    calc
      _ = ∑ i∈F∪A,fderiv ℝ (η i) x := Finset.sum_subset Finset.subset_union_left (fun i _ hi=>hZeroF i hi)
      _ = _ := (Finset.sum_subset Finset.subset_union_right (fun i _ hi=>hZeroA i hi)).symm
  rw [hD.fderiv,hFA]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hBound).trans_eq (by simp))

/-- The actual positive quotient has its genuine derivative bound from the original two derivatives, without assuming a quotient derivative certificate. -/
theorem norm_fderiv_normalized_scalar_le {n : ℕ}
    (η P : Domain n → ℝ) (x : Domain n) (hη : DifferentiableAt ℝ η x)
    (hP : DifferentiableAt ℝ P x) (hOne : 1≤P x) (hNonneg : 0≤η x) (hUpper : η x≤1)
    (B K : ℝ) (hDη : ‖fderiv ℝ η x‖≤B) (hDP : ‖fderiv ℝ P x‖≤K) :
    ‖fderiv ℝ (fun y=>η y/P y) x‖≤B+K := by
  have hPpos : 0<P x := zero_lt_one.trans_le hOne
  have hB : 0≤B := (norm_nonneg _).trans hDη
  have hK : 0≤K := (norm_nonneg _).trans hDP
  let L := (ContinuousLinearMap.toSpanSingleton ℝ (-((P x)^2)⁻¹)).comp (fderiv ℝ P x)
  have hInv : HasFDerivAt (fun y=>(P y)⁻¹) L x := (hasFDerivAt_inv hPpos.ne').comp x hP.hasFDerivAt
  have hCoeff : ‖ContinuousLinearMap.toSpanSingleton ℝ (-((P x)^2)⁻¹)‖≤1 := by
    rw [ContinuousLinearMap.norm_toSpanSingleton,norm_neg,Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    exact inv_le_one_of_one_le₀ (by nlinarith only [hOne])
  have hL : ‖L‖≤K := by
    calc
      _ ≤ ‖ContinuousLinearMap.toSpanSingleton ℝ (-((P x)^2)⁻¹)‖*‖fderiv ℝ P x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1*K := mul_le_mul hCoeff hDP (norm_nonneg _) zero_le_one
      _ = K := one_mul _
  have hD : HasFDerivAt (fun y=>η y/P y) (η x • L+(P x)⁻¹ • fderiv ℝ η x) x := by
    simpa only [div_eq_mul_inv,Pi.mul_apply] using hη.hasFDerivAt.fun_mul hInv
  have hηNorm : ‖η x‖≤1 := by rw [Real.norm_of_nonneg hNonneg];exact hUpper
  have hInvNorm : ‖(P x)⁻¹‖≤1 := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hPpos.le)]
    exact inv_le_one_of_one_le₀ hOne
  rw [hD.fderiv]
  calc
    _ ≤ ‖η x • L‖+‖(P x)⁻¹ • fderiv ℝ η x‖ := norm_add_le _ _
    _ = ‖η x‖*‖L‖+‖(P x)⁻¹‖*‖fderiv ℝ η x‖ := by rw [norm_smul,norm_smul]
    _ ≤ 1*K+1*B := add_le_add (mul_le_mul hηNorm hL (norm_nonneg _) zero_le_one)
      (mul_le_mul hInvNorm hDη (norm_nonneg _) zero_le_one)
    _ = B+K := by ring

end StationaryHarmonicMaps.Analysis

end
