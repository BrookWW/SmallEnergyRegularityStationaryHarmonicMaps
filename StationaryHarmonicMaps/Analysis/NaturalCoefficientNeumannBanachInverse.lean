module

public import StationaryHarmonicMaps.Analysis.NaturalCoefficientNeumannBanach
public import Mathlib.Analysis.Normed.Ring.Units

/-!
# An actual inverse for the small natural Neumann perturbation

The compensated operator norm gives a positive coefficient threshold
before the original fields. The genuine geometric-series unit supplies
I+T and its inverse, with inverse norm at most two.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

noncomputable section

namespace StationaryHarmonicMaps.Analysis

private theorem small_add_identity_inverse {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (T : V→L[ℝ]V) (hT : ‖T‖≤(1/2:ℝ)) :
    ∃!A : V≃L[ℝ]V,(∀X : V,A X=X+T X) ∧ ‖(A.symm : V→L[ℝ]V)‖≤2 := by
  have hTOne : ‖-T‖<1 := by rw [norm_neg];exact hT.trans_lt (by norm_num)
  let U := Units.oneSub (-T) hTOne
  let A : V≃L[ℝ]V := ContinuousLinearEquiv.ofUnit U
  have hA (X : V) : A X=X+T X := by
    change ((1 : V→L[ℝ]V)-(-T)) X=X+T X
    simp only [sub_neg_eq_add,add_apply,one_apply_eq_self]
  have hInverse (Y : V) : ‖A.symm Y‖≤2*‖Y‖ := by
    have hEquation : A.symm Y+T (A.symm Y)=Y := (hA (A.symm Y)).symm.trans (A.apply_symm_apply Y)
    have hRearr : A.symm Y=Y-T (A.symm Y) := eq_sub_of_add_eq hEquation
    have hBound : ‖A.symm Y‖≤‖Y‖+(1/2:ℝ)*‖A.symm Y‖ := by
      calc
        _=‖Y-T (A.symm Y)‖ := congrArg norm hRearr
        _≤‖Y‖+‖T (A.symm Y)‖ := norm_sub_le _ _
        _≤‖Y‖+‖T‖*‖A.symm Y‖ := add_le_add le_rfl (T.le_opNorm _)
        _≤_ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hT (norm_nonneg (A.symm Y)))
    linarith only [hBound]
  have hNorm : ‖(A.symm : V→L[ℝ]V)‖≤2 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num) hInverse
  refine ⟨A,⟨hA,hNorm⟩,?_⟩
  intro D hD
  apply ContinuousLinearEquiv.ext
  funext X
  exact (hD.1 X).trans (hA X).symm

private theorem inverse_of_unique_operator {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] {P : (V→L[ℝ]V)→Prop}
    (h : ∃!T,P T) (hSmall : ∀T,P T → ‖T‖≤(1/2:ℝ)) :
    ∃!T,P T ∧ ‖T‖≤(1/2:ℝ) ∧
      ∃!A : V≃L[ℝ]V,(∀X : V,A X=X+T X) ∧ ‖(A.symm : V→L[ℝ]V)‖≤2 := by
  obtain ⟨T,hT,hUnique⟩ := h
  have hTSmall := hSmall T hT
  refine ⟨T,⟨hT,hTSmall,small_add_identity_inverse T hTSmall⟩,?_⟩
  intro S hS
  exact hUnique S hS.1

/-- A coefficient threshold is chosen internally. The same unique
natural Neumann operator has norm at most one half, and the actual
I+T equivalence has its full inverse with norm at most two. -/
theorem exists_small_natural_coefficient_neumann_morrey_inverse
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀(m q : ℕ)
      (B : Ambient m→L[ℝ](Ambient q→L[ℝ]Ambient q)),
      ∃ε : ℝ,0<ε ∧ ∀(Z : Domain n→Gradient n m) (η : ℝ),
        (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
        (∀(ψ : Domain n→Ambient m) (Dψ : Domain n→Gradient n m),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) →
        0≤η → η≤ε →
        criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
        letI : NormedAddCommGroup (MeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ)) := Submodule.normedAddCommGroup _
        ∃!T : MeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ)→L[ℝ]MeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ),
          (‖T‖≤C*‖B‖*η ∧ ∀X : MeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ),
            let u : Domain n→Ambient q := (nativeMorreyMapClass (n:=n) (q:=q) ((n:ℝ)-2+γ)) X.val
            let Q : Domain n→Gradient n q := fun x i=>WithLp.toLp 2
              (fun j : Fin q=>(nativeMorreyHSClass (n:=n) (q:=q) ((n:ℝ)-2+γ)) (T X).val x (finProdFinEquiv (i,j)))
            ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
              MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
              IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
              IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
              (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
                ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) ∧
          ‖T‖≤(1/2:ℝ) ∧
          ∃!A : MeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ)≃L[ℝ]MeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ),
            (∀X,A X=X+T X) ∧
            ‖(A.symm : MeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ)→L[ℝ]MeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ))‖≤2 := by
  have hData := exists_unique_natural_coefficient_neumann_morrey_operator n hn γ hγ hγTwo
  let C := hData.choose
  have hC : 0<C := hData.choose_spec.1
  have H := hData.choose_spec.2
  refine ⟨C,hC,?_⟩
  intro m q B
  let D := C*(1+‖B‖)
  have hD : 0<D := mul_pos hC (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg B))
  let ε := (2*D)⁻¹
  have hε : 0<ε := inv_pos.mpr (mul_pos (by norm_num) hD)
  have hDE : D*ε=(1/2:ℝ) := by
    have hCancel : (2*D)*ε=1 := mul_inv_cancel₀ (mul_pos (by norm_num) hD).ne'
    linarith only [hCancel]
  refine ⟨ε,hε,?_⟩
  intro Z η hZ hNatural hη hηle hCritical
  letI : NormedAddCommGroup (MeanZeroNativeMorreySpace n q ((n:ℝ)-2+γ)) := Submodule.normedAddCommGroup _
  have hCoeff : C*‖B‖*η≤(1/2:ℝ) := by
    have hCoeff' : C*‖B‖*η≤D*ε := by
      calc
        _≤D*η := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith only [norm_nonneg B] : ‖B‖≤1+‖B‖) hC.le) hη
        _≤D*ε := mul_le_mul_of_nonneg_left hηle hD.le
    exact hCoeff'.trans_eq hDE
  exact inverse_of_unique_operator (H m q q B Z η hZ hNatural hη hCritical)
    (fun T hT=>hT.1.trans hCoeff)

@[expose] def effectiveNaturalNeumannInverseAmplitude (n : ℕ) (bilinearBound : ℚ) : ℚ :=
  EffectiveCoulomb.inverseAmplitude (effectiveNaturalNeumannOperatorConstant n) bilinearBound

theorem effectiveNaturalNeumannInverseAmplitude_pos (n : ℕ) (hn : 1 ≤ n)
    {bilinearBound : ℚ} (hBound : 0 ≤ bilinearBound) :
    0 < effectiveNaturalNeumannInverseAmplitude n bilinearBound :=
  EffectiveCoulomb.inverseAmplitude_pos (effectiveNaturalNeumannOperatorConstant_pos n hn) hBound

/-- A coefficient threshold is chosen internally. The same unique
natural Neumann operator has norm at most one half, and the actual
I+T equivalence has its full inverse with norm at most two. -/
theorem effective_small_natural_coefficient_neumann_morrey_inverse
    (n : ℕ) (hn : 2≤n) (bilinearBound : ℚ) (hBound : 0 ≤ bilinearBound) :
    ∀(m q : ℕ)
      (B : Ambient m→L[ℝ](Ambient q→L[ℝ]Ambient q)),
      ‖B‖ ≤ (bilinearBound : ℝ) → ∀(Z : Domain n→Gradient n m) (η : ℝ),
        (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
        (∀(ψ : Domain n→Ambient m) (Dψ : Domain n→Gradient n m),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) →
        0≤η → η≤(effectiveNaturalNeumannInverseAmplitude n bilinearBound : ℝ) →
        criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
        letI : NormedAddCommGroup (MeanZeroNativeMorreySpace n q ((n:ℝ)-1)) := Submodule.normedAddCommGroup _
        ∃!T : MeanZeroNativeMorreySpace n q ((n:ℝ)-1)→L[ℝ]MeanZeroNativeMorreySpace n q ((n:ℝ)-1),
          (‖T‖≤(effectiveNaturalNeumannOperatorConstant n : ℝ)*‖B‖*η ∧ ∀X : MeanZeroNativeMorreySpace n q ((n:ℝ)-1),
            let u : Domain n→Ambient q := (nativeMorreyMapClass (n:=n) (q:=q) ((n:ℝ)-1)) X.val
            let Q : Domain n→Gradient n q := fun x i=>WithLp.toLp 2
              (fun j : Fin q=>(nativeMorreyHSClass (n:=n) (q:=q) ((n:ℝ)-1)) (T X).val x (finProdFinEquiv (i,j)))
            ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
              MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
              IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
              IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
              (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
                ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) ∧
          ‖T‖≤(1/2:ℝ) ∧
          ∃!A : MeanZeroNativeMorreySpace n q ((n:ℝ)-1)≃L[ℝ]MeanZeroNativeMorreySpace n q ((n:ℝ)-1),
            (∀X,A X=X+T X) ∧
            ‖(A.symm : MeanZeroNativeMorreySpace n q ((n:ℝ)-1)→L[ℝ]MeanZeroNativeMorreySpace n q ((n:ℝ)-1))‖≤2 := by
  have H := effective_unique_natural_coefficient_neumann_morrey_operator n hn
  intro m q B hB Z η hZ hNatural hη hηle hCritical
  letI : NormedAddCommGroup (MeanZeroNativeMorreySpace n q ((n:ℝ)-1)) := Submodule.normedAddCommGroup _
  have hC : 0 < (effectiveNaturalNeumannOperatorConstant n : ℝ) := by
    exact_mod_cast effectiveNaturalNeumannOperatorConstant_pos n (by omega)
  have hCoeff : (effectiveNaturalNeumannOperatorConstant n : ℝ) * ‖B‖ * η ≤ 1 / 2 := by
    calc
      _ ≤ (effectiveNaturalNeumannOperatorConstant n : ℝ) * (bilinearBound : ℝ) * η :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hC.le) hη
      _ ≤ 1 / 2 := EffectiveCoulomb.inverseAmplitude_controls_product
        (effectiveNaturalNeumannOperatorConstant_pos n (by omega)) hBound hη hηle
  exact inverse_of_unique_operator (H m q q B Z η hZ hNatural hη hCritical)
    (fun T hT => hT.1.trans hCoeff)


end StationaryHarmonicMaps.Analysis

end
