module

public import StationaryHarmonicMaps.Analysis.NaturalCoefficientNeumannBanachRestriction
public import StationaryHarmonicMaps.Analysis.NaturalCoefficientNeumannBanachInverse

/-!
# The constrained small inverse from original natural coefficient data

Original critical natural coefficients produce the genuine compensated
operator and its inverse on the closed coefficient kernel. No response,
growth, preserved-kernel operator or inverse is assumed.
-/

public section
open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal
noncomputable section
namespace StationaryHarmonicMaps.Analysis

/-- The coefficient threshold and actual same-response kernel inverse are
constructed from the original natural coefficient field. The fixed linear
constraint is preserved by its explicit bilinear coefficient algebra. -/
theorem exists_small_fixed_kernel_natural_neumann_morrey_inverse
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    let ν : ℝ := (n:ℝ)-2+γ
    ∃C : ℝ,0<C ∧ ∀(m q d : ℕ)
      (B : Ambient m→L[ℝ](Ambient q→L[ℝ]Ambient q))
      (J : Ambient q→L[ℝ]Ambient d),
      let S := ConstrainedMeanZeroNativeMorreySpace n q d ν J
      ∃ε : ℝ,0<ε ∧ ∀(Z : Domain n→Gradient n m) (η : ℝ),
        (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
        (∀(ψ : Domain n→Ambient m) (Dψ : Domain n→Gradient n m),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) →
        0≤η → η≤ε →
        criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
        (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,∀w : Ambient q,
          J w=0 → J (B (Z x i) w)=0) →
        ∃T : MeanZeroNativeMorreySpace n q ν→L[ℝ]MeanZeroNativeMorreySpace n q ν,
          (‖T‖≤C*‖B‖*η ∧ ∀X : MeanZeroNativeMorreySpace n q ν,
            let u : Domain n→Ambient q := (nativeMorreyMapClass (n:=n) (q:=q) ν) X.val
            let Y : MeanZeroNativeMorreySpace n q ν := T X
            let Q : Domain n→Gradient n q := fun x i=>WithLp.toLp 2
              (fun j : Fin q=>(nativeMorreyHSClass (n:=n) (q:=q) ν) Y.val x (finProdFinEquiv (i,j)))
            ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
              MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
              IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
              IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
              (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
                ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) ∧
          ‖T‖≤(1/2:ℝ) ∧
          ∃!A : S≃L[ℝ]S,
            (∀X : S,(A X).val=X.val+T X.val) ∧
            ‖(A.symm : S→L[ℝ]S)‖≤2 := by
  let ν : ℝ := (n:ℝ)-2+γ
  have hData := exists_small_natural_coefficient_neumann_morrey_inverse n hn γ hγ hγTwo
  let C := hData.choose
  have hC : 0<C := hData.choose_spec.1
  have H := hData.choose_spec.2
  refine ⟨C,hC,?_⟩
  intro m q d B J
  let S := ConstrainedMeanZeroNativeMorreySpace n q d ν J
  have hThreshold := H m q B
  let ε := hThreshold.choose
  have hε : 0<ε := hThreshold.choose_spec.1
  have Hε := hThreshold.choose_spec.2
  refine ⟨ε,hε,?_⟩
  intro Z η hZ hNatural hη hηle hCritical hB
  have hOperator := Hε Z η hZ hNatural hη hηle hCritical
  let T := hOperator.choose
  have hT := hOperator.choose_spec.1
  refine ⟨T,hT.1,hT.2.1,?_⟩
  exact exists_natural_neumann_fixed_kernel_identity_inverse ν J B Z hB T
    (fun X ψ Dψ hψ=>(hT.1.2 X ψ Dψ hψ).2.2) hT.2.1

/-- The coefficient threshold and actual same-response kernel inverse are
constructed from the original natural coefficient field. The fixed linear
constraint is preserved by its explicit bilinear coefficient algebra. -/
theorem effective_small_fixed_kernel_natural_neumann_morrey_inverse
    (n : ℕ) (hn : 2≤n) (bilinearBound : ℚ) (hBound : 0 ≤ bilinearBound) :
    let ν : ℝ := (n:ℝ)-1
    ∀(m q d : ℕ)
      (B : Ambient m→L[ℝ](Ambient q→L[ℝ]Ambient q))
      (J : Ambient q→L[ℝ]Ambient d),
      ‖B‖ ≤ (bilinearBound : ℝ) →
      let S := ConstrainedMeanZeroNativeMorreySpace n q d ν J
      ∀(Z : Domain n→Gradient n m) (η : ℝ),
        (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
        (∀(ψ : Domain n→Ambient m) (Dψ : Domain n→Gradient n m),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) →
        0≤η → η≤(effectiveNaturalNeumannInverseAmplitude n bilinearBound : ℝ) →
        criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
        (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,∀w : Ambient q,
          J w=0 → J (B (Z x i) w)=0) →
        ∃T : MeanZeroNativeMorreySpace n q ν→L[ℝ]MeanZeroNativeMorreySpace n q ν,
          (‖T‖≤(effectiveNaturalNeumannOperatorConstant n : ℝ)*‖B‖*η ∧ ∀X : MeanZeroNativeMorreySpace n q ν,
            let u : Domain n→Ambient q := (nativeMorreyMapClass (n:=n) (q:=q) ν) X.val
            let Y : MeanZeroNativeMorreySpace n q ν := T X
            let Q : Domain n→Gradient n q := fun x i=>WithLp.toLp 2
              (fun j : Fin q=>(nativeMorreyHSClass (n:=n) (q:=q) ν) Y.val x (finProdFinEquiv (i,j)))
            ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
              MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
              IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
              IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) (ball (0:Domain n) 1) volume ∧
              (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
                ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i)) ∧
          ‖T‖≤(1/2:ℝ) ∧
          ∃!A : S≃L[ℝ]S,
            (∀X : S,(A X).val=X.val+T X.val) ∧
            ‖(A.symm : S→L[ℝ]S)‖≤2 := by
  intro ν
  have H := effective_small_natural_coefficient_neumann_morrey_inverse n hn bilinearBound hBound
  intro m q d B J hBnorm S
  have Hε := H m q B hBnorm
  intro Z η hZ hNatural hη hηle hCritical hB
  have hOperator := Hε Z η hZ hNatural hη hηle hCritical
  let T := hOperator.choose
  have hT := hOperator.choose_spec.1
  refine ⟨T,hT.1,hT.2.1,?_⟩
  exact exists_natural_neumann_fixed_kernel_identity_inverse ν J B Z hB T
    (fun X ψ Dψ hψ=>(hT.1.2 X ψ Dψ hψ).2.2) hT.2.1

end StationaryHarmonicMaps.Analysis
end
