module

public import StationaryHarmonicMaps.Analysis.SkewMorreyCommutator
public import StationaryHarmonicMaps.Analysis.NaturalCoefficientNeumannBanachKernelInverse

/-!
# The actual skew linearized Coulomb Neumann inverse

Original critical natural skew coefficients produce the commutator
Neumann operator and the actual identity perturbation inverse on the
same complete skew mean-zero native Morrey space.
-/

public section
open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal
noncomputable section
namespace StationaryHarmonicMaps.Analysis

/-- The original natural skew field constructs the same-response small
commutator operator and the actual I+N[Z,·] inverse on the genuine skew
native Banach carrier. Every native test and the full inverse bound remain
part of the produced conclusion. -/
theorem exists_small_skew_natural_neumann_morrey_inverse
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    let ν : ℝ := (n:ℝ)-2+γ
    ∃C : ℝ,0<C ∧ ∀(q : ℕ)
      (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q)),
      let B := morreyMatrixCommutator q e
      let S := SkewMeanZeroNativeMorreySpace n q ν e
      letI : NormedAddCommGroup S := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
      letI : SeminormedAddCommGroup S :=
        (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
      letI : NormedSpace ℝ S := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
      ∃ε : ℝ,0<ε ∧ ∀(Z : Domain n→Gradient n (q*q)) (η : ℝ),
        (∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0:Domain n) 1))) →
        (∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) →
        0≤η → η≤ε →
        criticalGradientMorreySquare Z (ball (0:Domain n) 1)≤ENNReal.ofReal (η^2) →
        (∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,
          star (e (Z x i))=-(e (Z x i))) →
        ∃T : MeanZeroNativeMorreySpace n (q*q) ν→L[ℝ]MeanZeroNativeMorreySpace n (q*q) ν,
          (‖T‖≤C*‖B‖*η ∧ ∀X : MeanZeroNativeMorreySpace n (q*q) ν,
            let u : Domain n→Ambient (q*q) := (nativeMorreyMapClass (n:=n) (q:=q*q) ν) X.val
            let Y : MeanZeroNativeMorreySpace n (q*q) ν := T X
            let Q : Domain n→Gradient n (q*q) := fun x i=>WithLp.toLp 2
              (fun j : Fin (q*q)=>(nativeMorreyHSClass (n:=n) (q:=q*q) ν) Y.val x (finProdFinEquiv (i,j)))
            ∀(ψ : Domain n→Ambient (q*q)) (Dψ : Domain n→Gradient n (q*q)),
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
  have hData := exists_small_fixed_kernel_natural_neumann_morrey_inverse n hn γ hγ hγTwo
  let C := hData.choose
  have hC : 0<C := hData.choose_spec.1
  have H := hData.choose_spec.2
  refine ⟨C,hC,?_⟩
  intro q e
  let S := SkewMeanZeroNativeMorreySpace n q ν e
  letI : NormedAddCommGroup S := Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)
  letI : SeminormedAddCommGroup S :=
    (Submodule.normedAddCommGroup (skewMeanZeroNativeMorreySubmodule n q ν e)).toSeminormedAddCommGroup
  letI : NormedSpace ℝ S := Submodule.normedSpace (skewMeanZeroNativeMorreySubmodule n q ν e)
  let B := morreyMatrixCommutator q e
  let J := skewMorreyCoordinateConstraint q e
  have hThreshold := H (q*q) (q*q) (q*q) B J
  let ε := hThreshold.choose
  have hε : 0<ε := hThreshold.choose_spec.1
  have Hε := hThreshold.choose_spec.2
  refine ⟨ε,hε,?_⟩
  intro Z η hZ hNatural hη hηle hCritical hSkew
  have hKernel : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i : Fin n,∀w : Ambient (q*q),
      J w=0 → J (B (Z x i) w)=0 := by
    filter_upwards [hSkew] with x hx
    intro i w hw
    exact morreyMatrixCommutator_preserves_skew_kernel q e (Z x i) w (hx i) hw
  exact Hε Z η hZ hNatural hη hηle hCritical hKernel

end StationaryHarmonicMaps.Analysis
end
