module

public import StationaryHarmonicMaps.Analysis.ClosedNormalTensorOperations
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtEncoding
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The actual smooth closed normal divergence range

The Hilbert coefficient space uses every original HS coefficient.
Membership in the constructed linear subspace means representation by an
actual smooth antisymmetric closed tensor with zero sphere contraction.
No image-surjectivity or weak regularity property is part of its carrier.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual divergences of the smooth closed normal tensor core form a genuine full-HS L2 linear subspace, with literal representation characterization. -/
theorem exists_smooth_closed_normal_divergence_submodule_unitBall (n q : ℕ) :
    let μ := volume.restrict (ball (0 : Domain n) 1)
    let E : Gradient n q → Ambient (n*q) := fun A=>WithLp.toLp 2
      (fun k=>A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    ∃ S : Submodule ℝ (Lp (Ambient (n*q)) 2 μ),∀ Z,Z∈S ↔
      ∃ B : Fin n → Fin n → Domain n → Ambient q,
        (∀ i j,ContDiff ℝ ∞ (B i j)) ∧
        (∀ i j x,B i j x = -B j i x) ∧
        (∀ i j k x,fderiv ℝ (B i j) x (EuclideanSpace.single k 1)+
          fderiv ℝ (B j k) x (EuclideanSpace.single i 1)+fderiv ℝ (B k i) x (EuclideanSpace.single j 1)=0) ∧
        (∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • B i j x)=0) ∧
        (Z : Domain n → Ambient (n*q)) =ᵐ[μ]
          (fun x=>E (fun j=>∑ i : Fin n,fderiv ℝ (B i j) x (EuclideanSpace.single i 1))) := by
  intro μ E
  classical
  let S : Submodule ℝ (Lp (Ambient (n*q)) 2 μ) :=
    { carrier := {Z | ∃ B : Fin n → Fin n → Domain n → Ambient q,
        (∀ i j,ContDiff ℝ ∞ (B i j)) ∧
        (∀ i j x,B i j x = -B j i x) ∧
        (∀ i j k x,fderiv ℝ (B i j) x (EuclideanSpace.single k 1)+
          fderiv ℝ (B j k) x (EuclideanSpace.single i 1)+fderiv ℝ (B k i) x (EuclideanSpace.single j 1)=0) ∧
        (∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • B i j x)=0) ∧
        (Z : Domain n → Ambient (n*q)) =ᵐ[μ]
          (fun x=>E (fun j=>∑ i : Fin n,fderiv ℝ (B i j) x (EuclideanSpace.single i 1)))}
      zero_mem' := by
        let B := fun (_i _j : Fin n) (_x : Domain n)=>(0:Ambient q)
        refine ⟨B,fun i j=>contDiff_const,?_,?_,?_,?_⟩
        · intro i j x
          exact (neg_zero (G := Ambient q)).symm
        · intro i j k x
          simp [B]
        · intro j x _hx
          simp only [B,smul_zero,Finset.sum_const_zero]
        · filter_upwards [Lp.coeFn_zero (Ambient (n*q)) 2 μ] with x hx
          change (0 : Lp (Ambient (n*q)) 2 μ) x = _
          rw [hx]
          ext k
          simp [E,B]
      add_mem' := by
        rintro Z W ⟨B,hB,hBS,hBD,hBN,hZ⟩ ⟨C,hC,hCS,hCD,hCN,hW⟩
        let N := fun a b x=>(-1:ℝ) • C a b x
        obtain ⟨hN,hNS,hND,hNN⟩ := smooth_closed_normal_twoTensor_smul (-1) C hC hCS hCD hCN
        let D := fun a b x=>B a b x-N a b x
        obtain ⟨hD,hDS,hDD,hDN⟩ := smooth_closed_normal_twoTensor_sub B N hB hN hBS hNS hBD hND hBN hNN
        have hFun (a b : Fin n) : D a b=B a b+C a b := by
          funext y
          simp only [D,N,neg_one_smul,sub_neg_eq_add,Pi.add_apply]
        have hDF (a b : Fin n) (x : Domain n) : fderiv ℝ (D a b) x =
            fderiv ℝ (B a b) x+fderiv ℝ (C a b) x := by
          rw [hFun]
          exact fderiv_add ((hB a b).differentiable (by simp) x) ((hC a b).differentiable (by simp) x)
        have hDiv (j : Fin n) (x : Domain n) : (∑ i : Fin n,fderiv ℝ (D i j) x (EuclideanSpace.single i 1)) =
            (∑ i : Fin n,fderiv ℝ (B i j) x (EuclideanSpace.single i 1))+
              (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)) := by
          simp only [hDF,add_apply,Finset.sum_add_distrib]
        refine ⟨D,hD,hDS,hDD,hDN,?_⟩
        filter_upwards [Lp.coeFn_add Z W,hZ,hW] with x hx hz hw
        rw [hx]
        change Z x+W x = _
        rw [hz,hw]
        ext k
        change ((∑ i : Fin n,fderiv ℝ (B i (finProdFinEquiv.symm k).1) x (EuclideanSpace.single i 1))
          (finProdFinEquiv.symm k).2)+
          ((∑ i : Fin n,fderiv ℝ (C i (finProdFinEquiv.symm k).1) x (EuclideanSpace.single i 1))
          (finProdFinEquiv.symm k).2) =
          (∑ i : Fin n,fderiv ℝ (D i (finProdFinEquiv.symm k).1) x (EuclideanSpace.single i 1))
            (finProdFinEquiv.symm k).2
        rw [hDiv]
        rfl
      smul_mem' := by
        rintro c Z ⟨B,hB,hBS,hBD,hBN,hZ⟩
        let D := fun a b x=>c • B a b x
        obtain ⟨hD,hDS,hDD,hDN⟩ := smooth_closed_normal_twoTensor_smul c B hB hBS hBD hBN
        have hDF (a b : Fin n) (x : Domain n) : fderiv ℝ (D a b) x=c • fderiv ℝ (B a b) x := by
          have H := (((hB a b).differentiable (by simp) x).hasFDerivAt.const_smul c).fderiv
          have heq : c • B a b=D a b := rfl
          rw [heq] at H
          exact H
        have hDiv (j : Fin n) (x : Domain n) : (∑ i : Fin n,fderiv ℝ (D i j) x (EuclideanSpace.single i 1)) =
            c • (∑ i : Fin n,fderiv ℝ (B i j) x (EuclideanSpace.single i 1)) := by
          simp only [hDF,smul_apply,Finset.smul_sum]
        refine ⟨D,hD,hDS,hDD,hDN,?_⟩
        filter_upwards [Lp.coeFn_smul c Z,hZ] with x hx hz
        rw [hx]
        change c • Z x = _
        rw [hz]
        ext k
        change c*((∑ i : Fin n,fderiv ℝ (B i (finProdFinEquiv.symm k).1) x (EuclideanSpace.single i 1))
          (finProdFinEquiv.symm k).2) =
          (∑ i : Fin n,fderiv ℝ (D i (finProdFinEquiv.symm k).1) x (EuclideanSpace.single i 1))
            (finProdFinEquiv.symm k).2
        rw [hDiv]
        rfl }
  exact ⟨S,fun _=>Iff.rfl⟩

end StationaryHarmonicMaps.Analysis

end
