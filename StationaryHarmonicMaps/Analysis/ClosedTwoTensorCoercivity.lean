module

public import StationaryHarmonicMaps.Analysis.ClosedTwoTensorGaffney
public import StationaryHarmonicMaps.Analysis.NormalOneFormCoercivity

/-!
# Actual full H1 coercivity of closed normal two-tensors

The original coefficient means come from the normal boundary condition.
The actual native Poincare estimate and the closed-tensor Gaffney bound
control both coefficient and derivative energies by the codifferential.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual smooth closed antisymmetric normal two-tensors satisfy complete coefficient H1 coercivity with a dimension-only constant. -/
theorem smooth_closed_normal_twoTensor_coercivity {n q : ℕ}
    (B : Fin n → Fin n → Domain n → Ambient q)
    (hB : ∀ i j, ContDiff ℝ ∞ (B i j))
    (hSkew : ∀ i j x, B i j x = -B j i x)
    (hClosed : ∀ i j k x,
      fderiv ℝ (B i j) x (EuclideanSpace.single k 1) +
        fderiv ℝ (B j k) x (EuclideanSpace.single i 1) +
        fderiv ℝ (B k i) x (EuclideanSpace.single j 1) = 0)
    (hNormal : ∀ j (x : Domain n), ‖x‖=1 → (∑ i : Fin n,x i • B i j x)=0) :
    let e := fun x : Domain n=>∑ j : Fin n,∑ i : Fin n,‖B i j x‖^2
    let g := fun x : Domain n=>∑ j : Fin n,∑ k : Fin n,∑ i : Fin n,
      ‖fderiv ℝ (B i j) x (EuclideanSpace.single k 1)‖^2
    let d := fun x : Domain n=>∑ j : Fin n,
      ‖∑ i : Fin n,fderiv ℝ (B i j) x (EuclideanSpace.single i 1)‖^2
    IntegrableOn e (ball (0 : Domain n) 1) volume ∧
      IntegrableOn g (ball (0 : Domain n) 1) volume ∧
      IntegrableOn d (ball (0 : Domain n) 1) volume ∧
      (∫ x in ball (0 : Domain n) 1,e x) +
        (∫ x in ball (0 : Domain n) 1,g x) ≤
          (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)*(∫ x in ball (0 : Domain n) 1,d x) := by
  intro e g d
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let Cp : ℝ := (2:ℝ)^(n+1)
  let ej := fun (j : Fin n) (x : Domain n)=>∑ i : Fin n,‖B i j x‖^2
  let gj := fun (j : Fin n) (x : Domain n)=>∑ k : Fin n,∑ i : Fin n,
    ‖fderiv ℝ (B i j) x (EuclideanSpace.single k 1)‖^2
  let dj := fun (j : Fin n) (x : Domain n)=>
    ‖∑ i : Fin n,fderiv ℝ (B i j) x (EuclideanSpace.single i 1)‖^2
  have hG := smooth_closed_normal_twoTensor_gaffney B hB hSkew hClosed hNormal
  have hC (j : Fin n) := smooth_normal_oneForm_coefficient_bound (fun i=>B i j)
    (fun i=>hB i j) (hNormal j)
  have heI : Integrable e μ := integrable_finsetSum _ (fun j _=>(hC j).1)
  have hsum : (∑ j : Fin n,∫ x,ej j x ∂μ) ≤
      (2*Cp)*(∑ j : Fin n,∫ x,gj j x ∂μ) +
        (2*(n:ℝ))*(∑ j : Fin n,∫ x,dj j x ∂μ) := by
    have H := Finset.sum_le_sum (s := Finset.univ) (fun j _=>(hC j).2.2.2)
    simpa only [Finset.sum_add_distrib,← Finset.mul_sum] using H
  have heEq : (∑ j : Fin n,∫ x,ej j x ∂μ)=∫ x,e x ∂μ :=
    (integral_finsetSum _ (fun j _=>(hC j).1)).symm
  have hgEq : (∑ j : Fin n,∫ x,gj j x ∂μ)=∫ x,g x ∂μ :=
    (integral_finsetSum _ (fun j _=>(hC j).2.1)).symm
  have hdEq : (∑ j : Fin n,∫ x,dj j x ∂μ)=∫ x,d x ∂μ :=
    (integral_finsetSum _ (fun j _=>(hC j).2.2.1)).symm
  rw [heEq,hgEq,hdEq] at hsum
  have hGrad : (∫ x,g x ∂μ) ≤ 2*(∫ x,d x ∂μ) := hG.2.2
  have hWeighted := mul_le_mul_of_nonneg_left hGrad (by positivity : (0:ℝ)≤2*Cp)
  refine ⟨heI,hG.1,hG.2.1,?_⟩
  change (∫ x,e x ∂μ)+(∫ x,g x ∂μ) ≤ (4*Cp+2*(n:ℝ)+2)*(∫ x,d x ∂μ)
  nlinarith only [hsum,hGrad,hWeighted]

end StationaryHarmonicMaps.Analysis

end
