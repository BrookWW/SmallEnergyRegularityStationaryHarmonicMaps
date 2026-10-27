/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.SystemMatrixPairing
public import StationaryHarmonicMaps.Analysis.DivCurlKernelCancellation

/-!
# Ordinary compensated pairing of the actual matrix system forcing

The actual rank-one matrix tests and their centered-cutoff products have
genuine native zero-boundary graphs. Testing the original full matrix
divergence equation gives the finite-index compensated identity for the
literal ordered forcing Σ Z_i(P*Dv_i), with ordinary integrability.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original full matrix divergence equation produces the actual
finite-index compensated forcing pairing. No component forcing equation,
product-test certificate or rearrangement of the matrix factors is assumed. -/
theorem native_system_matrix_compensated_pairing_ball {n m q : ℕ}
    (a : Domain n) (r : ℝ) (hr : 0<r)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (p : Domain n → Ambient m) (Dp : Domain n → Gradient n m)
    (hp : MemW12 (ballDomain a r) p Dp) (M : ℝ)
    (hpBound : ∀ᵐx∂volume.restrict (ball a r),‖p x‖≤M)
    (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q)
    (hv : MemW12 (ballDomain a r) v Dv) (N : ℝ)
    (hvBound : ∀ᵐx∂volume.restrict (ball a r),‖v x‖≤N)
    (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q)
    (hφ : HasZeroBoundaryValues (ballDomain a r) φ Dφ) (H : ℝ)
    (hφBound : ∀ᵐx∂volume.restrict (ball a r),‖φ x‖≤H)
    (Z : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q))
    (hZ : ∀i,MemLp (fun x=>E (Z x i)) 2 (volume.restrict (ball a r)))
    (hDiv : HolderToCK.WeakPoissonOn (ballDomain a r)
      (fun x i=>E (Z x i)) (fun _=>0))
    (c : Ambient q) :
    let T := fun (j : Fin q) x=>systemMatrixTestCoefficient E R j (p x) (φ x)
    let DT := fun (j : Fin q) x i=>systemMatrixTestCoefficient E R j (Dp x i) (φ x)+
      systemMatrixTestCoefficient E R j (p x) (Dφ x i)
    let W := fun x=>∑i : Fin n,Z x i (star (R (p x)) (Dv x i))
    (∀j,HasZeroBoundaryValues (ballDomain a r) (T j) (DT j)) ∧
    (∀j,HasZeroBoundaryValues (ballDomain a r) (fun x=>(v x-c) j • T j x)
      (fun x i=>(Dv x i) j • T j x+(v x-c) j • DT j x i)) ∧
    IntegrableOn (fun x=>inner ℝ (W x) (φ x)) (ball a r) volume ∧
    (∀j,IntegrableOn (fun x=>(v x-c) j*(∑i : Fin n,inner ℝ (E (Z x i)) (DT j x i))) (ball a r) volume) ∧
    (∫x in ball a r,inner ℝ (W x) (φ x))=
      -(∑j : Fin q,∫x in ball a r,(v x-c) j*(∑i : Fin n,inner ℝ (E (Z x i)) (DT j x i))) := by
  intro T DT W
  let μ := volume.restrict (ball a r)
  letI : IsFiniteMeasure (volume.restrict (ballDomain a r).val) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hT (j : Fin q) : HasZeroBoundaryValues (ballDomain a r) (T j) (DT j) :=
    zeroBoundary_bounded_native_bilinear_product_ball a r hr p Dp hp M hpBound
      (systemMatrixTestCoefficient E R j) φ Dφ hφ H hφBound
  let B := fun j : Fin q=>(PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin q=>ℝ) j).smulRight
    (ContinuousLinearMap.id ℝ (Ambient (q*q)))
  have hB (j : Fin q) (z : Ambient q) (w : Ambient (q*q)) : B j z w=z j • w := rfl
  have hTBound (j : Fin q) : ∀ᵐx∂μ,‖T j x‖≤‖systemMatrixTestCoefficient E R j‖*|M| * |H| := by
    filter_upwards [hpBound,hφBound] with x hx hφx
    calc
      _≤‖systemMatrixTestCoefficient E R j (p x)‖*‖φ x‖ :=
        (systemMatrixTestCoefficient E R j (p x)).le_opNorm _
      _≤(‖systemMatrixTestCoefficient E R j‖*|M|)*|H| := mul_le_mul
        (((systemMatrixTestCoefficient E R j).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (hx.trans (le_abs_self M)) (norm_nonneg _)))
        (hφx.trans (le_abs_self H)) (norm_nonneg _) (by positivity)
  have hvSub : MemW12 (ballDomain a r) (fun x=>v x-c) Dv :=
    ⟨(memW12Loc_sub_const hv.to_memW12Loc c).1,hv.2.1.sub (memLp_const c),hv.2.2⟩
  have hSubBound : ∀ᵐx∂μ,‖v x-c‖≤|N|+‖c‖ := by
    filter_upwards [hvBound] with x hx
    exact (norm_sub_le _ _).trans (add_le_add (hx.trans (le_abs_self N)) le_rfl)
  have hK (j : Fin q) : HasZeroBoundaryValues (ballDomain a r) (fun x=>(v x-c) j • T j x)
      (fun x i=>(Dv x i) j • T j x+(v x-c) j • DT j x i) := by
    simpa only [hB] using zeroBoundary_bounded_native_bilinear_product_ball a r hr
      (fun x=>v x-c) Dv hvSub (|N|+‖c‖) hSubBound (B j) (T j) (DT j) (hT j)
      (‖systemMatrixTestCoefficient E R j‖*|M| * |H|) (hTBound j)
  have hFirst (j : Fin q) (i : Fin n) : MemLp (fun x=>(Dv x i) j • T j x) 2 μ := by
    have H := (bounded_bilinear_L2_energy μ (B j).flip (T j) (hT j).1.2.1.aestronglyMeasurable
      (hTBound j) (fun x=>Dv x i) (hv.2.2 i)).1
    simpa only [ContinuousLinearMap.flip_apply,hB] using H
  have hSecond (j : Fin q) (i : Fin n) : MemLp (fun x=>(v x-c) j • DT j x i) 2 μ := by
    have H := (bounded_bilinear_L2_energy μ (B j) (fun x=>v x-c) hvSub.2.1.aestronglyMeasurable
      hSubBound (fun x=>DT j x i) ((hT j).1.2.2 i)).1
    simpa only [hB] using H
  have hFirstI (j : Fin q) : Integrable (fun x=>∑i : Fin n,inner ℝ (E (Z x i)) ((Dv x i) j • T j x)) μ :=
    integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hZ i) (hFirst j i))
  have hSecondI (j : Fin q) : Integrable (fun x=>∑i : Fin n,inner ℝ (E (Z x i)) ((v x-c) j • DT j x i)) μ :=
    integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hZ i) (hSecond j i))
  have hSecondPoint (j : Fin q) (x : Domain n) :
      (∑i : Fin n,inner ℝ (E (Z x i)) ((v x-c) j • DT j x i))=
      (v x-c) j*(∑i : Fin n,inner ℝ (E (Z x i)) (DT j x i)) := by
    simp only [real_inner_smul_right,Finset.mul_sum]
  have hCompI (j : Fin q) : Integrable
      (fun x=>(v x-c) j*(∑i : Fin n,inner ℝ (E (Z x i)) (DT j x i))) μ :=
    (hSecondI j).congr (Eventually.of_forall (hSecondPoint j))
  have hEq (j : Fin q) : (∫x,∑i : Fin n,inner ℝ (E (Z x i)) ((Dv x i) j • T j x) ∂μ)=
      -(∫x,(v x-c) j*(∑i : Fin n,inner ℝ (E (Z x i)) (DT j x i)) ∂μ) := by
    have H := (divergence_free_zeroBoundary_test (ballDomain a r)
      (fun x i=>E (Z x i)) hZ hDiv (hK j)).2
    simp only [inner_add_right,Finset.sum_add_distrib] at H
    change (∫x,(∑i : Fin n,inner ℝ (E (Z x i)) ((Dv x i) j • T j x))+
      (∑i : Fin n,inner ℝ (E (Z x i)) ((v x-c) j • DT j x i)) ∂μ)=0 at H
    rw [integral_add (hFirstI j) (hSecondI j)] at H
    simpa only [hSecondPoint] using eq_neg_of_add_eq_zero_left H
  have hPoint (x : Domain n) : inner ℝ (W x) (φ x)=
      ∑j : Fin q,∑i : Fin n,inner ℝ (E (Z x i)) ((Dv x i) j • T j x) := by
    simpa only [T,systemMatrixTestCoefficient_apply,real_inner_smul_right] using
      system_matrix_forcing_finite_pairing E hE (Z x) (R (p x)) (Dv x) (φ x)
  have hWI : Integrable (fun x=>inner ℝ (W x) (φ x)) μ :=
    (integrable_finsetSum _ (fun j _=>hFirstI j)).congr (Eventually.of_forall fun x=>(hPoint x).symm)
  refine ⟨hT,hK,hWI,hCompI,?_⟩
  calc
    _=∫x,∑j : Fin q,∑i : Fin n,inner ℝ (E (Z x i)) ((Dv x i) j • T j x) ∂μ :=
      integral_congr_ae (Eventually.of_forall hPoint)
    _=∑j : Fin q,∫x,∑i : Fin n,inner ℝ (E (Z x i)) ((Dv x i) j • T j x) ∂μ :=
      integral_finsetSum _ (fun j _=>hFirstI j)
    _=∑j : Fin q,-(∫x,(v x-c) j*(∑i : Fin n,inner ℝ (E (Z x i)) (DT j x i)) ∂μ) :=
      Finset.sum_congr rfl fun j _=>hEq j
    _=_ := by rw [Finset.sum_neg_distrib]

end StationaryHarmonicMaps.Analysis

end
