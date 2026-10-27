/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.BoundaryCompensatedBilinear
public import StationaryHarmonicMaps.Analysis.BoundedBilinearWeakL2
public import StationaryHarmonicMaps.Analysis.NeumannGradientProjection

/-!
# Constant modes of an actual natural bilinear coefficient

A bounded right coefficient gives the true full-HS L2 product estimate.
The original unrestricted native natural tests annihilate every constant
right mode. Ordinary centered and uncentered forcing pairings therefore
agree for every actual native Neumann test.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- A bounded original right coefficient gives genuine L2 columns and
its dimension-independent full-HS bilinear energy bound. -/
theorem bilinear_hs_energy_of_bounded_right {X : Type*} [MeasurableSpace X]
    {n m k q : ℕ} (μ : Measure X)
    (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q))
    (u : X → Ambient k) (hu : AEStronglyMeasurable u μ) (M : ℝ)
    (hBound : ∀ᵐx∂μ,‖u x‖≤M)
    (Z : X → Gradient n m) (hZ : ∀i,MemLp (fun x=>Z x i) 2 μ) :
    (∀i,MemLp (fun x=>B (Z x i) (u x)) 2 μ) ∧
      (∫x,hsNormSq (fun i=>B (Z x i) (u x)) ∂μ)≤
        (‖B‖*|M|)^2*(∫x,hsNormSq (Z x) ∂μ) := by
  have hColumn (i : Fin n) := bounded_bilinear_L2_energy μ B.flip u hu hBound
    (fun x=>Z x i) (hZ i)
  have hF (i : Fin n) : MemLp (fun x=>B (Z x i) (u x)) 2 μ := by
    simpa only [ContinuousLinearMap.flip_apply] using (hColumn i).1
  refine ⟨hF,?_⟩
  change (∫x,∑i : Fin n,‖B (Z x i) (u x)‖^2 ∂μ)≤
    (‖B‖*|M|)^2*(∫x,∑i : Fin n,‖Z x i‖^2 ∂μ)
  rw [integral_finsetSum _ (fun i _=>(hF i).integrable_norm_pow (by decide : (2 : ℕ)≠0)),
    integral_finsetSum _ (fun i _=>(hZ i).integrable_norm_pow (by decide : (2 : ℕ)≠0)),
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _=>by
    simpa only [ContinuousLinearMap.flip_apply,ContinuousLinearMap.opNorm_flip] using (hColumn i).2)

/-- A true centered L2 forcing and the original L2 coefficient produce
the uncentered original forcing without a bound on its constant mode. -/
theorem bilinear_raw_memLp_of_centered_unitBall {n m k q : ℕ}
    (Z : Domain n → Gradient n m)
    (hZ : ∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q))
    (u : Domain n → Ambient k) (c : Ambient k)
    (hCentered : ∀i,MemLp (fun x=>B (Z x i) (u x-c)) 2
      (volume.restrict (ball (0 : Domain n) 1))) :
    ∀i,MemLp (fun x=>B (Z x i) (u x)) 2 (volume.restrict (ball (0 : Domain n) 1)) := by
  intro i
  have hConstant : MemLp (fun x=>B (Z x i) c) 2 (volume.restrict (ball (0 : Domain n) 1)) := by
    have H : MemLp (fun x=>(B.flip c) (Z x i)) 2 (volume.restrict (ball (0 : Domain n) 1)) :=
      (B.flip c).lipschitz.comp_memLp (map_zero (B.flip c)) (hZ i)
    simpa only [ContinuousLinearMap.flip_apply] using H
  apply ((hCentered i).add hConstant).ae_eq
  exact Eventually.of_forall fun x=>by
    change B (Z x i) (u x-c)+B (Z x i) c=B (Z x i) (u x)
    rw [←map_add,sub_add_cancel]

/-- The original full native natural condition removes every actual
constant right mode from all genuine Neumann forcing pairings. -/
theorem natural_coefficient_centered_pairing_unitBall {n m k q : ℕ}
    (Z : Domain n → Gradient n m)
    (hZ : ∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hNatural : ∀(ψ : Domain n → Ambient m) (Dψ : Domain n → Gradient n m),
      MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
      (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0)
    (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q))
    (u : Domain n → Ambient k)
    (hRaw : ∀i,MemLp (fun x=>B (Z x i) (u x)) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (c : Ambient k) :
    (∀i,MemLp (fun x=>B (Z x i) (u x-c)) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
      ∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i))
          (ball (0 : Domain n) 1) volume ∧
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (B (Z x i) (u x-c)) (Dψ x i))
          (ball (0 : Domain n) 1) volume ∧
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (u x-c)) (Dψ x i))=
          ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i) := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  have hConstant (i : Fin n) : MemLp (fun x=>B (Z x i) c) 2 μ := by
    have H : MemLp (fun x=>(B.flip c) (Z x i)) 2 (volume.restrict (ball (0 : Domain n) 1)) :=
      (B.flip c).lipschitz.comp_memLp (map_zero (B.flip c)) (hZ i)
    simpa only [ContinuousLinearMap.flip_apply] using H
  have hCentered (i : Fin n) : MemLp (fun x=>B (Z x i) (u x-c)) 2 μ := by
    apply ((hRaw i).sub (hConstant i)).ae_eq
    exact Eventually.of_forall fun x=>(map_sub (B (Z x i)) (u x) c).symm
  refine ⟨hCentered,?_⟩
  intro ψ Dψ hψ
  have hRawI := integrable_column_pairing μ (fun x i=>B (Z x i) (u x)) Dψ hRaw hψ.2.2
  have hConstantI := integrable_column_pairing μ (fun x i=>B (Z x i) c) Dψ hConstant hψ.2.2
  have hCenteredI := integrable_column_pairing μ (fun x i=>B (Z x i) (u x-c)) Dψ hCentered hψ.2.2
  have hConstantZero : (∫x in ball (0 : Domain n) 1,
      ∑i : Fin n,inner ℝ (B (Z x i) c) (Dψ x i))=0 := by
    simpa only [ContinuousLinearMap.flip_apply] using
      natural_solenoidal_comp_clm_unitBall Z hNatural (B.flip c) ψ Dψ hψ
  have hPoint (x : Domain n) :
      (∑i : Fin n,inner ℝ (B (Z x i) (u x-c)) (Dψ x i))=
      (∑i : Fin n,inner ℝ (B (Z x i) (u x)) (Dψ x i))-
        (∑i : Fin n,inner ℝ (B (Z x i) c) (Dψ x i)) := by
    simp only [map_sub,inner_sub_left,Finset.sum_sub_distrib]
  refine ⟨hRawI,hCenteredI,?_⟩
  rw [integral_congr_ae (Eventually.of_forall hPoint),integral_sub hRawI hConstantI,
    hConstantZero,sub_zero]

end StationaryHarmonicMaps.Analysis

end
