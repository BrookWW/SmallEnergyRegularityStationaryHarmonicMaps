module

public import StationaryHarmonicMaps.Analysis.NormalOneFormMean
public import HarmonicMaps.Analysis.SobolevSmoothDensity
public import HolderToCK.Analysis.L2PairingContinuity

/-!
# Actual integration by parts for the normal smooth core

Zero normal contraction gives a true divergence identity against every
ambient smooth test. Whole-ball native graph density extends the same
identity to all native Sobolev tests with arbitrary boundary values.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The actual normal condition gives integration by parts against every ambient smooth vector test, without a support restriction. -/
theorem smooth_normal_oneForm_integration_by_parts {n q : ℕ}
    (A : Fin n → Domain n → Ambient q) (hA : ∀ i,ContDiff ℝ ∞ (A i))
    (hNormal : ∀ x : Domain n,‖x‖=1 → (∑ i : Fin n,x i • A i x)=0)
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ) :
    let d := fun x : Domain n=>∑ i : Fin n,fderiv ℝ (A i) x (EuclideanSpace.single i 1)
    IntegrableOn (fun x=>∑ i : Fin n,inner ℝ (A i x) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))
      (ball (0 : Domain n) 1) volume ∧
      IntegrableOn (fun x=>inner ℝ (d x) (ψ x)) (ball (0 : Domain n) 1) volume ∧
      (∫ x in ball (0 : Domain n) 1,∑ i : Fin n,inner ℝ (A i x) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        -(∫ x in ball (0 : Domain n) 1,inner ℝ (d x) (ψ x)) := by
  intro d
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let V := fun x : Domain n=>WithLp.toLp 2 (fun i : Fin n=>inner ℝ (A i x) (ψ x))
  have hV : ContDiff ℝ ∞ V := (contDiff_piLp 2).2 (fun i=>(hA i).inner ℝ hψ)
  have hd : ContDiff ℝ ∞ d := ContDiff.sum (fun i _=>
    ((hA i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hlCont : Continuous (fun x=>∑ i : Fin n,inner ℝ (A i x)
      (fderiv ℝ ψ x (EuclideanSpace.single i 1))) := continuous_finsetSum _ (fun i _=>
    (hA i).continuous.inner (((hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous))
  have hrCont : Continuous (fun x=>inner ℝ (d x) (ψ x)) := hd.continuous.inner hψ.continuous
  have hlI : Integrable (fun x=>∑ i : Fin n,inner ℝ (A i x)
      (fderiv ℝ ψ x (EuclideanSpace.single i 1))) μ :=
    (hlCont.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Domain n) 1)).mono_set ball_subset_closedBall
  have hrI : Integrable (fun x=>inner ℝ (d x) (ψ x)) μ :=
    (hrCont.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Domain n) 1)).mono_set ball_subset_closedBall
  have hFlux (x : Domain n) (hx : ‖x‖=1) : inner ℝ x (V x)=0 := by
    have heq : inner ℝ x (V x)=inner ℝ (∑ i : Fin n,x i • A i x) (ψ x) := by
      rw [PiLp.inner_apply]
      simp only [Real.inner_apply,V,sum_inner,real_inner_smul_left]
    rw [heq,hNormal x hx,inner_zero_left]
  have hD (x : Domain n) (i : Fin n) : (fderiv ℝ V x (EuclideanSpace.single i 1)) i =
      inner ℝ (A i x) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) +
        inner ℝ (fderiv ℝ (A i) x (EuclideanSpace.single i 1)) (ψ x) := by
    let πi := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n=>ℝ) i
    have heq : (fun y=>inner ℝ (A i y) (ψ y))=πi ∘ V := rfl
    have H := congrArg (fun L : Domain n →L[ℝ] ℝ=>L (EuclideanSpace.single i 1))
      (((hA i).differentiable (by simp) x).hasFDerivAt.inner ℝ
        (hψ.differentiable (by simp) x).hasFDerivAt).fderiv
    rw [heq,fderiv_comp x πi.differentiableAt (hV.differentiable (by simp) x),πi.fderiv] at H
    simpa only [ContinuousLinearMap.comp_apply,πi,PiLp.proj_apply,
      ContinuousLinearMap.prod_apply,fderivInnerCLM_apply] using H
  have hDiv (x : Domain n) : (∑ i : Fin n,(fderiv ℝ V x (EuclideanSpace.single i 1)) i) =
      (∑ i : Fin n,inner ℝ (A i x) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) + inner ℝ (d x) (ψ x) := by
    simp only [hD,Finset.sum_add_distrib,d,sum_inner]
  have H := (unitBall_integral_divergence_eq_zero V (hV.of_le (by simp)) hFlux).2
  rw [integral_congr_ae (Eventually.of_forall hDiv)] at H
  have hh : (∫ x,∑ i : Fin n,inner ℝ (A i x) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) ∂μ) +
      (∫ x,inner ℝ (d x) (ψ x) ∂μ)=0 := by
    rw [← integral_add hlI hrI]
    exact H
  exact ⟨hlI,hrI,eq_neg_of_add_eq_zero_left hh⟩

/-- The original normal smooth core satisfies the genuine boundary integration identity against every native whole-ball Sobolev test. -/
theorem smooth_normal_oneForm_native_integration_by_parts {n q : ℕ}
    (A : Fin n → Domain n → Ambient q) (hA : ∀ i,ContDiff ℝ ∞ (A i))
    (hNormal : ∀ x : Domain n,‖x‖=1 → (∑ i : Fin n,x i • A i x)=0)
    (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
    (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
    let d := fun x : Domain n=>∑ i : Fin n,fderiv ℝ (A i) x (EuclideanSpace.single i 1)
    IntegrableOn (fun x=>∑ i : Fin n,inner ℝ (A i x) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
      IntegrableOn (fun x=>inner ℝ (d x) (ψ x)) (ball (0 : Domain n) 1) volume ∧
      (∫ x in ball (0 : Domain n) 1,∑ i : Fin n,inner ℝ (A i x) (Dψ x i)) =
        -(∫ x in ball (0 : Domain n) 1,inner ℝ (d x) (ψ x)) := by
  intro d
  let μ := volume.restrict (ball (0 : Domain n) 1)
  have hALp (i : Fin n) : MemLp (A i) 2 μ :=
    (memW12_ball_of_ambient_c1 (0 : Domain n) 1 (A i) ((hA i).of_le (by simp))).2.1
  have hd : ContDiff ℝ ∞ d := ContDiff.sum (fun i _=>
    ((hA i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hdLp : MemLp d 2 μ :=
    (memW12_ball_of_ambient_c1 (0 : Domain n) 1 d (hd.of_le (by simp))).2.1
  have hlI : Integrable (fun x=>∑ i : Fin n,inner ℝ (A i x) (Dψ x i)) μ :=
    integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hALp i) (hψ.2.2 i))
  have hrI : Integrable (fun x=>inner ℝ (d x) (ψ x)) μ :=
    HolderToCK.integrable_inner_of_memLp_two hdLp hψ.2.1
  obtain ⟨f,hf,hfL,hfD,hconv,hDconv⟩ := hψ.smoothDensity_ball (by norm_num : (0:ℝ)<1)
  have hLeftLimit := tendsto_finsetSum Finset.univ (fun i _=>
    HolderToCK.tendsto_integral_inner_of_L2 (fun k=>hfD k i) (hψ.2.2 i) (hALp i) (hDconv i))
  have hRightLimit := HolderToCK.tendsto_integral_inner_of_L2 hfL hψ.2.1 hdLp hconv
  have hSeq (k : ℕ) : (∑ i : Fin n,∫ x,inner ℝ (A i x)
      (coordinateDerivative (f k) (hf k) i x) ∂μ) =
        -(∫ x,inner ℝ (d x) (f k x) ∂μ) := by
    rw [← integral_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hALp i) (hfD k i))]
    exact (smooth_normal_oneForm_integration_by_parts A hA hNormal (f k) (hf k)).2.2
  have hEq := tendsto_nhds_unique hLeftLimit (hRightLimit.neg.congr'
    (Eventually.of_forall fun k=>(hSeq k).symm))
  refine ⟨hlI,hrI,?_⟩
  rw [integral_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hALp i) (hψ.2.2 i))]
  exact hEq

end StationaryHarmonicMaps.Analysis

end
