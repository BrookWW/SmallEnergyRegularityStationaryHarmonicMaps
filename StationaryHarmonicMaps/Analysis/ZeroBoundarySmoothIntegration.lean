module

public import StationaryHarmonicMaps.Analysis.NormalOneFormIntegration

/-!
# Genuine zero-boundary integration against arbitrary smooth fields

The actual W0 compact smooth graph approximation removes the boundary
flux for each approximant. The divergence identity and actual L2 pairing
continuity therefore give integration by parts for the original graph
against every ambient smooth one-form, without a normal condition on
that one-form or a pointwise trace assumption on the original map.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- A genuine native W0 graph admits the full integration-by-parts identity against every actual ambient smooth one-form, with both integrabilities produced. -/
theorem zeroBoundary_smooth_oneForm_integration_by_parts {n q : ℕ}
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : HasZeroBoundaryValues (ballDomain (0:Domain n) 1) u Du)
    (A : Fin n → Domain n → Ambient q) (hA : ∀i,ContDiff ℝ ∞ (A i)) :
    let d := fun x : Domain n=>∑i : Fin n,fderiv ℝ (A i) x (EuclideanSpace.single i 1)
    IntegrableOn (fun x=>∑i : Fin n,inner ℝ (A i x) (Du x i)) (ball (0:Domain n) 1) volume ∧
      IntegrableOn (fun x=>inner ℝ (d x) (u x)) (ball (0:Domain n) 1) volume ∧
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (A i x) (Du x i))=
        -(∫x in ball (0:Domain n) 1,inner ℝ (d x) (u x)) := by
  intro d
  let μ := volume.restrict (ball (0:Domain n) 1)
  obtain ⟨huW,ψ,hψ,hcψ,hMap,hGrad⟩ := hu
  have hALp (i : Fin n) : MemLp (A i) 2 μ :=
    (memW12_ball_of_ambient_c1 (0:Domain n) 1 (A i) ((hA i).of_le (by simp))).2.1
  have hd : ContDiff ℝ ∞ d := ContDiff.sum (fun i _=>
    ((hA i).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const)
  have hdLp : MemLp d 2 μ :=
    (memW12_ball_of_ambient_c1 (0:Domain n) 1 d (hd.of_le (by simp))).2.1
  have hψLp (k : ℕ) : MemLp (ψ k) 2 μ := (hψ k).continuous.memLp_of_hasCompactSupport (hcψ k).1
  have hDψLp (k : ℕ) (i : Fin n) : MemLp (coordinateDerivative (ψ k) (hψ k) i) 2 μ :=
    (((hψ k).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hcψ k).1.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hLeftI : Integrable (fun x=>∑i : Fin n,inner ℝ (A i x) (Du x i)) μ :=
    integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hALp i) (huW.2.2 i))
  have hRightI : Integrable (fun x=>inner ℝ (d x) (u x)) μ :=
    HolderToCK.integrable_inner_of_memLp_two hdLp huW.2.1
  have hSeq (k : ℕ) :
      (∑i : Fin n,∫x,inner ℝ (A i x) (coordinateDerivative (ψ k) (hψ k) i x) ∂μ)=
        -(∫x,inner ℝ (d x) (ψ k x) ∂μ) := by
    let V := fun x : Domain n=>WithLp.toLp 2 (fun i : Fin n=>inner ℝ (A i x) (ψ k x))
    have hV : ContDiff ℝ ∞ V := (contDiff_piLp 2).2 (fun i=>(hA i).inner ℝ (hψ k))
    have hFlux (x : Domain n) (hx : ‖x‖=1) : inner ℝ x (V x)=0 := by
      have hNot : x∉tsupport (ψ k) := by
        intro h
        have H := (hcψ k).2 h
        change x∈ball (0:Domain n) 1 at H
        rw [mem_ball_zero_iff,hx] at H
        exact (lt_irrefl (1:ℝ)) H
      have hZero : ψ k x=0 := image_eq_zero_of_notMem_tsupport hNot
      simp only [V,hZero,inner_zero_right]
      exact inner_zero_right x
    have hD (x : Domain n) (i : Fin n) : (fderiv ℝ V x (EuclideanSpace.single i 1)) i=
        inner ℝ (A i x) (coordinateDerivative (ψ k) (hψ k) i x)+
          inner ℝ (fderiv ℝ (A i) x (EuclideanSpace.single i 1)) (ψ k x) := by
      let πi := PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin n=>ℝ) i
      have heq : (fun y=>inner ℝ (A i y) (ψ k y))=πi ∘ V := rfl
      have H := congrArg (fun L : Domain n →L[ℝ] ℝ=>L (EuclideanSpace.single i 1))
        (((hA i).differentiable (by simp) x).hasFDerivAt.inner ℝ
          ((hψ k).differentiable (by simp) x).hasFDerivAt).fderiv
      rw [heq,fderiv_comp x πi.differentiableAt (hV.differentiable (by simp) x),πi.fderiv] at H
      simpa only [ContinuousLinearMap.comp_apply,πi,PiLp.proj_apply,
        ContinuousLinearMap.prod_apply,fderivInnerCLM_apply,coordinateDerivative] using H
    have hDiv (x : Domain n) : (∑i : Fin n,(fderiv ℝ V x (EuclideanSpace.single i 1)) i)=
        (∑i : Fin n,inner ℝ (A i x) (coordinateDerivative (ψ k) (hψ k) i x))+inner ℝ (d x) (ψ k x) := by
      simp only [hD,Finset.sum_add_distrib,d,sum_inner]
    have H := (unitBall_integral_divergence_eq_zero V (hV.of_le (by simp)) hFlux).2
    rw [integral_congr_ae (Eventually.of_forall hDiv)] at H
    have hLI : Integrable (fun x=>∑i : Fin n,inner ℝ (A i x) (coordinateDerivative (ψ k) (hψ k) i x)) μ :=
      integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hALp i) (hDψLp k i))
    have hRI : Integrable (fun x=>inner ℝ (d x) (ψ k x)) μ :=
      HolderToCK.integrable_inner_of_memLp_two hdLp (hψLp k)
    rw [integral_add hLI hRI,integral_finsetSum _
      (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hALp i) (hDψLp k i))] at H
    exact eq_neg_of_add_eq_zero_left H
  have hLeftLimit := tendsto_finsetSum Finset.univ (fun i _=>
    HolderToCK.tendsto_integral_inner_of_L2 (fun k=>hDψLp k i) (huW.2.2 i) (hALp i) (hGrad i))
  have hRightLimit := HolderToCK.tendsto_integral_inner_of_L2 hψLp huW.2.1 hdLp hMap
  have hEq := tendsto_nhds_unique hLeftLimit (hRightLimit.neg.congr'
    (Eventually.of_forall fun k=>(hSeq k).symm))
  refine ⟨hLeftI,hRightI,?_⟩
  rw [integral_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hALp i) (huW.2.2 i))]
  exact hEq

end StationaryHarmonicMaps.Analysis

end
