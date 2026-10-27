module

public import StationaryHarmonicMaps.Analysis.HodgeDirichletOperator
public import StationaryHarmonicMaps.Analysis.NativeHarmonicGradient
public import HolderToCK.Analysis.WeakPoissonLocality

/-!
# Interior off-support bounds for the same Dirichlet operator

One genuine L2 Dirichlet operator is fixed before the raw input. Its literal
coefficient response has an actual native potential. On every contained
ball where the original input vanishes almost everywhere, the same response
is the gradient of a smooth harmonic representative, with an essential
bound and every finite-exponent bound on the half ball. These are interior
estimates; no boundary reflection or Lp operator estimate is asserted.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

private theorem weakPoisson_zero_of_native_response_ball {n q : ℕ}
    (a : Domain n) {R : ℝ} (hR : 0<R) (Q F : Domain n → Gradient n q)
    (hTests : ∀(v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
      HasZeroBoundaryValues (ballDomain a R) v Dv →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dv x i)) (Metric.ball a R) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (F x i) (Dv x i)) (Metric.ball a R) volume ∧
      (∫x in Metric.ball a R,∑i : Fin n,inner ℝ (Q x i) (Dv x i))=
        ∫x in Metric.ball a R,∑i : Fin n,inner ℝ (F x i) (Dv x i)) :
    HolderToCK.WeakPoissonOn (ballDomain a R) (fun x i=>Q x i-F x i) (fun _=>(0:Ambient q)) := by
  refine ⟨locallyIntegrableOn_zero,?_⟩
  intro ψ hψ hcψ hsψ
  let Dψ := fun (x : Domain n) (i : Fin n)=>fderiv ℝ ψ x (EuclideanSpace.single i 1)
  have hψL : MemLp ψ 2 (volume.restrict (Metric.ball a R)) :=
    hψ.continuous.memLp_of_hasCompactSupport hcψ
  have hDψ (i : Fin n) : MemLp (fun x=>Dψ x i) 2 (volume.restrict (Metric.ball a R)) :=
    ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hcψ.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hw : HasZeroBoundaryValues (ballDomain a R) ψ Dψ :=
    (memW12_of_c1 (ballDomain a R) (hψ.of_le (by simp)) hψL hDψ).zeroBoundary_of_compactSupport_ball
      hR hcψ hsψ
  obtain ⟨hQI,hFI,hEq⟩ := hTests ψ Dψ hw
  have hPoint (x : Domain n) :
      (∑i : Fin n,inner ℝ (Q x i-F x i) (Dψ x i))=
        (∑i : Fin n,inner ℝ (Q x i) (Dψ x i))-(∑i : Fin n,inner ℝ (F x i) (Dψ x i)) := by
    simp only [inner_sub_left,Finset.sum_sub_distrib]
  refine ⟨(hQI.sub hFI).congr (Eventually.of_forall fun x=>(hPoint x).symm),?_,?_⟩
  · simp only [inner_zero_left]
    exact integrable_zero _ _ _
  · change (∫x in Metric.ball a R,∑i : Fin n,inner ℝ (Q x i-F x i) (Dψ x i))=
      -(∫x in Metric.ball a R,inner ℝ (0:Ambient q) (ψ x))
    rw [integral_congr_ae (Eventually.of_forall hPoint),integral_sub hQI hFI,hEq,sub_self]
    simp only [inner_zero_left,integral_zero,neg_zero]

/-- The same contractive self-adjoint Dirichlet operator and its literal response have genuine harmonic-gradient bounds on every interior off-support ball. -/
theorem exists_dirichlet_L2_operator_interior_offSupport_bounds_unitBall {n q : ℕ} (hn : 2≤n) :
    let μ := volume.restrict (Metric.ball (0:Domain n) 1)
    let E : Gradient n q → Ambient (n*q) := fun A=>WithLp.toLp 2
      (fun k=>A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    ∃ T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
      ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀Z,T (T Z)=T Z) ∧
      ∀(F : Domain n → Gradient n q) (hF : ∀i,MemLp (fun x=>F x i) 2 μ),
        let A := (memLp_hs_flatten F hF).toLp (fun x=>E (F x))
        let Q := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2
          (fun j : Fin q=>(T A) x (finProdFinEquiv (i,j)))
        ∃ f : Domain n → Ambient q,
          HasZeroBoundaryValues (ballDomain (0:Domain n) 1) f Q ∧
          (∫x,hsNormSq (Q x) ∂μ)≤∫x,hsNormSq (F x) ∂μ ∧
          HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1)
            (fun x i=>Q x i-F x i) (fun _=>(0:Ambient q)) ∧
          ∀(a : Domain n) (R : PositiveRadius),Metric.ball a R.val⊆Metric.ball (0:Domain n) 1 →
            F =ᵐ[volume.restrict (Metric.ball a R.val)] (fun _=>(0:Gradient n q)) →
            ∃ U : Domain n → Ambient q,
              ContDiffOn ℝ ∞ U (Metric.ball a R.val) ∧
              U =ᵐ[volume.restrict (Metric.ball a R.val)] f ∧
              (∀x∈Metric.ball a R.val,Laplacian.laplacian U x=0) ∧
              Q =ᵐ[volume.restrict (Metric.ball a R.val)]
                (fun x i=>fderiv ℝ U x (EuclideanSpace.single i 1)) ∧
              let K := (volume.real (Metric.ball a (R.val/2)))⁻¹*
                (∫x in Metric.ball a R.val,hsNormSq (Q x))
              (∀x∈Metric.ball a (R.val/2),hsNormSq
                (fun i=>fderiv ℝ U x (EuclideanSpace.single i 1))≤K) ∧
              (∀ᵐx∂volume.restrict (Metric.ball a (R.val/2)),hsNormSq (Q x)≤K) ∧
              MemLp (fun x=>Real.sqrt (hsNormSq (Q x))) ⊤
                (volume.restrict (Metric.ball a (R.val/2))) ∧
              ∀p : ℝ,1≤p →
                MemLp (fun x=>Real.sqrt (hsNormSq (Q x))) (ENNReal.ofReal p)
                  (volume.restrict (Metric.ball a (R.val/2))) ∧
                IntegrableOn (fun x=>(Real.sqrt (hsNormSq (Q x)))^p) (Metric.ball a (R.val/2)) volume ∧
                (∫x in Metric.ball a (R.val/2),(Real.sqrt (hsNormSq (Q x)))^p)≤
                  volume.real (Metric.ball a (R.val/2))*(Real.sqrt K)^p := by
  intro μ E
  obtain ⟨T,hNorm,hSelf,hIdem,hResponse⟩ := exists_native_dirichlet_L2_projection_operator_ball
    (q:=q) (by omega : 1≤n) (0:Domain n) (by norm_num : (0:ℝ)<1)
  refine ⟨T,hNorm,hSelf,hIdem,?_⟩
  intro F hF A Q
  obtain ⟨f,hf,hEnergy,hTests⟩ := hResponse F hF
  have hEq := weakPoisson_zero_of_native_response_ball (0:Domain n) (by norm_num : (0:ℝ)<1) Q F hTests
  refine ⟨f,hf,hEnergy,hEq,?_⟩
  intro a R hSub hZero
  have hfLocal : MemW12 (ballDomain a R.val) f Q :=
    ⟨hf.1.1.mono hSub,hf.1.2.1.mono_measure (Measure.restrict_mono_set volume hSub),
      fun i=>(hf.1.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)⟩
  have hQEq : (fun x i=>Q x i-F x i) =ᵐ[volume.restrict (Metric.ball a R.val)] Q := by
    filter_upwards [hZero] with x hx
    funext i
    rw [hx]
    exact sub_zero (Q x i)
  have hHarmonic : HolderToCK.WeakPoissonOn (ballDomain a R.val) Q (fun _=>(0:Ambient q)) :=
    (hEq.mono hSub).congr hQEq (Eventually.of_forall fun _=>rfl)
  obtain ⟨U,hU,hAE,hLap,hGrad,_hDG,hPoint,hBound,hTop,hAll⟩ :=
    exists_smooth_harmonic_representative_with_original_gradient_ball hn a R f Q hfLocal hHarmonic
  exact ⟨U,hU,hAE,hLap,hGrad,hPoint,hBound,hTop,hAll⟩

end StationaryHarmonicMaps.Analysis

end
