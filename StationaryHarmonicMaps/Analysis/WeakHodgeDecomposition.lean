module

public import StationaryHarmonicMaps.Analysis.ClosedNormalTensorProjection
public import StationaryHarmonicMaps.Analysis.ClosedNormalHarmonicRemainder
public import StationaryHarmonicMaps.Analysis.HodgeDirichletPotential
public import HolderToCK.Analysis.WeakPoissonLocality

/-!
# Actual L2 decomposition with a coefficient-harmonic remainder

The raw one-form produces its genuine zero-boundary Dirichlet response and
native closed normal tensor response. Their original residual is locally
solenoidal and each original coefficient has zero distributional Laplacian.
Exterior closedness of the remainder and Lp dual estimates are separate
statements from this L2 construction.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

private theorem zero_weakPoisson_of_gradient_response {n q : ℕ} (Ω : OpenDomain n)
    (G F : Domain n → Gradient n q)
    (hTests : ∀ ψ : Domain n → Ambient q,ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω.val →
      IntegrableOn (fun x=>∑ i : Fin n,inner ℝ (G x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) Ω.val volume ∧
      IntegrableOn (fun x=>∑ i : Fin n,inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) Ω.val volume ∧
      (∫x in Ω.val,∑ i : Fin n,inner ℝ (G x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        ∫x in Ω.val,∑ i : Fin n,inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) :
    HolderToCK.WeakPoissonOn Ω (fun x i=>F x i-G x i) (fun _=>0) := by
  refine ⟨locallyIntegrableOn_zero,?_⟩
  intro ψ hψ hc hs
  obtain ⟨hGI,hFI,hEq⟩ := hTests ψ hψ hc hs
  have hPoint (x : Domain n) : (∑i : Fin n,inner ℝ (F x i-G x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      (∑i : Fin n,inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))-
        ∑i : Fin n,inner ℝ (G x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    simp only [inner_sub_left,Finset.sum_sub_distrib]
  refine ⟨(hFI.sub hGI).congr (Eventually.of_forall (fun x=>(hPoint x).symm)),?_,?_⟩
  · simp only [inner_zero_left]
    exact integrable_zero _ _ _
  · rw [integral_congr_ae (Eventually.of_forall hPoint),integral_sub hFI hGI,← hEq,sub_self]
    simp only [inner_zero_left,integral_zero,neg_zero]

private theorem integral_sub_sub {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g k : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) (hk : Integrable k μ) :
    (∫x,f x-g x-k x ∂μ)=(∫x,f x ∂μ)-(∫x,g x ∂μ)-(∫x,k x ∂μ) := by
  have H1 : (∫x,f x-g x-k x ∂μ)=(∫x,f x-g x ∂μ)-(∫x,k x ∂μ) := by
    simpa only [Pi.sub_apply] using integral_sub (hf.sub hg) hk
  have H2 : (∫x,f x-g x ∂μ)=(∫x,f x ∂μ)-(∫x,g x ∂μ) := by
    simpa only [Pi.sub_apply] using integral_sub hf hg
  exact H1.trans (congrArg (fun t : ℝ=>t-(∫x,k x ∂μ)) H2)

/-- Every original L2 one-form in arbitrary dimension at least two produces a genuine Dirichlet part, native closed normal tensor part and the same coefficient-harmonic residual, with all weak equations and energy bounds derived. -/
theorem exists_L2_closed_normal_decomposition_harmonic_remainder_unitBall {n q : ℕ} (hn : 2 ≤ n)
    (F : Domain n → Gradient n q)
    (hF : ∀ j,MemLp (fun x=>F x j) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    ∃ (f : Domain n → Ambient q) (Df : Domain n → Gradient n q)
      (b : Fin n → Fin n → Domain n → Ambient q)
      (Db : Fin n → Fin n → Domain n → Gradient n q) (P h : Domain n → Gradient n q),
      HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) f Df ∧
      (∀ i j,MemW12 (ballDomain (0 : Domain n) 1) (b i j) (Db i j)) ∧
      (∀ j,MemLp (fun x=>P x j) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ i j,b i j x = -b j i x) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ i j k,Db i j x k+Db j k x i+Db k i x j=0) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ j,(∑ i : Fin n,Db i j x i)=P x j) ∧
      (∀ (j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑ i : Fin n,inner ℝ (b i j x) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
        IntegrableOn (fun x=>inner ℝ (P x j) (ψ x)) (ball (0 : Domain n) 1) volume ∧
        (∫x in ball (0 : Domain n) 1,∑ i : Fin n,inner ℝ (b i j x) (Dψ x i)) =
          -(∫x in ball (0 : Domain n) 1,inner ℝ (P x j) (ψ x))) ∧
      (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        IntegrableOn (fun x=>∑ j : Fin n,inner ℝ (P x j) (Dψ x j)) (ball (0 : Domain n) 1) volume ∧
        (∫x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (P x j) (Dψ x j))=0) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : Domain n) 1),∀ j,
        F x j=Df x j+(∑ i : Fin n,Db i j x i)+h x j) ∧
      (∀ j,MemLp (fun x=>h x j) 2 (volume.restrict (ball (0 : Domain n) 1))) ∧
      HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) h (fun _=>0) ∧
      (∀ (j : Fin n) (ψ : Domain n → Ambient q),ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ ball (0 : Domain n) 1 →
        IntegrableOn (fun x=>inner ℝ (h x j) (Laplacian.laplacian ψ x)) (ball (0 : Domain n) 1) volume ∧
        (∫x in ball (0 : Domain n) 1,inner ℝ (h x j) (Laplacian.laplacian ψ x))=0) ∧
      ((∫x in ball (0 : Domain n) 1,hsNormSq (Df x))≤∫x in ball (0 : Domain n) 1,hsNormSq (F x)) ∧
      ((∫x in ball (0 : Domain n) 1,hsNormSq (P x))≤∫x in ball (0 : Domain n) 1,hsNormSq (F x)) ∧
      ((∫x in ball (0 : Domain n) 1,∑ j : Fin n,∑ i : Fin n,‖b i j x‖^2)+
        (∫x in ball (0 : Domain n) 1,∑ j : Fin n,∑ k : Fin n,∑ i : Fin n,‖Db i j x k‖^2) ≤
        (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)*(∫x in ball (0 : Domain n) 1,hsNormSq (F x))) ∧
      ∀ C : Fin n → Fin n → Domain n → Ambient q,
        (∀ i j,ContDiff ℝ ∞ (C i j)) → (∀ i j x,C i j x = -C j i x) →
        (∀ i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
          fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0) →
        (∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • C i j x)=0) →
        IntegrableOn (fun x=>∑ j : Fin n,inner ℝ (P x j)
          (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1))) (ball (0 : Domain n) 1) volume ∧
        IntegrableOn (fun x=>∑ j : Fin n,inner ℝ (F x j)
          (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1))) (ball (0 : Domain n) 1) volume ∧
        (∫x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (P x j)
          (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1))) =
        ∫x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (F x j)
          (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)) := by
  let Ω := ballDomain (0 : Domain n) 1
  let μ := volume.restrict (ball (0 : Domain n) 1)
  obtain ⟨f,Df,hf,hfEnergy,hfTests⟩ := exists_dirichlet_gradient_projection (by omega : 1≤n)
    (0 : Domain n) (by norm_num : (0:ℝ)<1) F hF
  obtain ⟨b,Db,P,hb,hP,hSkew,hClosed,hDivB,hNormal,hPNatural,_hSelf,hPEnergy,hBEnergy,hPTests⟩ :=
    exists_closed_normal_tensor_projection_unitBall F hF
  let h := fun (x : Domain n) (j : Fin n)=>F x j-Df x j-P x j
  have hHLp (j : Fin n) : MemLp (fun x=>h x j) 2 μ := ((hF j).sub (hf.1.2.2 j)).sub (hP j)
  have hFDf : HolderToCK.WeakPoissonOn Ω (fun x j=>F x j-Df x j) (fun _=>0) :=
    zero_weakPoisson_of_gradient_response Ω Df F hfTests
  have hPDiv : HolderToCK.WeakPoissonOn Ω P (fun _=>0) := by
    refine ⟨locallyIntegrableOn_zero,?_⟩
    intro ψ hψ _hc _hs
    have hW := memW12_ball_of_ambient_c1 (0 : Domain n) 1 ψ (hψ.of_le (by simp))
    obtain ⟨hI,hEq⟩ := hPNatural ψ _ hW
    refine ⟨hI,?_,?_⟩
    · simp only [inner_zero_left]
      exact integrable_zero _ _ _
    · simpa only [Ω,ballDomain,inner_zero_left,integral_zero,neg_zero] using hEq
  have hHDiv : HolderToCK.WeakPoissonOn Ω h (fun _=>0) := by
    have H := hFDf.sub hPDiv
    simpa only [sub_self] using H
  have hHTests (C : Fin n → Fin n → Domain n → Ambient q)
      (hC : ∀ i j,ContDiff ℝ ∞ (C i j)) (hCS : ∀ i j x,C i j x = -C j i x)
      (hCD : ∀ i j k x,fderiv ℝ (C i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (C j k) x (EuclideanSpace.single i 1)+fderiv ℝ (C k i) x (EuclideanSpace.single j 1)=0)
      (hCN : ∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • C i j x)=0) :
      (∫x in ball (0 : Domain n) 1,∑ j : Fin n,inner ℝ (h x j)
        (∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)))=0 := by
    let dC := fun (x : Domain n) (j : Fin n)=>∑ i : Fin n,fderiv ℝ (C i j) x (EuclideanSpace.single i 1)
    obtain ⟨hPI,hFI,hEq⟩ := hPTests C hC hCS hCD hCN
    obtain ⟨hDI,hDZero⟩ := (smooth_skew_normal_tensor_divergence_native_tests C hC hCS hCN).2 f Df hf.1
    have hDPairI : Integrable (fun x=>∑ j : Fin n,inner ℝ (Df x j) (dC x j)) μ :=
      hDI.congr (Eventually.of_forall (fun x=>Finset.sum_congr rfl (fun j _=>real_inner_comm _ _)))
    have hDPairZero : (∫x,∑ j : Fin n,inner ℝ (Df x j) (dC x j) ∂μ)=0 := by
      calc
        _ = ∫x,∑ j : Fin n,inner ℝ (dC x j) (Df x j) ∂μ := integral_congr_ae
          (Eventually.of_forall (fun x=>Finset.sum_congr rfl (fun j _=>real_inner_comm _ _)))
        _ = 0 := hDZero
    have hPoint (x : Domain n) : (∑ j : Fin n,inner ℝ (h x j) (dC x j)) =
        (∑ j : Fin n,inner ℝ (F x j) (dC x j))-(∑ j : Fin n,inner ℝ (Df x j) (dC x j))-
          (∑ j : Fin n,inner ℝ (P x j) (dC x j)) := by
      simp only [h,inner_sub_left,Finset.sum_sub_distrib]
    rw [integral_congr_ae (Eventually.of_forall hPoint)]
    rw [integral_sub_sub μ _ _ _ hFI hDPairI hPI,hDPairZero,sub_zero,← hEq,sub_self]
  have hHarmonic := coefficient_laplacian_pairing_zero_of_closed_normal_tests h hHLp hHDiv hHTests
  have hDecomp : ∀ᵐ x ∂μ,∀j,F x j=Df x j+(∑i : Fin n,Db i j x i)+h x j := by
    filter_upwards [hDivB] with x hx
    intro j
    rw [hx j]
    dsimp only [h]
    abel
  exact ⟨f,Df,b,Db,P,h,hf,hb,hP,hSkew,hClosed,hDivB,hNormal,hPNatural,hDecomp,hHLp,hHDiv,
    hHarmonic,hfEnergy,hPEnergy,hBEnergy,hPTests⟩

end StationaryHarmonicMaps.Analysis

end
