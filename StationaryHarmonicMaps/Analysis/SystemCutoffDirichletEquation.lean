module

public import StationaryHarmonicMaps.Analysis.OrthogonalFrameCutoff
public import StationaryHarmonicMaps.Analysis.HodgeDirichletUniqueness
public import HolderToCK.Analysis.WeakPoissonLocality

/-!
# The actual Dirichlet projection of the original matrix cutoff flux

The original native map equation and bounded orthogonal frame produce
literal cutoff flux, matrix connection, ordered forcing and all four
cutoff error terms. On every compactly contained positive-radius ball,
the original L2 Dirichlet gradient projection has the same signed weak
Poisson equation, with genuine L1 forcing and all native W0 tests.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The original frame-cutoff data construct the actual L2 Dirichlet
projection and its genuine equation `Δf=e-W` on each interior query.
No cutoff-flux equation or component forcing equation is an input. -/
theorem exists_system_cutoff_dirichlet_equation {n m q : ℕ} (hn : 1≤n)
    {Ω : OpenDomain n} {p : Domain n → Ambient m} {Dp : Domain n → Gradient n m}
    (hp : MemW12Loc Ω p Dp) {M : ℝ}
    (hb : ∀ᵐx∂volume.restrict Ω.val,‖p x‖≤M)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hOrth : ∀ᵐx∂volume.restrict Ω.val,star (R (p x))*R (p x)=1)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc Ω u Du)
    (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q))
    (hA : ∀i,LocallyMemL2 Ω (fun x=>A x i))
    (hEq : HolderToCK.WeakPoissonOn Ω Du (fun x=>-(∑i : Fin n,A x i (Du x i))))
    (c : Ambient q) (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ⊆Ω.val) :
    let v := fun x=>χ x • (u x-c)
    let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
    let Fv := fun x i=>star (R (p x)) (Dv x i)
    let Z := fun x i=>star (R (p x))*R (Dp x i)+star (R (p x))*A x i*R (p x)
    let W := fun x=>∑i : Fin n,Z x i (star (R (p x)) (Dv x i))
    let e := fun x=>
      (∑i : Fin n,fderiv ℝ χ x (EuclideanSpace.single i 1) • star (R (Dp x i)) (u x-c))+
      (2:ℝ) • (∑i : Fin n,fderiv ℝ χ x (EuclideanSpace.single i 1) • star (R (p x)) (Du x i))+
      Laplacian.laplacian χ x • star (R (p x)) (u x-c)+
      ∑i : Fin n,fderiv ℝ χ x (EuclideanSpace.single i 1) • Z x i (star (R (p x)) (u x-c))
    MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv ∧
    LocallyIntegrableOn W Ω.val volume ∧ LocallyIntegrableOn e Ω.val volume ∧
    HolderToCK.WeakPoissonOn Ω Fv (fun x=>e x-W x) ∧
    ∀(a : Domain n) (r : ℝ),0<r → closedBall a r⊆Ω.val →
      (∀i,MemLp (fun x=>Fv x i) 2 (volume.restrict (ball a r))) ∧
      IntegrableOn W (ball a r) volume ∧ IntegrableOn e (ball a r) volume ∧
      ∃(f : Domain n → Ambient q) (Df : Domain n → Gradient n q),
        HasZeroBoundaryValues (ballDomain a r) f Df ∧
        HolderToCK.WeakPoissonOn (ballDomain a r) Df (fun x=>e x-W x) ∧
        (∫x in ball a r,hsNormSq (Df x))≤∫x in ball a r,hsNormSq (Fv x) ∧
        ∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          HasZeroBoundaryValues (ballDomain a r) ψ Dψ →
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Df x i) (Dψ x i)) (ball a r) volume ∧
          IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Fv x i) (Dψ x i)) (ball a r) volume ∧
          (∫x in ball a r,∑i : Fin n,inner ℝ (Df x i) (Dψ x i))=
            ∫x in ball a r,∑i : Fin n,inner ℝ (Fv x i) (Dψ x i) := by
  intro v Dv Fv Z W e
  obtain ⟨hV,hELocal,hCutTests⟩ := weak_orthogonal_frame_cutoff hp hb R hOrth hu A hA hEq c χ hχ hcχ hsχ
  have hVLocal : MemW12Loc Ω v Dv :=
    (memW12_cutoff_sub_const hu c χ hχ hcχ hsχ).to_memW12Loc
  have hFLocal (i : Fin n) : LocallyMemL2 Ω (fun x=>Fv x i) :=
    locallyMemL2_operator_flux hp hb R hVLocal i
  have hZLocal (i : Fin n) : LocallyMemL2 Ω (fun x=>Z x i) :=
    locallyMemL2_frame_connection hp hb R A hA i
  have hWLocal : LocallyIntegrableOn W Ω.val volume :=
    locallyIntegrableOn_operator_contraction Z hZLocal Fv hFLocal
  have hRaw : HolderToCK.WeakPoissonOn Ω Fv (fun x=>e x-W x) := by
    refine ⟨hELocal.sub hWLocal,?_⟩
    intro ψ hψ hc hs
    obtain ⟨hFI,hWI,hEI,hIdentity⟩ := hCutTests ψ hψ hc hs
    refine ⟨hFI,?_,?_⟩
    · simp only [inner_sub_left]
      change IntegrableOn (fun x=>inner ℝ (e x) (ψ x)) Ω.val volume at hEI
      change IntegrableOn (fun x=>inner ℝ (W x) (ψ x)) Ω.val volume at hWI
      exact hEI.sub hWI
    · simp only [inner_sub_left]
      rw [integral_sub hEI hWI]
      linarith only [hIdentity]
  refine ⟨hV,hWLocal,hELocal,hRaw,?_⟩
  intro a r hr hClosed
  have hSub : ball a r⊆Ω.val := ball_subset_closedBall.trans hClosed
  have hF (i : Fin n) : MemLp (fun x=>Fv x i) 2 (volume.restrict (ball a r)) :=
    (hFLocal i (closedBall a r) (isCompact_closedBall a r) hClosed).mono_measure
      (Measure.restrict_mono_set volume ball_subset_closedBall)
  have hWI : IntegrableOn W (ball a r) volume :=
    (hWLocal.integrableOn_compact_subset hClosed (isCompact_closedBall a r)).mono_set ball_subset_closedBall
  have hEI : IntegrableOn e (ball a r) volume :=
    (hELocal.integrableOn_compact_subset hClosed (isCompact_closedBall a r)).mono_set ball_subset_closedBall
  obtain ⟨f,Df,hf,hEnergy,hSmooth⟩ := exists_dirichlet_gradient_projection hn a hr Fv hF
  have hQuery : HolderToCK.WeakPoissonOn (ballDomain a r) Fv (fun x=>e x-W x) := hRaw.mono hSub
  have hDfEquation : HolderToCK.WeakPoissonOn (ballDomain a r) Df (fun x=>e x-W x) := by
    refine ⟨hQuery.1,?_⟩
    intro ψ hψ hc hs
    obtain ⟨hDfI,_hFI,hProjection⟩ := hSmooth ψ hψ hc hs
    obtain ⟨_hRawI,hForcingI,hRawEquation⟩ := hQuery.2 ψ hψ hc hs
    exact ⟨hDfI,hForcingI,hProjection.trans hRawEquation⟩
  refine ⟨hF,hWI,hEI,f,Df,hf,hDfEquation,hEnergy,?_⟩
  intro ψ Dψ hψ
  exact gradient_pairing_eq_on_zeroBoundary_of_smooth (ballDomain a r) Df Fv hf.1.2.2 hF
    (fun φ hφ hc hs=>(hSmooth φ hφ hc hs).2.2) hψ

end StationaryHarmonicMaps.Analysis

end
