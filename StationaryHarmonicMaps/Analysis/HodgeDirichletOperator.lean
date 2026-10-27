module

public import StationaryHarmonicMaps.Analysis.HodgeDirichletUniqueness
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The same actual L2 Dirichlet gradient operator

The literal range of original compact smooth gradients determines one
closed Hilbert subspace and one genuine self-adjoint idempotent CLM before
any raw field is chosen. Its actual coefficient response has the original
smooth test identities. On a positive-dimensional ball the same operator
output recovers a native zero-boundary potential and all native tests.
No Lp operator estimate is assumed or asserted.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The literal compact-gradient range gives one genuine contractive self-adjoint L2 projection, with true same-operator responses for every original raw L2 field. -/
theorem exists_compact_gradient_L2_projection_operator {n q : ℕ} (Ω : OpenDomain n) :
    let μ := volume.restrict Ω.val
    let E : Gradient n q → Ambient (n*q) := fun A=>WithLp.toLp 2
      (fun k=>A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    let G : Set (Lp (Ambient (n*q)) 2 μ) := {Z | ∃ψ : Domain n → Ambient q,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ⊆Ω.val ∧
      (Z : Domain n → Ambient (n*q)) =ᵐ[μ]
        (fun x=>E (fun i=>fderiv ℝ ψ x (EuclideanSpace.single i 1)))}
    ∃ T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
      ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀Z,T (T Z)=T Z) ∧
      T.range=(Submodule.span ℝ G).topologicalClosure ∧
      ∀ (F : Domain n → Gradient n q) (hF : ∀i,MemLp (fun x=>F x i) 2 μ),
        let A := (memLp_hs_flatten F hF).toLp (fun x=>E (F x))
        let Q := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2
          (fun j : Fin q=>(T A) x (finProdFinEquiv (i,j)))
        (∀i,MemLp (fun x=>Q x i) 2 μ) ∧
        (∫x,hsNormSq (Q x) ∂μ)≤∫x,hsNormSq (F x) ∂μ ∧
        ∀ (ψ : Domain n → Ambient q),ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ⊆Ω.val →
          Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) μ ∧
          Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) μ ∧
          (∫x,∑i : Fin n,inner ℝ (Q x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) ∂μ)=
            ∫x,∑i : Fin n,inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) ∂μ := by
  intro μ E G
  obtain ⟨S,hS⟩ := exists_smooth_compact_gradient_submodule (q:=q) Ω
  have hSG : (S : Set (Lp (Ambient (n*q)) 2 μ))=G := Set.ext hS
  have hSpan : Submodule.span ℝ G=S := by rw [← hSG];exact Submodule.span_eq S
  let T := S.topologicalClosure.starProjection
  have hRange : T.range=(Submodule.span ℝ G).topologicalClosure := by
    rw [hSpan]
    exact Submodule.range_starProjection S.topologicalClosure
  refine ⟨T,S.topologicalClosure.starProjection_norm_le,isSelfAdjoint_starProjection _,?_,hRange,?_⟩
  · intro Z
    exact Submodule.starProjection_eq_self_iff.mpr (S.topologicalClosure.starProjection_apply_mem Z)
  · intro F hF A Q
    have hA : (A : Domain n → Ambient (n*q)) =ᵐ[μ] (fun x=>E (F x)) :=
      (memLp_hs_flatten F hF).coeFn_toLp
    have hQ (i : Fin n) : MemLp (fun x=>Q x i) 2 μ := memLp_hs_unflatten (T A) (Lp.memLp (T A)) i
    have hNorm (Z : Lp (Ambient (n*q)) 2 μ) : ‖Z‖^2=∫x,‖Z x‖^2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      exact integral_congr_ae (Eventually.of_forall fun x=>real_inner_self_eq_norm_sq (Z x))
    have hANorm : ‖A‖^2=∫x,hsNormSq (F x) ∂μ := by
      rw [hNorm]
      apply integral_congr_ae
      filter_upwards [hA] with x hx
      rw [hx]
      exact hs_flatten_norm_sq (F x)
    have hQEnergy : (∫x,hsNormSq (Q x) ∂μ)≤∫x,hsNormSq (F x) ∂μ := by
      calc
        _ = ‖T A‖^2 := by
          rw [hNorm]
          exact integral_congr_ae (Eventually.of_forall fun x=>hs_unflatten_hsNormSq ((T A) x))
        _ ≤ ‖A‖^2 := pow_le_pow_left₀ (norm_nonneg _) (S.topologicalClosure.norm_starProjection_apply_le A) 2
        _ = _ := hANorm
    refine ⟨hQ,hQEnergy,?_⟩
    intro ψ hψ hc hs
    let Dψ := fun (x : Domain n) (i : Fin n)=>fderiv ℝ ψ x (EuclideanSpace.single i 1)
    have hDψ (i : Fin n) : MemLp (fun x=>Dψ x i) 2 μ :=
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))
    have hEDψ : MemLp (fun x=>E (Dψ x)) 2 μ := memLp_hs_flatten Dψ hDψ
    let Z : Lp (Ambient (n*q)) 2 μ := hEDψ.toLp (fun x=>E (Dψ x))
    have hZ : (Z : Domain n → Ambient (n*q)) =ᵐ[μ] (fun x=>E (Dψ x)) := hEDψ.coeFn_toLp
    have hZS : Z∈S := (hS Z).mpr ⟨ψ,hψ,hc,hs,hZ⟩
    have hOrth := S.topologicalClosure.starProjection_inner_eq_zero A Z
      (S.le_topologicalClosure hZS)
    have hInner : inner ℝ (T A) Z=inner ℝ A Z := by
      change inner ℝ (A-T A) Z=0 at hOrth
      rw [inner_sub_left] at hOrth
      exact (sub_eq_zero.mp hOrth).symm
    have hQI : Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ :=
      integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hQ i) (hDψ i))
    have hFI : Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i)) μ :=
      integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hF i) (hDψ i))
    have hEncQ (x : Domain n) : E (Q x)=(T A) x := hs_flatten_unflatten ((T A) x)
    have hQZ : inner ℝ (T A) Z=∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hZ] with x hx
      rw [hx,← hEncQ x]
      exact hs_flatten_inner (Q x) (Dψ x)
    have hAZ : inner ℝ A Z=∫x,∑i : Fin n,inner ℝ (F x i) (Dψ x i) ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hA,hZ] with x hx hy
      rw [hx,hy]
      exact hs_flatten_inner (F x) (Dψ x)
    exact ⟨hQI,hFI,hQZ.symm.trans (hInner.trans hAZ)⟩

/-- On a positive-dimensional ball, one fixed actual contractive self-adjoint L2 gradient operator produces a genuine native W0 potential and every native W0 test for each raw L2 input. -/
theorem exists_native_dirichlet_L2_projection_operator_ball {n q : ℕ} (hn : 1≤n)
    (a : Domain n) {R : ℝ} (hR : 0<R) :
    let μ := volume.restrict (Metric.ball a R)
    let E : Gradient n q → Ambient (n*q) := fun A=>WithLp.toLp 2
      (fun k=>A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    ∃ T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
      ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀Z,T (T Z)=T Z) ∧
      ∀ (F : Domain n → Gradient n q) (hF : ∀i,MemLp (fun x=>F x i) 2 μ),
        let A := (memLp_hs_flatten F hF).toLp (fun x=>E (F x))
        let Q := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2
          (fun j : Fin q=>(T A) x (finProdFinEquiv (i,j)))
        ∃ f : Domain n → Ambient q,HasZeroBoundaryValues (ballDomain a R) f Q ∧
          (∫x,hsNormSq (Q x) ∂μ)≤∫x,hsNormSq (F x) ∂μ ∧
          ∀ (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
            HasZeroBoundaryValues (ballDomain a R) v Dv →
            Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dv x i)) μ ∧
            Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Dv x i)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (Q x i) (Dv x i) ∂μ)=
              ∫x,∑i : Fin n,inner ℝ (F x i) (Dv x i) ∂μ := by
  intro μ E
  let Ω := ballDomain a R
  obtain ⟨T,hNorm,hSelf,hIdem,hRange,hResponse⟩ :=
    exists_compact_gradient_L2_projection_operator (q:=q) Ω
  refine ⟨T,hNorm,hSelf,hIdem,?_⟩
  intro F hF A Q
  have hPmem : T A∈T.range := ⟨A,rfl⟩
  rw [hRange] at hPmem
  obtain ⟨ψ,hψ,hconv⟩ := exists_smooth_gradient_approximation_of_mem_closedSpan Ω (T A) hPmem
  obtain ⟨f,hf,_hMapLimit⟩ := exists_zeroBoundary_potential_of_encoded_gradient_limit hn a hR ψ
    (fun k=>(hψ k).1) (fun k=>(hψ k).2.1) (fun k=>(hψ k).2.2) (T A) (Lp.memLp (T A)) hconv
  obtain ⟨hQ,hEnergy,hSmooth⟩ := hResponse F hF
  refine ⟨f,hf,hEnergy,?_⟩
  intro v Dv hv
  exact gradient_pairing_eq_on_zeroBoundary_of_smooth Ω Q F hQ hF
    (fun φ hφ hc hs=>(hSmooth φ hφ hc hs).2.2) hv

end StationaryHarmonicMaps.Analysis

end
