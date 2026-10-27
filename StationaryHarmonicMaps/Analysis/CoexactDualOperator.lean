/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.ClosedNormalTensorProjection
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The relative coexact projection and its native dual responses

The actual smooth closed normal divergence space determines a single
self-adjoint Hilbert projection. Every output has a native closed normal
two-tensor potential, with coercivity controlled by that same output.
The projection retains the complete L2 pairing against arbitrary raw data.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- One relative coexact L2 operator produces actual native tensor potentials
for all its outputs and preserves the full pairing against raw dual fields. -/
theorem exists_native_coexact_L2_projection_operator_unitBall (n q : ℕ) :
    let μ := volume.restrict (ball (0 : Domain n) 1)
    let E : Gradient n q → Ambient (n*q) := fun A=>WithLp.toLp 2
      (fun k=>A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    let D := fun (V : Domain n → Ambient (n*q)) (x : Domain n) (j : Fin n)=>
      WithLp.toLp 2 (fun a : Fin q=>V x (finProdFinEquiv (j,a)))
    let G : Set (Lp (Ambient (n*q)) 2 μ) := {Z | ∃ B : Fin n → Fin n → Domain n → Ambient q,
      (∀ i j,ContDiff ℝ ∞ (B i j)) ∧
      (∀ i j x,B i j x = -B j i x) ∧
      (∀ i j k x,fderiv ℝ (B i j) x (EuclideanSpace.single k 1)+
        fderiv ℝ (B j k) x (EuclideanSpace.single i 1)+fderiv ℝ (B k i) x (EuclideanSpace.single j 1)=0) ∧
      (∀ j (x : Domain n),‖x‖=1 → (∑ i : Fin n,x i • B i j x)=0) ∧
      (Z : Domain n → Ambient (n*q)) =ᵐ[μ]
        (fun x=>E (fun j=>∑ i : Fin n,fderiv ℝ (B i j) x (EuclideanSpace.single i 1)))}
    ∃ T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
      ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀ V,T (T V)=T V) ∧
      T.range=(Submodule.span ℝ G).topologicalClosure ∧
      (∀ V W : Lp (Ambient (n*q)) 2 μ,Integrable (fun x=>∑ j : Fin n,inner ℝ (D (T V) x j) (D W x j)) μ ∧
        Integrable (fun x=>∑ j : Fin n,inner ℝ (D V x j) (D (T W) x j)) μ ∧
        (∫x,∑ j : Fin n,inner ℝ (D (T V) x j) (D W x j) ∂μ)=
          ∫x,∑ j : Fin n,inner ℝ (D V x j) (D (T W) x j) ∂μ) ∧
      ∀ V : Lp (Ambient (n*q)) 2 μ,
        ∃ (b : Fin n → Fin n → Domain n → Ambient q)
          (Db : Fin n → Fin n → Domain n → Gradient n q),
          (∀ i j,MemW12 (ballDomain (0 : Domain n) 1) (b i j) (Db i j)) ∧
          (∀ᵐ x ∂μ,∀ i j,b i j x = -b j i x) ∧
          (∀ᵐ x ∂μ,∀ i j k,Db i j x k+Db j k x i+Db k i x j=0) ∧
          (∀ᵐ x ∂μ,∀ j,(∑ i : Fin n,Db i j x i)=D (T V) x j) ∧
          (∀ (j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑ i : Fin n,inner ℝ (b i j x) (Dψ x i)) μ ∧
            Integrable (fun x=>inner ℝ (D (T V) x j) (ψ x)) μ ∧
            (∫x,∑ i : Fin n,inner ℝ (b i j x) (Dψ x i) ∂μ)=
              -(∫x,inner ℝ (D (T V) x j) (ψ x) ∂μ)) ∧
          (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑ j : Fin n,inner ℝ (D (T V) x j) (Dψ x j)) μ ∧
            (∫x,∑ j : Fin n,inner ℝ (D (T V) x j) (Dψ x j) ∂μ)=0) ∧
          Integrable (fun x=>∑ j : Fin n,∑ i : Fin n,‖b i j x‖^2) μ ∧
          Integrable (fun x=>∑ j : Fin n,∑ k : Fin n,∑ i : Fin n,‖Db i j x k‖^2) μ ∧
          (∫x,hsNormSq (D (T V) x) ∂μ)≤∫x,hsNormSq (D V x) ∂μ ∧
          (∫x,∑ j : Fin n,∑ i : Fin n,‖b i j x‖^2 ∂μ)+
            (∫x,∑ j : Fin n,∑ k : Fin n,∑ i : Fin n,‖Db i j x k‖^2 ∂μ)≤
              (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)*(∫x,hsNormSq (D (T V) x) ∂μ) := by
  intro μ E D G
  obtain ⟨S,hS⟩ := exists_smooth_closed_normal_divergence_submodule_unitBall n q
  have hSG : (S : Set (Lp (Ambient (n*q)) 2 μ))=G := Set.ext hS
  have hSpan : Submodule.span ℝ G=S := by
    rw [← hSG]
    exact Submodule.span_eq S
  let T := S.topologicalClosure.starProjection
  have hRange : T.range=(Submodule.span ℝ G).topologicalClosure := by
    rw [hSpan]
    exact Submodule.range_starProjection S.topologicalClosure
  have hPair (V W : Lp (Ambient (n*q)) 2 μ) :
      inner ℝ V W=∫x,∑ j : Fin n,inner ℝ (D V x j) (D W x j) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun x=>by
      have hVE : E (D V x)=V x := hs_flatten_unflatten (V x)
      have hWE : E (D W x)=W x := hs_flatten_unflatten (W x)
      change inner ℝ (V x) (W x)=∑ j : Fin n,inner ℝ (D V x j) (D W x j)
      rw [← hVE,← hWE]
      exact hs_flatten_inner (D V x) (D W x)
  have hNorm (V : Lp (Ambient (n*q)) 2 μ) : ‖V‖^2=∫x,hsNormSq (D V x) ∂μ := by
    rw [← real_inner_self_eq_norm_sq,hPair]
    exact integral_congr_ae (Eventually.of_forall fun x=>by
      simp only [hsNormSq,real_inner_self_eq_norm_sq])
  refine ⟨T,S.topologicalClosure.starProjection_norm_le,isSelfAdjoint_starProjection _,?_,hRange,?_,?_⟩
  · intro V
    exact Submodule.starProjection_eq_self_iff.mpr (S.topologicalClosure.starProjection_apply_mem V)
  · intro V W
    have hI (A B : Lp (Ambient (n*q)) 2 μ) :
        Integrable (fun x=>∑ j : Fin n,inner ℝ (D A x j) (D B x j)) μ :=
      integrable_finsetSum _ (fun j _=>HolderToCK.integrable_inner_of_memLp_two
        (memLp_hs_unflatten A (Lp.memLp A) j) (memLp_hs_unflatten B (Lp.memLp B) j))
    refine ⟨hI (T V) W,hI V (T W),?_⟩
    rw [← hPair,← hPair]
    exact S.topologicalClosure.inner_starProjection_left_eq_right V W
  · intro V
    let Z := T V
    have hZmem : Z∈S.topologicalClosure := S.topologicalClosure.starProjection_apply_mem V
    have hSeq : ∃ A : ℕ → Lp (Ambient (n*q)) 2 μ,(∀ s,A s∈S) ∧ Tendsto A atTop (𝓝 Z) := by
      apply mem_closure_iff_seq_limit.mp
      rw [← Submodule.topologicalClosure_coe]
      exact hZmem
    obtain ⟨A,hA,hAConv⟩ := hSeq
    choose B hB hSkew hClosed hNormal hRep using (fun s=>(hS (A s)).mp (hA s))
    have hP (j : Fin n) : MemLp (fun x=>D Z x j) 2 μ := memLp_hs_unflatten Z (Lp.memLp Z) j
    have hEncConv : Tendsto (fun s=>eLpNorm (fun x=>E (fun j=>∑ i : Fin n,
        fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))-Z x) 2 μ) atTop (𝓝 0) := by
      have H := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' A Z).mp hAConv
      apply H.congr
      intro s
      apply eLpNorm_congr_ae
      filter_upwards [hRep s] with x hx
      change A s x-Z x=E (fun j=>∑ i : Fin n,fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))-Z x
      rw [hx]
    have hConv (j : Fin n) : Tendsto (fun s=>eLpNorm (fun x=>(∑ i : Fin n,
        fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))-D Z x j) 2 μ) atTop (𝓝 0) := by
      have H := hs_unflatten_column_l2_limit hEncConv j
      apply H.congr
      intro s
      apply eLpNorm_congr_ae
      exact Eventually.of_forall (fun x=>by
        change (WithLp.toLp 2 (fun a : Fin q=>(E (fun j=>∑ i : Fin n,
          fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))) (finProdFinEquiv (j,a))))-D Z x j =
            (∑ i : Fin n,fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))-D Z x j
        congr 1
        exact congrFun (hs_unflatten_flatten (fun j=>∑ i : Fin n,
          fderiv ℝ (B s i j) x (EuclideanSpace.single i 1))) j)
    obtain ⟨b,Db,hb,hMap,hGrad,hs,hc,hd,hn⟩ :=
      exists_closed_normal_native_tensor_of_divergence_strong_limit B hB hSkew hClosed hNormal (D Z) hP hConv
    obtain ⟨hBI,hDI,_hPI,hCoercive⟩ := closed_normal_tensor_strong_limit_energy_bound
      B hB hSkew hClosed hNormal b Db hb hMap hGrad (D Z) hP hConv
    have hNatural := skew_normal_tensor_divergence_limit_native_tests B hB hSkew hNormal (D Z) hP hConv
    refine ⟨b,Db,hb,hs,hc,hd,hn,hNatural,hBI,hDI,?_,hCoercive⟩
    rw [← hNorm,← hNorm]
    exact pow_le_pow_left₀ (norm_nonneg _) (S.topologicalClosure.norm_starProjection_apply_le V) 2

end StationaryHarmonicMaps.Analysis

end
