module

public import StationaryHarmonicMaps.Analysis.CoexactNeumannIdentity
public import HarmonicMaps.Analysis.SobolevAECongruence

/-!
# One actual native Neumann L2 projection

The complement of the relative coexact projection is contractive,
self-adjoint and idempotent. Its original decoded output is the explicit
gradient of a mean-zero native potential and satisfies every native
Neumann test against the same original raw field.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- A single contractive self-adjoint Neumann projection produces the same native response and all unrestricted-boundary tests for every raw L2 input. -/
theorem exists_native_neumann_L2_projection_operator_unitBall {n q : ℕ} (hn : 1≤n) :
    let μ := volume.restrict (ball (0 : Domain n) 1)
    let E : Gradient n q → Ambient (n*q) := fun G=>WithLp.toLp 2
      (fun k=>G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    ∃ N : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
      ‖N‖≤1 ∧ IsSelfAdjoint N ∧ (∀V,N (N V)=N V) ∧
      ∀ (F : Domain n → Gradient n q) (hF : ∀j,MemLp (fun x=>F x j) 2 μ),
        let V := (memLp_hs_flatten F hF).toLp (fun x=>E (F x))
        let Q := fun x j=>WithLp.toLp 2 (fun a : Fin q=>(N V) x (finProdFinEquiv (j,a)))
        ∃f : Domain n → Ambient q,MemW12 (ballDomain (0 : Domain n) 1) f Q ∧
          (∫x,f x ∂μ)=0 ∧ (∫x,hsNormSq (Q x) ∂μ)≤∫x,hsNormSq (F x) ∂μ ∧
          ∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑j : Fin n,inner ℝ (Q x j) (Dψ x j)) μ ∧
            Integrable (fun x=>∑j : Fin n,inner ℝ (F x j) (Dψ x j)) μ ∧
            (∫x,∑j : Fin n,inner ℝ (Q x j) (Dψ x j) ∂μ)=
              ∫x,∑j : Fin n,inner ℝ (F x j) (Dψ x j) ∂μ := by
  intro μ E
  let D := fun (V : Domain n → Ambient (n*q)) x j=>WithLp.toLp 2
    (fun a : Fin q=>V x (finProdFinEquiv (j,a)))
  obtain ⟨T,_hNorm,hSelf,hIdem,_hRange,_hPair,_hTensor,hNative⟩ :=
    exists_coexact_projection_with_neumann_complement_unitBall (q := q) hn
  let N : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ := 1-T
  have hNApply (V : Lp (Ambient (n*q)) 2 μ) : N V=V-T V := rfl
  have hAdj : T.adjoint=T := by simpa only [IsSelfAdjoint,ContinuousLinearMap.star_eq_adjoint] using hSelf
  have hNPoint (V : Lp (Ambient (n*q)) 2 μ) : ‖N V‖≤‖V‖ := by
    have H := ContinuousLinearMap.adjoint_inner_right T V (T V)
    rw [hAdj,hIdem,real_inner_self_eq_norm_sq] at H
    have hSquare : ‖N V‖^2≤‖V‖^2 := by
      rw [hNApply,norm_sub_sq_real,H]
      nlinarith only [sq_nonneg ‖T V‖]
    nlinarith only [hSquare,norm_nonneg (N V),norm_nonneg V]
  have hNormN : ‖N‖≤1 := N.opNorm_le_bound (by norm_num) fun V=>by simpa only [one_mul] using hNPoint V
  have hSelfN : IsSelfAdjoint N := by
    change star (1-T)=1-T
    rw [star_sub,star_one]
    exact congrArg (fun z=>1-z) hSelf
  have hIdemN (V : Lp (Ambient (n*q)) 2 μ) : N (N V)=N V := by
    simp only [hNApply,map_sub,hIdem,sub_self,sub_zero]
  have hNorm (V : Lp (Ambient (n*q)) 2 μ) : ‖V‖^2=∫x,hsNormSq (D V x) ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall fun x=>by
      change inner ℝ (V x) (V x)=hsNormSq (D V x)
      rw [real_inner_self_eq_norm_sq]
      exact (hs_unflatten_hsNormSq (V x)).symm
  refine ⟨N,hNormN,hSelfN,hIdemN,?_⟩
  intro F hF V Q
  have hV : (V : Domain n → Ambient (n*q))=ᵐ[μ](fun x=>E (F x)) := (memLp_hs_flatten F hF).coeFn_toLp
  have hDV : D V=ᵐ[μ]F := by
    filter_upwards [hV] with x hx
    change (fun j=>WithLp.toLp 2 (fun a : Fin q=>V x (finProdFinEquiv (j,a))))=F x
    rw [hx]
    exact hs_unflatten_flatten (F x)
  have hQ : Q=ᵐ[μ](fun x j=>D V x j-D (T V) x j) := by
    filter_upwards [Lp.coeFn_sub V (T V)] with x hx
    funext j
    change WithLp.toLp 2 (fun a : Fin q=>(N V) x (finProdFinEquiv (j,a)))=D V x j-D (T V) x j
    rw [hNApply]
    ext a
    have H := congrArg (fun z : Ambient (n*q)=>z (finProdFinEquiv (j,a))) hx
    simpa only [Pi.sub_apply,PiLp.sub_apply] using H
  obtain ⟨f,hf,hMean,hTests,_hUnique⟩ := hNative V
  have hfQ : MemW12 (ballDomain (0 : Domain n) 1) f Q :=
    hf.congr_ae (Eventually.of_forall fun _=>rfl) hQ.symm
  have hEnergy : (∫x,hsNormSq (Q x) ∂μ)≤∫x,hsNormSq (F x) ∂μ := by
    calc
      _=‖N V‖^2 := (hNorm (N V)).symm
      _≤‖V‖^2 := pow_le_pow_left₀ (norm_nonneg _) (hNPoint V) 2
      _=∫x,hsNormSq (D V x) ∂μ := hNorm V
      _=_ := integral_congr_ae (hDV.mono fun x hx=>congrArg hsNormSq hx)
  refine ⟨f,hfQ,hMean,hEnergy,?_⟩
  intro ψ Dψ hψ
  obtain ⟨hI,hEq⟩ := hTests ψ Dψ hψ
  have hLeft : (fun x=>∑j : Fin n,inner ℝ (D V x j-D (T V) x j) (Dψ x j))=ᵐ[μ]
      (fun x=>∑j : Fin n,inner ℝ (Q x j) (Dψ x j)) := by
    filter_upwards [hQ] with x hx
    simp only [hx]
  have hRight : (fun x=>∑j : Fin n,inner ℝ (D V x j) (Dψ x j))=ᵐ[μ]
      (fun x=>∑j : Fin n,inner ℝ (F x j) (Dψ x j)) := by
    filter_upwards [hDV] with x hx
    rw [hx]
  have hFI := integrable_finsetSum Finset.univ fun j _=>HolderToCK.integrable_inner_of_memLp_two (hF j) (hψ.2.2 j)
  exact ⟨hI.congr hLeft,hFI,(integral_congr_ae hLeft).symm.trans (hEq.trans (integral_congr_ae hRight))⟩

end StationaryHarmonicMaps.Analysis

end
