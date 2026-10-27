module

public import StationaryHarmonicMaps.Analysis.NeumannOperatorGoodLambda
public import StationaryHarmonicMaps.Analysis.MaximalGoodLambdaMoment

/-!
# Original higher moments of one actual Neumann operator

One genuine Neumann L2 operator precedes all original fields and every
higher exponent. Its actual near/far construction produces good-lambda
levels internally. Finite-cap absorption and original-value domination
then give true higher HS moments of the same literal decoded response.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

@[expose] noncomputable def effectiveNeumannDensityMomentConstant (n : ℕ) (s : ℝ) : ℝ :=
  effectiveUniformGoodLambdaMomentConstant n (n+1) (effectiveNeumannGoodLambdaAmplitude n)
    (densityGoodLambdaTailFactor n) s

theorem effectiveNeumannDensityMomentConstant_pos (n : ℕ) (s : ℝ) (hs : 1<s) :
    0 < effectiveNeumannDensityMomentConstant n s :=
  effectiveUniformGoodLambdaMomentConstant_pos n (n+1) _ _ s (by omega) hs
    (effectiveNeumannGoodLambdaAmplitude_one_lt n).le (densityGoodLambdaTailFactor_pos n)

/-- One actual Neumann projection preserves every finite input HS-square moment of order greater than one; no output moment or level certificate is a premise. -/
theorem exists_neumann_operator_all_high_moments_unitBall_explicit (n : ℕ) (hn : 2≤n) :
    ∃ C : {s : ℝ //1<s} → ℝ,(∀s,0<C s) ∧
      C = (fun s => effectiveNeumannDensityMomentConstant n s.val) ∧ ∀q : ℕ,
      let μ := volume.restrict (ball (0:Domain n) 1)
      let E : Gradient n q → Ambient (n*q) := fun G=>WithLp.toLp 2
        (fun k=>G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      let Z := fun (G : Domain n → Gradient n q) x i=>(ball (0:Domain n) 1).indicator (fun y=>G y i) x
      ∃T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
        ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀V,T (T V)=T V) ∧
        ∀(F : Domain n → Gradient n q) (hF : ∀i,MemLp (fun x=>F x i) 2 μ),
          let V := (memLp_hs_flatten F hF).toLp (fun x=>E (F x))
          let Q := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2
            (fun j : Fin q=>(T V) x (finProdFinEquiv (i,j)))
          let F₀ := Z F
          let Q₀ := Z Q
          ∃u : Domain n → Ambient q,
            MemW12 (ballDomain (0:Domain n) 1) u Q ∧
            (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
              MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
              Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ ∧
              Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i)) μ ∧
              (∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ)=
                ∫x,∑i : Fin n,inner ℝ (F x i) (Dψ x i) ∂μ) ∧
            HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1) (fun x i=>Q x i-F x i) (fun _=>0) ∧
            (∀i,MemLp (fun x=>F₀ x i) 2 volume) ∧ (∀i,MemLp (fun x=>Q₀ x i) 2 volume) ∧
            (∫x,hsNormSq (Q₀ x))≤∫x,hsNormSq (F₀ x) ∧
            ∀s : {s : ℝ //1<s},(∫⁻x,(ENNReal.ofReal (hsNormSq (F₀ x)))^s.val)<∞ →
              (∫⁻x,(ENNReal.ofReal (hsNormSq (Q₀ x)))^s.val)≤
                ENNReal.ofReal (C s)*(∫⁻x,(ENNReal.ofReal (hsNormSq (F₀ x)))^s.val) ∧
              (∫⁻x,(ENNReal.ofReal (hsNormSq (Q₀ x)))^s.val)<∞ := by
  classical
  obtain ⟨A,D,_hA,_hD,hAEq,hDEq,HT⟩ := exists_neumann_operator_goodLambda_unitBall_explicit n hn
  rw [hAEq,hDEq] at HT
  let C := fun s : {s : ℝ //1<s} => effectiveNeumannDensityMomentConstant n s.val
  have hC (s : {s : ℝ //1<s}) : 0<C s :=
    effectiveNeumannDensityMomentConstant_pos n s.val s.property
  have H (s : {s : ℝ //1<s}) :=
    effective_uniform_maximal_goodLambda_moment_bound n (n+1)
      (effectiveNeumannGoodLambdaAmplitude n) (densityGoodLambdaTailFactor n)
      s.val s.property (effectiveNeumannGoodLambdaAmplitude_one_lt n).le
      (densityGoodLambdaTailFactor_pos n)
  refine ⟨C,hC,rfl,?_⟩
  intro q μ E Z
  obtain ⟨T,hT,hSelf,hIdem,Hresponse⟩ := HT q
  refine ⟨T,hT,hSelf,hIdem,?_⟩
  intro F hF V Q F₀ Q₀
  obtain ⟨u,hu,hNat,hEquation,hF₀,hQ₀,hFI,hQI,hEnergy,hGood⟩ := Hresponse F hF
  refine ⟨u,hu,hNat,hEquation,hF₀,hQ₀,hEnergy,?_⟩
  intro s hMoment
  apply H s (fun x=>hsNormSq (Q₀ x)) (fun x=>hsNormSq (F₀ x)) hQI hFI
    (Eventually.of_forall fun x=>hsNormSq_nonneg (Q₀ x))
    (Eventually.of_forall fun x=>hsNormSq_nonneg (F₀ x)) hMoment
  intro δ hδ hδOne L hL
  exact hGood L δ hL hδ.le hδOne

theorem exists_neumann_operator_all_high_moments_unitBall (n : ℕ) (hn : 2≤n) :
    ∃ C : {s : ℝ //1<s} → ℝ,(∀s,0<C s) ∧ ∀q : ℕ,
      let μ := volume.restrict (ball (0:Domain n) 1)
      let E : Gradient n q → Ambient (n*q) := fun G=>WithLp.toLp 2
        (fun k=>G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      let Z := fun (G : Domain n → Gradient n q) x i=>(ball (0:Domain n) 1).indicator (fun y=>G y i) x
      ∃T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
        ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀V,T (T V)=T V) ∧
        ∀(F : Domain n → Gradient n q) (hF : ∀i,MemLp (fun x=>F x i) 2 μ),
          let V := (memLp_hs_flatten F hF).toLp (fun x=>E (F x))
          let Q := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2
            (fun j : Fin q=>(T V) x (finProdFinEquiv (i,j)))
          let F₀ := Z F
          let Q₀ := Z Q
          ∃u : Domain n → Ambient q,
            MemW12 (ballDomain (0:Domain n) 1) u Q ∧
            (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
              MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
              Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ ∧
              Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i)) μ ∧
              (∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ)=
                ∫x,∑i : Fin n,inner ℝ (F x i) (Dψ x i) ∂μ) ∧
            HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1) (fun x i=>Q x i-F x i) (fun _=>0) ∧
            (∀i,MemLp (fun x=>F₀ x i) 2 volume) ∧ (∀i,MemLp (fun x=>Q₀ x i) 2 volume) ∧
            (∫x,hsNormSq (Q₀ x))≤∫x,hsNormSq (F₀ x) ∧
            ∀s : {s : ℝ //1<s},(∫⁻x,(ENNReal.ofReal (hsNormSq (F₀ x)))^s.val)<∞ →
              (∫⁻x,(ENNReal.ofReal (hsNormSq (Q₀ x)))^s.val)≤
                ENNReal.ofReal (C s)*(∫⁻x,(ENNReal.ofReal (hsNormSq (F₀ x)))^s.val) ∧
              (∫⁻x,(ENNReal.ofReal (hsNormSq (Q₀ x)))^s.val)<∞ := by
  obtain ⟨C,hC,_hCEq,H⟩ := exists_neumann_operator_all_high_moments_unitBall_explicit n hn
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end
