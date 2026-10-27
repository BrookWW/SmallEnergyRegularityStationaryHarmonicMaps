module

public import StationaryHarmonicMaps.Analysis.DirichletOperatorGoodLambda
public import StationaryHarmonicMaps.Analysis.MaximalGoodLambdaMoment

/-!
# Original higher moments of one actual Dirichlet operator

One genuine Dirichlet L2 operator precedes all original fields and every
higher exponent. Its actual near/far construction produces good-lambda
levels internally. Finite-cap absorption and original-value domination
then give true higher HS moments of the same literal decoded response.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- One actual Dirichlet projection preserves every finite input HS-square moment of order greater than one; no output moment or level certificate is a premise. -/

@[expose] noncomputable def dirichletDensityMomentConstant (n : ℕ) (s : ℝ) : ℝ :=
  effectiveUniformGoodLambdaMomentConstant n (n+1)
    (dirichletGoodLambdaAmplitude n) (densityGoodLambdaTailFactor n) s

@[expose] def dirichletFixedHighMomentMajorant (n : ℕ) : ℕ :=
  uniformGoodLambdaMomentMajorant n (n+1)
    (dirichletGoodLambdaAmplitude n) (densityGoodLambdaTailFactor n)

theorem exists_dirichlet_operator_all_high_moments_unitBall_explicit (n : ℕ) (hn : 2≤n) :
    ∃ C : {s : ℝ //1<s} → ℝ,(∀s,0<C s) ∧ C = (fun s => dirichletDensityMomentConstant n s.val) ∧ ∀q : ℕ,
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
            HasZeroBoundaryValues (ballDomain (0:Domain n) 1) u Q ∧
            HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1) (fun x i=>Q x i-F x i) (fun _=>0) ∧
            (∀i,MemLp (fun x=>F₀ x i) 2 volume) ∧ (∀i,MemLp (fun x=>Q₀ x i) 2 volume) ∧
            (∫x,hsNormSq (Q₀ x))≤∫x,hsNormSq (F₀ x) ∧
            ∀s : {s : ℝ //1<s},(∫⁻x,(ENNReal.ofReal (hsNormSq (F₀ x)))^s.val)<∞ →
              (∫⁻x,(ENNReal.ofReal (hsNormSq (Q₀ x)))^s.val)≤
                ENNReal.ofReal (C s)*(∫⁻x,(ENNReal.ofReal (hsNormSq (F₀ x)))^s.val) ∧
              (∫⁻x,(ENNReal.ofReal (hsNormSq (Q₀ x)))^s.val)<∞ := by
  classical
  obtain ⟨A,D,hA,hD,hAFormula,hDFormula,HT⟩ := exists_dirichlet_operator_goodLambda_unitBall_explicit n hn
  have hANat : 1 ≤ (dirichletGoodLambdaAmplitude n : ℝ) := by rw [← hAFormula]; exact hA.le
  have hDNat : 0 < (densityGoodLambdaTailFactor n : ℝ) := by rw [← hDFormula]; exact hD
  let C : {s : ℝ // 1<s} → ℝ := fun s => dirichletDensityMomentConstant n s.val
  have hC (s : {s : ℝ //1<s}) : 0 < C s :=
    effectiveUniformGoodLambdaMomentConstant_pos n (n+1)
      (dirichletGoodLambdaAmplitude n) (densityGoodLambdaTailFactor n) s.val
      (Nat.succ_pos n) s.property hANat hDNat
  refine ⟨C,hC,rfl,?_⟩
  intro q μ E Z
  obtain ⟨T,hT,hSelf,hIdem,Hresponse⟩ := HT q
  refine ⟨T,hT,hSelf,hIdem,?_⟩
  intro F hF V Q F₀ Q₀
  obtain ⟨u,hu,hEquation,hF₀,hQ₀,hFI,hQI,hEnergy,hGood⟩ := Hresponse F hF
  refine ⟨u,hu,hEquation,hF₀,hQ₀,hEnergy,?_⟩
  intro s hMoment
  apply effective_uniform_maximal_goodLambda_moment_bound n (n+1)
    (dirichletGoodLambdaAmplitude n) (densityGoodLambdaTailFactor n) s.val
    s.property hANat hDNat (fun x=>hsNormSq (Q₀ x)) (fun x=>hsNormSq (F₀ x)) hQI hFI
    (Eventually.of_forall fun x=>hsNormSq_nonneg (Q₀ x))
    (Eventually.of_forall fun x=>hsNormSq_nonneg (F₀ x)) hMoment
  intro δ hδ hδOne L hL
  rw [hAFormula,hDFormula] at hGood
  exact hGood L δ hL hδ.le hδOne

theorem exists_dirichlet_operator_all_high_moments_unitBall (n : ℕ) (hn : 2≤n) :
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
            HasZeroBoundaryValues (ballDomain (0:Domain n) 1) u Q ∧
            HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1) (fun x i=>Q x i-F x i) (fun _=>0) ∧
            (∀i,MemLp (fun x=>F₀ x i) 2 volume) ∧ (∀i,MemLp (fun x=>Q₀ x i) 2 volume) ∧
            (∫x,hsNormSq (Q₀ x))≤∫x,hsNormSq (F₀ x) ∧
            ∀s : {s : ℝ //1<s},(∫⁻x,(ENNReal.ofReal (hsNormSq (F₀ x)))^s.val)<∞ →
              (∫⁻x,(ENNReal.ofReal (hsNormSq (Q₀ x)))^s.val)≤
                ENNReal.ofReal (C s)*(∫⁻x,(ENNReal.ofReal (hsNormSq (F₀ x)))^s.val) ∧
              (∫⁻x,(ENNReal.ofReal (hsNormSq (Q₀ x)))^s.val)<∞ := by
  obtain ⟨C,hC,_hFormula,H⟩ := exists_dirichlet_operator_all_high_moments_unitBall_explicit n hn
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end
