module

public import StationaryHarmonicMaps.Analysis.SameNeumannDensitySplit
public import StationaryHarmonicMaps.Analysis.RealDensityGoodLambda

/-!
# Actual good-lambda estimate for the Neumann gradient projection

One fixed L2 operator produces the original weak Neumann response and
all near/far responses. Its actual raw-field factory supplies the real
density decomposition used in the full-scale maximal estimate.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The same genuine Neumann projection, fixed before the raw field, satisfies a dimension-only full-scale good-lambda estimate; the original native potential and weak PDE are retained. -/
theorem exists_neumann_operator_goodLambda_unitBall (n : ℕ) (hn : 2≤n) :
    ∃A D : ℝ,1<A ∧ 0<D ∧ ∀q : ℕ,
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
          let f := fun x=>hsNormSq (Q₀ x)
          let k := fun x=>hsNormSq (F₀ x)
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
            Integrable k volume ∧ Integrable f volume ∧ (∫x,f x)≤∫x,k x ∧
            ∀(L δ : ℝ),0<L → 0≤δ → δ≤1 →
              volume {x | ENNReal.ofReal (A*L)<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x ∧
                dyadicBallMaximal (fun y=>ENNReal.ofReal (k y)) x≤ENNReal.ofReal (δ*L)}≤
              ENNReal.ofReal (D*δ)*volume {x | ENNReal.ofReal L<dyadicBallMaximal (fun y=>ENNReal.ofReal (f y)) x} := by
  obtain ⟨C,hC,HT⟩ := exists_same_neumann_operator_near_far_density_split n hn
  obtain ⟨A,D,hA,hD,Hgood⟩ := exists_real_density_goodLambda_constants n (by omega) C hC
  refine ⟨A,D,hA,hD,?_⟩
  intro q μ E Z
  obtain ⟨T,hT,hSelf,hIdem,Hresponse⟩ := HT q
  refine ⟨T,hT,hSelf,hIdem,?_⟩
  intro F hF V Q F₀ Q₀ f k
  obtain ⟨u,hu,hNat,hEq,hF₀,hQ₀,hk,hf,hEnergy,Hsplit⟩ := Hresponse F hF
  refine ⟨u,hu,hNat,hEq,hF₀,hQ₀,hk,hf,hEnergy,?_⟩
  apply Hgood f k hf hk (fun x=>hsNormSq_nonneg (Q₀ x)) (fun x=>hsNormSq_nonneg (F₀ x))
  intro a R hR
  obtain ⟨_hN,_hFar,hg,hh,_hAE,hDensity,hNear,_hFarZero,hFarBound⟩ := Hsplit a R hR
  exact ⟨_,_,hg,hh,(fun x=>hsNormSq_nonneg _),(fun x=>hsNormSq_nonneg _),hDensity,hNear,hFarBound⟩

end StationaryHarmonicMaps.Analysis

end
