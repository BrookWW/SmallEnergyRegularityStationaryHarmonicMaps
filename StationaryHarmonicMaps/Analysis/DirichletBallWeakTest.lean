module

public import StationaryHarmonicMaps.Analysis.BoundedDirichletBallDualTest
public import StationaryHarmonicMaps.Analysis.WeakPoissonBoundedTest

/-!
# Genuine weak-equation testing on arbitrary balls

The same bounded native dual test on the original ball is constructed before any forcing or
error field. Every original weak flux equation with actual L2 error and
L1 forcing then admits this test, with both pairings integrable and the
signed original power-pairing identity proved from that equation.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The actual bounded dual test admits every original L2-error/L1-forcing weak equation, with genuine pairing integrabilities and the original signed power identity. -/
theorem exists_bounded_dirichlet_dual_weak_test_ball (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1<p) (hpTwo : p<2) (hDual : (n:ℝ)<p/(p-1)) :
    ∃C K : ℝ,0<C ∧ 0<K ∧ ∀(q : ℕ) (a : Domain n) (R : ℝ),0<R →
      let μ := volume.restrict (ball a R)
      let r := p/(p-1)
      ∀(u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
        HasZeroBoundaryValues (ballDomain a R) u Du →
        ∃(φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
          HasZeroBoundaryValues (ballDomain a R) φ Dφ ∧
          MemLp (fun x=>WithLp.toLp 2 (fun k : Fin (n*q)=>
            Dφ x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) (ENNReal.ofReal r) μ ∧
          MemLp φ ⊤ μ ∧
          (∀ᵐx∂μ,‖φ x‖≤K*R^(1-(n:ℝ)/r)*(∫y,(hsNormSq (Du y))^(p/2) ∂μ)^(1/r)) ∧
          Integrable (fun x=>(hsNormSq (Du x))^(p/2)) μ ∧
          Integrable (fun x=>(hsNormSq (Dφ x))^(r/2)) μ ∧
          (∫x,(hsNormSq (Dφ x))^(r/2) ∂μ)≤C*(∫x,(hsNormSq (Du x))^(p/2) ∂μ) ∧
          ∀(E : Domain n → Gradient n q) (F : Domain n → Ambient q),
            (∀i,MemLp (fun x=>E x i) 2 μ) → Integrable F μ →
            HolderToCK.WeakPoissonOn (ballDomain a R) (fun x i=>Du x i-E x i) F →
            Integrable (fun x=>∑i : Fin n,inner ℝ (E x i) (Dφ x i)) μ ∧
            Integrable (fun x=>inner ℝ (F x) (φ x)) μ ∧
            (∫x,(hsNormSq (Du x))^(p/2) ∂μ)=
              (∫x,∑i : Fin n,inner ℝ (E x i) (Dφ x i) ∂μ)-(∫x,inner ℝ (F x) (φ x) ∂μ) := by
  obtain ⟨C,K,hC,hK,Hdual⟩ := exists_bounded_native_dirichlet_dual_test_ball n hn p hpOne hpTwo hDual
  refine ⟨C,K,hC,hK,?_⟩
  intro q a R hR μ r u Du hu
  obtain ⟨φ,Dφ,hφ,hLp,_hColumns,hInfinity,hSup,hPairI,hInputI,hOutputI,hPair,hMoment⟩ := Hdual q a R hR u Du hu
  refine ⟨φ,Dφ,hφ,hLp,hInfinity,hSup,hInputI,hOutputI,hMoment,?_⟩
  intro E F hE hF hEquation
  have hFlux (i : Fin n) : MemLp (fun x=>Du x i-E x i) 2 μ := (hu.1.2.2 i).sub (hE i)
  have hEI : Integrable (fun x=>∑i : Fin n,inner ℝ (E x i) (Dφ x i)) μ :=
    integrable_finsetSum Finset.univ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hE i) (hφ.1.2.2 i))
  obtain ⟨_hFluxPairI,hFI,hTest⟩ := weakPoissonOn_bounded_zeroBoundary_test hEquation hFlux hF hφ hSup
  refine ⟨hEI,hFI,?_⟩
  simp only [inner_sub_left,Finset.sum_sub_distrib] at hTest
  change (∫x,(∑i : Fin n,inner ℝ (Du x i) (Dφ x i))-(∑i : Fin n,inner ℝ (E x i) (Dφ x i)) ∂μ)=
    -(∫x,inner ℝ (F x) (φ x) ∂μ) at hTest
  rw [integral_sub hPairI hEI,hPair] at hTest
  linarith only [hTest]

theorem exists_bounded_dirichlet_dual_weak_test_ball_fixed_explicit (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1<p) (hpTwo : p<2) (hDual : (n:ℝ)<p/(p-1))
    (hConjugate : p/(p-1)=((2*n+1 : ℕ) : ℝ)) :
    ∃C K : ℝ,0<C ∧ 0<K ∧ C = (dirichletFixedHighMomentMajorant n : ℝ) ∧
      K = (boundedDirichletFixedTestMajorant n : ℝ) ∧ ∀(q : ℕ) (a : Domain n) (R : ℝ),0<R →
      let μ := volume.restrict (ball a R)
      let r := p/(p-1)
      ∀(u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
        HasZeroBoundaryValues (ballDomain a R) u Du →
        ∃(φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
          HasZeroBoundaryValues (ballDomain a R) φ Dφ ∧
          MemLp (fun x=>WithLp.toLp 2 (fun k : Fin (n*q)=>
            Dφ x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) (ENNReal.ofReal r) μ ∧
          MemLp φ ⊤ μ ∧
          (∀ᵐx∂μ,‖φ x‖≤K*R^(1-(n:ℝ)/r)*(∫y,(hsNormSq (Du y))^(p/2) ∂μ)^(1/r)) ∧
          Integrable (fun x=>(hsNormSq (Du x))^(p/2)) μ ∧
          Integrable (fun x=>(hsNormSq (Dφ x))^(r/2)) μ ∧
          (∫x,(hsNormSq (Dφ x))^(r/2) ∂μ)≤C*(∫x,(hsNormSq (Du x))^(p/2) ∂μ) ∧
          ∀(E : Domain n → Gradient n q) (F : Domain n → Ambient q),
            (∀i,MemLp (fun x=>E x i) 2 μ) → Integrable F μ →
            HolderToCK.WeakPoissonOn (ballDomain a R) (fun x i=>Du x i-E x i) F →
            Integrable (fun x=>∑i : Fin n,inner ℝ (E x i) (Dφ x i)) μ ∧
            Integrable (fun x=>inner ℝ (F x) (φ x)) μ ∧
            (∫x,(hsNormSq (Du x))^(p/2) ∂μ)=
              (∫x,∑i : Fin n,inner ℝ (E x i) (Dφ x i) ∂μ)-(∫x,inner ℝ (F x) (φ x) ∂μ) := by
  obtain ⟨C,K,hC,hK,hCF,hKF,Hdual⟩ := exists_bounded_native_dirichlet_dual_test_ball_fixed_explicit n hn p hpOne hpTwo hDual hConjugate
  refine ⟨C,K,hC,hK,hCF,hKF,?_⟩
  intro q a R hR μ r u Du hu
  obtain ⟨φ,Dφ,hφ,hLp,_hColumns,hInfinity,hSup,hPairI,hInputI,hOutputI,hPair,hMoment⟩ := Hdual q a R hR u Du hu
  refine ⟨φ,Dφ,hφ,hLp,hInfinity,hSup,hInputI,hOutputI,hMoment,?_⟩
  intro E F hE hF hEquation
  have hFlux (i : Fin n) : MemLp (fun x=>Du x i-E x i) 2 μ := (hu.1.2.2 i).sub (hE i)
  have hEI : Integrable (fun x=>∑i : Fin n,inner ℝ (E x i) (Dφ x i)) μ :=
    integrable_finsetSum Finset.univ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hE i) (hφ.1.2.2 i))
  obtain ⟨_hFluxPairI,hFI,hTest⟩ := weakPoissonOn_bounded_zeroBoundary_test hEquation hFlux hF hφ hSup
  refine ⟨hEI,hFI,?_⟩
  simp only [inner_sub_left,Finset.sum_sub_distrib] at hTest
  change (∫x,(∑i : Fin n,inner ℝ (Du x i) (Dφ x i))-(∑i : Fin n,inner ℝ (E x i) (Dφ x i)) ∂μ)=
    -(∫x,inner ℝ (F x) (φ x) ∂μ) at hTest
  rw [integral_sub hPairI hEI,hPair] at hTest
  linarith only [hTest]

end StationaryHarmonicMaps.Analysis

end
