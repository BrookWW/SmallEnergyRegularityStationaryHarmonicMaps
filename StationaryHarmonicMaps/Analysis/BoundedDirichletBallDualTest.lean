module

public import StationaryHarmonicMaps.Analysis.DirichletBallDualTest
public import StationaryHarmonicMaps.Analysis.NativeSupercriticalTestBound

/-!
# Bounded native dual tests on arbitrary balls

The same actual native dual test is essentially bounded when its conjugate
exponent exceeds the physical dimension. The bound retains the exact
radius power and the original full-HS input moment.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem sqrt_hs_rpow {n q : ℕ} (A : Gradient n q) (s : ℝ) :
    (Real.sqrt (hsNormSq A))^s=(hsNormSq A)^(s/2) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul (hsNormSq_nonneg A)]
  congr 1
  ring

/-- Original native W0 data on every positive-radius ball produce the same exact dual test, with its genuine supercritical essential bound and all original pairings and moments. -/
@[expose] def boundedDirichletFixedTestMajorant (n : ℕ) : ℕ :=
  nativeZeroBoundaryFixedSupercriticalMajorant n * (1+dirichletFixedHighMomentMajorant n)

theorem exists_bounded_native_dirichlet_dual_test_ball_explicit (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1<p) (hpTwo : p<2) (hDual : (n:ℝ)<p/(p-1)) :
    ∃C K : ℝ,0<C ∧ 0<K ∧
      C = dirichletLpMomentConstant n (p/(p-1)) ∧
      K = nativeZeroBoundarySupercriticalConstant n (p/(p-1)) *
        (dirichletLpMomentConstant n (p/(p-1)))^(1/(p/(p-1))) ∧ ∀(q : ℕ) (a : Domain n) (R : ℝ),0<R →
      let μ := volume.restrict (ball a R)
      let r := p/(p-1)
      ∀(u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
        HasZeroBoundaryValues (ballDomain a R) u Du →
        ∃(φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
          HasZeroBoundaryValues (ballDomain a R) φ Dφ ∧
          MemLp (fun x=>WithLp.toLp 2 (fun k : Fin (n*q)=>
            Dφ x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) (ENNReal.ofReal r) μ ∧
          (∀i,MemLp (fun x=>Dφ x i) (ENNReal.ofReal r) μ) ∧
          MemLp φ ⊤ μ ∧
          (∀ᵐx∂μ,‖φ x‖≤K*R^(1-(n:ℝ)/r)*(∫y,(hsNormSq (Du y))^(p/2) ∂μ)^(1/r)) ∧
          Integrable (fun x=>∑i : Fin n,inner ℝ (Du x i) (Dφ x i)) μ ∧
          Integrable (fun x=>(hsNormSq (Du x))^(p/2)) μ ∧
          Integrable (fun x=>(hsNormSq (Dφ x))^(r/2)) μ ∧
          (∫x,∑i : Fin n,inner ℝ (Du x i) (Dφ x i) ∂μ)=∫x,(hsNormSq (Du x))^(p/2) ∂μ ∧
          (∫x,(hsNormSq (Dφ x))^(r/2) ∂μ)≤C*(∫x,(hsNormSq (Du x))^(p/2) ∂μ) := by
  have hpm : 0<p-1 := by linarith only [hpOne]
  have hr : 0<p/(p-1) := div_pos (zero_lt_one.trans hpOne) hpm
  obtain ⟨C,hC,hCFormula,Hdual⟩ := exists_native_dirichlet_dual_test_ball_explicit n hn p hpOne hpTwo
  obtain ⟨S,hS,hSFormula,Hsup⟩ := exists_native_zeroBoundary_supercritical_bound_explicit n hn (p/(p-1)) hDual
  let K := S*C^(1/(p/(p-1)))
  have hK : 0<K := mul_pos hS (Real.rpow_pos_of_pos hC _)
  refine ⟨C,K,hC,hK,hCFormula,?_,?_⟩
  · dsimp only [K]
    rw [hCFormula,hSFormula]
  intro q a R hR μ r u Du hu
  obtain ⟨φ,Dφ,hφ,hLp,hPairI,hInputI,hOutputI,hPair,hMoment⟩ := Hdual q a R hR u Du hu
  let E := fun (A : Gradient n q)=>WithLp.toLp 2
    (fun k : Fin (n*q)=>A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  have hColumns (i : Fin n) : MemLp (fun x=>Dφ x i) (ENNReal.ofReal r) μ := by
    have H := memLp_hs_unflatten_exponent (fun x=>E (Dφ x)) (ENNReal.ofReal r) hLp i
    exact H.ae_eq (Eventually.of_forall fun x=>congrFun (hs_unflatten_flatten (Dφ x)) i)
  obtain ⟨_hOriginalI,hSup,hInfinity⟩ := Hsup q a R φ Dφ hR hφ hColumns
  let B := ∫y,(hsNormSq (Du y))^(p/2) ∂μ
  let J := ∫y,(Real.sqrt (hsNormSq (Dφ y)))^r ∂μ
  have hB : 0≤B := integral_nonneg fun y=>Real.rpow_nonneg (hsNormSq_nonneg _) _
  have hJ : 0≤J := integral_nonneg fun y=>Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hJBound : J≤C*B := by simpa only [J,B,sqrt_hs_rpow] using hMoment
  have hSup' : ∀ᵐx∂μ,‖φ x‖≤S*R^(1-(n:ℝ)/r)*J^(1/r) := hSup
  refine ⟨φ,Dφ,hφ,hLp,hColumns,hInfinity,?_,hPairI,hInputI,hOutputI,hPair,hMoment⟩
  filter_upwards [hSup'] with x hx
  calc
    _≤S*R^(1-(n:ℝ)/r)*J^(1/r) := hx
    _≤S*R^(1-(n:ℝ)/r)*(C*B)^(1/r) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hJ hJBound (one_div_nonneg.mpr hr.le))
      (mul_nonneg hS.le (Real.rpow_nonneg hR.le _))
    _=K*R^(1-(n:ℝ)/r)*B^(1/r) := by rw [Real.mul_rpow hC.le hB];dsimp only [K,r];ring

theorem exists_bounded_native_dirichlet_dual_test_ball (n : ℕ) (hn : 2≤n)
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
          (∀i,MemLp (fun x=>Dφ x i) (ENNReal.ofReal r) μ) ∧
          MemLp φ ⊤ μ ∧
          (∀ᵐx∂μ,‖φ x‖≤K*R^(1-(n:ℝ)/r)*(∫y,(hsNormSq (Du y))^(p/2) ∂μ)^(1/r)) ∧
          Integrable (fun x=>∑i : Fin n,inner ℝ (Du x i) (Dφ x i)) μ ∧
          Integrable (fun x=>(hsNormSq (Du x))^(p/2)) μ ∧
          Integrable (fun x=>(hsNormSq (Dφ x))^(r/2)) μ ∧
          (∫x,∑i : Fin n,inner ℝ (Du x i) (Dφ x i) ∂μ)=∫x,(hsNormSq (Du x))^(p/2) ∂μ ∧
          (∫x,(hsNormSq (Dφ x))^(r/2) ∂μ)≤C*(∫x,(hsNormSq (Du x))^(p/2) ∂μ) := by
  obtain ⟨C,K,hC,hK,_hCF,_hKF,H⟩ := exists_bounded_native_dirichlet_dual_test_ball_explicit n hn p hpOne hpTwo hDual
  exact ⟨C,K,hC,hK,H⟩

theorem exists_bounded_native_dirichlet_dual_test_ball_fixed_explicit (n : ℕ) (hn : 2≤n)
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
          (∀i,MemLp (fun x=>Dφ x i) (ENNReal.ofReal r) μ) ∧
          MemLp φ ⊤ μ ∧
          (∀ᵐx∂μ,‖φ x‖≤K*R^(1-(n:ℝ)/r)*(∫y,(hsNormSq (Du y))^(p/2) ∂μ)^(1/r)) ∧
          Integrable (fun x=>∑i : Fin n,inner ℝ (Du x i) (Dφ x i)) μ ∧
          Integrable (fun x=>(hsNormSq (Du x))^(p/2)) μ ∧
          Integrable (fun x=>(hsNormSq (Dφ x))^(r/2)) μ ∧
          (∫x,∑i : Fin n,inner ℝ (Du x i) (Dφ x i) ∂μ)=∫x,(hsNormSq (Du x))^(p/2) ∂μ ∧
          (∫x,(hsNormSq (Dφ x))^(r/2) ∂μ)≤C*(∫x,(hsNormSq (Du x))^(p/2) ∂μ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hConj : p/(p-1)=2*(n : ℝ)+1 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hConjugate
  obtain ⟨C,K,hC,hK,hCF,hKF,H⟩ := exists_bounded_native_dirichlet_dual_test_ball_explicit n hn p hpOne hpTwo hDual
  have hCeq : C = (dirichletFixedHighMomentMajorant n : ℝ) := by
    rw [hCF,hConj]
    exact dirichletLpMomentConstant_fixed n hn
  have hKbound : K ≤ (boundedDirichletFixedTestMajorant n : ℝ) := by
    rw [hKF,hConj,dirichletLpMomentConstant_fixed n hn]
    have hRoot := effective_root_majorant_helper (dirichletFixedHighMomentMajorant n : ℝ)
      (2*(n : ℝ)+1) (Nat.cast_nonneg _) (by linarith only [hnR])
    have hSup := nativeZeroBoundarySupercriticalConstant_fixed_le n hn
    have Hmul := mul_le_mul hSup hRoot (by positivity : 0 ≤
      (dirichletFixedHighMomentMajorant n : ℝ)^(1/(2*(n : ℝ)+1))) (Nat.cast_nonneg _)
    simpa only [boundedDirichletFixedTestMajorant, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using Hmul
  refine ⟨(dirichletFixedHighMomentMajorant n : ℝ),(boundedDirichletFixedTestMajorant n : ℝ),
    hCeq ▸ hC,lt_of_lt_of_le hK hKbound,rfl,rfl,?_⟩
  intro q a R hR μ r u Du hu
  obtain ⟨φ,Dφ,hφ,hLp,hColumns,hInfinity,hSup,hPairI,hInputI,hOutputI,hPair,hMoment⟩ := H q a R hR u Du hu
  refine ⟨φ,Dφ,hφ,hLp,hColumns,hInfinity,?_,hPairI,hInputI,hOutputI,hPair,?_⟩
  · filter_upwards [hSup] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKbound (Real.rpow_nonneg hR.le _))
      (Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (hsNormSq_nonneg _) _) _))
  · simpa only [hCeq] using hMoment

end StationaryHarmonicMaps.Analysis

end
