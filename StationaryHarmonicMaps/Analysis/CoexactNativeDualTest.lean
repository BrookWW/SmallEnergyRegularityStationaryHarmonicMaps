module

public import StationaryHarmonicMaps.Analysis.CoexactOperatorAllLp
public import StationaryHarmonicMaps.Analysis.DirichletNativeDualTest

/-!
# Actual relative native coexact dual tests

An original natural solenoidal L2 field is fixed by the same relative
coexact projection: testing its native gradient complement with itself
proves this directly. Applying that actual projection to the literal
power-duality field constructs a closed normal H1 tensor with the exact
power pairing and a conjugate Lp estimate for its divergence.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem norm_sq_half_rpow_coexact {E : Type*} [NormedAddCommGroup E]
    (v : E) (p : ℝ) : (‖v‖^2)^(p/2)=‖v‖^p := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg v)]
  congr 1
  ring

/-- The original natural solenoidal field produces an actual relative closed
normal native tensor whose divergence has the conjugate moment and exact
power pairing. No conjugate estimate on the full tensor derivative is assumed. -/
theorem exists_native_coexact_dual_test_unitBall_explicit (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1<p) (hpTwo : p<2) :
    ∃C : ℝ,0<C ∧ C = effectiveCoexactLpMomentConstant n (p/(p-1)) ∧ ∀q : ℕ,
      let μ := volume.restrict (ball (0:Domain n) 1)
      let r := p/(p-1)
      ∀F : Domain n → Gradient n q,
        (∀i,MemLp (fun x=>F x i) 2 μ) →
        (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x,∑i : Fin n,inner ℝ (F x i) (Dψ x i) ∂μ)=0) →
        ∃(c : Fin n → Fin n → Domain n → Ambient q)
          (Dc : Fin n → Fin n → Domain n → Gradient n q) (Q : Domain n → Gradient n q),
          (∀i j,MemW12 (ballDomain (0:Domain n) 1) (c i j) (Dc i j)) ∧
          (∀ᵐx∂μ,∀i j,c i j x= -c j i x) ∧
          (∀ᵐx∂μ,∀i j k,Dc i j x k+Dc j k x i+Dc k i x j=0) ∧
          (∀ᵐx∂μ,∀j,(∑i : Fin n,Dc i j x i)=Q x j) ∧
          (∀(j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (c i j x) (Dψ x i)) μ ∧
            Integrable (fun x=>inner ℝ (Q x j) (ψ x)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (c i j x) (Dψ x i) ∂μ)=-(∫x,inner ℝ (Q x j) (ψ x) ∂μ)) ∧
          (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ)=0) ∧
          ((∫x,∑j : Fin n,∑i : Fin n,‖c i j x‖^2 ∂μ)+
            (∫x,∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Dc i j x k‖^2 ∂μ)≤
              (4*(2 : ℝ)^(n+1)+2*(n : ℝ)+2)*(∫x,hsNormSq (Q x) ∂μ)) ∧
          MemLp (fun x=>WithLp.toLp 2 (fun k : Fin (n*q)=>
            Q x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) (ENNReal.ofReal r) μ ∧
          Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Q x i)) μ ∧
          Integrable (fun x=>(hsNormSq (F x))^(p/2)) μ ∧
          Integrable (fun x=>(hsNormSq (Q x))^(r/2)) μ ∧
          (∫x,∑i : Fin n,inner ℝ (F x i) (Q x i) ∂μ)=∫x,(hsNormSq (F x))^(p/2) ∂μ ∧
          (∫x,(hsNormSq (Q x))^(r/2) ∂μ)≤C*(∫x,(hsNormSq (F x))^(p/2) ∂μ) := by
  have hp0 : 0<p := zero_lt_one.trans hpOne
  have hpm : 0<p-1 := by linarith only [hpOne]
  have hrTwo : 2<p/(p-1) := (lt_div_iff₀ hpm).mpr (by linarith only [hpTwo])
  have hrOne : 1<p/(p-1) := lt_trans (by norm_num) hrTwo
  have hr0 : 0<p/(p-1) := zero_lt_one.trans hrOne
  obtain ⟨Cp,hCp,hCpEq,HT⟩ := exists_same_coexact_operator_all_lp_unitBall_explicit n hn
  refine ⟨Cp ⟨p/(p-1),hrOne⟩,hCp _,?_,?_⟩
  · rw [hCpEq]
  intro q μ r F hF hFNatural
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let E : Gradient n q → Ambient (n*q) := fun G=>WithLp.toLp 2
    (fun k=>G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  let D := fun (P : Domain n → Ambient (n*q)) x i=>WithLp.toLp 2
    (fun j : Fin q=>P x (finProdFinEquiv (i,j)))
  have hFlat : MemLp (fun x=>E (F x)) 2 μ := memLp_hs_flatten F hF
  let W := hFlat.toLp (fun x=>E (F x))
  have hWAE : (W : Domain n → Ambient (n*q)) =ᵐ[μ] (fun x=>E (F x)) := hFlat.coeFn_toLp
  have hDW : D W =ᵐ[μ] F := by
    filter_upwards [hWAE] with x hx
    change (fun i : Fin n=>WithLp.toLp 2 (fun j : Fin q=>W x (finProdFinEquiv (i,j))))=F x
    rw [hx]
    exact hs_unflatten_flatten (F x)
  obtain ⟨T,_hT,hSelf,_hIdem,Hresponse⟩ := HT q
  obtain ⟨u,_b,_Db,hu,_hb,_hSkew,_hClosed,_hDiv,_hNormal,hPNatural,_hH1,_hEnergy,_hCore,_hLp⟩ := Hresponse W
  have hColW (i : Fin n) : MemLp (fun x=>D W x i) 2 μ := memLp_hs_unflatten W (Lp.memLp W) i
  have hColP (i : Fin n) : MemLp (fun x=>D (T W) x i) 2 μ := memLp_hs_unflatten (T W) (Lp.memLp (T W)) i
  have hIF := integrable_finsetSum Finset.univ (fun i _=>
    HolderToCK.integrable_inner_of_memLp_two (hColW i) (hu.2.2 i))
  have hIP := (hPNatural u _ hu).1
  have hWZero : (∫x,∑i : Fin n,inner ℝ (D W x i) (D W x i-D (T W) x i) ∂μ)=0 := by
    calc
      _=(∫x,∑i : Fin n,inner ℝ (F x i) (D W x i-D (T W) x i) ∂μ) := by
        apply integral_congr_ae
        filter_upwards [hDW] with x hx
        rw [hx]
      _=0 := hFNatural u _ hu
  have hZeroEnergy : (∫x,hsNormSq (fun i=>D W x i-D (T W) x i) ∂μ)=0 := by
    simp only [hsNormSq,← real_inner_self_eq_norm_sq,inner_sub_left,Finset.sum_sub_distrib]
    rw [integral_sub hIF hIP,hWZero,(hPNatural u _ hu).2,sub_self]
  have hZeroAE := (integral_eq_zero_iff_of_nonneg
    (fun x=>hsNormSq_nonneg (fun i=>D W x i-D (T W) x i)) hu.integrable_hsNormSq).mp hZeroEnergy
  have hUnique : D (T W)=ᵐ[μ]D W := by
    filter_upwards [hZeroAE] with x hx
    funext i
    symm
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    have H := Finset.single_le_sum (fun j _=>sq_nonneg ‖D W x j-D (T W) x j‖) (Finset.mem_univ i)
    change ‖D W x i-D (T W) x i‖^2≤hsNormSq (fun j=>D W x j-D (T W) x j) at H
    rw [hx] at H
    exact le_antisymm H (sq_nonneg _)
  have hFix : T W=W := by
    apply Lp.ext
    filter_upwards [hUnique] with x hx
    calc
      (T W) x=E (D (T W) x) := (hs_flatten_unflatten ((T W) x)).symm
      _=E (D W x) := congrArg E hx
      _=W x := hs_flatten_unflatten (W x)
  let G := fun x=>‖W x‖^(p-2) • W x
  obtain ⟨hGTwo,hGr⟩ := dual_power_test_memLp μ p hpOne hpTwo W (Lp.memLp W)
  let Y := hGTwo.toLp G
  have hYAE : (Y : Domain n → Ambient (n*q)) =ᵐ[μ] G := hGTwo.coeFn_toLp
  have hYr : MemLp (fun x=>Y x) (ENNReal.ofReal r) μ := hGr.ae_eq hYAE.symm
  obtain ⟨_v,c,Dc,_hv,hc,hSkew,hClosed,hDiv,hNormal,hNatural,hH1,_hEnergy,_hCoreY,Hpφ⟩ := Hresponse Y
  obtain ⟨hTYr,hBound⟩ := Hpφ ⟨r,hrOne⟩ hYr
  have hφLp : MemLp (fun x=>E (D (T Y) x)) (ENNReal.ofReal r) μ := by
    simpa only [E,D,hs_flatten_unflatten] using hTYr
  have hIpair : Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (D (T Y) x i)) μ :=
    integrable_finsetSum Finset.univ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hF i) (memLp_hs_unflatten (T Y) (Lp.memLp (T Y)) i))
  have hWp := memLp_real_of_memL2 (fun x=>W x) hpTwo.le (Lp.memLp W)
  have hIW : Integrable (fun x=>‖W x‖^p) μ := integrable_norm_rpow_of_memLp_real _ hp0.le hWp
  have hIT : Integrable (fun x=>‖(T Y) x‖^r) μ := integrable_norm_rpow_of_memLp_real _ hr0.le hTYr
  have hPower (A : Gradient n q) (t : ℝ) : (hsNormSq A)^(t/2)=‖E A‖^t := by
    rw [← hs_flatten_norm_sq A]
    exact norm_sq_half_rpow_coexact _ t
  have hInputAE : (fun x=>(hsNormSq (F x))^(p/2)) =ᵐ[μ] (fun x=>‖W x‖^p) := by
    filter_upwards [hWAE] with x hx
    rw [hPower,hx]
  have hOutput (x : Domain n) : (hsNormSq (D (T Y) x))^(r/2)=‖(T Y) x‖^r := by
    rw [hPower]
    rw [show E (D (T Y) x)=(T Y) x from hs_flatten_unflatten ((T Y) x)]
  have hYMoment : (∫x,‖Y x‖^r ∂μ)=∫x,‖W x‖^p ∂μ := by
    apply integral_congr_ae
    filter_upwards [hYAE] with x hx
    rw [hx]
    exact (dual_power_vector_identities p hpOne (W x)).2.2
  have hPairY : inner ℝ W Y=∫x,‖W x‖^p ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hYAE] with x hx
    rw [hx]
    exact (dual_power_vector_identities p hpOne (W x)).2.1
  have hPairT : (∫x,∑i : Fin n,inner ℝ (F x i) (D (T Y) x i) ∂μ)=inner ℝ W (T Y) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hWAE] with x hx
    change (∑i : Fin n,inner ℝ (F x i) (D (T Y) x i))=inner ℝ (W x) ((T Y) x)
    rw [hx,← hs_flatten_inner (F x) (D (T Y) x)]
    congr 1
    exact hs_flatten_unflatten ((T Y) x)
  have hSym := hSelf.isSymmetric W Y
  change inner ℝ (T W) Y=inner ℝ W (T Y) at hSym
  rw [hFix] at hSym
  refine ⟨c,Dc,D (T Y),hc,hSkew,hClosed,hDiv,hNormal,hNatural,hH1,hφLp,hIpair,hIW.congr hInputAE.symm,hIT.congr (Eventually.of_forall fun x=>(hOutput x).symm),?_,?_⟩
  · rw [hPairT,← hSym,hPairY]
    exact (integral_congr_ae hInputAE).symm
  · simp_rw [hOutput]
    rw [hYMoment] at hBound
    exact hBound.trans_eq (by rw [integral_congr_ae hInputAE])

theorem exists_native_coexact_dual_test_unitBall (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1<p) (hpTwo : p<2) :
    ∃C : ℝ,0<C ∧ ∀q : ℕ,
      let μ := volume.restrict (ball (0:Domain n) 1)
      let r := p/(p-1)
      ∀F : Domain n → Gradient n q,
        (∀i,MemLp (fun x=>F x i) 2 μ) →
        (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
          (∫x,∑i : Fin n,inner ℝ (F x i) (Dψ x i) ∂μ)=0) →
        ∃(c : Fin n → Fin n → Domain n → Ambient q)
          (Dc : Fin n → Fin n → Domain n → Gradient n q) (Q : Domain n → Gradient n q),
          (∀i j,MemW12 (ballDomain (0:Domain n) 1) (c i j) (Dc i j)) ∧
          (∀ᵐx∂μ,∀i j,c i j x= -c j i x) ∧
          (∀ᵐx∂μ,∀i j k,Dc i j x k+Dc j k x i+Dc k i x j=0) ∧
          (∀ᵐx∂μ,∀j,(∑i : Fin n,Dc i j x i)=Q x j) ∧
          (∀(j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (c i j x) (Dψ x i)) μ ∧
            Integrable (fun x=>inner ℝ (Q x j) (ψ x)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (c i j x) (Dψ x i) ∂μ)=-(∫x,inner ℝ (Q x j) (ψ x) ∂μ)) ∧
          (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ)=0) ∧
          ((∫x,∑j : Fin n,∑i : Fin n,‖c i j x‖^2 ∂μ)+
            (∫x,∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Dc i j x k‖^2 ∂μ)≤
              (4*(2 : ℝ)^(n+1)+2*(n : ℝ)+2)*(∫x,hsNormSq (Q x) ∂μ)) ∧
          MemLp (fun x=>WithLp.toLp 2 (fun k : Fin (n*q)=>
            Q x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) (ENNReal.ofReal r) μ ∧
          Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Q x i)) μ ∧
          Integrable (fun x=>(hsNormSq (F x))^(p/2)) μ ∧
          Integrable (fun x=>(hsNormSq (Q x))^(r/2)) μ ∧
          (∫x,∑i : Fin n,inner ℝ (F x i) (Q x i) ∂μ)=∫x,(hsNormSq (F x))^(p/2) ∂μ ∧
          (∫x,(hsNormSq (Q x))^(r/2) ∂μ)≤C*(∫x,(hsNormSq (F x))^(p/2) ∂μ) := by
  obtain ⟨C,hC,_hCEq,H⟩ := exists_native_coexact_dual_test_unitBall_explicit n hn p hpOne hpTwo
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end
