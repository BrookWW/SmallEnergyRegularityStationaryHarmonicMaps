module

public import StationaryHarmonicMaps.Analysis.CoexactNativeDualTest
public import StationaryHarmonicMaps.Analysis.CoexactNativeVariationalPairing
public import StationaryHarmonicMaps.Analysis.AffineHSMoment

/-!
# Actual native coexact power-dual tensors on arbitrary balls

Positive affine pullback preserves natural solenoidality. Pulling the
unit-ball dual tensor back with the inverse length multiplier preserves
its original native normal identity and unscaled divergence. The exact
power pairing and conjugate moment therefore have the same Jacobian.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem memW12_const_smul_native {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (c : ℝ) :
    MemW12 Ω (fun x=>c • u x) (fun x i=>c • Du x i) := by
  have H := memW12Loc_continuousLinearMap hu.to_memW12Loc
    (c • ContinuousLinearMap.id ℝ (Ambient q))
  exact ⟨H.1,hu.2.1.const_smul c,fun i=>(hu.2.2 i).const_smul c⟩

/-- The original natural identity transports under a positive affine ball
map without changing the field's amplitude. -/
theorem natural_solenoidal_affineBall {n q : ℕ}
    (a b : Domain n) {t : ℝ} (ht : 0<t) (R : ℝ)
    (F : Domain n → Gradient n q)
    (hNatural : ∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain a R) ψ Dψ →
      (∫x in ball a R,∑i : Fin n,inner ℝ (F x i) (Dψ x i))=0) :
    ∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain b (R/t)) ψ Dψ →
      (∫x in ball b (R/t),∑i : Fin n,inner ℝ
        (F (a+t • (x-b)) i) (Dψ x i))=0 := by
  intro ψ Dψ hψ
  let Ψ := fun x=>ψ (b+t⁻¹ • (x-a))
  let DΨ := fun x i=>t⁻¹ • Dψ (b+t⁻¹ • (x-a)) i
  have hRadius : R/t/t⁻¹=R := by field_simp
  have hΨ : MemW12 (ballDomain a R) Ψ DΨ := by
    simpa only [hRadius] using hψ.affineBall_pullback a (inv_pos.mpr ht)
  have H := integral_affineBall a b ht R
    (fun x=>∑i : Fin n,inner ℝ (F x i) (DΨ x i))
  rw [hNatural Ψ DΨ hΨ,smul_zero] at H
  have hpnt (x : Domain n) : (∑i : Fin n,inner ℝ
      (F (a+t • (x-b)) i) (DΨ (a+t • (x-b)) i))=
      t⁻¹*(∑i : Fin n,inner ℝ (F (a+t • (x-b)) i) (Dψ x i)) := by
    simp only [DΨ,add_sub_cancel_left,smul_smul,inv_mul_cancel₀ ht.ne',one_smul,
      add_sub_cancel,real_inner_smul_right,Finset.mul_sum]
  simp_rw [hpnt] at H
  rw [integral_const_mul] at H
  exact (mul_eq_zero.mp H).resolve_left (inv_ne_zero ht.ne')

/-- Affine transport of an original native normal tensor identity uses
the inverse length multiplier on the tensor and no amplitude multiplier
on its divergence. All transported integrability is proved. -/
theorem native_normal_tensor_affineBall {n q : ℕ}
    (a b : Domain n) {t : ℝ} (ht : 0<t) (R : ℝ)
    (c : Fin n → Fin n → Domain n → Ambient q)
    (Q : Domain n → Gradient n q)
    (hNormal : ∀(j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain a R) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (c i j x) (Dψ x i)) (ball a R) volume ∧
      IntegrableOn (fun x=>inner ℝ (Q x j) (ψ x)) (ball a R) volume ∧
      (∫x in ball a R,∑i : Fin n,inner ℝ (c i j x) (Dψ x i))=
        -(∫x in ball a R,inner ℝ (Q x j) (ψ x))) :
    ∀(j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain b (R/t)) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ
        (t⁻¹ • c i j (a+t • (x-b))) (Dψ x i)) (ball b (R/t)) volume ∧
      IntegrableOn (fun x=>inner ℝ (Q (a+t • (x-b)) j) (ψ x)) (ball b (R/t)) volume ∧
      (∫x in ball b (R/t),∑i : Fin n,inner ℝ
        (t⁻¹ • c i j (a+t • (x-b))) (Dψ x i))=
        -(∫x in ball b (R/t),inner ℝ (Q (a+t • (x-b)) j) (ψ x)) := by
  intro j ψ Dψ hψ
  let Ψ := fun x=>ψ (b+t⁻¹ • (x-a))
  let DΨ := fun x i=>t⁻¹ • Dψ (b+t⁻¹ • (x-a)) i
  have hRadius : R/t/t⁻¹=R := by field_simp
  have hΨ : MemW12 (ballDomain a R) Ψ DΨ := by
    simpa only [hRadius] using hψ.affineBall_pullback a (inv_pos.mpr ht)
  obtain ⟨hLeft,hRight,hEq⟩ := hNormal j Ψ DΨ hΨ
  have hpntL (x : Domain n) : (∑i : Fin n,inner ℝ
      (c i j (a+t • (x-b))) (DΨ (a+t • (x-b)) i))=
      ∑i : Fin n,inner ℝ (t⁻¹ • c i j (a+t • (x-b))) (Dψ x i) := by
    simp only [DΨ,add_sub_cancel_left,smul_smul,inv_mul_cancel₀ ht.ne',one_smul,
      add_sub_cancel,real_inner_smul_right,real_inner_smul_left]
  have hpntR (x : Domain n) : inner ℝ (Q (a+t • (x-b)) j) (Ψ (a+t • (x-b)))=
      inner ℝ (Q (a+t • (x-b)) j) (ψ x) := by
    simp only [Ψ,add_sub_cancel_left,smul_smul,inv_mul_cancel₀ ht.ne',one_smul,add_sub_cancel]
  have hLI := integrable_affineBall a b ht R hLeft
  have hRI := integrable_affineBall a b ht R hRight
  simp_rw [hpntL] at hLI
  simp_rw [hpntR] at hRI
  refine ⟨hLI,hRI,?_⟩
  have hL := integral_affineBall a b ht R
    (fun x=>∑i : Fin n,inner ℝ (c i j x) (DΨ x i))
  have hR := integral_affineBall a b ht R (fun x=>inner ℝ (Q x j) (Ψ x))
  simp_rw [hpntL] at hL
  simp_rw [hpntR] at hR
  rw [hL,hR,hEq,smul_neg]

/-- Original natural solenoidal L2 data on every positive-radius ball
produce an actual closed normal native coexact tensor with exact power
pairing and a ball-independent conjugate moment constant. -/
theorem exists_native_coexact_dual_test_ball (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1<p) (hpTwo : p<2) :
    ∃C : ℝ,0<C ∧ ∀(q : ℕ) (a : Domain n) (R : ℝ),0<R →
      let μ := volume.restrict (ball a R)
      let r := p/(p-1)
      ∀F : Domain n → Gradient n q,
        (∀i,MemLp (fun x=>F x i) 2 μ) →
        (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain a R) ψ Dψ →
          (∫x,∑i : Fin n,inner ℝ (F x i) (Dψ x i) ∂μ)=0) →
        ∃(c : Fin n → Fin n → Domain n → Ambient q)
          (Dc : Fin n → Fin n → Domain n → Gradient n q)
          (Q : Domain n → Gradient n q),
          (∀i j,MemW12 (ballDomain a R) (c i j) (Dc i j)) ∧
          (∀i,MemLp (fun x=>Q x i) 2 μ) ∧
          (∀ᵐx∂μ,∀i j,c i j x= -c j i x) ∧
          (∀ᵐx∂μ,∀i j k,Dc i j x k+Dc j k x i+Dc k i x j=0) ∧
          (∀ᵐx∂μ,∀j,(∑i : Fin n,Dc i j x i)=Q x j) ∧
          (∀(j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain a R) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (c i j x) (Dψ x i)) μ ∧
            Integrable (fun x=>inner ℝ (Q x j) (ψ x)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (c i j x) (Dψ x i) ∂μ)=
              -(∫x,inner ℝ (Q x j) (ψ x) ∂μ)) ∧
          (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain a R) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ)=0) ∧
          ((∫x,∑j : Fin n,∑i : Fin n,‖c i j x‖^2 ∂μ)+
            R^2*(∫x,∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Dc i j x k‖^2 ∂μ)≤
              (4*(2 : ℝ)^(n+1)+2*(n : ℝ)+2)*R^2*(∫x,hsNormSq (Q x) ∂μ)) ∧
          MemLp (fun x=>WithLp.toLp 2 (fun k : Fin (n*q)=>
            Q x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) (ENNReal.ofReal r) μ ∧
          Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Q x i)) μ ∧
          Integrable (fun x=>(hsNormSq (F x))^(p/2)) μ ∧
          Integrable (fun x=>(hsNormSq (Q x))^(r/2)) μ ∧
          (∫x,∑i : Fin n,inner ℝ (F x i) (Q x i) ∂μ)=
            ∫x,(hsNormSq (F x))^(p/2) ∂μ ∧
          (∫x,(hsNormSq (Q x))^(r/2) ∂μ)≤C*(∫x,(hsNormSq (F x))^(p/2) ∂μ) := by
  obtain ⟨C,hC,Hunit⟩ := exists_native_coexact_dual_test_unitBall n hn p hpOne hpTwo
  refine ⟨C,hC,?_⟩
  intro q a R hR μ r F hF hNatural
  let U := fun x i=>F (a+R • x) i
  have hU (i : Fin n) : MemLp (fun x=>U x i) 2
      (volume.restrict (ball (0:Domain n) 1)) := by
    simpa only [div_self hR.ne',sub_zero] using memLp_affineBall a (0:Domain n) hR R (hF i)
  have hUNatural : ∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (U x i) (Dψ x i))=0 := by
    simpa only [div_self hR.ne',sub_zero,U] using
      natural_solenoidal_affineBall a (0:Domain n) hR R F hNatural
  obtain ⟨b,Db,V,hb,hSkew,hClosed,hDiv,hNormal,hVNatural,hH1,hVr,hPairI,hUI,hVI,hPair,hMoment⟩ :=
    Hunit q U hU hUNatural
  let A := fun x : Domain n=>R⁻¹ • (x-a)
  let c := fun i j x=>R • b i j (A x)
  let Dc := fun i j x k=>Db i j (A x) k
  let Q := fun x i=>V (A x) i
  have hc (i j : Fin n) : MemW12 (ballDomain a R) (c i j) (Dc i j) := by
    have H := memW12_const_smul_native
      ((hb i j).affineBall_pullback a (inv_pos.mpr hR)) R
    simpa only [one_div,inv_inv,zero_add,smul_smul,mul_inv_cancel₀ hR.ne',one_smul,c,Dc,A] using H
  have hSkewBack : ∀ᵐx∂μ,∀i j,c i j x= -c j i x := by
    have H := ae_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 hSkew
    simp only [one_div,inv_inv,zero_add] at H
    filter_upwards [H] with x hx i j
    exact congrArg (fun z : Ambient q=>R • z) (hx i j) |>.trans (smul_neg _ _)
  have hClosedBack : ∀ᵐx∂μ,∀i j k,Dc i j x k+Dc j k x i+Dc k i x j=0 := by
    simpa only [one_div,inv_inv,zero_add,Dc,A] using
      ae_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 hClosed
  have hDivBack : ∀ᵐx∂μ,∀j,(∑i : Fin n,Dc i j x i)=Q x j := by
    simpa only [one_div,inv_inv,zero_add,Dc,Q,A] using
      ae_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 hDiv
  have hQ := memLp_native_tensor_divergence (ballDomain a R) c Dc hc Q hDivBack
  have hNormalBack : ∀(j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain a R) ψ Dψ →
      Integrable (fun x=>∑i : Fin n,inner ℝ (c i j x) (Dψ x i)) μ ∧
      Integrable (fun x=>inner ℝ (Q x j) (ψ x)) μ ∧
      (∫x,∑i : Fin n,inner ℝ (c i j x) (Dψ x i) ∂μ)=
        -(∫x,inner ℝ (Q x j) (ψ x) ∂μ) := by
    simpa only [one_div,inv_inv,zero_add,c,Q,A,IntegrableOn] using
      native_normal_tensor_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 b V hNormal
  have hQNatural : ∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain a R) ψ Dψ →
      Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ ∧
      (∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ)=0 := by
    have H := natural_solenoidal_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 V
      (fun ψ Dψ hψ=>(hVNatural ψ Dψ hψ).2)
    simp only [one_div,inv_inv,zero_add] at H
    intro ψ Dψ hψ
    exact ⟨integrable_finsetSum Finset.univ (fun i _=>
      HolderToCK.integrable_inner_of_memLp_two (hQ i) (hψ.2.2 i)),H ψ Dψ hψ⟩
  have hQr : MemLp (fun x=>WithLp.toLp 2 (fun k : Fin (n*q)=>
      Q x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) (ENNReal.ofReal r) μ := by
    simpa only [one_div,inv_inv,zero_add,Q,A] using
      memLp_affineBall_exponent (0:Domain n) a (inv_pos.mpr hR) 1 (ENNReal.ofReal r) hVr
  have hFQI : Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Q x i)) μ :=
    integrable_finsetSum Finset.univ (fun i _=>
      HolderToCK.integrable_inner_of_memLp_two (hF i) (hQ i))
  have hUA (x : Domain n) : U (R⁻¹ • (x-a))=F x := by
    funext i
    simp only [U,smul_smul,mul_inv_cancel₀ hR.ne',one_smul,add_sub_cancel]
  have hFI : Integrable (fun x=>(hsNormSq (F x))^(p/2)) μ := by
    have H := integrable_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 hUI
    simpa only [one_div,inv_inv,zero_add,hUA,IntegrableOn,μ] using H
  have hQI : Integrable (fun x=>(hsNormSq (Q x))^(r/2)) μ := by
    simpa only [one_div,inv_inv,zero_add,Q,A,r,IntegrableOn,μ] using
      integrable_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 hVI
  have hInputScale : (∫x,(hsNormSq (F x))^(p/2) ∂μ)=
      R^n*(∫x in ball (0:Domain n) 1,(hsNormSq (U x))^(p/2)) := by
    have H := integral_affineBall (0:Domain n) a (inv_pos.mpr hR) 1
      (fun x=>(hsNormSq (U x))^(p/2))
    simpa only [one_div,inv_inv,zero_add,inv_pow,smul_eq_mul,A,hUA] using H
  have hOutputScale : (∫x,(hsNormSq (Q x))^(r/2) ∂μ)=
      R^n*(∫x in ball (0:Domain n) 1,(hsNormSq (V x))^(r/2)) := by
    simpa only [one_div,inv_inv,zero_add,inv_pow,smul_eq_mul,Q,A] using
      integral_affineBall (0:Domain n) a (inv_pos.mpr hR) 1
        (fun x=>(hsNormSq (V x))^(r/2))
  have hPairScale : (∫x,∑i : Fin n,inner ℝ (F x i) (Q x i) ∂μ)=
      R^n*(∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (U x i) (V x i)) := by
    have H := integral_affineBall (0:Domain n) a (inv_pos.mpr hR) 1
      (fun x=>∑i : Fin n,inner ℝ (U x i) (V x i))
    simpa only [one_div,inv_inv,zero_add,inv_pow,smul_eq_mul,A,hUA,Q] using H
  have hCScale : (∫x,∑j : Fin n,∑i : Fin n,‖c i j x‖^2 ∂μ)=
      R^n*R^2*(∫x in ball (0:Domain n) 1,∑j : Fin n,∑i : Fin n,‖b i j x‖^2) := by
    simp only [c,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,← Finset.mul_sum]
    rw [integral_const_mul]
    have H := integral_affineBall (0:Domain n) a (inv_pos.mpr hR) 1
      (fun x=>∑j : Fin n,∑i : Fin n,‖b i j x‖^2)
    simp only [one_div,inv_inv,zero_add,inv_pow,smul_eq_mul] at H
    rw [H]
    ring
  have hDcScale : (∫x,∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Dc i j x k‖^2 ∂μ)=
      R^n*(∫x in ball (0:Domain n) 1,∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Db i j x k‖^2) := by
    simpa only [one_div,inv_inv,zero_add,inv_pow,smul_eq_mul,Dc,A] using
      integral_affineBall (0:Domain n) a (inv_pos.mpr hR) 1
        (fun x=>∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Db i j x k‖^2)
  have hQEnergyScale : (∫x,hsNormSq (Q x) ∂μ)=R^n*(∫x in ball (0:Domain n) 1,hsNormSq (V x)) := by
    simpa only [one_div,inv_inv,zero_add,inv_pow,smul_eq_mul,Q,A] using
      integral_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 (fun x=>hsNormSq (V x))
  have hH1Back : (∫x,∑j : Fin n,∑i : Fin n,‖c i j x‖^2 ∂μ)+
      R^2*(∫x,∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Dc i j x k‖^2 ∂μ)≤
      (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)*R^2*(∫x,hsNormSq (Q x) ∂μ) := by
    rw [hCScale,hDcScale,hQEnergyScale]
    have H := mul_le_mul_of_nonneg_left hH1 (mul_nonneg (pow_nonneg hR.le n) (sq_nonneg R))
    nlinarith only [H]
  refine ⟨c,Dc,Q,hc,hQ,hSkewBack,hClosedBack,hDivBack,hNormalBack,hQNatural,hH1Back,
    hQr,hFQI,hFI,hQI,?_,?_⟩
  · rw [hPairScale,hPair,← hInputScale]
  · rw [hOutputScale,hInputScale]
    exact (mul_le_mul_of_nonneg_left hMoment (pow_nonneg hR.le n)).trans_eq (by ring)

end StationaryHarmonicMaps.Analysis

end
