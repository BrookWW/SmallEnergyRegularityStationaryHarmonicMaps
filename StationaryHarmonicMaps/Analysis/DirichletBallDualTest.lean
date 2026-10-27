module

public import StationaryHarmonicMaps.Analysis.DirichletNativeDualTest
public import StationaryHarmonicMaps.Analysis.AffineHSMoment
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtLpDecoding

/-!
# Actual native dual tests on arbitrary balls

Affine transport of the original native zero-boundary graph produces the
unit-ball dual test. Multiplying its inverse pullback by R^(2-p) retains
its exact original power pairing and its scale-independent conjugate
full-HS moment bound.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem tendsto_eLpNorm_const_smul_sub {X : Type*} [MeasurableSpace X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X)
    (m : ℕ → X → E) (u : X → E) (c : ℝ)
    (hlim : Tendsto (fun k=>eLpNorm (m k-u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k=>eLpNorm ((c • m k)-(c • u)) 2 μ) atTop (𝓝 0) := by
  simp_rw [← smul_sub,eLpNorm_const_smul]
  simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr (by simp))

private theorem zeroBoundary_const_smul_ball {n q : ℕ} (a : Domain n) (R c : ℝ)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : HasZeroBoundaryValues (ballDomain a R) u Du) :
    HasZeroBoundaryValues (ballDomain a R) (fun x=>c • u x) (fun x i=>c • Du x i) := by
  obtain ⟨hu,m,hm,hc,hlim,hDlim⟩ := hu
  let M : ℕ → Domain n → Ambient q := fun k x=>c • m k x
  have hM (k : ℕ) : ContDiff ℝ ∞ (M k) := (hm k).const_smul c
  have hDM (k : ℕ) (i : Fin n) (x : Domain n) :
      coordinateDerivative (M k) (hM k) i x=c • coordinateDerivative (m k) (hm k) i x := by
    exact congrArg (fun D : Domain n →L[ℝ] Ambient q=>D (EuclideanSpace.single i 1))
      (((hm k).differentiable (by simp) x).hasFDerivAt.const_smul c).fderiv
  have hMc (k : ℕ) : HasCompactSupport (M k) ∧ tsupport (M k)⊆ball a R :=
    ⟨HasCompactSupport.smul_left (f:=fun _ : Domain n=>c) (hc k).1,(tsupport_smul_subset_right (fun _ : Domain n=>c) (m k)).trans (hc k).2⟩
  have hMW (k : ℕ) : MemW12 (ballDomain a R) (M k)
      (fun x i=>coordinateDerivative (M k) (hM k) i x) := by
    apply memW12_of_contDiff _ (hM k)
    · exact (hM k).continuous.memLp_of_hasCompactSupport (hMc k).1
    · intro i
      exact ((hM k).continuous_fderiv (by simp) |>.clm_apply continuous_const).memLp_of_hasCompactSupport
        ((hMc k).1.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hConv : Tendsto (fun k=>eLpNorm (M k-(fun x=>c • u x)) 2 (volume.restrict (ball a R))) atTop (𝓝 0) :=
    tendsto_eLpNorm_const_smul_sub _ m u c hlim
  have hDConv (i : Fin n) : Tendsto (fun k=>eLpNorm
      (fun x=>coordinateDerivative (M k) (hM k) i x-c • Du x i) 2 (volume.restrict (ball a R))) atTop (𝓝 0) := by
    simp_rw [hDM]
    exact tendsto_eLpNorm_const_smul_sub _ (fun k x=>coordinateDerivative (m k) (hm k) i x)
      (fun x=>Du x i) c (hDlim i)
  exact ⟨MemW12.of_L2_limit_ball a R hMW (hu.2.1.const_smul c)
    (fun i=>(hu.2.2 i).const_smul c) hConv hDConv,M,hM,hMc,hConv,hDConv⟩

private theorem hs_power_integrable_of_native {n q : ℕ} (a : Domain n) (R : ℝ)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : HasZeroBoundaryValues (ballDomain a R) u Du) (p : ℝ) (hp0 : 0<p) (hp2 : p≤2) :
    IntegrableOn (fun x=>(hsNormSq (Du x))^(p/2)) (ball a R) volume := by
  letI : IsFiniteMeasure (volume.restrict (ballDomain a R).val) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let E := fun (A : Gradient n q)=>WithLp.toLp 2 (fun k : Fin (n*q)=>A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  have hE := memLp_real_of_memL2 (fun x=>E (Du x)) hp2 (memLp_hs_flatten Du hu.1.2.2)
  have H := integrable_norm_rpow_of_memLp_real _ hp0.le hE
  have heq (x : Domain n) : ‖E (Du x)‖^p=(hsNormSq (Du x))^(p/2) := by
    rw [← hs_flatten_norm_sq]
    change ‖E (Du x)‖^p=(‖E (Du x)‖^2)^(p/2)
    rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg _)]
    congr 1;ring
  simpa only [heq,ballDomain,IntegrableOn] using H

/-- Every original native W0 graph on a positive-radius ball has a genuine native conjugate test with exact original power pairing and dimension-only full-HS moment control. -/
theorem exists_native_dirichlet_dual_test_ball (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1<p) (hpTwo : p<2) :
    ∃C : ℝ,0<C ∧ ∀(q : ℕ) (a : Domain n) (R : ℝ),0<R →
      let μ := volume.restrict (ball a R)
      let r := p/(p-1)
      ∀(u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
        HasZeroBoundaryValues (ballDomain a R) u Du →
        ∃(φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
          HasZeroBoundaryValues (ballDomain a R) φ Dφ ∧
          MemLp (fun x=>WithLp.toLp 2 (fun k : Fin (n*q)=>
            Dφ x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) (ENNReal.ofReal r) μ ∧
          Integrable (fun x=>∑i : Fin n,inner ℝ (Du x i) (Dφ x i)) μ ∧
          Integrable (fun x=>(hsNormSq (Du x))^(p/2)) μ ∧
          Integrable (fun x=>(hsNormSq (Dφ x))^(r/2)) μ ∧
          (∫x,∑i : Fin n,inner ℝ (Du x i) (Dφ x i) ∂μ)=∫x,(hsNormSq (Du x))^(p/2) ∂μ ∧
          (∫x,(hsNormSq (Dφ x))^(r/2) ∂μ)≤C*(∫x,(hsNormSq (Du x))^(p/2) ∂μ) := by
  obtain ⟨C,hC,Hunit⟩ := exists_native_dirichlet_dual_test_unitBall n hn p hpOne hpTwo
  refine ⟨C,hC,?_⟩
  intro q a R hR μ r u Du hu
  let U := fun x=>u (a+R • x)
  let DU := fun x i=>R • Du (a+R • x) i
  have hU : HasZeroBoundaryValues (ballDomain (0:Domain n) 1) U DU := by
    simpa only [div_self hR.ne',sub_zero] using hu.affineBall_pullback (0:Domain n) hR
  obtain ⟨ψ,Dψ,hψ,hψLp,_hψPairI,hUI,hψI,hψPair,hψBound⟩ := Hunit q U DU hU
  let α := R^(1-p)
  let β := R^(2-p)
  let φ := fun x=>β • ψ (R⁻¹ • (x-a))
  let Dφ := fun x i=>α • Dψ (R⁻¹ • (x-a)) i
  have hα : 0<α := Real.rpow_pos_of_pos hR _
  have hβ : 0<β := Real.rpow_pos_of_pos hR _
  have hScale : β*R⁻¹=α := by
    dsimp only [α,β]
    rw [← Real.rpow_neg_one,← Real.rpow_add hR]
    congr 1;ring
  have hBack := hψ.affineBall_pullback a (inv_pos.mpr hR)
  have hBack' : HasZeroBoundaryValues (ballDomain a R) (fun x=>ψ (R⁻¹ • (x-a)))
      (fun x i=>R⁻¹ • Dψ (R⁻¹ • (x-a)) i) := by
    simpa only [one_div,inv_inv,zero_add] using hBack
  have hφ : HasZeroBoundaryValues (ballDomain a R) φ Dφ := by
    simpa only [φ,Dφ,smul_smul,hScale] using zeroBoundary_const_smul_ball a R β hBack'
  let E := fun (A : Gradient n q)=>WithLp.toLp 2 (fun k : Fin (n*q)=>A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  have hLpBack : MemLp (fun x=>E (Dψ (R⁻¹ • (x-a)))) (ENNReal.ofReal r) μ := by
    simpa only [one_div,inv_inv,zero_add] using
      memLp_affineBall_exponent (0:Domain n) a (inv_pos.mpr hR) 1 (ENNReal.ofReal r) hψLp
  have hφLp : MemLp (fun x=>E (Dφ x)) (ENNReal.ofReal r) μ := by
    exact hLpBack.const_smul α
  have hInputI := hs_power_integrable_of_native a R u Du hu p (zero_lt_one.trans hpOne) hpTwo.le
  have hPairI : Integrable (fun x=>∑i : Fin n,inner ℝ (Du x i) (Dφ x i)) μ :=
    integrable_finsetSum Finset.univ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hu.1.2.2 i) (hφ.1.2.2 i))
  have hMomentScale : (∫x,(hsNormSq (Dφ x))^(r/2) ∂μ)=
      R^n*α^r*(∫x in ball (0:Domain n) 1,(hsNormSq (Dψ x))^(r/2)) := by
    have H := integral_hs_half_power_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 α r Dψ
    simpa only [one_div,inv_inv,zero_add,inv_pow,inv_inv,abs_of_pos hα,Dφ,μ] using H
  have hOutputI : Integrable (fun x=>(hsNormSq (Dφ x))^(r/2)) μ := by
    have H := (integrable_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 hψI).const_mul (α^r)
    have heq (x : Domain n) : (hsNormSq (Dφ x))^(r/2)=α^r*(hsNormSq (Dψ (R⁻¹ • (x-a))))^(r/2) := by
      dsimp only [Dφ]
      rw [hsNormSq_const_smul,Real.mul_rpow (sq_nonneg α) (hsNormSq_nonneg _)]
      congr 1
      rw [← Real.rpow_natCast,← Real.rpow_mul hα.le]
      congr 1;ring
    have H' : Integrable (fun x=>α^r*(hsNormSq (Dψ (R⁻¹ • (x-a))))^(r/2)) μ := by
      simpa only [μ,r,one_div,inv_inv,zero_add] using H
    exact H'.congr (Eventually.of_forall fun x=>(heq x).symm)
  have hInputScale : (∫x in ball (0:Domain n) 1,(hsNormSq (DU x))^(p/2))=
      (R^n)⁻¹*R^p*(∫x,(hsNormSq (Du x))^(p/2) ∂μ) := by
    simpa only [DU,div_self hR.ne',sub_zero,abs_of_pos hR,μ] using
      integral_hs_half_power_affineBall a (0:Domain n) hR R R p Du
  have hαPower : α^r=R^(-p) := by
    dsimp only [α,r]
    rw [← Real.rpow_mul hR.le]
    congr 1
    field_simp [ne_of_gt (show 0<p-1 by linarith only [hpOne])]
    ring
  have hCancel : R^n*α^r*((R^n)⁻¹*R^p)=1 := by
    rw [hαPower,Real.rpow_neg hR.le]
    field_simp
  have hPairScale : (∫x,∑i : Fin n,inner ℝ (Du x i) (Dφ x i) ∂μ)=
      R^n*α/R*(∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (DU x i) (Dψ x i)) := by
    have H := integral_affineBall (0:Domain n) a (inv_pos.mpr hR) 1
      (fun x=>∑i : Fin n,inner ℝ (DU x i) (Dψ x i))
    have hpnt (x : Domain n) : (∑i : Fin n,inner ℝ (Du x i) (Dφ x i))=
        (α/R)*(∑i : Fin n,inner ℝ (DU (R⁻¹ • (x-a)) i) (Dψ (R⁻¹ • (x-a)) i)) := by
      simp only [DU,Dφ,smul_smul,mul_inv_cancel₀ hR.ne',one_smul,add_sub_cancel,real_inner_smul_left,real_inner_smul_right,← Finset.mul_sum]
      field_simp [hR.ne']
    simp_rw [hpnt]
    rw [integral_const_mul]
    simp only [one_div,inv_inv,zero_add,inv_pow,inv_inv,smul_eq_mul] at H
    rw [H]
    ring
  refine ⟨φ,Dφ,hφ,hφLp,hPairI,hInputI,hOutputI,?_,?_⟩
  · rw [hPairScale,hψPair,hInputScale]
    have hαR : α/R=R^(-p) := by
      dsimp only [α]
      calc
        R^(1-p)/R=R^(1-p)/R^(1:ℝ) := by rw [Real.rpow_one]
        _=R^((1-p)-1) := (Real.rpow_sub hR _ _).symm
        _=R^(-p) := by congr 1;ring
    rw [mul_div_assoc,hαR]
    rw [← hαPower]
    calc
      _=(R^n*α^r*((R^n)⁻¹*R^p))*(∫x,(hsNormSq (Du x))^(p/2) ∂μ) := by ring
      _=_ := by rw [hCancel,one_mul]
  · rw [hMomentScale]
    have H := mul_le_mul_of_nonneg_left hψBound (mul_nonneg (pow_nonneg hR.le n) (Real.rpow_nonneg hα.le r))
    rw [hInputScale] at H
    calc
      _ ≤ R^n*α^r*(C*((R^n)⁻¹*R^p*(∫x,(hsNormSq (Du x))^(p/2) ∂μ))) := H
      _ = (R^n*α^r*((R^n)⁻¹*R^p))*(C*(∫x,(hsNormSq (Du x))^(p/2) ∂μ)) := by ring
      _ = _ := by rw [hCancel,one_mul]

end StationaryHarmonicMaps.Analysis

end
