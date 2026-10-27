module

public import StationaryHarmonicMaps.Analysis.DirichletOperatorLpMorrey
public import HarmonicMaps.Analysis.SobolevAECongruence

/-!
# Actual native Dirichlet dual tests

The original native zero-boundary gradient is fixed by the genuine
Dirichlet projection, as follows from its actual weak equation and
native uniqueness. The literal power-duality field then produces an
actual native test through the same operator. Its full HS pairing and
conjugate moment are proved from the original data.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem norm_sq_half_rpow {E : Type*} [NormedAddCommGroup E]
    (v : E) (p : ℝ) : (‖v‖^2)^(p/2)=‖v‖^p := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg v)]
  congr 1
  ring

/-- Original native zero-boundary data produce a genuine conjugate-exponent native test, its actual integrable pairing, exact power pairing, and full-HS moment control. -/
theorem exists_native_dirichlet_dual_test_unitBall (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1<p) (hpTwo : p<2) :
    ∃C : ℝ,0<C ∧ ∀q : ℕ,
      let μ := volume.restrict (ball (0:Domain n) 1)
      let r := p/(p-1)
      ∀(u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
        HasZeroBoundaryValues (ballDomain (0:Domain n) 1) u Du →
        ∃(φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
          HasZeroBoundaryValues (ballDomain (0:Domain n) 1) φ Dφ ∧
          MemLp (fun x=>WithLp.toLp 2 (fun k : Fin (n*q)=>
            Dφ x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) (ENNReal.ofReal r) μ ∧
          Integrable (fun x=>∑i : Fin n,inner ℝ (Du x i) (Dφ x i)) μ ∧
          Integrable (fun x=>(hsNormSq (Du x))^(p/2)) μ ∧
          Integrable (fun x=>(hsNormSq (Dφ x))^(r/2)) μ ∧
          (∫x,∑i : Fin n,inner ℝ (Du x i) (Dφ x i) ∂μ)=∫x,(hsNormSq (Du x))^(p/2) ∂μ ∧
          (∫x,(hsNormSq (Dφ x))^(r/2) ∂μ)≤C*(∫x,(hsNormSq (Du x))^(p/2) ∂μ) := by
  have hp0 : 0<p := zero_lt_one.trans hpOne
  have hpm : 0<p-1 := by linarith only [hpOne]
  have hrTwo : 2<p/(p-1) := (lt_div_iff₀ hpm).mpr (by linarith only [hpTwo])
  have hrOne : 1<p/(p-1) := lt_trans (by norm_num) hrTwo
  have hr0 : 0<p/(p-1) := zero_lt_one.trans hrOne
  obtain ⟨Cp,_Cm,hCp,_hCm,HT⟩ := exists_same_dirichlet_operator_all_lp_and_power_growth_unitBall n hn
  refine ⟨Cp ⟨p/(p-1),hrOne⟩,hCp _,?_⟩
  intro q μ r u Du hu
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let E : Gradient n q → Ambient (n*q) := fun G=>WithLp.toLp 2
    (fun k=>G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  let D := fun (P : Domain n → Ambient (n*q)) x i=>WithLp.toLp 2
    (fun j : Fin q=>P x (finProdFinEquiv (i,j)))
  have hDu (i : Fin n) : MemLp (fun x=>Du x i) 2 μ := hu.1.2.2 i
  have hFlat : MemLp (fun x=>E (Du x)) 2 μ := memLp_hs_flatten Du hDu
  let W := hFlat.toLp (fun x=>E (Du x))
  have hWAE : (W : Domain n → Ambient (n*q)) =ᵐ[μ] (fun x=>E (Du x)) := hFlat.coeFn_toLp
  have hDW : D W =ᵐ[μ] Du := by
    filter_upwards [hWAE] with x hx
    change (fun i : Fin n=>WithLp.toLp 2 (fun j : Fin q=>W x (finProdFinEquiv (i,j))))=Du x
    rw [hx]
    exact hs_unflatten_flatten (Du x)
  have huDW : HasZeroBoundaryValues (ballDomain (0:Domain n) 1) u (D W) :=
    hu.congr_ae (EventuallyEq.refl _ _) hDW.symm
  obtain ⟨T,_hT,hSelf,_hIdem,Hresponse⟩ := HT q
  obtain ⟨v,hv,hEq,_hEnergy,_hLp,_hGrowth⟩ := Hresponse W
  have hColW (i : Fin n) : MemLp (fun x=>D W x i) 2 μ := memLp_hs_unflatten W (Lp.memLp W) i
  have hPairW : ∀(ψ : Domain n → Ambient q),ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ⊆ball (0:Domain n) 1 →
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (D (T W) x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (D W x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    intro ψ hψ hcψ hsψ
    have hDψ (i : Fin n) : MemLp (fun x=>fderiv ℝ ψ x (EuclideanSpace.single i 1)) 2 μ :=
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hcψ.fderiv_apply ℝ (EuclideanSpace.single i 1))
    have hQI := integrable_finsetSum Finset.univ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hv.1.2.2 i) (hDψ i))
    have hWI := integrable_finsetSum Finset.univ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hColW i) (hDψ i))
    have H := (hEq.2 ψ hψ hcψ hsψ).2.2
    simp only [inner_sub_left,Finset.sum_sub_distrib] at H
    rw [integral_sub hQI hWI] at H
    simp only [inner_zero_left,integral_zero,neg_zero] at H
    exact sub_eq_zero.mp H
  have hUnique := dirichlet_gradient_response_unique_ae (by omega : 1≤n)
    (0:Domain n) (by norm_num : (0:ℝ)<1) (D W) hColW hv huDW hPairW (fun _ _ _ _=>rfl)
  have hFix : T W=W := by
    apply Lp.ext
    filter_upwards [hUnique.2] with x hx
    change D (T W) x=D W x at hx
    calc
      (T W) x=E (D (T W) x) := (hs_flatten_unflatten ((T W) x)).symm
      _=E (D W x) := congrArg E hx
      _=W x := hs_flatten_unflatten (W x)
  let G := fun x=>‖W x‖^(p-2) • W x
  obtain ⟨hGTwo,hGr⟩ := dual_power_test_memLp μ p hpOne hpTwo W (Lp.memLp W)
  let Y := hGTwo.toLp G
  have hYAE : (Y : Domain n → Ambient (n*q)) =ᵐ[μ] G := hGTwo.coeFn_toLp
  have hYr : MemLp (fun x=>Y x) (ENNReal.ofReal r) μ := hGr.ae_eq hYAE.symm
  obtain ⟨φ,hφ,_hEqφ,_hEnergyφ,Hpφ,_hGrowthφ⟩ := Hresponse Y
  obtain ⟨hTYr,hBound⟩ := Hpφ ⟨r,hrOne⟩ hYr
  have hφLp : MemLp (fun x=>E (D (T Y) x)) (ENNReal.ofReal r) μ := by
    simpa only [E,D,hs_flatten_unflatten] using hTYr
  have hIpair : Integrable (fun x=>∑i : Fin n,inner ℝ (Du x i) (D (T Y) x i)) μ :=
    integrable_finsetSum Finset.univ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hDu i) (hφ.1.2.2 i))
  have hWp := memLp_real_of_memL2 (fun x=>W x) hpTwo.le (Lp.memLp W)
  have hIW : Integrable (fun x=>‖W x‖^p) μ := integrable_norm_rpow_of_memLp_real _ hp0.le hWp
  have hIT : Integrable (fun x=>‖(T Y) x‖^r) μ := integrable_norm_rpow_of_memLp_real _ hr0.le hTYr
  have hPower (A : Gradient n q) (t : ℝ) : (hsNormSq A)^(t/2)=‖E A‖^t := by
    rw [← hs_flatten_norm_sq A]
    exact norm_sq_half_rpow _ t
  have hInputAE : (fun x=>(hsNormSq (Du x))^(p/2)) =ᵐ[μ] (fun x=>‖W x‖^p) := by
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
  have hPairT : (∫x,∑i : Fin n,inner ℝ (Du x i) (D (T Y) x i) ∂μ)=inner ℝ W (T Y) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hWAE] with x hx
    change (∑i : Fin n,inner ℝ (Du x i) (D (T Y) x i))=inner ℝ (W x) ((T Y) x)
    rw [hx,← hs_flatten_inner (Du x) (D (T Y) x)]
    congr 1
    exact hs_flatten_unflatten ((T Y) x)
  have hSym := hSelf.isSymmetric W Y
  change inner ℝ (T W) Y=inner ℝ W (T Y) at hSym
  rw [hFix] at hSym
  refine ⟨φ,D (T Y),hφ,hφLp,hIpair,hIW.congr hInputAE.symm,hIT.congr (Eventually.of_forall fun x=>(hOutput x).symm),?_,?_⟩
  · rw [hPairT,← hSym,hPairY]
    exact (integral_congr_ae hInputAE).symm
  · simp_rw [hOutput]
    rw [hYMoment] at hBound
    exact hBound.trans_eq (by rw [integral_congr_ae hInputAE])

end StationaryHarmonicMaps.Analysis

end
