module

public import StationaryHarmonicMaps.Analysis.DirichletOperatorHighMoments
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Actual class moments of the fixed Dirichlet operator

Literal HS decoding and encoding identify every original L2 class with
its original coefficient field. The same operator's higher HS moments
therefore give genuine vector Lr membership and ordinary norm-moment
bounds. Its actual zero-boundary potential and signed weak PDE remain
part of the conclusion.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem decoded_zeroExtension_moment {n q : ℕ}
    (P : Domain n → Ambient (n*q)) {r : ℝ} (hr : 0<r) :
    (∫⁻x,(ENNReal.ofReal (hsNormSq (fun i=>(ball (0:Domain n) 1).indicator
      (fun y=>WithLp.toLp 2 (fun j : Fin q=>P y (finProdFinEquiv (i,j)))) x)))^(r/2))=
      ∫⁻x,ENNReal.ofReal (‖P x‖^r) ∂volume.restrict (ball (0:Domain n) 1) := by
  classical
  have hPower (x : Domain n) : (ENNReal.ofReal (‖P x‖^2))^(r/2)=ENNReal.ofReal (‖P x‖^r) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by positivity : 0≤r/2),
      ← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg _)]
    congr 2
    ring
  have hPoint : (fun x=>(ENNReal.ofReal (hsNormSq (fun i=>(ball (0:Domain n) 1).indicator
      (fun y=>WithLp.toLp 2 (fun j : Fin q=>P y (finProdFinEquiv (i,j)))) x)))^(r/2))=
      (ball (0:Domain n) 1).indicator (fun x=>ENNReal.ofReal (‖P x‖^r)) := by
    funext x
    by_cases hx : x∈ball (0:Domain n) 1
    · simp only [indicator_of_mem hx,hs_unflatten_hsNormSq,hPower]
    · simp only [indicator_of_notMem hx,hsNormSq,norm_zero,zero_pow (by decide : (2:ℕ)≠0),
        Finset.sum_const_zero,ENNReal.ofReal_zero,ENNReal.zero_rpow_of_pos (by positivity : 0<r/2)]
  rw [hPoint,lintegral_indicator measurableSet_ball]

/-- One actual Dirichlet projection on L2 classes has all higher real norm-moment bounds and actual higher Lr membership for the same original input and output classes. -/
theorem exists_dirichlet_class_all_high_moments_unitBall (n : ℕ) (hn : 2≤n) :
    ∃ C : {r : ℝ //2<r} → ℝ,(∀r,0<C r) ∧ ∀q : ℕ,
      let μ := volume.restrict (ball (0:Domain n) 1)
      let D := fun (P : Domain n → Ambient (n*q)) x i=>WithLp.toLp 2
        (fun j : Fin q=>P x (finProdFinEquiv (i,j)))
      ∃T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
        ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀V,T (T V)=T V) ∧
        ∀W : Lp (Ambient (n*q)) 2 μ,∃u : Domain n → Ambient q,
          HasZeroBoundaryValues (ballDomain (0:Domain n) 1) u (D (T W)) ∧
          HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1)
            (fun x i=>D (T W) x i-D W x i) (fun _=>0) ∧
          ∀r : {r : ℝ //2<r},MemLp (fun x=>W x) (ENNReal.ofReal r.val) μ →
            MemLp (fun x=>(T W) x) (ENNReal.ofReal r.val) μ ∧
            (∫x,‖(T W) x‖^r.val ∂μ)≤C r*(∫x,‖W x‖^r.val ∂μ) := by
  classical
  obtain ⟨C₀,hC₀,HT⟩ := exists_dirichlet_operator_all_high_moments_unitBall n hn
  let s := fun r : {r : ℝ //2<r}=>(⟨r.val/2,by linarith [r.property]⟩ : {s : ℝ //1<s})
  refine ⟨(fun r=>C₀ (s r)),(fun r=>hC₀ (s r)),?_⟩
  intro q μ D
  obtain ⟨T,hT,hSelf,hIdem,Hresponse⟩ := HT q
  refine ⟨T,hT,hSelf,hIdem,?_⟩
  intro W
  let F := D W
  have hF (i : Fin n) : MemLp (fun x=>F x i) 2 μ := memLp_hs_unflatten W (Lp.memLp W) i
  let E : Gradient n q → Ambient (n*q) := fun G=>WithLp.toLp 2
    (fun k=>G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  let V := (memLp_hs_flatten F hF).toLp (fun x=>E (F x))
  have hEnc (x : Domain n) : E (F x)=W x := hs_flatten_unflatten (W x)
  have hV : V=W := by
    calc
      _=(Lp.memLp W).toLp W := (MemLp.toLp_eq_toLp_iff (memLp_hs_flatten F hF) (Lp.memLp W)).mpr
        (Eventually.of_forall hEnc)
      _=W := Lp.toLp_coeFn W (Lp.memLp W)
  obtain ⟨u,hu,hEq,_hF₀,_hQ₀,_hEnergy,Hmoment⟩ := Hresponse F hF
  change HasZeroBoundaryValues (ballDomain (0:Domain n) 1) u (D (T V)) at hu
  change HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1)
    (fun x i=>D (T V) x i-D W x i) (fun _=>0) at hEq
  rw [hV] at hu hEq
  refine ⟨u,hu,hEq,?_⟩
  intro r hW
  have hr0 : 0<r.val := lt_trans (by norm_num) r.property
  have hp0 : ENNReal.ofReal r.val≠0 := (ENNReal.ofReal_pos.mpr hr0).ne'
  have hWI : Integrable (fun x=>‖W x‖^r.val) μ := by
    simpa only [ENNReal.toReal_ofReal hr0.le] using hW.integrable_norm_rpow hp0 ENNReal.ofReal_ne_top
  have hInput : (∫⁻x,ENNReal.ofReal (‖W x‖^r.val) ∂μ)<∞ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x=>Real.rpow_nonneg (norm_nonneg (W x)) _)).mp hWI.hasFiniteIntegral
  have hM := Hmoment (s r) (by
    simpa only [s,F,D,decoded_zeroExtension_moment (P:=W) hr0] using hInput)
  change (∫⁻x,(ENNReal.ofReal (hsNormSq (fun i=>(ball (0:Domain n) 1).indicator
    (fun y=>D (T V) y i) x)))^(r.val/2))≤_ ∧
      (∫⁻x,(ENNReal.ofReal (hsNormSq (fun i=>(ball (0:Domain n) 1).indicator
        (fun y=>D (T V) y i) x)))^(r.val/2))<∞ at hM
  rw [hV,decoded_zeroExtension_moment (P:=T W) hr0] at hM
  have hOutputFinite : (∫⁻x,ENNReal.ofReal (‖(T W) x‖^r.val) ∂μ)<∞ := hM.2
  have hOI : Integrable (fun x=>‖(T W) x‖^r.val) μ :=
    ⟨((Lp.aestronglyMeasurable (T W)).norm.aemeasurable.pow_const r.val).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x=>Real.rpow_nonneg (norm_nonneg ((T W) x)) _)).mpr hOutputFinite⟩
  have hOutputLp : MemLp (fun x=>(T W) x) (ENNReal.ofReal r.val) μ :=
    (integrable_norm_rpow_iff (Lp.aestronglyMeasurable (T W)) hp0 ENNReal.ofReal_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal hr0.le] using hOI)
  refine ⟨hOutputLp,?_⟩
  have hBound : (∫⁻x,ENNReal.ofReal (‖(T W) x‖^r.val) ∂μ)≤
      ENNReal.ofReal (C₀ (s r))*(∫⁻x,ENNReal.ofReal (‖W x‖^r.val) ∂μ) := by
    simpa only [s,F,D,decoded_zeroExtension_moment (P:=W) hr0] using hM.1
  rw [← ofReal_integral_eq_lintegral_ofReal hOI (Eventually.of_forall fun x=>Real.rpow_nonneg (norm_nonneg ((T W) x)) _),
    ← ofReal_integral_eq_lintegral_ofReal hWI (Eventually.of_forall fun x=>Real.rpow_nonneg (norm_nonneg (W x)) _),
    ← ENNReal.ofReal_mul (hC₀ (s r)).le] at hBound
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (hC₀ (s r)).le
    (integral_nonneg fun x=>Real.rpow_nonneg (norm_nonneg (W x)) _))).mp hBound

end StationaryHarmonicMaps.Analysis

end
