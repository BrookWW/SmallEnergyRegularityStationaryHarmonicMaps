module

public import StationaryHarmonicMaps.Analysis.NeumannOperatorHighMoments
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Actual class moments of the fixed Neumann operator

Literal HS decoding and encoding identify every original L2 class with
its original coefficient field. The same operator's higher HS moments
therefore give genuine vector Lr membership and ordinary norm-moment
bounds. Its actual native Neumann potential and all natural tests and signed weak PDE remain
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

@[expose] noncomputable def effectiveNeumannHighMomentConstant (n : ℕ) (r : ℝ) : ℝ :=
  effectiveNeumannDensityMomentConstant n (r/2)

@[expose] def effectiveNeumannDimensionalMomentConstant (n : ℕ) : ℕ :=
  uniformGoodLambdaMomentMajorant n (n+1) (effectiveNeumannGoodLambdaAmplitude n)
    (densityGoodLambdaTailFactor n)

theorem effectiveNeumannHighMomentConstant_pos (n : ℕ) (r : ℝ) (hr : 2<r) :
    0 < effectiveNeumannHighMomentConstant n r :=
  effectiveNeumannDensityMomentConstant_pos n (r/2) (by linarith)

theorem effectiveNeumannHighMomentConstant_dimensional (n : ℕ) (hn : 2≤n) :
    effectiveNeumannHighMomentConstant n ((2*n+1 : ℕ) : ℝ) =
      (effectiveNeumannDimensionalMomentConstant n : ℝ) := by
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  apply effectiveUniformGoodLambdaMomentConstant_eq_majorant
  · simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    linarith
  · simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    linarith

/-- One actual Neumann projection on L2 classes has all higher real norm-moment bounds and actual higher Lr membership and all native natural tests for the same original input and output classes. -/
theorem exists_neumann_class_all_high_moments_unitBall_explicit (n : ℕ) (hn : 2≤n) :
    ∃ C : {r : ℝ //2<r} → ℝ,(∀r,0<C r) ∧
      C = (fun r => effectiveNeumannHighMomentConstant n r.val) ∧ ∀q : ℕ,
      let μ := volume.restrict (ball (0:Domain n) 1)
      let D := fun (P : Domain n → Ambient (n*q)) x i=>WithLp.toLp 2
        (fun j : Fin q=>P x (finProdFinEquiv (i,j)))
      ∃T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
        ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀V,T (T V)=T V) ∧
        ∀W : Lp (Ambient (n*q)) 2 μ,∃u : Domain n → Ambient q,
          MemW12 (ballDomain (0:Domain n) 1) u (D (T W)) ∧
          (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (D (T W) x i) (Dψ x i)) μ ∧
            Integrable (fun x=>∑i : Fin n,inner ℝ (D W x i) (Dψ x i)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (D (T W) x i) (Dψ x i) ∂μ)=
              ∫x,∑i : Fin n,inner ℝ (D W x i) (Dψ x i) ∂μ) ∧
          HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1)
            (fun x i=>D (T W) x i-D W x i) (fun _=>0) ∧
          ∀r : {r : ℝ //2<r},MemLp (fun x=>W x) (ENNReal.ofReal r.val) μ →
            MemLp (fun x=>(T W) x) (ENNReal.ofReal r.val) μ ∧
            (∫x,‖(T W) x‖^r.val ∂μ)≤C r*(∫x,‖W x‖^r.val ∂μ) := by
  classical
  obtain ⟨C₀,hC₀,hC₀Eq,HT⟩ := exists_neumann_operator_all_high_moments_unitBall_explicit n hn
  let s := fun r : {r : ℝ //2<r}=>(⟨r.val/2,by linarith [r.property]⟩ : {s : ℝ //1<s})
  refine ⟨(fun r=>C₀ (s r)),(fun r=>hC₀ (s r)),?_,?_⟩
  · funext r
    rw [hC₀Eq]
    rfl
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
  obtain ⟨u,hu,hNat,hEq,_hF₀,_hQ₀,_hEnergy,Hmoment⟩ := Hresponse F hF
  change MemW12 (ballDomain (0:Domain n) 1) u (D (T V)) at hu
  change HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1)
    (fun x i=>D (T V) x i-D W x i) (fun _=>0) at hEq
  change ∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
    MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
    Integrable (fun x=>∑i : Fin n,inner ℝ (D (T V) x i) (Dψ x i)) μ ∧
    Integrable (fun x=>∑i : Fin n,inner ℝ (D W x i) (Dψ x i)) μ ∧
    (∫x,∑i : Fin n,inner ℝ (D (T V) x i) (Dψ x i) ∂μ)=
      ∫x,∑i : Fin n,inner ℝ (D W x i) (Dψ x i) ∂μ at hNat
  rw [hV] at hu hNat hEq
  refine ⟨u,hu,hNat,hEq,?_⟩
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

theorem exists_neumann_class_all_high_moments_unitBall (n : ℕ) (hn : 2≤n) :
    ∃ C : {r : ℝ //2<r} → ℝ,(∀r,0<C r) ∧ ∀q : ℕ,
      let μ := volume.restrict (ball (0:Domain n) 1)
      let D := fun (P : Domain n → Ambient (n*q)) x i=>WithLp.toLp 2
        (fun j : Fin q=>P x (finProdFinEquiv (i,j)))
      ∃T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
        ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀V,T (T V)=T V) ∧
        ∀W : Lp (Ambient (n*q)) 2 μ,∃u : Domain n → Ambient q,
          MemW12 (ballDomain (0:Domain n) 1) u (D (T W)) ∧
          (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
            MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
            Integrable (fun x=>∑i : Fin n,inner ℝ (D (T W) x i) (Dψ x i)) μ ∧
            Integrable (fun x=>∑i : Fin n,inner ℝ (D W x i) (Dψ x i)) μ ∧
            (∫x,∑i : Fin n,inner ℝ (D (T W) x i) (Dψ x i) ∂μ)=
              ∫x,∑i : Fin n,inner ℝ (D W x i) (Dψ x i) ∂μ) ∧
          HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1)
            (fun x i=>D (T W) x i-D W x i) (fun _=>0) ∧
          ∀r : {r : ℝ //2<r},MemLp (fun x=>W x) (ENNReal.ofReal r.val) μ →
            MemLp (fun x=>(T W) x) (ENNReal.ofReal r.val) μ ∧
            (∫x,‖(T W) x‖^r.val ∂μ)≤C r*(∫x,‖W x‖^r.val ∂μ) := by
  obtain ⟨C,hC,_hCEq,H⟩ := exists_neumann_class_all_high_moments_unitBall_explicit n hn
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end
