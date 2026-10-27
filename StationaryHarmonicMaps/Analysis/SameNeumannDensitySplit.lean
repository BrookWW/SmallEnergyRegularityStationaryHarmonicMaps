module

public import StationaryHarmonicMaps.Analysis.SameNeumannOperatorOffSupport

/-!
# Actual near and far densities for the same Neumann operator

The original and both truncated inputs use one previously fixed operator.
Linearity first holds for the actual L2 classes; the representative split
is then obtained almost everywhere. All global HS integrabilities, the
near energy bound, and the far essential bound are produced from the
original raw L2 field. No maximal-function or good-lambda estimate is an
input to this construction.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

private theorem hs_indicator_density {n q : ℕ} (S : Set (Domain n))
    (G : Domain n → Gradient n q) :
    (fun x=>hsNormSq (fun i=>S.indicator (fun y=>G y i) x))=S.indicator (fun x=>hsNormSq (G x)) := by
  classical
  funext x
  by_cases hx : x∈S
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx,hsNormSq,norm_zero,
      zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero]

private theorem integral_hs_indicator {n q : ℕ} (S : Set (Domain n)) (hS : MeasurableSet S)
    (G : Domain n → Gradient n q) :
    (∫x,hsNormSq (fun i=>S.indicator (fun y=>G y i) x))=∫x in S,hsNormSq (G x) := by
  rw [hs_indicator_density,integral_indicator hS]

private theorem hs_add_bound {n q : ℕ} (A B : Gradient n q) :
    hsNormSq (fun i=>A i+B i)≤2*hsNormSq A+2*hsNormSq B := by
  have hEach (i : Fin n) : ‖A i+B i‖^2≤2*‖A i‖^2+2*‖B i‖^2 := by
    have H := sq_nonneg ‖A i-B i‖
    rw [norm_sub_sq_real] at H
    rw [norm_add_sq_real]
    linarith
  calc
    _≤∑i : Fin n,(2*‖A i‖^2+2*‖B i‖^2) := Finset.sum_le_sum (fun i _=>hEach i)
    _=_ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum];rfl

private theorem hs_sub_bound {n q : ℕ} (A B : Gradient n q) :
    hsNormSq (fun i=>A i-B i)≤2*hsNormSq A+2*hsNormSq B := by
  have hEach (i : Fin n) : ‖A i-B i‖^2≤2*‖A i‖^2+2*‖B i‖^2 := by
    have H := sq_nonneg ‖A i+B i‖
    rw [norm_add_sq_real] at H
    rw [norm_sub_sq_real]
    linarith
  calc
    _≤∑i : Fin n,(2*‖A i‖^2+2*‖B i‖^2) := Finset.sum_le_sum (fun i _=>hEach i)
    _=_ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum];rfl

/-- One actual Neumann operator produces genuine near/far class responses for every raw field and query, their global AE split and integrabilities, the actual near energy control, and the far local bound in terms of the same original output and input. -/
theorem effective_same_neumann_operator_near_far_density_split (n : ℕ) (hn : 2≤n) :
    ∀q : ℕ,
      let μ := volume.restrict (ball (0:Domain n) 1)
      let E : Gradient n q → Ambient (n*q) := fun G=>WithLp.toLp 2
        (fun k=>G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      let Z := fun (G : Domain n → Gradient n q) x i=>(ball (0:Domain n) 1).indicator (fun y=>G y i) x
      ∃T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
        ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀A,T (T A)=T A) ∧
        ∀(F : Domain n → Gradient n q) (hF : ∀i,MemLp (fun x=>F x i) 2 μ),
          let A := (memLp_hs_flatten F hF).toLp (fun x=>E (F x))
          let Q := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2
            (fun j : Fin q=>(T A) x (finProdFinEquiv (i,j)))
          let F₀ := Z F
          let Q₀ := Z Q
          ∃u : Domain n → Ambient q,MemW12 (ballDomain (0:Domain n) 1) u Q ∧
            (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
              MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
              Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ ∧
              Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i)) μ ∧
              (∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ)=
                ∫x,∑i : Fin n,inner ℝ (F x i) (Dψ x i) ∂μ) ∧
            HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1) (fun x i=>Q x i-F x i) (fun _=>0) ∧
            (∀i,MemLp (fun x=>F₀ x i) 2 volume) ∧ (∀i,MemLp (fun x=>Q₀ x i) 2 volume) ∧
            Integrable (fun x=>hsNormSq (F₀ x)) volume ∧ Integrable (fun x=>hsNormSq (Q₀ x)) volume ∧
            (∫x,hsNormSq (Q₀ x))≤∫x,hsNormSq (F₀ x) ∧
            ∀(a : Domain n) (R : ℝ),0<R →
              let B := ball a (256*R)
              let FN := fun x i=>B.indicator (fun y=>F y i) x
              let FF := fun x i=>F x i-FN x i
              let hN : ∀i,MemLp (fun x=>FN x i) 2 μ := fun i=>(hF i).indicator measurableSet_ball
              let hFar : ∀i,MemLp (fun x=>FF x i) 2 μ := fun i=>(hF i).sub (hN i)
              let AN := (memLp_hs_flatten FN hN).toLp (fun x=>E (FN x))
              let AF := (memLp_hs_flatten FF hFar).toLp (fun x=>E (FF x))
              let QN := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2
                (fun j : Fin q=>(T AN) x (finProdFinEquiv (i,j)))
              let QF := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2
                (fun j : Fin q=>(T AF) x (finProdFinEquiv (i,j)))
              let g := fun x=>hsNormSq (Z QN x)
              let h := fun x=>hsNormSq (Z QF x)
              (∀i,MemLp (fun x=>Z QN x i) 2 volume) ∧ (∀i,MemLp (fun x=>Z QF x i) 2 volume) ∧
              Integrable g volume ∧ Integrable h volume ∧
              Q₀ =ᵐ[volume] (fun x i=>Z QN x i+Z QF x i) ∧
              (∀ᵐx∂volume,hsNormSq (Q₀ x)≤2*g x+2*h x) ∧
              (∫x,g x)≤∫x in B,hsNormSq (F₀ x) ∧
              (∀x∈B,FF x=0) ∧
              ∀ᵐx∂volume.restrict (ball a R),h x≤
                2*(effectiveNeumannOffSupportConstant n : ℝ)*(volume.real B)⁻¹*((∫y in B,hsNormSq (Q₀ y))+(∫y in B,hsNormSq (F₀ y))) := by
  let C : ℝ := effectiveNeumannOffSupportConstant n
  have hC : 0 < C := effectiveNeumannOffSupportConstant_pos n
  have HT := effective_same_neumann_operator_all_ball_offSupport_bounds n hn
  intro q μ E Z
  obtain ⟨T,hNorm,hSelf,hIdem,Hresponse⟩ := HT q
  refine ⟨T,hNorm,hSelf,hIdem,?_⟩
  intro F hF A Q F₀ Q₀
  obtain ⟨u,hu,hEnergy,hNat,hEq,hQ₀,_HqueryOriginal⟩ := Hresponse F hF
  have hF₀ (i : Fin n) : MemLp (fun x=>F₀ x i) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr (hF i)
  have hIF₀ : Integrable (fun x=>hsNormSq (F₀ x)) volume :=
    integrable_finsetSum _ (fun i _=>(hF₀ i).integrable_norm_pow (by decide : (2:ℕ)≠0))
  have hIQ₀ : Integrable (fun x=>hsNormSq (Q₀ x)) volume :=
    integrable_finsetSum _ (fun i _=>(hQ₀ i).integrable_norm_pow (by decide : (2:ℕ)≠0))
  have hEnergy₀ : (∫x,hsNormSq (Q₀ x))≤∫x,hsNormSq (F₀ x) := by
    rw [integral_hs_indicator _ measurableSet_ball Q,integral_hs_indicator _ measurableSet_ball F]
    exact hEnergy
  refine ⟨u,hu,hNat,hEq,hF₀,hQ₀,hIF₀,hIQ₀,hEnergy₀,?_⟩
  intro a R hR B FN FF hN hFar AN AF QN QF g h
  obtain ⟨_uN,_huN,hEnergyN,_hNatN,_hEqN,hQN₀,_HqueryN⟩ := Hresponse FN hN
  obtain ⟨_uF,_huF,_hEnergyF,_hNatF,_hEqF,hQF₀,HqueryFar⟩ := Hresponse FF hFar
  have hIG : Integrable g volume :=
    integrable_finsetSum _ (fun i _=>(hQN₀ i).integrable_norm_pow (by decide : (2:ℕ)≠0))
  have hIH : Integrable h volume :=
    integrable_finsetSum _ (fun i _=>(hQF₀ i).integrable_norm_pow (by decide : (2:ℕ)≠0))
  have hEPoint (x : Domain n) : E (FF x)=E (F x)-E (FN x) := by ext k;rfl
  have hEF := memLp_hs_flatten F hF
  have hEN := memLp_hs_flatten FN hN
  have hEFF := memLp_hs_flatten FF hFar
  have hAF : AF=A-AN := by
    calc
      _=(hEF.sub hEN).toLp ((fun x=>E (F x))-(fun x=>E (FN x))) :=
        (MemLp.toLp_eq_toLp_iff hEFF (hEF.sub hEN)).mpr (Eventually.of_forall hEPoint)
      _=_ := MemLp.toLp_sub hEF hEN
  have hClass : T A=T AN+T AF := by rw [hAF,map_sub];abel
  have hClassAE : (T A : Domain n → Ambient (n*q)) =ᵐ[μ]
      (fun x=>(T AN) x+(T AF) x) := by
    rw [hClass]
    exact Lp.coeFn_add (T AN) (T AF)
  have hOriginalAE : Q =ᵐ[μ] (fun x i=>QN x i+QF x i) := by
    filter_upwards [hClassAE] with x hx
    funext i
    change WithLp.toLp 2 (fun j : Fin q=>(T A) x (finProdFinEquiv (i,j)))=QN x i+QF x i
    rw [hx]
    ext j
    rfl
  have hGlobalAE : Q₀ =ᵐ[volume] (fun x i=>Z QN x i+Z QF x i) := by
    have hConditional := (ae_restrict_iff' measurableSet_ball).mp hOriginalAE
    filter_upwards [hConditional] with x hx
    by_cases hIn : x∈ball (0:Domain n) 1
    · have H := hx hIn
      funext i
      simpa only [Q₀,Z,indicator_of_mem hIn] using congrFun H i
    · funext i
      simp only [Q₀,Z,indicator_of_notMem hIn,zero_add]
  have hDensity : ∀ᵐx∂volume,hsNormSq (Q₀ x)≤2*g x+2*h x := by
    filter_upwards [hGlobalAE] with x hx
    change hsNormSq (Q₀ x)≤2*hsNormSq (Z QN x)+2*hsNormSq (Z QF x)
    rw [hx]
    exact hs_add_bound (Z QN x) (Z QF x)
  have hNearField : Z FN=(fun x i=>B.indicator (fun y=>F₀ y i) x) := by
    funext x i
    by_cases hUnit : x∈ball (0:Domain n) 1 <;> by_cases hB : x∈B <;>
      simp only [Z,FN,F₀,Set.indicator,hUnit,hB,ite_true,ite_false]
  have hNearEnergy : (∫x,g x)≤∫x in B,hsNormSq (F₀ x) := by
    calc
      _=(∫x in ball (0:Domain n) 1,hsNormSq (QN x)) := integral_hs_indicator _ measurableSet_ball QN
      _≤(∫x in ball (0:Domain n) 1,hsNormSq (FN x)) := hEnergyN
      _=(∫x,hsNormSq (Z FN x)) := (integral_hs_indicator _ measurableSet_ball FN).symm
      _=(∫x,hsNormSq (fun i=>B.indicator (fun y=>F₀ y i) x)) := by rw [hNearField]
      _=_ := integral_hs_indicator B measurableSet_ball F₀
  have hFarZero (x : Domain n) (hx : x∈B) : FF x=0 := by
    funext i
    simp only [FF,FN,indicator_of_mem hx,sub_self,Pi.zero_apply]
  have hFarAE : ∀ᵐx∂volume,hsNormSq (Z QF x)≤2*hsNormSq (Q₀ x)+2*hsNormSq (Z QN x) := by
    filter_upwards [hGlobalAE] with x hx
    have H : Z QF x=(fun i=>Q₀ x i-Z QN x i) := by
      funext i
      have Hi := congrFun hx i
      rw [Hi]
      abel
    rw [H]
    exact hs_sub_bound (Q₀ x) (Z QN x)
  have hFarLocal : (∫x in B,h x)≤2*(∫x in B,hsNormSq (Q₀ x))+2*(∫x in B,g x) := by
    calc
      _≤∫x in B,2*hsNormSq (Q₀ x)+2*g x :=
        integral_mono_ae hIH.integrableOn ((hIQ₀.const_mul 2).add (hIG.const_mul 2)).integrableOn
          (hFarAE.filter_mono (ae_mono Measure.restrict_le_self))
      _=_ := by
        rw [integral_add (hIQ₀.integrableOn.const_mul 2) (hIG.integrableOn.const_mul 2),
          integral_const_mul,integral_const_mul]
  have hNearLocal : (∫x in B,g x)≤∫x,g x :=
    integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun x=>hsNormSq_nonneg (Z QN x)) hIG
  have hFarEnergy : (∫x in B,h x)≤2*((∫x in B,hsNormSq (Q₀ x))+(∫x in B,hsNormSq (F₀ x))) := by
    exact hFarLocal.trans ((add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (hNearLocal.trans hNearEnergy) (by norm_num : (0:ℝ)≤2))).trans_eq (by ring))
  have hFarInput : FF =ᵐ[volume.restrict (ball (0:Domain n) 1∩B)] (fun _=>(0:Gradient n q)) := by
    filter_upwards [ae_restrict_mem (measurableSet_ball.inter measurableSet_ball)] with x hx
    exact hFarZero x hx.2
  have hFarBound := HqueryFar a R hR hFarInput
  refine ⟨hQN₀,hQF₀,hIG,hIH,hGlobalAE,hDensity,hNearEnergy,hFarZero,?_⟩
  filter_upwards [hFarBound] with x hx
  calc
    h x≤C*(volume.real B)⁻¹*(∫y in B,h y) := hx
    _≤C*(volume.real B)⁻¹*(2*((∫y in B,hsNormSq (Q₀ y))+(∫y in B,hsNormSq (F₀ y)))) :=
      mul_le_mul_of_nonneg_left hFarEnergy (mul_nonneg hC.le (inv_nonneg.mpr ENNReal.toReal_nonneg))
    _=_ := by ring

/-- One actual Neumann operator produces genuine near/far class responses for every raw field and query, their global AE split and integrabilities, the actual near energy control, and the far local bound in terms of the same original output and input. -/
theorem exists_same_neumann_operator_near_far_density_split (n : ℕ) (hn : 2≤n) :
    ∃C : ℝ,0<C ∧ ∀q : ℕ,
      let μ := volume.restrict (ball (0:Domain n) 1)
      let E : Gradient n q → Ambient (n*q) := fun G=>WithLp.toLp 2
        (fun k=>G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      let Z := fun (G : Domain n → Gradient n q) x i=>(ball (0:Domain n) 1).indicator (fun y=>G y i) x
      ∃T : Lp (Ambient (n*q)) 2 μ →L[ℝ] Lp (Ambient (n*q)) 2 μ,
        ‖T‖≤1 ∧ IsSelfAdjoint T ∧ (∀A,T (T A)=T A) ∧
        ∀(F : Domain n → Gradient n q) (hF : ∀i,MemLp (fun x=>F x i) 2 μ),
          let A := (memLp_hs_flatten F hF).toLp (fun x=>E (F x))
          let Q := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2
            (fun j : Fin q=>(T A) x (finProdFinEquiv (i,j)))
          let F₀ := Z F
          let Q₀ := Z Q
          ∃u : Domain n → Ambient q,MemW12 (ballDomain (0:Domain n) 1) u Q ∧
            (∀ (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
              MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
              Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ ∧
              Integrable (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i)) μ ∧
              (∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ)=
                ∫x,∑i : Fin n,inner ℝ (F x i) (Dψ x i) ∂μ) ∧
            HolderToCK.WeakPoissonOn (ballDomain (0:Domain n) 1) (fun x i=>Q x i-F x i) (fun _=>0) ∧
            (∀i,MemLp (fun x=>F₀ x i) 2 volume) ∧ (∀i,MemLp (fun x=>Q₀ x i) 2 volume) ∧
            Integrable (fun x=>hsNormSq (F₀ x)) volume ∧ Integrable (fun x=>hsNormSq (Q₀ x)) volume ∧
            (∫x,hsNormSq (Q₀ x))≤∫x,hsNormSq (F₀ x) ∧
            ∀(a : Domain n) (R : ℝ),0<R →
              let B := ball a (256*R)
              let FN := fun x i=>B.indicator (fun y=>F y i) x
              let FF := fun x i=>F x i-FN x i
              let hN : ∀i,MemLp (fun x=>FN x i) 2 μ := fun i=>(hF i).indicator measurableSet_ball
              let hFar : ∀i,MemLp (fun x=>FF x i) 2 μ := fun i=>(hF i).sub (hN i)
              let AN := (memLp_hs_flatten FN hN).toLp (fun x=>E (FN x))
              let AF := (memLp_hs_flatten FF hFar).toLp (fun x=>E (FF x))
              let QN := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2
                (fun j : Fin q=>(T AN) x (finProdFinEquiv (i,j)))
              let QF := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2
                (fun j : Fin q=>(T AF) x (finProdFinEquiv (i,j)))
              let g := fun x=>hsNormSq (Z QN x)
              let h := fun x=>hsNormSq (Z QF x)
              (∀i,MemLp (fun x=>Z QN x i) 2 volume) ∧ (∀i,MemLp (fun x=>Z QF x i) 2 volume) ∧
              Integrable g volume ∧ Integrable h volume ∧
              Q₀ =ᵐ[volume] (fun x i=>Z QN x i+Z QF x i) ∧
              (∀ᵐx∂volume,hsNormSq (Q₀ x)≤2*g x+2*h x) ∧
              (∫x,g x)≤∫x in B,hsNormSq (F₀ x) ∧
              (∀x∈B,FF x=0) ∧
              ∀ᵐx∂volume.restrict (ball a R),h x≤
                2*C*(volume.real B)⁻¹*((∫y in B,hsNormSq (Q₀ y))+(∫y in B,hsNormSq (F₀ y))) := by
  exact ⟨(effectiveNeumannOffSupportConstant n : ℝ), effectiveNeumannOffSupportConstant_pos n,
    effective_same_neumann_operator_near_far_density_split n hn⟩

end StationaryHarmonicMaps.Analysis

end
