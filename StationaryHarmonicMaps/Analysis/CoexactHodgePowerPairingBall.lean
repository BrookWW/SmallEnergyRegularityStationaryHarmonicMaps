module

public import StationaryHarmonicMaps.Analysis.CoexactNativeDualTestBall
public import StationaryHarmonicMaps.Analysis.CoexactFrameCutoffPairing

/-!
# Actual relative coexact frame-cutoff power pairings on arbitrary balls

Affine transport of the actual unit-ball relative decomposition gives
the original field's closed normal coexact tensor and genuine native
gradient complement on each positive-radius ball. The original natural
coexact field supplies its power dual, and the literal native frame
product gives the compensated pairing on that same query ball.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem memW12_const_smul_for_coexact {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (c : ℝ) :
    MemW12 Ω (fun x=>c • u x) (fun x i=>c • Du x i) := by
  have H := memW12Loc_continuousLinearMap hu.to_memW12Loc
    (c • ContinuousLinearMap.id ℝ (Ambient q))
  exact ⟨H.1,hu.2.1.const_smul c,fun i=>(hu.2.2 i).const_smul c⟩

/-- Every original L2 field on a positive-radius ball has an actual
closed normal relative coexact component, a native gradient complement,
and its pairing identity against every original natural solenoidal L2
field on that ball. -/
theorem exists_relative_coexact_native_pairing_ball {n q : ℕ} (hn : 2≤n)
    (a : Domain n) (R : ℝ) (hR : 0<R)
    (F : Domain n → Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball a R))) :
    ∃(b : Fin n → Fin n → Domain n → Ambient q)
      (Db : Fin n → Fin n → Domain n → Gradient n q)
      (P : Domain n → Gradient n q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
      MemW12 (ballDomain a R) u Du ∧
      (∀i j,MemW12 (ballDomain a R) (b i j) (Db i j)) ∧
      (∀i,MemLp (fun x=>P x i) 2 (volume.restrict (ball a R))) ∧
      (∀ᵐx∂volume.restrict (ball a R),∀i j,b i j x= -b j i x) ∧
      (∀ᵐx∂volume.restrict (ball a R),∀i j k,Db i j x k+Db j k x i+Db k i x j=0) ∧
      (∀ᵐx∂volume.restrict (ball a R),∀j,(∑i : Fin n,Db i j x i)=P x j) ∧
      (∀(j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain a R) ψ Dψ →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (b i j x) (Dψ x i)) (ball a R) volume ∧
        IntegrableOn (fun x=>inner ℝ (P x j) (ψ x)) (ball a R) volume ∧
        (∫x in ball a R,∑i : Fin n,inner ℝ (b i j x) (Dψ x i))=
          -(∫x in ball a R,inner ℝ (P x j) (ψ x))) ∧
      (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain a R) ψ Dψ →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (P x i) (Dψ x i)) (ball a R) volume ∧
        (∫x in ball a R,∑i : Fin n,inner ℝ (P x i) (Dψ x i))=0) ∧
      (∀ᵐx∂volume.restrict (ball a R),∀i,F x i=Du x i+P x i) ∧
      ((∫x in ball a R,hsNormSq (P x))≤∫x in ball a R,hsNormSq (F x)) ∧
      ∀Q : Domain n → Gradient n q,
        (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball a R))) →
        (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain a R) ψ Dψ →
          (∫x in ball a R,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (P x i) (Q x i)) (ball a R) volume ∧
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (F x i) (Q x i)) (ball a R) volume ∧
        (∫x in ball a R,∑i : Fin n,inner ℝ (P x i) (Q x i))=
          ∫x in ball a R,∑i : Fin n,inner ℝ (F x i) (Q x i) := by
  let μ := volume.restrict (ball a R)
  let U := fun x i=>F (a+R • x) i
  have hU (i : Fin n) : MemLp (fun x=>U x i) 2
      (volume.restrict (ball (0:Domain n) 1)) := by
    simpa only [div_self hR.ne',sub_zero] using memLp_affineBall a (0:Domain n) hR R (hF i)
  obtain ⟨b₀,Db₀,P₀,u₀,Du₀,hu₀,hb₀,hP₀,hSkew,hClosed,hDiv,hNormal,hNatural,hDecomp,hEnergy,_hPair⟩ :=
    exists_relative_coexact_native_pairing_unitBall hn U hU
  let A := fun x : Domain n=>R⁻¹ • (x-a)
  let b := fun i j x=>R • b₀ i j (A x)
  let Db := fun i j x k=>Db₀ i j (A x) k
  let P := fun x i=>P₀ (A x) i
  let u := fun x=>R • u₀ (A x)
  let Du := fun x i=>Du₀ (A x) i
  have hu : MemW12 (ballDomain a R) u Du := by
    have H := memW12_const_smul_for_coexact (hu₀.affineBall_pullback a (inv_pos.mpr hR)) R
    simpa only [one_div,inv_inv,zero_add,smul_smul,mul_inv_cancel₀ hR.ne',one_smul,u,Du,A] using H
  have hb (i j : Fin n) : MemW12 (ballDomain a R) (b i j) (Db i j) := by
    have H := memW12_const_smul_for_coexact ((hb₀ i j).affineBall_pullback a (inv_pos.mpr hR)) R
    simpa only [one_div,inv_inv,zero_add,smul_smul,mul_inv_cancel₀ hR.ne',one_smul,b,Db,A] using H
  have hP (i : Fin n) : MemLp (fun x=>P x i) 2 μ := by
    simpa only [one_div,inv_inv,zero_add,P,A] using
      memLp_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 (hP₀ i)
  have hSkewBack : ∀ᵐx∂μ,∀i j,b i j x= -b j i x := by
    have H := ae_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 hSkew
    simp only [one_div,inv_inv,zero_add] at H
    filter_upwards [H] with x hx i j
    exact congrArg (fun z : Ambient q=>R • z) (hx i j) |>.trans (smul_neg _ _)
  have hClosedBack : ∀ᵐx∂μ,∀i j k,Db i j x k+Db j k x i+Db k i x j=0 := by
    simpa only [one_div,inv_inv,zero_add,Db,A] using
      ae_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 hClosed
  have hDivBack : ∀ᵐx∂μ,∀j,(∑i : Fin n,Db i j x i)=P x j := by
    simpa only [one_div,inv_inv,zero_add,Db,P,A] using
      ae_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 hDiv
  have hNormalBack : ∀(j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain a R) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (b i j x) (Dψ x i)) (ball a R) volume ∧
      IntegrableOn (fun x=>inner ℝ (P x j) (ψ x)) (ball a R) volume ∧
      (∫x in ball a R,∑i : Fin n,inner ℝ (b i j x) (Dψ x i))=
        -(∫x in ball a R,inner ℝ (P x j) (ψ x)) := by
    simpa only [one_div,inv_inv,zero_add,b,P,A] using
      native_normal_tensor_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 b₀ P₀ hNormal
  have hNaturalBack : ∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain a R) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (P x i) (Dψ x i)) (ball a R) volume ∧
      (∫x in ball a R,∑i : Fin n,inner ℝ (P x i) (Dψ x i))=0 := by
    have H := natural_solenoidal_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 P₀
      (fun ψ Dψ hψ=>(hNatural ψ Dψ hψ).2)
    simp only [one_div,inv_inv,zero_add] at H
    intro ψ Dψ hψ
    exact ⟨integrable_finsetSum Finset.univ (fun i _=>
      HolderToCK.integrable_inner_of_memLp_two (hP i) (hψ.2.2 i)),H ψ Dψ hψ⟩
  have hUA (x : Domain n) : U (R⁻¹ • (x-a))=F x := by
    funext i
    simp only [U,smul_smul,mul_inv_cancel₀ hR.ne',one_smul,add_sub_cancel]
  have hDecompBack : ∀ᵐx∂μ,∀i,F x i=Du x i+P x i := by
    have H := ae_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 hDecomp
    simpa only [one_div,inv_inv,zero_add,hUA,Du,P,A] using H
  have hPScale : (∫x,hsNormSq (P x) ∂μ)=R^n*(∫x in ball (0:Domain n) 1,hsNormSq (P₀ x)) := by
    simpa only [one_div,inv_inv,zero_add,inv_pow,smul_eq_mul,P,A] using
      integral_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 (fun x=>hsNormSq (P₀ x))
  have hFScale : (∫x,hsNormSq (F x) ∂μ)=R^n*(∫x in ball (0:Domain n) 1,hsNormSq (U x)) := by
    simpa only [one_div,inv_inv,zero_add,inv_pow,smul_eq_mul,hUA] using
      integral_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 (fun x=>hsNormSq (U x))
  have hEnergyBack : (∫x,hsNormSq (P x) ∂μ)≤∫x,hsNormSq (F x) ∂μ := by
    rw [hPScale,hFScale]
    exact mul_le_mul_of_nonneg_left hEnergy (pow_nonneg hR.le n)
  refine ⟨b,Db,P,u,Du,hu,hb,hP,hSkewBack,hClosedBack,hDivBack,hNormalBack,
    hNaturalBack,hDecompBack,hEnergyBack,?_⟩
  intro Q hQ hQNatural
  exact native_coexact_pairing_of_gradient_complement (ballDomain a R) F P u Du hu
    hF hP hDecompBack Q hQ hQNatural

/-- The actual relative Hodge coexact component of the original frame-cutoff
field has a genuine closed normal native power-dual tensor, and its exact
power moment equals the compensated frame derivative pairing. -/
theorem exists_coexact_hodge_power_frame_pairing_ball
    (n : ℕ) (hn : 2≤n) (s : ℝ) (hsOne : 1<s) (hsTwo : s<2) :
    ∃C : ℝ,0<C ∧ ∀m q : ℕ,
      ∀(a : Domain n) (R : ℝ),0<R →
      ∀(p : Domain n → Ambient m) (Dp : Domain n → Gradient n m),
      MemW12 (ballDomain a R) p Dp →
      ∀M : ℝ,(∀ᵐx∂volume.restrict (ball a R),‖p x‖≤M) →
      ∀L : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q),
      ∀(v : Domain n → Ambient q) (Dv : Domain n → Gradient n q),
      HasZeroBoundaryValues (ballDomain a R) v Dv →
      ∀N : ℝ,(∀ᵐx∂volume.restrict (ball a R),‖v x‖≤N) →
      ∀(x₀ : Domain n) (t : ℝ),0<t → ball x₀ t⊆ball a R → ∀z : Ambient q,
      let μ := volume.restrict (ball x₀ t)
      let r := s/(s-1)
      ∃(b : Fin n → Fin n → Domain n → Ambient q)
        (Db : Fin n → Fin n → Domain n → Gradient n q)
        (P : Domain n → Gradient n q)
        (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
        (c : Fin n → Fin n → Domain n → Ambient q)
        (Dc : Fin n → Fin n → Domain n → Gradient n q)
        (Q : Domain n → Gradient n q),
        MemW12 (ballDomain x₀ t) u Du ∧
        (∀i j,MemW12 (ballDomain x₀ t) (b i j) (Db i j)) ∧
        (∀i,MemLp (fun x=>P x i) 2 μ) ∧
        (∀ᵐx∂μ,∀i j,b i j x= -b j i x) ∧
        (∀ᵐx∂μ,∀i j k,Db i j x k+Db j k x i+Db k i x j=0) ∧
        (∀ᵐx∂μ,∀j,(∑i : Fin n,Db i j x i)=P x j) ∧
        (∀(j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain x₀ t) ψ Dψ →
          Integrable (fun x=>∑i : Fin n,inner ℝ (b i j x) (Dψ x i)) μ ∧
          Integrable (fun x=>inner ℝ (P x j) (ψ x)) μ ∧
          (∫x,∑i : Fin n,inner ℝ (b i j x) (Dψ x i) ∂μ)=
            -(∫x,inner ℝ (P x j) (ψ x) ∂μ)) ∧
        (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain x₀ t) ψ Dψ →
          Integrable (fun x=>∑i : Fin n,inner ℝ (P x i) (Dψ x i)) μ ∧
          (∫x,∑i : Fin n,inner ℝ (P x i) (Dψ x i) ∂μ)=0) ∧
        (∀ᵐx∂μ,∀i,L (p x) (Dv x i)=Du x i+P x i) ∧
        ((∫x,hsNormSq (P x) ∂μ)≤
          ∫x,hsNormSq (fun i=>L (p x) (Dv x i)) ∂μ) ∧
        (∀i j,MemW12 (ballDomain x₀ t) (c i j) (Dc i j)) ∧
        (∀i,MemLp (fun x=>Q x i) 2 μ) ∧
        (∀ᵐx∂μ,∀i j,c i j x= -c j i x) ∧
        (∀ᵐx∂μ,∀i j k,Dc i j x k+Dc j k x i+Dc k i x j=0) ∧
        (∀ᵐx∂μ,∀j,(∑i : Fin n,Dc i j x i)=Q x j) ∧
        (∀(j : Fin n) (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain x₀ t) ψ Dψ →
          Integrable (fun x=>∑i : Fin n,inner ℝ (c i j x) (Dψ x i)) μ ∧
          Integrable (fun x=>inner ℝ (Q x j) (ψ x)) μ ∧
          (∫x,∑i : Fin n,inner ℝ (c i j x) (Dψ x i) ∂μ)=
            -(∫x,inner ℝ (Q x j) (ψ x) ∂μ)) ∧
        (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain x₀ t) ψ Dψ →
          Integrable (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) μ ∧
          (∫x,∑i : Fin n,inner ℝ (Q x i) (Dψ x i) ∂μ)=0) ∧
        ((∫x,∑j : Fin n,∑i : Fin n,‖c i j x‖^2 ∂μ)+
          t^2*(∫x,∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Dc i j x k‖^2 ∂μ)≤
            (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)*t^2*(∫x,hsNormSq (Q x) ∂μ)) ∧
        MemLp (fun x=>WithLp.toLp 2 (fun k : Fin (n*q)=>
          Q x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) (ENNReal.ofReal r) μ ∧
        Integrable (fun x=>∑i : Fin n,inner ℝ (P x i) (Q x i)) μ ∧
        Integrable (fun x=>∑i : Fin n,inner ℝ (L (p x) (Dv x i)) (Q x i)) μ ∧
        Integrable (fun x=>∑i : Fin n,inner ℝ (L (Dp x i) (v x-z)) (Q x i)) μ ∧
        Integrable (fun x=>(hsNormSq (P x))^(s/2)) μ ∧
        Integrable (fun x=>(hsNormSq (Q x))^(r/2)) μ ∧
        (∫x,∑i : Fin n,inner ℝ (P x i) (Q x i) ∂μ)=
          ∫x,∑i : Fin n,inner ℝ (L (p x) (Dv x i)) (Q x i) ∂μ ∧
        (∫x,∑i : Fin n,inner ℝ (P x i) (Q x i) ∂μ)=
          -(∫x,∑i : Fin n,inner ℝ (L (Dp x i) (v x-z)) (Q x i) ∂μ) ∧
        (∫x,∑i : Fin n,inner ℝ (P x i) (Q x i) ∂μ)=
          ∫x,(hsNormSq (P x))^(s/2) ∂μ ∧
        (∫x,∑i : Fin n,inner ℝ (L (p x) (Dv x i)) (Q x i) ∂μ)=
          ∫x,(hsNormSq (P x))^(s/2) ∂μ ∧
        (∫x,(hsNormSq (P x))^(s/2) ∂μ)=
          -(∫x,∑i : Fin n,inner ℝ (L (Dp x i) (v x-z)) (Q x i) ∂μ) ∧
        (∫x,(hsNormSq (Q x))^(r/2) ∂μ)≤C*(∫x,(hsNormSq (P x))^(s/2) ∂μ) := by
  obtain ⟨C,hC,hDual⟩ := exists_native_coexact_dual_test_ball n hn s hsOne hsTwo
  refine ⟨C,hC,?_⟩
  intro m q a R hR p Dp hp M hpBound L v Dv hv N hvBound x₀ t ht hSub z μ r
  let F := fun x i=>L (p x) (Dv x i)
  have hF (i : Fin n) : MemLp (fun x=>F x i) 2 μ :=
    (memLp_bounded_native_frame_columns (ballDomain a R) p Dp hp M hpBound L Dv
      hv.1.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)
  obtain ⟨b,Db,P,u,Du,hu,hb,hP,hSkew,hClosed,hDiv,hNormal,hNatural,hDecomp,hEnergy,hPair⟩ :=
    exists_relative_coexact_native_pairing_ball hn x₀ t ht F hF
  obtain ⟨c,Dc,Q,hc,hQ,hCSkew,hCClosed,hCDiv,hCNormal,hQNatural,hCH1,hQr,
    hPQI,hPI,hQI,hPower,hMoment⟩ :=
    hDual q x₀ t ht P hP (fun ψ Dψ hψ=>(hNatural ψ Dψ hψ).2)
  obtain ⟨_hPQI',hFQI,hPairEq⟩ := hPair Q hQ (fun ψ Dψ hψ=>(hQNatural ψ Dψ hψ).2)
  obtain ⟨_hF',_hA,hFQI',hAQI,hComp⟩ :=
    native_frame_cutoff_solenoidal_pairing_ball a R hR p Dp hp M hpBound L v Dv hv N hvBound
      x₀ t hSub z Q hQ (fun ψ Dψ hψ=>(hQNatural ψ Dψ hψ).2)
  have hFPower : (∫x,∑i : Fin n,inner ℝ (F x i) (Q x i) ∂μ)=
      ∫x,(hsNormSq (P x))^(s/2) ∂μ := hPairEq.symm.trans hPower
  refine ⟨b,Db,P,u,Du,c,Dc,Q,hu,hb,hP,hSkew,hClosed,hDiv,hNormal,hNatural,
    hDecomp,hEnergy,hc,hQ,hCSkew,hCClosed,hCDiv,hCNormal,hQNatural,hCH1,hQr,
    hPQI,hFQI,hAQI,hPI,hQI,hPairEq,hPairEq.trans hComp,hPower,hFPower,?_,hMoment⟩
  exact hFPower.symm.trans hComp

end StationaryHarmonicMaps.Analysis

end
