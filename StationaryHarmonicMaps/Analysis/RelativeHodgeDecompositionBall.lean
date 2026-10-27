module

public import StationaryHarmonicMaps.Analysis.RelativeHodgeAffine
public import StationaryHarmonicMaps.Analysis.CoexactHodgePowerPairingBall
public import StationaryHarmonicMaps.Analysis.HodgeEnergyIdentity
public import StationaryHarmonicMaps.Analysis.ZeroBoundaryLinearMap

/-!
# The same full relative Hodge decomposition on an arbitrary ball

The original unit-ball construction is transported with a length factor
on both potentials and the relative tensor, and no amplitude factor on
one-forms or displayed derivatives. The same actual harmonic remainder
retains a native primitive, all distribution tests and its zero divergence.
The tensor graph energy has the genuine physical squared-length weight.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

private theorem relative_memW12_const_smul {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (c : ℝ) :
    MemW12 Ω (fun x=>c • u x) (fun x i=>c • Du x i) := by
  have H := memW12Loc_continuousLinearMap hu.to_memW12Loc (c • ContinuousLinearMap.id ℝ (Ambient q))
  exact ⟨H.1,hu.2.1.const_smul c,fun i=>(hu.2.2 i).const_smul c⟩

/-- Original raw L2 data on every positive-radius ball produce one full
relative decomposition, actual native Dirichlet and coexact pairings,
its same harmonic-gradient remainder and the correct weighted tensor energy. -/
theorem exists_L2_relative_hodge_decomposition_ball {n q : ℕ} (hn : 2≤n)
    (a : Domain n) (R : ℝ) (hR : 0<R) (F : Domain n → Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball a R))) :
    ∃(f : Domain n → Ambient q) (Df : Domain n → Gradient n q)
      (b : Fin n → Fin n → Domain n → Ambient q)
      (Db : Fin n → Fin n → Domain n → Gradient n q)
      (P h : Domain n → Gradient n q) (g : Domain n → Ambient q),
      HasZeroBoundaryValues (ballDomain a R) f Df ∧
      MemW12 (ballDomain a R) g h ∧ (∫x in ball a R,g x)=0 ∧
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
      (∀ᵐx∂volume.restrict (ball a R),∀i,F x i=Df x i+P x i+h x i) ∧
      HolderToCK.WeakPoissonOn (ballDomain a R) h (fun _=>0) ∧
      (∀(j : Fin n) (ψ : Domain n → Ambient q),ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ⊆ball a R →
        IntegrableOn (fun x=>inner ℝ (h x j) (Laplacian.laplacian ψ x)) (ball a R) volume ∧
        (∫x in ball a R,inner ℝ (h x j) (Laplacian.laplacian ψ x))=0) ∧
      ((∫x in ball a R,hsNormSq (Df x))≤∫x in ball a R,hsNormSq (F x)) ∧
      ((∫x in ball a R,hsNormSq (P x))≤∫x in ball a R,hsNormSq (F x)) ∧
      ((∫x in ball a R,∑j : Fin n,∑i : Fin n,‖b i j x‖^2)+
        R^2*(∫x in ball a R,∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Db i j x k‖^2)≤
        (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)*R^2*(∫x in ball a R,hsNormSq (F x))) ∧
      MemW12 (ballDomain a R) (f+g) (fun x i=>Df x i+h x i) ∧
      (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        HasZeroBoundaryValues (ballDomain a R) ψ Dψ →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Df x i) (Dψ x i)) (ball a R) volume ∧
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i)) (ball a R) volume ∧
        (∫x in ball a R,∑i : Fin n,inner ℝ (Df x i) (Dψ x i))=
          ∫x in ball a R,∑i : Fin n,inner ℝ (F x i) (Dψ x i)) ∧
      (∀Q : Domain n → Gradient n q,
        (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball a R))) →
        (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
          MemW12 (ballDomain a R) ψ Dψ →
          (∫x in ball a R,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) →
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (P x i) (Q x i)) (ball a R) volume ∧
        IntegrableOn (fun x=>∑i : Fin n,inner ℝ (F x i) (Q x i)) (ball a R) volume ∧
        (∫x in ball a R,∑i : Fin n,inner ℝ (P x i) (Q x i))=
          ∫x in ball a R,∑i : Fin n,inner ℝ (F x i) (Q x i)) ∧
      ((∫x in ball a R,hsNormSq (Df x))+(∫x in ball a R,hsNormSq (P x))+
        (∫x in ball a R,hsNormSq (h x))=∫x in ball a R,hsNormSq (F x)) ∧
      (∫x in ball a R,hsNormSq (h x))≤∫x in ball a R,hsNormSq (F x) := by
  let μ := volume.restrict (ball a R)
  let U := fun x i=>F (a+R • x) i
  have hU (i : Fin n) : MemLp (fun x=>U x i) 2 (volume.restrict (ball (0:Domain n) 1)) := by
    simpa only [div_self hR.ne',sub_zero] using memLp_affineBall a (0:Domain n) hR R (hF i)
  obtain ⟨f₀,Df₀,b₀,Db₀,P₀,h₀,g₀,hf₀,hg₀,hMean₀,hb₀,hP₀,hSkew,hClosed,hDiv,hNormal,hNatural,
    hDecomp,hHLp,hHDiv,hHarm,hfEnergy,hPEnergy,hBEnergy,_hCore⟩ :=
    exists_L2_relative_hodge_decomposition_unitBall hn U hU
  let A := fun x : Domain n=>R⁻¹ • (x-a)
  let f := fun x=>R • f₀ (A x)
  let Df := fun x i=>Df₀ (A x) i
  let b := fun i j x=>R • b₀ i j (A x)
  let Db := fun i j x k=>Db₀ i j (A x) k
  let P := fun x i=>P₀ (A x) i
  let h := fun x i=>h₀ (A x) i
  let g := fun x=>R • g₀ (A x)
  have hf : HasZeroBoundaryValues (ballDomain a R) f Df := by
    have H := zeroBoundary_continuousLinearMap (hf₀.affineBall_pullback a (inv_pos.mpr hR))
      (R • ContinuousLinearMap.id ℝ (Ambient q))
    simpa only [one_div,inv_inv,zero_add,smul_apply,ContinuousLinearMap.id_apply,smul_smul,
      mul_inv_cancel₀ hR.ne',one_smul,f,Df,A] using H
  have hg : MemW12 (ballDomain a R) g h := by
    have H := relative_memW12_const_smul (hg₀.affineBall_pullback a (inv_pos.mpr hR)) R
    simpa only [one_div,inv_inv,zero_add,smul_smul,mul_inv_cancel₀ hR.ne',one_smul,g,h,A] using H
  have hb (i j : Fin n) : MemW12 (ballDomain a R) (b i j) (Db i j) := by
    have H := relative_memW12_const_smul ((hb₀ i j).affineBall_pullback a (inv_pos.mpr hR)) R
    simpa only [one_div,inv_inv,zero_add,smul_smul,mul_inv_cancel₀ hR.ne',one_smul,b,Db,A] using H
  have hP (i : Fin n) : MemLp (fun x=>P x i) 2 μ := by
    simpa only [one_div,inv_inv,zero_add,P,A] using memLp_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 (hP₀ i)
  have hMean : (∫x in ball a R,g x)=0 := by
    change (∫x in ball a R,R • g₀ (R⁻¹ • (x-a)))=0
    rw [integral_smul]
    have H := integral_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 g₀
    simp only [one_div,inv_inv,zero_add,inv_pow,hMean₀,smul_zero] at H
    rw [H,smul_zero]
  have hSkewBack : ∀ᵐx∂μ,∀i j,b i j x= -b j i x := by
    have H := ae_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 hSkew
    simp only [one_div,inv_inv,zero_add] at H
    filter_upwards [H] with x hx i j
    exact congrArg (fun z : Ambient q=>R • z) (hx i j) |>.trans (smul_neg _ _)
  have hClosedBack : ∀ᵐx∂μ,∀i j k,Db i j x k+Db j k x i+Db k i x j=0 := by
    simpa only [one_div,inv_inv,zero_add,Db,A] using ae_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 hClosed
  have hDivBack : ∀ᵐx∂μ,∀j,(∑i : Fin n,Db i j x i)=P x j := by
    simpa only [one_div,inv_inv,zero_add,Db,P,A] using ae_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 hDiv
  have hNormalBack := native_normal_tensor_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 b₀ P₀ hNormal
  simp only [one_div,inv_inv,zero_add] at hNormalBack
  have hNaturalBack : ∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 (ballDomain a R) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (P x i) (Dψ x i)) (ball a R) volume ∧
      (∫x in ball a R,∑i : Fin n,inner ℝ (P x i) (Dψ x i))=0 := by
    have H := natural_solenoidal_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 P₀
      (fun ψ Dψ hψ=>(hNatural ψ Dψ hψ).2)
    simp only [one_div,inv_inv,zero_add] at H
    intro ψ Dψ hψ
    exact ⟨integrable_finsetSum _ (fun i _=>HolderToCK.integrable_inner_of_memLp_two (hP i) (hψ.2.2 i)),H ψ Dψ hψ⟩
  have hUA (x : Domain n) : U (A x)=F x := by
    funext i
    simp only [U,A,smul_smul,mul_inv_cancel₀ hR.ne',one_smul,add_sub_cancel]
  have hDecompBack : ∀ᵐx∂μ,∀i,F x i=Df x i+P x i+h x i := by
    have H := ae_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 hDecomp
    simp only [one_div,inv_inv,zero_add] at H
    filter_upwards [H, hDivBack] with x hx hd i
    have HE := hx i
    change U (A x) i=Df x i+(∑j : Fin n,Db j i x j)+h x i at HE
    simpa only [hUA,hd] using HE
  have hZeroBound : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),‖(0:Ambient q)‖≤(0:ℝ)*hsNormSq (h₀ x) :=
    Eventually.of_forall fun _=>by simp
  have Hweak := hHDiv.affineBall_pullback hg₀ 0 hZeroBound a (inv_pos.mpr hR)
  have HweakZero : HolderToCK.WeakPoissonOn (ballDomain a R)
      (fun x i=>R⁻¹ • h₀ (A x) i) (fun _=>(0:Ambient q)) := by
    simpa only [one_div,inv_inv,zero_add,smul_zero,A] using Hweak
  have hHDivBack : HolderToCK.WeakPoissonOn (ballDomain a R) h (fun _=>0) := by
    have H := weakPoissonOn_zero_const_smul HweakZero R
    simpa only [smul_smul,mul_inv_cancel₀ hR.ne',one_smul,h] using H
  have hHarmBack := coefficient_harmonic_vector_tests_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 h₀ hHarm
  simp only [one_div,inv_inv,zero_add] at hHarmBack
  have hScale (V : Domain n → ℝ) : (∫x,V (A x) ∂μ)=R^n*(∫x in ball (0:Domain n) 1,V x) := by
    simpa only [one_div,inv_inv,zero_add,inv_pow,smul_eq_mul,A] using
      integral_affineBall (0:Domain n) a (inv_pos.mpr hR) 1 V
  have hFScale : (∫x,hsNormSq (F x) ∂μ)=R^n*(∫x in ball (0:Domain n) 1,hsNormSq (U x)) := by
    simpa only [hUA] using hScale (fun x=>hsNormSq (U x))
  have hfEnergyBack : (∫x,hsNormSq (Df x) ∂μ)≤∫x,hsNormSq (F x) ∂μ := by
    rw [hScale (fun x=>hsNormSq (Df₀ x)),hFScale]
    exact mul_le_mul_of_nonneg_left hfEnergy (pow_nonneg hR.le n)
  have hPEnergyBack : (∫x,hsNormSq (P x) ∂μ)≤∫x,hsNormSq (F x) ∂μ := by
    rw [hScale (fun x=>hsNormSq (P₀ x)),hFScale]
    exact mul_le_mul_of_nonneg_left hPEnergy (pow_nonneg hR.le n)
  have hBScale : (∫x,∑j : Fin n,∑i : Fin n,‖b i j x‖^2 ∂μ)=
      R^2*(R^n*(∫x in ball (0:Domain n) 1,∑j : Fin n,∑i : Fin n,‖b₀ i j x‖^2)) := by
    simp only [b,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,←Finset.mul_sum]
    rw [integral_const_mul,hScale (fun x=>∑j : Fin n,∑i : Fin n,‖b₀ i j x‖^2)]
  have hDBScale : (∫x,∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Db i j x k‖^2 ∂μ)=
      R^n*(∫x in ball (0:Domain n) 1,∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Db₀ i j x k‖^2) :=
    hScale (fun x=>∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Db₀ i j x k‖^2)
  have hBEnergyBack : (∫x,∑j : Fin n,∑i : Fin n,‖b i j x‖^2 ∂μ)+
      R^2*(∫x,∑j : Fin n,∑k : Fin n,∑i : Fin n,‖Db i j x k‖^2 ∂μ)≤
      (4*(2:ℝ)^(n+1)+2*(n:ℝ)+2)*R^2*(∫x,hsNormSq (F x) ∂μ) := by
    rw [hBScale,hDBScale,hFScale]
    have H := mul_le_mul_of_nonneg_left hBEnergy (mul_nonneg (sq_nonneg R) (pow_nonneg hR.le n))
    nlinarith only [H]
  have hComp : MemW12 (ballDomain a R) (f+g) (fun x i=>Df x i+h x i) :=
    ⟨hasWeakGradient_add hf.1.1 hg.1,hf.1.2.1.add hg.2.1,fun i=>(hf.1.2.2 i).add (hg.2.2 i)⟩
  have hCompDecomp : ∀ᵐx∂μ,∀i,F x i=(Df x i+h x i)+P x i := by
    filter_upwards [hDecompBack] with x hx i
    rw [hx i]
    abel
  have hPTests := fun Q hQ hQN=>native_coexact_pairing_of_gradient_complement (ballDomain a R)
    F P (f+g) (fun x i=>Df x i+h x i) hComp hF hP hCompDecomp Q hQ hQN
  have hSmoothProjection (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
      (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆ball a R) :
      (∫x in ball a R,∑i : Fin n,inner ℝ (Df x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))=
        ∫x in ball a R,∑i : Fin n,inner ℝ (F x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    let Dψ := fun x i=>fderiv ℝ ψ x (EuclideanSpace.single i 1)
    have hψW := memW12_ball_of_ambient_c1 a R ψ (hψ.of_le (by simp))
    have hDI := integrable_finsetSum Finset.univ (fun i _=>
      HolderToCK.integrable_inner_of_memLp_two (hf.1.2.2 i) (hψW.2.2 i))
    obtain ⟨hPI,hPZero⟩ := hNaturalBack ψ Dψ hψW
    obtain ⟨hHI,_hZI,hHZero⟩ := hHDivBack.2 ψ hψ hc hs
    simp only [inner_zero_left,integral_zero,neg_zero] at hHZero
    have hPoint : (fun x=>∑i : Fin n,inner ℝ (F x i) (Dψ x i))=ᵐ[μ]
        (fun x=>(∑i : Fin n,inner ℝ (Df x i) (Dψ x i))+
          (∑i : Fin n,inner ℝ (P x i) (Dψ x i))+(∑i : Fin n,inner ℝ (h x i) (Dψ x i))) := by
      filter_upwards [hDecompBack] with x hx
      simp only [hx,inner_add_left,Finset.sum_add_distrib]
    change Integrable (fun x=>∑i : Fin n,inner ℝ (Df x i) (Dψ x i)) μ at hDI
    change Integrable (fun x=>∑i : Fin n,inner ℝ (P x i) (Dψ x i)) μ at hPI
    change Integrable (fun x=>∑i : Fin n,inner ℝ (h x i) (Dψ x i)) μ at hHI
    change (∫x,∑i : Fin n,inner ℝ (P x i) (Dψ x i) ∂μ)=0 at hPZero
    change (∫x,∑i : Fin n,inner ℝ (h x i) (Dψ x i) ∂μ)=0 at hHZero
    change (∫x,∑i : Fin n,inner ℝ (Df x i) (Dψ x i) ∂μ)=
      ∫x,∑i : Fin n,inner ℝ (F x i) (Dψ x i) ∂μ
    have HI1 := integral_add (μ:=μ) (hDI.add hPI) hHI
    have HI2 := integral_add (μ:=μ) hDI hPI
    simp only [Pi.add_apply] at HI1 HI2
    rw [integral_congr_ae hPoint,HI1,HI2,hPZero,hHZero,add_zero,add_zero]
  have hDfTests := fun ψ Dψ hψ=>gradient_pairing_eq_on_zeroBoundary_of_smooth (ballDomain a R)
    Df F hf.1.2.2 hF hSmoothProjection (v:=ψ) (Dv:=Dψ) hψ
  have hDfSelf : (∫x,hsNormSq (Df x) ∂μ)=∫x,∑i : Fin n,inner ℝ (F x i) (Df x i) ∂μ := by
    simpa only [μ,ballDomain,hsNormSq,real_inner_self_eq_norm_sq] using (hDfTests f Df hf).2.2
  have hPSelf : (∫x,hsNormSq (P x) ∂μ)=∫x,∑i : Fin n,inner ℝ (F x i) (P x i) ∂μ := by
    simpa only [μ,ballDomain,hsNormSq,real_inner_self_eq_norm_sq] using
      (hPTests P hP (fun ψ Dψ hψ=>(hNaturalBack ψ Dψ hψ).2)).2.2
  have hOrth : (∫x,∑i : Fin n,inner ℝ (Df x i) (P x i) ∂μ)=0 := by
    simpa only [real_inner_comm] using (hNaturalBack f Df hf.1).2
  obtain ⟨_hHLp,_hHI,hPyth,hHEnergy⟩ := hs_residual_energy_identity_of_projection_pairings μ F Df P h hF hf.1.2.2 hP
    hDecompBack hDfSelf hPSelf hOrth
  exact ⟨f,Df,b,Db,P,h,g,hf,hg,hMean,hb,hP,hSkewBack,hClosedBack,hDivBack,hNormalBack,
    hNaturalBack,hDecompBack,hHDivBack,hHarmBack,hfEnergyBack,hPEnergyBack,hBEnergyBack,hComp,hDfTests,hPTests,hPyth,hHEnergy⟩

end StationaryHarmonicMaps.Analysis

end
