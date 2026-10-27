/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.SameNeumannDensitySplit
public import StationaryHarmonicMaps.Analysis.EffectiveCoulombConstants
public import StationaryHarmonicMaps.Analysis.NeumannGradientUniqueness
public import StationaryHarmonicMaps.Analysis.GeometricRpowIteration

/-!
# Full power growth for the original native Neumann response

The same genuine near/far operator split gives a radius recurrence for the
original, unnormalized energy. Real-power iteration then controls all
centers and all positive radii. Native uniqueness identifies this response
with any original native Neumann graph and its displayed weak gradient.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem integral_zero_extended_hs_ball {n q : ℕ}
    (F : Domain n → Gradient n q) (a : Domain n) (r : ℝ) :
    (∫x in ball a r,hsNormSq (fun i=>(ball (0 : Domain n) 1).indicator (fun y=>F y i) x))=
      ∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x) := by
  classical
  have hPoint : (fun x=>hsNormSq (fun i=>(ball (0 : Domain n) 1).indicator (fun y=>F y i) x))=
      (ball (0 : Domain n) 1).indicator (fun x=>hsNormSq (F x)) := by
    funext x
    by_cases hx : x∈ball (0 : Domain n) 1
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,hsNormSq,norm_zero,zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero]
  rw [hPoint,setIntegral_indicator measurableSet_ball]

private theorem integral_zero_extended_hs {n q : ℕ} (F : Domain n → Gradient n q) :
    (∫x,hsNormSq (fun i=>(ball (0 : Domain n) 1).indicator (fun y=>F y i) x))=
      ∫x in ball (0 : Domain n) 1,hsNormSq (F x) := by
  classical
  have hPoint : (fun x=>hsNormSq (fun i=>(ball (0 : Domain n) 1).indicator (fun y=>F y i) x))=
      (ball (0 : Domain n) 1).indicator (fun x=>hsNormSq (F x)) := by
    funext x
    by_cases hx : x∈ball (0 : Domain n) 1
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,hsNormSq,norm_zero,zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero]
  rw [hPoint,integral_indicator measurableSet_ball]

private theorem same_center_volume_ratio {n : ℕ} (a : Domain n) (r θ : ℝ)
    (hr : 0<r) (hθ : 0<θ) :
    volume.real (ball a (θ*r))*(volume.real (ball a r))⁻¹=θ^n := by
  have hV := (HolderToCK.ball_volume_real_pos (0 : Domain n) (by norm_num : (0:ℝ)<1)).ne'
  rw [HolderToCK.ball_volume_real a (mul_pos hθ hr),HolderToCK.ball_volume_real a hr,mul_pow]
  field_simp [pow_ne_zero n hr.ne',hV]

@[expose] noncomputable def nativeNeumannPowerConstant (n : ℕ) (ν θ : ℝ) : ℝ :=
  let C : ℝ := effectiveNeumannOffSupportConstant n
  1 + (1 + (2 + 4 * C) / (θ ^ ν - 4 * C * θ ^ n)) / θ ^ ν

@[expose] def effectiveNativeNeumannPowerConstant (n : ℕ) : ℚ :=
  let C : ℚ := effectiveNeumannOffSupportConstant n
  let θ := EffectiveCoulomb.naturalPowerScale (2 * C)
  1 + (1 + (2 + 4 * C) / (θ ^ (n - 1) - 4 * C * θ ^ n)) / θ ^ (n - 1)

theorem effectiveNativeNeumannPowerConstant_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < effectiveNativeNeumannPowerConstant n := by
  let C : ℚ := effectiveNeumannOffSupportConstant n
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hθ := EffectiveCoulomb.naturalPowerScale_pos (show 0 ≤ 2 * C by positivity)
  have hgap := EffectiveCoulomb.naturalPowerScale_gap n hn (show 0 ≤ 2 * C by positivity)
  have hgap' : 0 < EffectiveCoulomb.naturalPowerScale (2 * C) ^ (n - 1) -
      4 * C * EffectiveCoulomb.naturalPowerScale (2 * C) ^ n := by
    convert hgap using 1; ring
  unfold effectiveNativeNeumannPowerConstant
  change 0 < 1 + (1 + (2 + 4 * C) / _) / _
  positivity

/-- Original full truncated power growth of raw forcing gives full truncated
growth of the same original native Neumann gradient for every exponent below dimension. -/
theorem native_neumann_full_real_power_growth_at_scale (n : ℕ) (hn : 2≤n)
    (ν : ℝ) (hν : 0≤ν) (_hνn : ν<(n:ℝ))
    (θ : ℝ) (hθ : 0 < θ) (hθCap : θ ≤ 1 / 256)
    (hSmall : 4 * (effectiveNeumannOffSupportConstant n : ℝ) * θ ^ ((n : ℝ) - ν) ≤ 1 / 2) :
    ∀(q : ℕ) (u : Domain n → Ambient q)
      (Du F : Domain n → Gradient n q) (K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      0≤K →
      (∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))≤K*r^ν) →
      (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Du x i) (Dψ x i))=
          ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (F x i) (Dψ x i)) →
      ∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤nativeNeumannPowerConstant n ν θ*K*r^ν := by
  let C : ℝ := effectiveNeumannOffSupportConstant n
  have hC : 0 < C := effectiveNeumannOffSupportConstant_pos n
  have HT := effective_same_neumann_operator_near_far_density_split n hn
  have hθOne : θ<1 := lt_of_le_of_lt hθCap (by norm_num)
  have hPow : θ^n=θ^((n:ℝ)-ν)*θ^ν := by
    rw [← Real.rpow_natCast,← Real.rpow_add hθ]
    congr 1
    ring
  let ρ := 4*C*θ^n
  have hScale : ρ≤(1/2:ℝ)*θ^ν := by
    have H := mul_le_mul_of_nonneg_right hSmall (Real.rpow_nonneg hθ.le ν)
    simpa only [ρ,hPow,mul_assoc] using H
  have hρ : 0≤ρ := by dsimp only [ρ];positivity
  have hGap : ρ<θ^ν := hScale.trans_lt (by nlinarith only [Real.rpow_pos_of_pos hθ ν])
  let A₀ := 2+4*C
  let L₀ := (1+A₀/(θ^ν-ρ))/θ^ν
  let L := 1+L₀
  have hA₀ : 0<A₀ := by dsimp only [A₀];positivity
  have hL₀ : 0<L₀ := by dsimp only [L₀];positivity
  have hL : 0<L := by dsimp only [L];positivity
  have hOneL : 1≤L := le_add_of_nonneg_right hL₀.le
  have hL₀L : L₀≤L := by dsimp only [L];linarith
  have heq : nativeNeumannPowerConstant n ν θ = L := rfl
  rw [heq]
  intro q u Du F K hu hF hK hGrowth hNat
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let E : Gradient n q → Ambient (n*q) := fun G=>WithLp.toLp 2
    (fun k=>G (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  let Z := fun (G : Domain n → Gradient n q) x i=>(ball (0 : Domain n) 1).indicator (fun y=>G y i) x
  obtain ⟨T,_hT,_hSelf,_hIdem,Hresponse⟩ := HT q
  let W := (memLp_hs_flatten F hF).toLp (fun x=>E (F x))
  let Q := fun (x : Domain n) (i : Fin n)=>WithLp.toLp 2 (fun j : Fin q=>(T W) x (finProdFinEquiv (i,j)))
  let F₀ := Z F
  let Q₀ := Z Q
  obtain ⟨v,hv,hNatQ,_hEq,_hF₀,_hQ₀,_hFI,hQI,hEnergy,Hsplit⟩ := Hresponse F hF
  have hDuQ : Du=ᵐ[μ]Q := native_neumann_gradient_response_unique_ae
    (ballDomain (0 : Domain n) 1) u v Du Q hu hv
      (fun ψ Dψ hψ=>(hNat ψ Dψ hψ).trans (hNatQ ψ Dψ hψ).2.2.symm)
  have hFGrowth (a : Domain n) (ha : a∈ball (0 : Domain n) 1) (r : ℝ) (hr : 0<r) :
      (∫x in ball a r,hsNormSq (F₀ x))≤K*r^ν := by
    rw [integral_zero_extended_hs_ball F a r]
    exact hGrowth a ha r hr
  have hFTotal : (∫x,hsNormSq (F₀ x))≤K := by
    rw [integral_zero_extended_hs F]
    have H := hGrowth 0 (mem_ball_self (by norm_num : (0:ℝ)<1)) 1 (by norm_num)
    simpa only [inter_self,Real.one_rpow,mul_one] using H
  have hQTotal : (∫x,hsNormSq (Q₀ x))≤K := hEnergy.trans hFTotal
  have hSplit (a : Domain n) (R : ℝ) (hR : 0<R) :
      ∃g h : Domain n → ℝ,(∀x,0≤g x) ∧ (∀x,0≤h x) ∧
        Integrable g volume ∧ Integrable h volume ∧
        (∀ᵐx∂volume,hsNormSq (Q₀ x)≤2*g x+2*h x) ∧
        (∫x,g x)≤∫x in ball a (256*R),hsNormSq (F₀ x) ∧
        ∀ᵐx∂volume.restrict (ball a R),h x≤2*C*(volume.real (ball a (256*R)))⁻¹*
          ((∫y in ball a (256*R),hsNormSq (Q₀ y))+(∫y in ball a (256*R),hsNormSq (F₀ y))) := by
    obtain ⟨_hQN,_hQF,hg,hh,_hSplit,hD,hNear,_hZero,hFar⟩ := Hsplit a R hR
    exact ⟨_,_,fun x=>hsNormSq_nonneg _,fun x=>hsNormSq_nonneg _,hg,hh,hD,hNear,hFar⟩
  intro a ha r hr
  let e := fun t : ℝ=>∫x in ball a t,hsNormSq (Q₀ x)
  let f := fun t : ℝ=>∫x in ball a t,hsNormSq (F₀ x)
  have hFull (t : ℝ) : e t≤K :=
    (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun x=>hsNormSq_nonneg _) hQI).trans hQTotal
  have hStep (t : ℝ) (ht : 0<t) (_htOne : t≤1) : e (θ*t)≤ρ*e t+(A₀*K)*t^ν := by
    obtain ⟨g,h,hg0,_hh0,hgI,hhI,hDensity,hNear,hFar⟩ := hSplit a (t/256) (by positivity)
    have hScaleR : (256:ℝ)*(t/256)=t := by ring
    rw [hScaleR] at hNear hFar
    have hSub : ball a (θ*t)⊆ball a (t/256) := ball_subset_ball (by nlinarith only [hθCap,ht])
    have hFarSmall := hFar.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub))
    have hFarI : (∫x in ball a (θ*t),h x)≤2*C*θ^n*(e t+f t) := by
      calc
        _≤∫_x in ball a (θ*t),2*C*(volume.real (ball a t))⁻¹*(e t+f t) :=
          integral_mono_ae hhI.integrableOn (integrableOn_const measure_ball_ne_top) hFarSmall
        _=(volume.real (ball a (θ*t))*(volume.real (ball a t))⁻¹)*(2*C*(e t+f t)) := by
          rw [integral_const]
          rw [measureReal_restrict_apply_univ,smul_eq_mul]
          ring
        _=2*C*θ^n*(e t+f t) := by rw [same_center_volume_ratio a t θ ht hθ];ring
    have hNearI : (∫x in ball a (θ*t),g x)≤f t :=
      (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hg0) hgI).trans hNear
    have hRec : e (θ*t)≤ρ*e t+(2+4*C*θ^n)*f t := by
      calc
        _≤∫x in ball a (θ*t),2*g x+2*h x := integral_mono_ae hQI.integrableOn
          ((hgI.const_mul 2).add (hhI.const_mul 2)).integrableOn
          (hDensity.filter_mono (ae_mono Measure.restrict_le_self))
        _=2*(∫x in ball a (θ*t),g x)+2*(∫x in ball a (θ*t),h x) := by
          rw [integral_add (hgI.integrableOn.const_mul 2) (hhI.integrableOn.const_mul 2),integral_const_mul,integral_const_mul]
        _≤2*f t+2*(2*C*θ^n*(e t+f t)) := add_le_add
          (mul_le_mul_of_nonneg_left hNearI (by norm_num)) (mul_le_mul_of_nonneg_left hFarI (by norm_num))
        _=_ := by dsimp only [ρ];ring
    have hCoeff : 2+4*C*θ^n≤A₀ := by
      have H : 4*C*θ^n≤4*C*1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hθ.le hθOne.le) (by positivity : 0≤4*C)
      dsimp only [A₀]
      linarith only [H]
    have hForce : (2+4*C*θ^n)*f t≤(A₀*K)*t^ν := by
      calc
        _≤A₀*f t := mul_le_mul_of_nonneg_right hCoeff (integral_nonneg fun x=>hsNormSq_nonneg _)
        _≤A₀*(K*t^ν) := mul_le_mul_of_nonneg_left (hFGrowth a ha t ht) hA₀.le
        _=_ := by ring
    exact hRec.trans (add_le_add le_rfl hForce)
  have hResult : e r≤L*K*r^ν := by
    by_cases hrOne : r≤1
    · have hMono (s t : ℝ) (_hs : 0<s) (hst : s≤t) (_ht : t≤1) : e s≤e t :=
        integral_mono_measure (Measure.restrict_mono_set volume (ball_subset_ball hst))
          (Eventually.of_forall fun x=>hsNormSq_nonneg _) hQI.integrableOn
      have hBase : e 1≤K*(1:ℝ)^ν := by simpa only [Real.one_rpow,mul_one] using hFull 1
      have H := all_radius_rpow_bound_of_recurrence e hν hθ hθOne hρ hGap
        (mul_nonneg hA₀.le hK) hK (by norm_num : (0:ℝ)<1) hMono hBase hStep r hr hrOne
      have H' : e r≤L₀*K*r^ν := H.trans_eq (by dsimp only [L₀];ring)
      exact H'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL₀L hK) (Real.rpow_nonneg hr.le ν))
    · have hPower : 1≤r^ν := by
        simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1) (not_le.mp hrOne).le hν
      calc
        _≤K := hFull r
        _≤L*K := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hOneL hK
        _≤L*K*r^ν := le_mul_of_one_le_right (mul_nonneg hL.le hK) hPower
  have hAE : Du=ᵐ[volume.restrict (ball a r∩ball (0 : Domain n) 1)]Q :=
    hDuQ.filter_mono (ae_mono (Measure.restrict_mono_set volume inter_subset_right))
  calc
    _=∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Q x) :=
      integral_congr_ae (hAE.mono fun x hx=>congrArg hsNormSq hx)
    _=e r := (integral_zero_extended_hs_ball Q a r).symm
    _≤_ := hResult

/-- Original full truncated power growth of raw forcing gives full truncated
growth of the same original native Neumann gradient for every exponent below dimension. -/
theorem effective_native_neumann_full_power_growth (n : ℕ) (hn : 2≤n)
    :
    ∀(q : ℕ) (u : Domain n → Ambient q)
      (Du F : Domain n → Gradient n q) (K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      0≤K →
      (∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))≤K*r^((n : ℝ) - 1)) →
      (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Du x i) (Dψ x i))=
          ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (F x i) (Dψ x i)) →
      ∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤(effectiveNativeNeumannPowerConstant n : ℝ)*K*r^((n : ℝ) - 1) := by
  let C : ℚ := effectiveNeumannOffSupportConstant n
  have hC : 0 ≤ C := Nat.cast_nonneg _
  let t := EffectiveCoulomb.naturalPowerScale (2 * C)
  have ht : 0 < t := EffectiveCoulomb.naturalPowerScale_pos (by positivity)
  have htcap : t ≤ 1 / 256 := EffectiveCoulomb.naturalPowerScale_le (by positivity)
  have hsmall : 4 * C * t ≤ 1 / 2 := by
    convert EffectiveCoulomb.naturalPowerScale_absorbs (show 0 ≤ 2 * C by positivity) using 1; ring
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hSmallR : 4 * (effectiveNeumannOffSupportConstant n : ℝ) *
      (t : ℝ) ^ ((n : ℝ) - ((n : ℝ) - 1)) ≤ 1 / 2 := by
    rw [show (n : ℝ) - ((n : ℝ) - 1) = 1 by ring, Real.rpow_one]
    have H : ((4 * C * t : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hsmall
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at H
    simpa only [C, Rat.cast_natCast] using H
  have htcapR : (t : ℝ) ≤ 1 / 256 := by
    have H : (t : ℝ) ≤ ((1 / 256 : ℚ) : ℝ) := Rat.cast_le.mpr htcap
    norm_num at H ⊢
    exact H
  have H := native_neumann_full_real_power_growth_at_scale n hn ((n : ℝ) - 1)
    (by linarith only [hnR]) (by linarith) (t : ℝ)
    (by exact_mod_cast ht) htcapR hSmallR
  have hν : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hcoef : nativeNeumannPowerConstant n ((n : ℝ) - 1) (t : ℝ) =
      (effectiveNativeNeumannPowerConstant n : ℝ) := by
    simp only [nativeNeumannPowerConstant, effectiveNativeNeumannPowerConstant,
      Rat.cast_add, Rat.cast_one, Rat.cast_div, Rat.cast_mul, Rat.cast_sub,
      Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast, hν, Real.rpow_natCast, t, C]
  simpa only [hcoef] using H

theorem nativeNeumannPowerConstant_le_effective (n : ℕ) (hn : 2 ≤ n)
    (ν : ℝ) (_hν : 0 ≤ ν) (hνCap : ν ≤ (n : ℝ) - 1) :
    nativeNeumannPowerConstant n ν
      (EffectiveCoulomb.naturalPowerScale (2 * (effectiveNeumannOffSupportConstant n : ℚ)) : ℝ) ≤
        (effectiveNativeNeumannPowerConstant n : ℝ) := by
  let C : ℝ := effectiveNeumannOffSupportConstant n
  let t := EffectiveCoulomb.naturalPowerScale (2 * (effectiveNeumannOffSupportConstant n : ℚ))
  let θ : ℝ := t
  have ht : 0 < t := EffectiveCoulomb.naturalPowerScale_pos (by positivity)
  have hθ : 0 < θ := by change 0 < (t : ℝ); exact_mod_cast ht
  have hθOne : θ ≤ 1 := by
    have H : (t : ℝ) ≤ ((1 / 256 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (EffectiveCoulomb.naturalPowerScale_le (by positivity))
    norm_num at H
    exact H.trans (by norm_num)
  have hνNat : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hPower : θ ^ ((n - 1 : ℕ) : ℝ) ≤ θ ^ ν :=
    Real.rpow_le_rpow_of_exponent_ge hθ hθOne (by simpa only [← hνNat] using hνCap)
  have hGap : 0 < θ ^ ((n - 1 : ℕ) : ℝ) - 4 * C * θ ^ n := by
    have H : (0 : ℝ) < ((t ^ (n - 1) -
        2 * (2 * (effectiveNeumannOffSupportConstant n : ℚ)) * t ^ n : ℚ) : ℝ) :=
      Rat.cast_pos.mpr (EffectiveCoulomb.naturalPowerScale_gap n (by omega) (by positivity))
    norm_num only [Rat.cast_sub, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast] at H
    rw [Real.rpow_natCast]
    dsimp only [θ, C]
    convert H using 1; ring
  have hDen := sub_le_sub_right hPower (4 * C * θ ^ n)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  have hNum : 1 + (2 + 4 * C) / (θ ^ ν - 4 * C * θ ^ n) ≤
      1 + (2 + 4 * C) / (θ ^ ((n - 1 : ℕ) : ℝ) - 4 * C * θ ^ n) := by
    simpa only [add_comm] using add_le_add_left
      (div_le_div_of_nonneg_left (show 0 ≤ 2 + 4 * C by positivity) hGap hDen) 1
  have H := div_le_div₀ (show 0 ≤ 1 + (2 + 4 * C) /
      (θ ^ ((n - 1 : ℕ) : ℝ) - 4 * C * θ ^ n) by positivity)
    hNum (Real.rpow_pos_of_pos hθ _) hPower
  have hEq : nativeNeumannPowerConstant n ((n : ℝ) - 1) θ =
      (effectiveNativeNeumannPowerConstant n : ℝ) := by
    simp only [nativeNeumannPowerConstant, effectiveNativeNeumannPowerConstant,
      Rat.cast_add, Rat.cast_one, Rat.cast_div, Rat.cast_mul, Rat.cast_sub,
      Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast, hνNat, Real.rpow_natCast, θ, t]
  rw [← hEq]
  unfold nativeNeumannPowerConstant
  dsimp only
  have H' : 1 + (1 + (2 + 4 * C) / (θ ^ ν - 4 * C * θ ^ n)) / θ ^ ν ≤
      1 + (1 + (2 + 4 * C) / (θ ^ ((n - 1 : ℕ) : ℝ) - 4 * C * θ ^ n)) /
        θ ^ ((n - 1 : ℕ) : ℝ) := by linarith only [H]
  simpa only [C, hνNat] using H'

/-- Original full truncated power growth of raw forcing gives full truncated
growth of the same original native Neumann gradient for every exponent below dimension. -/
theorem effective_native_neumann_full_power_growth_of_exponent_le (n : ℕ) (hn : 2≤n)
    (ν : ℝ) (hν : 0≤ν) (hνCap : ν ≤ (n : ℝ) - 1) :
    ∀(q : ℕ) (u : Domain n → Ambient q)
      (Du F : Domain n → Gradient n q) (K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      0≤K →
      (∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))≤K*r^ν) →
      (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Du x i) (Dψ x i))=
          ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (F x i) (Dψ x i)) →
      ∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤(effectiveNativeNeumannPowerConstant n : ℝ)*K*r^ν := by
  let t := EffectiveCoulomb.naturalPowerScale (2 * (effectiveNeumannOffSupportConstant n : ℚ))
  let θ : ℝ := t
  have ht : 0 < t := EffectiveCoulomb.naturalPowerScale_pos (by positivity)
  have hθ : 0 < θ := by change 0 < (t : ℝ); exact_mod_cast ht
  have hθCap : θ ≤ 1 / 256 := by
    have H : (t : ℝ) ≤ ((1 / 256 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (EffectiveCoulomb.naturalPowerScale_le (by positivity))
    norm_num at H ⊢
    exact H
  have hSmallOne : 4 * (effectiveNeumannOffSupportConstant n : ℝ) * θ ≤ 1 / 2 := by
    have H : ((2 * (2 * (effectiveNeumannOffSupportConstant n : ℚ)) * t : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (EffectiveCoulomb.naturalPowerScale_absorbs (by positivity))
    norm_num only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_div, Rat.cast_one] at H
    dsimp only [θ]
    convert H using 1; ring
  have hSmall : 4 * (effectiveNeumannOffSupportConstant n : ℝ) * θ ^ ((n : ℝ) - ν) ≤ 1 / 2 := by
    have hPower : θ ^ ((n : ℝ) - ν) ≤ θ := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hθ
        (hθCap.trans (by norm_num : (1 / 256 : ℝ) ≤ 1)) (by linarith only [hνCap] : 1 ≤ (n : ℝ) - ν)
    exact (mul_le_mul_of_nonneg_left hPower (by positivity)).trans hSmallOne
  have H := native_neumann_full_real_power_growth_at_scale n hn ν hν
    (by linarith only [hνCap]) θ hθ hθCap hSmall
  have hCoeff := nativeNeumannPowerConstant_le_effective n hn ν hν hνCap
  intro q u Du F K hu hF hK hGrowth hNat a ha r hr
  exact (H q u Du F K hu hF hK hGrowth hNat a ha r hr).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCoeff hK) (Real.rpow_nonneg hr.le ν))

/-- Original full truncated power growth of raw forcing gives full truncated
growth of the same original native Neumann gradient for every exponent below dimension. -/
theorem exists_native_neumann_full_real_power_growth (n : ℕ) (hn : 2≤n)
    (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n:ℝ)) :
    ∃ L : ℝ,0<L ∧ ∀(q : ℕ) (u : Domain n → Ambient q)
      (Du F : Domain n → Gradient n q) (K : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
      0≤K →
      (∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))≤K*r^ν) →
      (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
        MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
        (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Du x i) (Dψ x i))=
          ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (F x i) (Dψ x i)) →
      ∀a : Domain n,a∈ball (0 : Domain n) 1 → ∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤L*K*r^ν := by
  let C : ℝ := effectiveNeumannOffSupportConstant n
  have hC : 0 < C := effectiveNeumannOffSupportConstant_pos n
  obtain ⟨θ,hθ,hθCap,hSmall⟩ := exists_positive_rpow_bound
    (C:=4*C) (p:=(n:ℝ)-ν) (a:=1/2) (cap:=1/256)
    (by positivity) (sub_pos.mpr hνn) (by norm_num) (by norm_num)
  have hθOne : θ<1 := lt_of_le_of_lt hθCap (by norm_num)
  have hPow : θ^n=θ^((n:ℝ)-ν)*θ^ν := by
    rw [← Real.rpow_natCast,← Real.rpow_add hθ]
    congr 1
    ring
  let ρ := 4*C*θ^n
  have hScale : ρ≤(1/2:ℝ)*θ^ν := by
    have H := mul_le_mul_of_nonneg_right hSmall (Real.rpow_nonneg hθ.le ν)
    simpa only [ρ,hPow,mul_assoc] using H
  have hρ : 0≤ρ := by dsimp only [ρ];positivity
  have hGap : ρ<θ^ν := hScale.trans_lt (by nlinarith only [Real.rpow_pos_of_pos hθ ν])
  let A₀ := 2+4*C
  let L₀ := (1+A₀/(θ^ν-ρ))/θ^ν
  let L := 1+L₀
  have hA₀ : 0<A₀ := by dsimp only [A₀];positivity
  have hL₀ : 0<L₀ := by dsimp only [L₀];positivity
  have hL : 0<L := by dsimp only [L];positivity
  have hOneL : 1≤L := le_add_of_nonneg_right hL₀.le
  have hL₀L : L₀≤L := by dsimp only [L];linarith
  exact ⟨L, hL, native_neumann_full_real_power_growth_at_scale n hn ν hν hνn θ hθ hθCap hSmall⟩

end StationaryHarmonicMaps.Analysis

end
