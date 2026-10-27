module

public import StationaryHarmonicMaps.Analysis.SystemCompensatedHodgeFields
public import StationaryHarmonicMaps.Analysis.HodgeLowPComparison

/-!
# Actual one-ball compensated decay of the original cutoff gradient

One same relative Hodge decomposition supplies both compensated fields
and its actual harmonic remainder. The genuine lower-power comparison
and the original finite envelope produce the scale-correct small-ball
bound for the original cutoff's displayed weak gradient.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem nonnegative_sum_real_power_le (a b p : ℝ)
    (ha : 0≤a) (hb : 0≤b) (hp : 0≤p) :
    (a+b)^p≤(2 : ℝ)^p*(a^p+b^p) := by
  by_cases h : a≤b
  · calc
      _≤(2*b)^p := Real.rpow_le_rpow (add_nonneg ha hb) (by linarith only [h]) hp
      _=(2 : ℝ)^p*b^p := Real.mul_rpow (by norm_num) hb
      _≤_ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.rpow_nonneg ha _))
        (Real.rpow_nonneg (by norm_num) _)
  · calc
      _≤(2*a)^p := Real.rpow_le_rpow (add_nonneg ha hb) (by linarith only [not_le.mp h]) hp
      _=(2 : ℝ)^p*a^p := Real.mul_rpow (by norm_num) ha
      _≤_ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg hb _))
        (Real.rpow_nonneg (by norm_num) _)

private theorem power_moment_of_root_bound (p : ℝ) (hp : 0<p) {I b : ℝ}
    (hI : 0≤I) (H : I^(1/p)≤b) : I≤b^p := by
  have HH := Real.rpow_le_rpow (Real.rpow_nonneg hI _) H hp.le
  simpa only [one_div,Real.rpow_inv_rpow hI hp.ne'] using HH

/-- Original compact-target system data and a given small critical
native Coulomb frame give the actual cutoff gradient its one-ball
compensated decay. No decomposition or component estimate is an input. -/
theorem exists_compact_target_one_ball_compensated_decay
    (n : ℕ) (hn : 2≤n) (p : ℝ) (hpOne : 1<p) (hpTwo : p<2)
    (hpConj : (n : ℝ)<p/(p-1)) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (δ A B L : ℝ) (hδ : 0<δ) (hδOne : δ<1) (hA : 0≤A) (hB : 0≤B) (hL : 0≤L) :
    ∃C : ℝ,0<C ∧ ∀(N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),u x∈N.carrierSet) → 0≤η → η≤1 →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀(P : Domain n → Ambient (q*q)) (DP : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) P DP →
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (P x))*R (P x)=1) →
        criticalGradientMorreySquare DP (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
        ∀Ω : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
          (∀i,MemLp (fun x=>Ω x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) Du (fun x=>-(∑i : Fin n,Ω x i (Du x i))) →
          let Z := fun x i=>star (R (P x))*R (DP x i)+star (R (P x))*Ω x i*R (P x)
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) (fun x i=>E (Z x i)) (fun _=>0) →
          criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
          ∀χ : Domain n → ℝ,ContDiff ℝ ∞ χ → HasCompactSupport χ →
            tsupport χ⊆closedBall (0 : Domain n) (3/4 : ℝ) →
            (∀x,|χ x|≤A) → (∀(x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) →
            (∀x,|Laplacian.laplacian χ x|≤L) →
            let c := ⨍y in ball (0 : Domain n) 1,u y
            let v := fun x=>χ x • (u x-c)
            let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
            let Φ := fun (x : Domain n) (r : ℝ)=>r^(p-(n : ℝ))*∫y in ball x r,(Real.sqrt (hsNormSq (Dv y)))^p
            let Ψ := fun t : ℝ=>sSup {z : ℝ | ∃x r,0<r ∧ r≤t ∧ z=Φ x r}
            MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv ∧
            ∀(a : Domain n) (t : ℝ),0<t → t≤1/128 → closedBall a (t/2)⊆ball (0 : Domain n) 1 →
              ∀θ : ℝ,0<θ → θ≤1/2 →
                IntegrableOn (fun x=>(Real.sqrt (hsNormSq (Dv x)))^p) (ball a (θ*(t/2))) volume ∧
                (∫x in ball a (θ*(t/2)),(Real.sqrt (hsNormSq (Dv x)))^p)≤
                  C*((η^p+θ^n)*(Ψ (8*t))*t^((n : ℝ)-p)+η^p*t^((n : ℝ)-p*δ)) := by
  have hp : 0<p := zero_lt_one.trans hpOne
  obtain ⟨D,hD,HFields⟩ := exists_compact_target_same_compensated_hodge_fields
    n hn p hpOne hpTwo hpConj q E R hRE hER hE δ A B L hδ hδOne hA hB hL
  obtain ⟨H,hH,HCompare⟩ := exists_hodge_low_power_small_ball_comparison n hn p hpOne.le hpTwo.le
  let T := (1+(2 : ℝ)^p)*D^p
  have hT : 0≤T := mul_nonneg (by positivity) (Real.rpow_nonneg hD.le _)
  let C := 1+H*(1+T)
  have hC : 0<C := by dsimp only [C];positivity
  have hHTC : H*T≤C := by dsimp only [C];nlinarith only [hH]
  have hHC : H≤C := by dsimp only [C];nlinarith only [hH,hT]
  refine ⟨C,hC,?_⟩
  intro N u Du η hu hTarget hη hηOne hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
    χ hχ hcχ hsχ hχA hDχ hLap c v Dv Φ Ψ
  obtain ⟨hV,HQuery⟩ := HFields N u Du η hu hTarget hη hηOne hCritical P DP hP hOrth hDPCritical
    Ω hΩ hEq hDiv hZCritical χ hχ hcχ hsχ hχA hDχ hLap
  refine ⟨hV,?_⟩
  intro a t ht htCap hClosed θ hθ hθHalf
  let r := t/2
  have hr : 0<r := half_pos ht
  let μ := volume.restrict (ball a r)
  have hSub : ball a r⊆ball (0 : Domain n) 1 := ball_subset_closedBall.trans hClosed
  let Fv := fun x i=>star (R (P x)) (Dv x i)
  obtain ⟨f,Df,Q,h,g,hf,hg,hQ,hDecomp,_hNatural,_hHDiv,hHarm,_hDI,_hQI,hDBound,hQBound,_hPyth⟩ :=
    HQuery a t ht htCap hClosed
  let Λ : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q) :=
    (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).toContinuousLinearMap.comp R
  have hΛ (z : Ambient (q*q)) : Λ z=star (R z) := rfl
  have hPBound : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖P x‖≤Real.sqrt (q : ℝ) :=
    ae_orthogonal_coordinates_bound (Ω:=ballDomain (0 : Domain n) 1) E R hER hE P hOrth
  have hVParent : MemW12 (ballDomain (0 : Domain n) 1) v Dv := memW12_of_openDomain_subset hV (subset_univ _)
  have hF (i : Fin n) : MemLp (fun x=>Fv x i) 2 μ := by
    have HH := (memLp_bounded_native_frame_columns (ballDomain (0 : Domain n) 1) P DP hP
      (Real.sqrt (q : ℝ)) hPBound Λ Dv hVParent.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)
    simpa only [hΛ] using HH
  obtain ⟨hFSmallI,hSmall⟩ := HCompare q a ⟨r,hr⟩ Fv Df Q h hF hf.1.2.2 hQ hg.2.2 hDecomp hHarm θ hθ hθHalf
  have hFrame : ∀ᵐx∂μ,hsNormSq (Fv x)=hsNormSq (Dv x) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hSub hOrth] with x hx
    have hStar : star (star (R (P x)))*star (R (P x))=1 := by
      simpa only [star_star] using mul_star_eq_one_of_star_mul_eq_one (R (P x)) hx
    exact Finset.sum_congr rfl fun i _=>norm_sq_apply_orthogonal (star (R (P x))) hStar (Dv x i)
  have hDensity : (fun x=>(Real.sqrt (hsNormSq (Fv x)))^p)=ᵐ[μ]
      (fun x=>(Real.sqrt (hsNormSq (Dv x)))^p) := hFrame.mono fun x hx=>by
    change (Real.sqrt (hsNormSq (Fv x)))^p=(Real.sqrt (hsNormSq (Dv x)))^p
    rw [hx]
  have hSmallSub : ball a (θ*r)⊆ball a r := ball_subset_ball (by nlinarith only [hθHalf,hr])
  have hDensitySmall := ae_restrict_of_ae_restrict_of_subset hSmallSub hDensity
  have hSmallEq : (∫x in ball a (θ*r),(Real.sqrt (hsNormSq (Fv x)))^p)=
      ∫x in ball a (θ*r),(Real.sqrt (hsNormSq (Dv x)))^p := integral_congr_ae hDensitySmall
  have hPowHS (V : Gradient n q) : (Real.sqrt (hsNormSq V))^p=(hsNormSq V)^(p/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (hsNormSq_nonneg _)]
    congr 1
    ring
  let ID := ∫x in ball a r,(Real.sqrt (hsNormSq (Df x)))^p
  let IQ := ∫x in ball a r,(Real.sqrt (hsNormSq (Q x)))^p
  let IF := ∫x in ball a r,(Real.sqrt (hsNormSq (Fv x)))^p
  have hID : 0≤ID := integral_nonneg fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hIQ : 0≤IQ := integral_nonneg fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _
  obtain ⟨_hV',hPsi,hGrowth⟩ := cutoff_capped_envelope_lp_growth n hn p hpOne.le hpTwo.le A B hA hB
    q u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ t ht htCap
  have hPsiRoot : 0≤(Ψ (8*t))^(1/p) := Real.rpow_nonneg hPsi _
  have hDMain : 0≤D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p) :=
    mul_nonneg (mul_nonneg (mul_nonneg hD.le hη) (Real.rpow_nonneg ht.le _)) hPsiRoot
  have hDErr : 0≤D*η*t^((n : ℝ)/p-δ) :=
    mul_nonneg (mul_nonneg hD.le hη) (Real.rpow_nonneg ht.le _)
  have hMainPower : (D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p))^p=
      D^p*η^p*t^((n : ℝ)-p)*(Ψ (8*t)) := by
    rw [Real.mul_rpow (mul_nonneg (mul_nonneg hD.le hη) (Real.rpow_nonneg ht.le _)) hPsiRoot,
      Real.mul_rpow (mul_nonneg hD.le hη) (Real.rpow_nonneg ht.le _),Real.mul_rpow hD.le hη,
      ←Real.rpow_mul ht.le,←Real.rpow_mul hPsi]
    rw [show ((n : ℝ)/p-1)*p=(n : ℝ)-p by field_simp,
      show (1/p)*p=1 by field_simp,Real.rpow_one]
  have hErrorPower : (D*η*t^((n : ℝ)/p-δ))^p=D^p*η^p*t^((n : ℝ)-p*δ) := by
    rw [Real.mul_rpow (mul_nonneg hD.le hη) (Real.rpow_nonneg ht.le _),Real.mul_rpow hD.le hη,
      ←Real.rpow_mul ht.le]
    congr 1
    field_simp
  let E₁ := η^p*(Ψ (8*t))*t^((n : ℝ)-p)
  let E₂ := η^p*t^((n : ℝ)-p*δ)
  have hE₁ : 0≤E₁ := mul_nonneg (mul_nonneg (Real.rpow_nonneg hη _) hPsi) (Real.rpow_nonneg ht.le _)
  have hE₂ : 0≤E₂ := mul_nonneg (Real.rpow_nonneg hη _) (Real.rpow_nonneg ht.le _)
  have hIDBound : ID≤(2 : ℝ)^p*D^p*(E₁+E₂) := by
    have hIDPower : ID=∫x in ball a r,(hsNormSq (Df x))^(p/2) :=
      integral_congr_ae (Eventually.of_forall fun x=>hPowHS (Df x))
    have HD : ID^(1/p)≤D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+D*η*t^((n : ℝ)/p-δ) := by
      rw [hIDPower]
      exact hDBound
    calc
      _≤(D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+D*η*t^((n : ℝ)/p-δ))^p := power_moment_of_root_bound p hp hID HD
      _≤(2 : ℝ)^p*((D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p))^p+(D*η*t^((n : ℝ)/p-δ))^p) :=
        nonnegative_sum_real_power_le _ _ p hDMain hDErr hp.le
      _=_ := by rw [hMainPower,hErrorPower];dsimp only [E₁,E₂];ring
  have hIQBound : IQ≤D^p*E₁ := by
    have hIQPower : IQ=∫x in ball a r,(hsNormSq (Q x))^(p/2) :=
      integral_congr_ae (Eventually.of_forall fun x=>hPowHS (Q x))
    have HQ : IQ^(1/p)≤D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p) := by
      rw [hIQPower]
      exact hQBound
    exact (power_moment_of_root_bound p hp hIQ HQ).trans_eq (by rw [hMainPower];dsimp only [E₁];ring)
  have hComponentSum : ID+IQ≤T*(E₁+E₂) := by
    have HM := mul_nonneg (Real.rpow_nonneg hD.le p) hE₂
    dsimp only [T]
    nlinarith only [hIDBound,hIQBound,HM]
  have hIFBound : IF≤(Ψ (8*t))*t^((n : ℝ)-p) := by
    have HH := hGrowth a r hr (by dsimp only [r];linarith only [ht])
    rw [one_div,Real.rpow_inv_rpow hPsi hp.ne'] at HH
    have hnReal : (2 : ℝ)≤n := by exact_mod_cast hn
    have hRadius : r^((n : ℝ)-p)≤t^((n : ℝ)-p) := Real.rpow_le_rpow hr.le (by dsimp only [r];linarith only [ht])
      (sub_nonneg.mpr (hpTwo.le.trans hnReal))
    calc
      IF=∫x in ball a r,(Real.sqrt (hsNormSq (Dv x)))^p := integral_congr_ae hDensity
      _≤(Ψ (8*t))*r^((n : ℝ)-p) := HH
      _≤_ := mul_le_mul_of_nonneg_left hRadius hPsi
  have hθN : 0≤θ^n := pow_nonneg hθ.le n
  refine ⟨hFSmallI.congr hDensitySmall,?_⟩
  rw [←hSmallEq]
  calc
    _≤H*(ID+IQ+θ^n*IF) := hSmall
    _≤H*(T*(E₁+E₂)+θ^n*((Ψ (8*t))*t^((n : ℝ)-p))) := mul_le_mul_of_nonneg_left
      (add_le_add hComponentSum (mul_le_mul_of_nonneg_left hIFBound hθN)) hH.le
    _=(H*T)*E₁+(H*T)*E₂+H*(θ^n*(Ψ (8*t))*t^((n : ℝ)-p)) := by ring
    _≤C*E₁+C*E₂+C*(θ^n*(Ψ (8*t))*t^((n : ℝ)-p)) := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_right hHTC hE₁) (mul_le_mul_of_nonneg_right hHTC hE₂))
      (mul_le_mul_of_nonneg_right hHC (mul_nonneg (mul_nonneg hθN hPsi) (Real.rpow_nonneg ht.le _)))
    _=C*((η^p+θ^n)*(Ψ (8*t))*t^((n : ℝ)-p)+η^p*t^((n : ℝ)-p*δ)) := by dsimp only [E₁,E₂];ring

@[expose] def effectiveOneBallCompensatedConstant (n q B L : ℕ) : ℚ :=
  1+(effectiveHodgeLowPowerConstant n : ℚ)*
    (1+5*(1+effectiveSystemCompensatedHodgeConstant n q B L)^2)

theorem effectiveOneBallCompensatedConstant_pos (n q B L : ℕ) :
    0<effectiveOneBallCompensatedConstant n q B L := by
  have H : 0<(effectiveHodgeLowPowerConstant n : ℚ) := by
    exact_mod_cast effectiveHodgeLowPowerConstant_pos n
  unfold effectiveOneBallCompensatedConstant
  positivity

theorem effective_compact_target_one_ball_compensated_decay
    (n : ℕ) (hn : 2≤n) (p : ℝ) (hpOne : 1<p) (hpTwo : p<2)
    (hpConj : (n : ℝ)<p/(p-1)) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (A : ℝ) (B L : ℕ) (hA : 0≤A)
    (hConjugate : p/(p-1)=((2*n+1 : ℕ) : ℝ)) :
    ∀(N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),u x∈N.carrierSet) → 0≤η → η≤1 →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀(P : Domain n → Ambient (q*q)) (DP : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) P DP →
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (P x))*R (P x)=1) →
        criticalGradientMorreySquare DP (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
        ∀Ω : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
          (∀i,MemLp (fun x=>Ω x i) 2 (volume.restrict (ball (0 : Domain n) 1))) →
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) Du (fun x=>-(∑i : Fin n,Ω x i (Du x i))) →
          let Z := fun x i=>star (R (P x))*R (DP x i)+star (R (P x))*Ω x i*R (P x)
          HolderToCK.WeakPoissonOn (ballDomain (0 : Domain n) 1) (fun x i=>E (Z x i)) (fun _=>0) →
          criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
          ∀χ : Domain n → ℝ,ContDiff ℝ ∞ χ → HasCompactSupport χ →
            tsupport χ⊆closedBall (0 : Domain n) (3/4 : ℝ) →
            (∀x,|χ x|≤A) → (∀(x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) →
            (∀x,|Laplacian.laplacian χ x|≤L) →
            let c := ⨍y in ball (0 : Domain n) 1,u y
            let v := fun x=>χ x • (u x-c)
            let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
            let Φ := fun (x : Domain n) (r : ℝ)=>r^(p-(n : ℝ))*∫y in ball x r,(Real.sqrt (hsNormSq (Dv y)))^p
            let Ψ := fun t : ℝ=>sSup {z : ℝ | ∃x r,0<r ∧ r≤t ∧ z=Φ x r}
            MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv ∧
            ∀(a : Domain n) (t : ℝ),0<t → t≤1/128 → closedBall a (t/2)⊆ball (0 : Domain n) 1 →
              ∀θ : ℝ,0<θ → θ≤1/2 →
                IntegrableOn (fun x=>(Real.sqrt (hsNormSq (Dv x)))^p) (ball a (θ*(t/2))) volume ∧
                (∫x in ball a (θ*(t/2)),(Real.sqrt (hsNormSq (Dv x)))^p)≤
                  (effectiveOneBallCompensatedConstant n q B L : ℝ)*((η^p+θ^n)*(Ψ (8*t))*t^((n : ℝ)-p)+η^p*t^((n : ℝ)-p*(1/2 : ℝ))) := by
  have hp : 0<p := zero_lt_one.trans hpOne
  let δ : ℝ := 1/2
  have hδOne : δ<1 := by norm_num [δ]
  have hB : 0≤(B : ℝ) := Nat.cast_nonneg B
  obtain ⟨D,hD,hDEq,HFields⟩ := effective_compact_target_same_compensated_hodge_fields
    n hn p hpOne hpTwo hpConj q E R hRE hER hE A B L hA hConjugate
  let H : ℝ := effectiveHodgeLowPowerConstant n
  have hH : 0<H := effectiveHodgeLowPowerConstant_pos n
  have HCompare := effective_hodge_low_power_small_ball_comparison n hn p hpOne.le hpTwo.le
  let T := (1+(2 : ℝ)^p)*D^p
  have hT : 0≤T := mul_nonneg (by positivity) (Real.rpow_nonneg hD.le _)
  let C : ℝ := effectiveOneBallCompensatedConstant n q B L
  have hTwo : (2 : ℝ)^p≤4 := by
    calc
      _≤(2 : ℝ)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hpTwo.le
      _=4 := by norm_num
  have hDPower : D^p≤(1+D)^2 := by
    calc
      _≤(1+D)^p := Real.rpow_le_rpow hD.le (by linarith) hp.le
      _≤(1+D)^(2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hpTwo.le
      _=(1+D)^2 := by rw [Real.rpow_two]
  have hTMajorant : T≤5*(1+D)^2 := by
    exact mul_le_mul (by linarith only [hTwo] : 1+(2 : ℝ)^p≤5)
      hDPower (Real.rpow_nonneg hD.le _) (by norm_num)
  have hCast : C=1+H*(1+5*(1+D)^2) := by
    rw [hDEq]
    simp only [C,effectiveOneBallCompensatedConstant,Rat.cast_add,Rat.cast_one,
      Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_pow,H]
  have hHTC : H*T≤C := by
    rw [hCast]
    have HT := mul_le_mul_of_nonneg_left hTMajorant hH.le
    nlinarith only [HT,hH]
  have hHC : H≤C := by
    rw [hCast]
    nlinarith only [hH,sq_nonneg (1+D)]
  intro N u Du η hu hTarget hη hηOne hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
    χ hχ hcχ hsχ hχA hDχ hLap c v Dv Φ Ψ
  obtain ⟨hV,HQuery⟩ := HFields N u Du η hu hTarget hη hηOne hCritical P DP hP hOrth hDPCritical
    Ω hΩ hEq hDiv hZCritical χ hχ hcχ hsχ hχA hDχ hLap
  refine ⟨hV,?_⟩
  intro a t ht htCap hClosed θ hθ hθHalf
  let r := t/2
  have hr : 0<r := half_pos ht
  let μ := volume.restrict (ball a r)
  have hSub : ball a r⊆ball (0 : Domain n) 1 := ball_subset_closedBall.trans hClosed
  let Fv := fun x i=>star (R (P x)) (Dv x i)
  obtain ⟨f,Df,Q,h,g,hf,hg,hQ,hDecomp,_hNatural,_hHDiv,hHarm,_hDI,_hQI,hDBound,hQBound,_hPyth⟩ :=
    HQuery a t ht htCap hClosed
  let Λ : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q) :=
    (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).toContinuousLinearMap.comp R
  have hΛ (z : Ambient (q*q)) : Λ z=star (R z) := rfl
  have hPBound : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖P x‖≤Real.sqrt (q : ℝ) :=
    ae_orthogonal_coordinates_bound (Ω:=ballDomain (0 : Domain n) 1) E R hER hE P hOrth
  have hVParent : MemW12 (ballDomain (0 : Domain n) 1) v Dv := memW12_of_openDomain_subset hV (subset_univ _)
  have hF (i : Fin n) : MemLp (fun x=>Fv x i) 2 μ := by
    have HH := (memLp_bounded_native_frame_columns (ballDomain (0 : Domain n) 1) P DP hP
      (Real.sqrt (q : ℝ)) hPBound Λ Dv hVParent.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)
    simpa only [hΛ] using HH
  obtain ⟨hFSmallI,hSmall⟩ := HCompare q a ⟨r,hr⟩ Fv Df Q h hF hf.1.2.2 hQ hg.2.2 hDecomp hHarm θ hθ hθHalf
  have hFrame : ∀ᵐx∂μ,hsNormSq (Fv x)=hsNormSq (Dv x) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hSub hOrth] with x hx
    have hStar : star (star (R (P x)))*star (R (P x))=1 := by
      simpa only [star_star] using mul_star_eq_one_of_star_mul_eq_one (R (P x)) hx
    exact Finset.sum_congr rfl fun i _=>norm_sq_apply_orthogonal (star (R (P x))) hStar (Dv x i)
  have hDensity : (fun x=>(Real.sqrt (hsNormSq (Fv x)))^p)=ᵐ[μ]
      (fun x=>(Real.sqrt (hsNormSq (Dv x)))^p) := hFrame.mono fun x hx=>by
    change (Real.sqrt (hsNormSq (Fv x)))^p=(Real.sqrt (hsNormSq (Dv x)))^p
    rw [hx]
  have hSmallSub : ball a (θ*r)⊆ball a r := ball_subset_ball (by nlinarith only [hθHalf,hr])
  have hDensitySmall := ae_restrict_of_ae_restrict_of_subset hSmallSub hDensity
  have hSmallEq : (∫x in ball a (θ*r),(Real.sqrt (hsNormSq (Fv x)))^p)=
      ∫x in ball a (θ*r),(Real.sqrt (hsNormSq (Dv x)))^p := integral_congr_ae hDensitySmall
  have hPowHS (V : Gradient n q) : (Real.sqrt (hsNormSq V))^p=(hsNormSq V)^(p/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (hsNormSq_nonneg _)]
    congr 1
    ring
  let ID := ∫x in ball a r,(Real.sqrt (hsNormSq (Df x)))^p
  let IQ := ∫x in ball a r,(Real.sqrt (hsNormSq (Q x)))^p
  let IF := ∫x in ball a r,(Real.sqrt (hsNormSq (Fv x)))^p
  have hID : 0≤ID := integral_nonneg fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hIQ : 0≤IQ := integral_nonneg fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _
  obtain ⟨_hV',hPsi,hGrowth⟩ := cutoff_capped_envelope_lp_growth n hn p hpOne.le hpTwo.le A B hA hB
    q u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ t ht htCap
  have hPsiRoot : 0≤(Ψ (8*t))^(1/p) := Real.rpow_nonneg hPsi _
  have hDMain : 0≤D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p) :=
    mul_nonneg (mul_nonneg (mul_nonneg hD.le hη) (Real.rpow_nonneg ht.le _)) hPsiRoot
  have hDErr : 0≤D*η*t^((n : ℝ)/p-δ) :=
    mul_nonneg (mul_nonneg hD.le hη) (Real.rpow_nonneg ht.le _)
  have hMainPower : (D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p))^p=
      D^p*η^p*t^((n : ℝ)-p)*(Ψ (8*t)) := by
    rw [Real.mul_rpow (mul_nonneg (mul_nonneg hD.le hη) (Real.rpow_nonneg ht.le _)) hPsiRoot,
      Real.mul_rpow (mul_nonneg hD.le hη) (Real.rpow_nonneg ht.le _),Real.mul_rpow hD.le hη,
      ←Real.rpow_mul ht.le,←Real.rpow_mul hPsi]
    rw [show ((n : ℝ)/p-1)*p=(n : ℝ)-p by field_simp,
      show (1/p)*p=1 by field_simp,Real.rpow_one]
  have hErrorPower : (D*η*t^((n : ℝ)/p-δ))^p=D^p*η^p*t^((n : ℝ)-p*δ) := by
    rw [Real.mul_rpow (mul_nonneg hD.le hη) (Real.rpow_nonneg ht.le _),Real.mul_rpow hD.le hη,
      ←Real.rpow_mul ht.le]
    congr 1
    field_simp
  let E₁ := η^p*(Ψ (8*t))*t^((n : ℝ)-p)
  let E₂ := η^p*t^((n : ℝ)-p*δ)
  have hE₁ : 0≤E₁ := mul_nonneg (mul_nonneg (Real.rpow_nonneg hη _) hPsi) (Real.rpow_nonneg ht.le _)
  have hE₂ : 0≤E₂ := mul_nonneg (Real.rpow_nonneg hη _) (Real.rpow_nonneg ht.le _)
  have hIDBound : ID≤(2 : ℝ)^p*D^p*(E₁+E₂) := by
    have hIDPower : ID=∫x in ball a r,(hsNormSq (Df x))^(p/2) :=
      integral_congr_ae (Eventually.of_forall fun x=>hPowHS (Df x))
    have HD : ID^(1/p)≤D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+D*η*t^((n : ℝ)/p-δ) := by
      rw [hIDPower]
      exact hDBound
    calc
      _≤(D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+D*η*t^((n : ℝ)/p-δ))^p := power_moment_of_root_bound p hp hID HD
      _≤(2 : ℝ)^p*((D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p))^p+(D*η*t^((n : ℝ)/p-δ))^p) :=
        nonnegative_sum_real_power_le _ _ p hDMain hDErr hp.le
      _=_ := by rw [hMainPower,hErrorPower];dsimp only [E₁,E₂];ring
  have hIQBound : IQ≤D^p*E₁ := by
    have hIQPower : IQ=∫x in ball a r,(hsNormSq (Q x))^(p/2) :=
      integral_congr_ae (Eventually.of_forall fun x=>hPowHS (Q x))
    have HQ : IQ^(1/p)≤D*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p) := by
      rw [hIQPower]
      exact hQBound
    exact (power_moment_of_root_bound p hp hIQ HQ).trans_eq (by rw [hMainPower];dsimp only [E₁];ring)
  have hComponentSum : ID+IQ≤T*(E₁+E₂) := by
    have HM := mul_nonneg (Real.rpow_nonneg hD.le p) hE₂
    dsimp only [T]
    nlinarith only [hIDBound,hIQBound,HM]
  have hIFBound : IF≤(Ψ (8*t))*t^((n : ℝ)-p) := by
    have HH := hGrowth a r hr (by dsimp only [r];linarith only [ht])
    rw [one_div,Real.rpow_inv_rpow hPsi hp.ne'] at HH
    have hnReal : (2 : ℝ)≤n := by exact_mod_cast hn
    have hRadius : r^((n : ℝ)-p)≤t^((n : ℝ)-p) := Real.rpow_le_rpow hr.le (by dsimp only [r];linarith only [ht])
      (sub_nonneg.mpr (hpTwo.le.trans hnReal))
    calc
      IF=∫x in ball a r,(Real.sqrt (hsNormSq (Dv x)))^p := integral_congr_ae hDensity
      _≤(Ψ (8*t))*r^((n : ℝ)-p) := HH
      _≤_ := mul_le_mul_of_nonneg_left hRadius hPsi
  have hθN : 0≤θ^n := pow_nonneg hθ.le n
  refine ⟨hFSmallI.congr hDensitySmall,?_⟩
  rw [←hSmallEq]
  calc
    _≤H*(ID+IQ+θ^n*IF) := hSmall
    _≤H*(T*(E₁+E₂)+θ^n*((Ψ (8*t))*t^((n : ℝ)-p))) := mul_le_mul_of_nonneg_left
      (add_le_add hComponentSum (mul_le_mul_of_nonneg_left hIFBound hθN)) hH.le
    _=(H*T)*E₁+(H*T)*E₂+H*(θ^n*(Ψ (8*t))*t^((n : ℝ)-p)) := by ring
    _≤C*E₁+C*E₂+C*(θ^n*(Ψ (8*t))*t^((n : ℝ)-p)) := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_right hHTC hE₁) (mul_le_mul_of_nonneg_right hHTC hE₂))
      (mul_le_mul_of_nonneg_right hHC (mul_nonneg (mul_nonneg hθN hPsi) (Real.rpow_nonneg ht.le _)))
    _=C*((η^p+θ^n)*(Ψ (8*t))*t^((n : ℝ)-p)+η^p*t^((n : ℝ)-p*δ)) := by dsimp only [E₁,E₂];ring

end StationaryHarmonicMaps.Analysis

end
