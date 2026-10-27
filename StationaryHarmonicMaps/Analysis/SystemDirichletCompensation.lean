module

public import StationaryHarmonicMaps.Analysis.SystemNativeForcingCompensation
public import StationaryHarmonicMaps.Analysis.DirichletBallWeakTest
public import StationaryHarmonicMaps.Analysis.OrthogonalConnectionIntegrability
public import StationaryHarmonicMaps.Analysis.OperatorFluxIntegrability

/-!
# The same Dirichlet component of the ordered matrix cutoff equation

The actual zero-boundary solution satisfies the original signed equation
with the literal matrix forcing and an actual L1 cutoff error. Its own
constructed power dual gives both ordinary pairings. Matrix compensation
and the actual error integral control this same original gradient.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Original compact-target data and the actual signed matrix Dirichlet
component equation give the same original gradient its compensated bound,
with the true L1 error and its exact physical scale retained. -/
theorem exists_compact_target_system_dirichlet_compensated_bound (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1<p) (hpTwo : p<2) (hpConj : (n : ℝ)<p/(p-1)) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (A B : ℝ) (hA : 0≤A) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),u x∈N.carrierSet) → 0≤η → η≤1 →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀χ : Domain n → ℝ,ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ⊆closedBall (0 : Domain n) (3/4 : ℝ) →
        (∀x,|χ x|≤A) → (∀(x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) →
        let c := ⨍y in ball (0 : Domain n) 1,u y
        let v := fun x=>χ x • (u x-c)
        let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
        let Φ := fun (x : Domain n) (r : ℝ)=>r^(p-(n : ℝ))*∫y in ball x r,(Real.sqrt (hsNormSq (Dv y)))^p
        let Ψ := fun t : ℝ=>sSup {z : ℝ | ∃x r,0<r ∧ r≤t ∧ z=Φ x r}
        let s := p/(p-1)
        ∀(Ω : OpenDomain n) (P : Domain n → Ambient (q*q)) (DP : Domain n → Gradient n (q*q)),
          MemW12Loc Ω P DP →
          (∀ᵐx∂volume.restrict Ω.val,star (R (P x))*R (P x)=1) →
          criticalGradientMorreySquare DP Ω.val≤ENNReal.ofReal (η^2) →
          ∀Z : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
            (∀i,MemLp (fun x=>E (Z x i)) 2 (volume.restrict Ω.val)) →
            HolderToCK.WeakPoissonOn Ω (fun x i=>E (Z x i)) (fun _=>0) →
            criticalGradientMorreySquare (fun x i=>E (Z x i)) Ω.val≤ENNReal.ofReal (η^2) →
            ∀(a : Domain n) (t : ℝ),0<t → t≤1/128 → closedBall a (t/2)⊆Ω.val →
              let W := fun x=>∑i : Fin n,Z x i (star (R (P x)) (Dv x i))
              ∀(e : Domain n → Ambient q),IntegrableOn e (ball a (t/2)) volume →
                ∀(f : Domain n → Ambient q) (Df : Domain n → Gradient n q),
                  HasZeroBoundaryValues (ballDomain a (t/2)) f Df →
                  HolderToCK.WeakPoissonOn (ballDomain a (t/2)) Df (fun x=>e x-W x) →
                  MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv ∧
                  IntegrableOn (fun x=>(hsNormSq (Df x))^(p/2)) (ball a (t/2)) volume ∧
                  (∫x in ball a (t/2),(hsNormSq (Df x))^(p/2))^(1/p)≤
                    C*(η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+
                      t^(1-(n : ℝ)/s)*(∫x in ball a (t/2),‖e x‖)) := by
  have hp : 0<p := zero_lt_one.trans hpOne
  let s := p/(p-1)
  have hs : 0<s := div_pos hp (sub_pos.mpr hpOne)
  obtain ⟨D,hD,HD1⟩ := exists_compact_target_system_forcing_supercritical_bound n hn p hpOne hpTwo.le hpConj q E R hER hE A B hA hB
  obtain ⟨G,K,hG,hK,Hdual⟩ := exists_bounded_dirichlet_dual_weak_test_ball n hn p hpOne hpTwo hpConj
  let C := 1+D*G^(1/s)+K
  have hCG : D*G^(1/s)≤C := by dsimp only [C];linarith only [hK]
  have hCK : K≤C := by
    have HDG : 0≤D*G^(1/s) := mul_nonneg hD.le (Real.rpow_nonneg hG.le _)
    dsimp only [C]
    linarith only [HDG]
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro N u Du η hu hTarget hη hηOne hCritical χ hχ hcχ hsχ hχA hDχ c v Dv Φ Ψ pConj
    Ω P DP hP hOrth hDPCritical Z hZ hDiv hZCritical a t ht htCap hClosed W e he f Df hf hEquation
  let r := t/2
  let μ := volume.restrict (ball a r)
  have hr : 0<r := half_pos ht
  have hSub : ball a r⊆Ω.val := ball_subset_closedBall.trans hClosed
  let I := ∫x,(hsNormSq (Df x))^(p/2) ∂μ
  have hI : 0≤I := integral_nonneg fun _=>Real.rpow_nonneg (hsNormSq_nonneg _) _
  obtain ⟨φ,Dφ,hφ,hφLp,_hInfinity,hSup,hInputI,_hOutputI,hMoment,Hweak⟩ := Hdual q a r hr f Df hf
  have hColumns (i : Fin n) : MemLp (fun x=>Dφ x i) (ENNReal.ofReal s) μ := by
    have H := memLp_hs_unflatten_exponent
      (fun x=>WithLp.toLp 2 (fun k : Fin (n*q)=>Dφ x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))
      (ENNReal.ofReal s) hφLp i
    exact H.ae_eq (Eventually.of_forall fun x=>congrFun (hs_unflatten_flatten (Dφ x)) i)
  obtain ⟨hV,hWφI,_hTestI,hComp⟩ := HD1 N u Du η hu hTarget hη hηOne hCritical
    χ hχ hcχ hsχ hχA hDχ Ω P DP hP hOrth hDPCritical Z hZ hDiv hZCritical
    a t ht htCap hClosed φ Dφ hφ hColumns
  have hPBound := ae_orthogonal_coordinates_bound E R hER hE P hOrth
  have hZLocal (i : Fin n) : LocallyMemL2 Ω (fun x=>Z x i) := by
    intro S hS hSΩ
    have H := R.lipschitz.comp_memLp (map_zero R)
      ((hZ i).mono_measure (Measure.restrict_mono_set volume hSΩ))
    exact H.ae_eq (Eventually.of_forall fun x=>hRE (Z x i))
  have hVΩ : MemW12 Ω v Dv := memW12_of_openDomain_subset hV (subset_univ _)
  have hFluxLocal := locallyMemL2_operator_flux hP hPBound R hVΩ.to_memW12Loc
  have hWLocal : LocallyIntegrableOn W Ω.val volume :=
    locallyIntegrableOn_operator_contraction Z hZLocal _ hFluxLocal
  have hWI : Integrable W μ :=
    (hWLocal.integrableOn_compact_subset hClosed (isCompact_closedBall a r)).mono_set ball_subset_closedBall
  have heI : Integrable e μ := he
  have hFI : Integrable (fun x=>e x-W x) μ := heI.sub hWI
  have hZero (i : Fin n) : MemLp (fun _ : Domain n=>(0 : Ambient q)) 2 μ := MemLp.zero
  have hEq : HolderToCK.WeakPoissonOn (ballDomain a r)
      (fun x i=>Df x i-(0 : Ambient q)) (fun x=>e x-W x) := by
    simpa only [sub_zero] using hEquation
  obtain ⟨_hZeroPair,hFφI,hPower⟩ := Hweak (fun _ _=>0) (fun x=>e x-W x) hZero hFI hEq
  simp only [inner_zero_left,Finset.sum_const_zero,integral_zero,zero_sub] at hPower
  have heφI : Integrable (fun x=>inner ℝ (e x) (φ x)) μ := by
    apply (hFφI.add hWφI).congr
    exact Eventually.of_forall fun x=>by
      change inner ℝ (e x-W x) (φ x)+inner ℝ (W x) (φ x)=inner ℝ (e x) (φ x)
      rw [inner_sub_left,sub_add_cancel]
  have hForcePair : (∫x,inner ℝ (e x-W x) (φ x) ∂μ)=
      (∫x,inner ℝ (e x) (φ x) ∂μ)-(∫x,inner ℝ (W x) (φ x) ∂μ) := by
    simp only [inner_sub_left]
    exact integral_sub heφI hWφI
  have hExact : I=(∫x,inner ℝ (W x) (φ x) ∂μ)-(∫x,inner ℝ (e x) (φ x) ∂μ) := by
    rw [hForcePair] at hPower
    exact hPower.trans (neg_sub _ _)
  let J := ∫x,(Real.sqrt (hsNormSq (Dφ x)))^s ∂μ
  have hJ : 0≤J := integral_nonneg fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hPowerHS (x : Domain n) : (Real.sqrt (hsNormSq (Dφ x)))^s=(hsNormSq (Dφ x))^(s/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (hsNormSq_nonneg _)]
    congr 1
    ring
  have hMoment' : J≤G*I := by simpa only [J,I,hPowerHS] using hMoment
  obtain ⟨_hV,hPsiNonneg,_hGrowth⟩ := cutoff_capped_envelope_lp_growth n hn p hpOne.le hpTwo.le A B hA hB
    q u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ t ht htCap
  let L := η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)
  have hL : 0≤L := mul_nonneg (mul_nonneg hη (Real.rpow_nonneg ht.le _)) (Real.rpow_nonneg hPsiNonneg _)
  have hComp' : |∫x,inner ℝ (W x) (φ x) ∂μ|≤(D*L*G^(1/s))*I^(1/s) := by
    calc
      _≤D*L*J^(1/s) := by simpa only [L,J,mul_assoc] using hComp
      _≤D*L*(G*I)^(1/s) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hJ hMoment' (one_div_nonneg.mpr hs.le)) (mul_nonneg hD.le hL)
      _=_ := by rw [Real.mul_rpow hG.le hI];ring
  let H := K*r^(1-(n : ℝ)/s)*I^(1/s)
  have hH : 0≤H := mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg hr.le _)) (Real.rpow_nonneg hI _)
  let Err := ∫x,‖e x‖ ∂μ
  have hErr : 0≤Err := integral_nonneg fun _=>norm_nonneg _
  have hErrBound : |∫x,inner ℝ (e x) (φ x) ∂μ|≤H*Err := by
    calc
      _≤∫x,‖inner ℝ (e x) (φ x)‖ ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x=>inner ℝ (e x) (φ x))
      _≤∫x,H*‖e x‖ ∂μ := integral_mono_ae heφI.norm (heI.norm.const_mul H) (by
        filter_upwards [hSup] with x hx
        exact (norm_inner_le_norm (𝕜:=ℝ) (e x) (φ x)).trans
          ((mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans_eq (mul_comm _ _)))
      _=H*Err := integral_const_mul _ _
  let B₀ := D*L*G^(1/s)+K*r^(1-(n : ℝ)/s)*Err
  have hB₀ : 0≤B₀ := add_nonneg (mul_nonneg (mul_nonneg hD.le hL) (Real.rpow_nonneg hG.le _))
    (mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg hr.le _)) hErr)
  have hStep : I≤B₀*I^(1/s) := by
    have HN := neg_le_abs (∫x,inner ℝ (e x) (φ x) ∂μ)
    have HW := le_abs_self (∫x,inner ℝ (W x) (φ x) ∂μ)
    calc
      I=(∫x,inner ℝ (W x) (φ x) ∂μ)-(∫x,inner ℝ (e x) (φ x) ∂μ) := hExact
      _≤|∫x,inner ℝ (W x) (φ x) ∂μ|+|∫x,inner ℝ (e x) (φ x) ∂μ| := by linarith only [HN,HW]
      _≤(D*L*G^(1/s))*I^(1/s)+H*Err := add_le_add hComp' hErrBound
      _=B₀*I^(1/s) := by dsimp only [B₀,H];ring
  have hRoot : I^(1/p)≤B₀ := by
    by_cases hZero : I=0
    · rw [hZero,Real.zero_rpow (one_div_pos.mpr hp).ne']
      exact hB₀
    · have hPos : 0<I := lt_of_le_of_ne hI (Ne.symm hZero)
      have hConj : p.HolderConjugate s := Real.HolderConjugate.conjExponent hpOne
      have hInv : 1/p+1/s=1 := by simpa only [one_div] using hConj.inv_add_inv_eq_one
      have hSplit : I=I^(1/p)*I^(1/s) := by rw [←Real.rpow_add hPos,hInv,Real.rpow_one]
      exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hPos (1/s))).mp
        (by simpa only [mul_comm] using hSplit.symm.trans_le hStep)
  have hExponent : 0≤1-(n : ℝ)/s := (sub_pos.mpr ((div_lt_one hs).mpr hpConj)).le
  have hRadius : r^(1-(n : ℝ)/s)≤t^(1-(n : ℝ)/s) :=
    Real.rpow_le_rpow hr.le (by dsimp only [r];linarith only [ht]) hExponent
  refine ⟨hV,hInputI,hRoot.trans ?_⟩
  calc
    B₀≤(D*G^(1/s))*L+K*t^(1-(n : ℝ)/s)*Err := by
      have HN := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRadius hK.le) hErr
      dsimp only [B₀]
      nlinarith only [HN]
    _≤C*L+C*(t^(1-(n : ℝ)/s)*Err) := add_le_add
      (mul_le_mul_of_nonneg_right hCG hL)
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hCK (mul_nonneg (Real.rpow_nonneg ht.le _) hErr))
    _=C*(L+t^(1-(n : ℝ)/s)*Err) := by ring

@[expose] def effectiveSystemDirichletConstant (n q : ℕ) : ℚ :=
  1+effectiveSystemForcingConstant n q*(1+(dirichletFixedHighMomentMajorant n : ℚ))+
    (boundedDirichletFixedTestMajorant n : ℚ)

theorem exists_compact_target_system_dirichlet_compensated_bound_effective (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1<p) (hpTwo : p<2) (hpConj : (n : ℝ)<p/(p-1)) (hConjugate : p/(p-1)=((2*n+1 : ℕ) : ℝ)) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (A B : ℝ) (hA : 0≤A) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ C = (effectiveSystemDirichletConstant n q : ℝ) ∧ ∀(N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),u x∈N.carrierSet) → 0≤η → η≤1 →
      criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀χ : Domain n → ℝ,ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ⊆closedBall (0 : Domain n) (3/4 : ℝ) →
        (∀x,|χ x|≤A) → (∀(x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) →
        let c := ⨍y in ball (0 : Domain n) 1,u y
        let v := fun x=>χ x • (u x-c)
        let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
        let Φ := fun (x : Domain n) (r : ℝ)=>r^(p-(n : ℝ))*∫y in ball x r,(Real.sqrt (hsNormSq (Dv y)))^p
        let Ψ := fun t : ℝ=>sSup {z : ℝ | ∃x r,0<r ∧ r≤t ∧ z=Φ x r}
        let s := p/(p-1)
        ∀(Ω : OpenDomain n) (P : Domain n → Ambient (q*q)) (DP : Domain n → Gradient n (q*q)),
          MemW12Loc Ω P DP →
          (∀ᵐx∂volume.restrict Ω.val,star (R (P x))*R (P x)=1) →
          criticalGradientMorreySquare DP Ω.val≤ENNReal.ofReal (η^2) →
          ∀Z : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q),
            (∀i,MemLp (fun x=>E (Z x i)) 2 (volume.restrict Ω.val)) →
            HolderToCK.WeakPoissonOn Ω (fun x i=>E (Z x i)) (fun _=>0) →
            criticalGradientMorreySquare (fun x i=>E (Z x i)) Ω.val≤ENNReal.ofReal (η^2) →
            ∀(a : Domain n) (t : ℝ),0<t → t≤1/128 → closedBall a (t/2)⊆Ω.val →
              let W := fun x=>∑i : Fin n,Z x i (star (R (P x)) (Dv x i))
              ∀(e : Domain n → Ambient q),IntegrableOn e (ball a (t/2)) volume →
                ∀(f : Domain n → Ambient q) (Df : Domain n → Gradient n q),
                  HasZeroBoundaryValues (ballDomain a (t/2)) f Df →
                  HolderToCK.WeakPoissonOn (ballDomain a (t/2)) Df (fun x=>e x-W x) →
                  MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv ∧
                  IntegrableOn (fun x=>(hsNormSq (Df x))^(p/2)) (ball a (t/2)) volume ∧
                  (∫x in ball a (t/2),(hsNormSq (Df x))^(p/2))^(1/p)≤
                    C*(η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)+
                      t^(1-(n : ℝ)/s)*(∫x in ball a (t/2),‖e x‖)) := by
  have hp : 0<p := zero_lt_one.trans hpOne
  let s := p/(p-1)
  have hs : 0<s := div_pos hp (sub_pos.mpr hpOne)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hHalf : (1/2 : ℝ) ≤ 1-(n : ℝ)/(p/(p-1)) := by
    rw [hConjugate]
    have hden : (0 : ℝ) < ((2*n+1 : ℕ) : ℝ) := by positivity
    have H : (n : ℝ)/((2*n+1 : ℕ) : ℝ) ≤ (1/2 : ℝ) :=
      (div_le_iff₀ hden).mpr (by push_cast; linarith)
    linarith only [H]
  obtain ⟨D,hD,hDF,HD1⟩ := exists_compact_target_system_forcing_supercritical_bound_effective
    n hn p hpOne hpTwo.le hpConj hHalf q E R hER hE A B hA hB
  obtain ⟨G,K,hG,hK,hGF,hKF,Hdual⟩ := exists_bounded_dirichlet_dual_weak_test_ball_fixed_explicit
    n hn p hpOne hpTwo hpConj hConjugate
  let C : ℝ := effectiveSystemDirichletConstant n q
  have hCast : C = 1+D*(1+G)+K := by
    dsimp only [C,effectiveSystemDirichletConstant]
    simp only [Rat.cast_add,Rat.cast_one,Rat.cast_mul,Rat.cast_natCast]
    rw [hDF,hGF,hKF]
  have hGrow : G^(1/s) ≤ 1+G :=
    effective_root_majorant_helper G s hG.le (by dsimp only [s]; linarith only [hpConj,hnR])
  have hCG : D*G^(1/s) ≤ C := by
    have H := mul_le_mul_of_nonneg_left hGrow hD.le
    rw [hCast]
    linarith only [H,hK]
  have hCK : K ≤ C := by
    rw [hCast]
    have H : 0 ≤ D*(1+G) := by positivity
    linarith only [H]
  have hC : 0<C := by rw [hCast]; positivity
  refine ⟨C,hC,rfl,?_⟩
  intro N u Du η hu hTarget hη hηOne hCritical χ hχ hcχ hsχ hχA hDχ c v Dv Φ Ψ pConj
    Ω P DP hP hOrth hDPCritical Z hZ hDiv hZCritical a t ht htCap hClosed W e he f Df hf hEquation
  let r := t/2
  let μ := volume.restrict (ball a r)
  have hr : 0<r := half_pos ht
  have hSub : ball a r⊆Ω.val := ball_subset_closedBall.trans hClosed
  let I := ∫x,(hsNormSq (Df x))^(p/2) ∂μ
  have hI : 0≤I := integral_nonneg fun _=>Real.rpow_nonneg (hsNormSq_nonneg _) _
  obtain ⟨φ,Dφ,hφ,hφLp,_hInfinity,hSup,hInputI,_hOutputI,hMoment,Hweak⟩ := Hdual q a r hr f Df hf
  have hColumns (i : Fin n) : MemLp (fun x=>Dφ x i) (ENNReal.ofReal s) μ := by
    have H := memLp_hs_unflatten_exponent
      (fun x=>WithLp.toLp 2 (fun k : Fin (n*q)=>Dφ x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))
      (ENNReal.ofReal s) hφLp i
    exact H.ae_eq (Eventually.of_forall fun x=>congrFun (hs_unflatten_flatten (Dφ x)) i)
  obtain ⟨hV,hWφI,_hTestI,hComp⟩ := HD1 N u Du η hu hTarget hη hηOne hCritical
    χ hχ hcχ hsχ hχA hDχ Ω P DP hP hOrth hDPCritical Z hZ hDiv hZCritical
    a t ht htCap hClosed φ Dφ hφ hColumns
  have hPBound := ae_orthogonal_coordinates_bound E R hER hE P hOrth
  have hZLocal (i : Fin n) : LocallyMemL2 Ω (fun x=>Z x i) := by
    intro S hS hSΩ
    have H := R.lipschitz.comp_memLp (map_zero R)
      ((hZ i).mono_measure (Measure.restrict_mono_set volume hSΩ))
    exact H.ae_eq (Eventually.of_forall fun x=>hRE (Z x i))
  have hVΩ : MemW12 Ω v Dv := memW12_of_openDomain_subset hV (subset_univ _)
  have hFluxLocal := locallyMemL2_operator_flux hP hPBound R hVΩ.to_memW12Loc
  have hWLocal : LocallyIntegrableOn W Ω.val volume :=
    locallyIntegrableOn_operator_contraction Z hZLocal _ hFluxLocal
  have hWI : Integrable W μ :=
    (hWLocal.integrableOn_compact_subset hClosed (isCompact_closedBall a r)).mono_set ball_subset_closedBall
  have heI : Integrable e μ := he
  have hFI : Integrable (fun x=>e x-W x) μ := heI.sub hWI
  have hZero (i : Fin n) : MemLp (fun _ : Domain n=>(0 : Ambient q)) 2 μ := MemLp.zero
  have hEq : HolderToCK.WeakPoissonOn (ballDomain a r)
      (fun x i=>Df x i-(0 : Ambient q)) (fun x=>e x-W x) := by
    simpa only [sub_zero] using hEquation
  obtain ⟨_hZeroPair,hFφI,hPower⟩ := Hweak (fun _ _=>0) (fun x=>e x-W x) hZero hFI hEq
  simp only [inner_zero_left,Finset.sum_const_zero,integral_zero,zero_sub] at hPower
  have heφI : Integrable (fun x=>inner ℝ (e x) (φ x)) μ := by
    apply (hFφI.add hWφI).congr
    exact Eventually.of_forall fun x=>by
      change inner ℝ (e x-W x) (φ x)+inner ℝ (W x) (φ x)=inner ℝ (e x) (φ x)
      rw [inner_sub_left,sub_add_cancel]
  have hForcePair : (∫x,inner ℝ (e x-W x) (φ x) ∂μ)=
      (∫x,inner ℝ (e x) (φ x) ∂μ)-(∫x,inner ℝ (W x) (φ x) ∂μ) := by
    simp only [inner_sub_left]
    exact integral_sub heφI hWφI
  have hExact : I=(∫x,inner ℝ (W x) (φ x) ∂μ)-(∫x,inner ℝ (e x) (φ x) ∂μ) := by
    rw [hForcePair] at hPower
    exact hPower.trans (neg_sub _ _)
  let J := ∫x,(Real.sqrt (hsNormSq (Dφ x)))^s ∂μ
  have hJ : 0≤J := integral_nonneg fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hPowerHS (x : Domain n) : (Real.sqrt (hsNormSq (Dφ x)))^s=(hsNormSq (Dφ x))^(s/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (hsNormSq_nonneg _)]
    congr 1
    ring
  have hMoment' : J≤G*I := by simpa only [J,I,hPowerHS] using hMoment
  obtain ⟨_hV,hPsiNonneg,_hGrowth⟩ := cutoff_capped_envelope_lp_growth n hn p hpOne.le hpTwo.le A B hA hB
    q u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ t ht htCap
  let L := η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)
  have hL : 0≤L := mul_nonneg (mul_nonneg hη (Real.rpow_nonneg ht.le _)) (Real.rpow_nonneg hPsiNonneg _)
  have hComp' : |∫x,inner ℝ (W x) (φ x) ∂μ|≤(D*L*G^(1/s))*I^(1/s) := by
    calc
      _≤D*L*J^(1/s) := by simpa only [L,J,mul_assoc] using hComp
      _≤D*L*(G*I)^(1/s) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hJ hMoment' (one_div_nonneg.mpr hs.le)) (mul_nonneg hD.le hL)
      _=_ := by rw [Real.mul_rpow hG.le hI];ring
  let H := K*r^(1-(n : ℝ)/s)*I^(1/s)
  have hH : 0≤H := mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg hr.le _)) (Real.rpow_nonneg hI _)
  let Err := ∫x,‖e x‖ ∂μ
  have hErr : 0≤Err := integral_nonneg fun _=>norm_nonneg _
  have hErrBound : |∫x,inner ℝ (e x) (φ x) ∂μ|≤H*Err := by
    calc
      _≤∫x,‖inner ℝ (e x) (φ x)‖ ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x=>inner ℝ (e x) (φ x))
      _≤∫x,H*‖e x‖ ∂μ := integral_mono_ae heφI.norm (heI.norm.const_mul H) (by
        filter_upwards [hSup] with x hx
        exact (norm_inner_le_norm (𝕜:=ℝ) (e x) (φ x)).trans
          ((mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans_eq (mul_comm _ _)))
      _=H*Err := integral_const_mul _ _
  let B₀ := D*L*G^(1/s)+K*r^(1-(n : ℝ)/s)*Err
  have hB₀ : 0≤B₀ := add_nonneg (mul_nonneg (mul_nonneg hD.le hL) (Real.rpow_nonneg hG.le _))
    (mul_nonneg (mul_nonneg hK.le (Real.rpow_nonneg hr.le _)) hErr)
  have hStep : I≤B₀*I^(1/s) := by
    have HN := neg_le_abs (∫x,inner ℝ (e x) (φ x) ∂μ)
    have HW := le_abs_self (∫x,inner ℝ (W x) (φ x) ∂μ)
    calc
      I=(∫x,inner ℝ (W x) (φ x) ∂μ)-(∫x,inner ℝ (e x) (φ x) ∂μ) := hExact
      _≤|∫x,inner ℝ (W x) (φ x) ∂μ|+|∫x,inner ℝ (e x) (φ x) ∂μ| := by linarith only [HN,HW]
      _≤(D*L*G^(1/s))*I^(1/s)+H*Err := add_le_add hComp' hErrBound
      _=B₀*I^(1/s) := by dsimp only [B₀,H];ring
  have hRoot : I^(1/p)≤B₀ := by
    by_cases hZero : I=0
    · rw [hZero,Real.zero_rpow (one_div_pos.mpr hp).ne']
      exact hB₀
    · have hPos : 0<I := lt_of_le_of_ne hI (Ne.symm hZero)
      have hConj : p.HolderConjugate s := Real.HolderConjugate.conjExponent hpOne
      have hInv : 1/p+1/s=1 := by simpa only [one_div] using hConj.inv_add_inv_eq_one
      have hSplit : I=I^(1/p)*I^(1/s) := by rw [←Real.rpow_add hPos,hInv,Real.rpow_one]
      exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hPos (1/s))).mp
        (by simpa only [mul_comm] using hSplit.symm.trans_le hStep)
  have hExponent : 0≤1-(n : ℝ)/s := (sub_pos.mpr ((div_lt_one hs).mpr hpConj)).le
  have hRadius : r^(1-(n : ℝ)/s)≤t^(1-(n : ℝ)/s) :=
    Real.rpow_le_rpow hr.le (by dsimp only [r];linarith only [ht]) hExponent
  refine ⟨hV,hInputI,hRoot.trans ?_⟩
  calc
    B₀≤(D*G^(1/s))*L+K*t^(1-(n : ℝ)/s)*Err := by
      have HN := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRadius hK.le) hErr
      dsimp only [B₀]
      nlinarith only [HN]
    _≤C*L+C*(t^(1-(n : ℝ)/s)*Err) := add_le_add
      (mul_le_mul_of_nonneg_right hCG hL)
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hCK (mul_nonneg (Real.rpow_nonneg ht.le _) hErr))
    _=C*(L+t^(1-(n : ℝ)/s)*Err) := by ring

end StationaryHarmonicMaps.Analysis

end
