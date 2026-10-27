module

public import StationaryHarmonicMaps.Analysis.SystemCutoffCompensation
public import StationaryHarmonicMaps.Analysis.SystemMatrixSupercriticalEnergy
public import StationaryHarmonicMaps.Analysis.OrthogonalCoefficientBounds
public import StationaryHarmonicMaps.Analysis.EffectiveOperatorCoordinates

/-!
# Scale-correct compensation of the actual ordered matrix forcing

The original compact-target cutoff supplies the actual envelope and
native scalar observations. The original supercritical W0 test supplies
all matrix-test energies. Original critical frame and connection bounds
give the exact physical radius power in the ordinary forcing pairing.
-/

@[expose] public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- The actual source matrix forcing has its ordinary compensated
supercritical native-test bound. Matrix tests, their energies and all
pairing integrability are proved from original data inside the proof. -/
theorem exists_compact_target_system_forcing_supercritical_bound (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1<p) (hpTwo : p≤2) (hpConj : (n : ℝ)<p/(p-1)) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀z,E (R z)=z)
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
              ∀(φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
                HasZeroBoundaryValues (ballDomain a (t/2)) φ Dφ →
                (∀i,MemLp (fun x=>Dφ x i) (ENNReal.ofReal s) (volume.restrict (ball a (t/2)))) →
                let W := fun x=>∑i : Fin n,Z x i (star (R (P x)) (Dv x i))
                MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv ∧
                IntegrableOn (fun x=>inner ℝ (W x) (φ x)) (ball a (t/2)) volume ∧
                IntegrableOn (fun x=>(Real.sqrt (hsNormSq (Dφ x)))^s) (ball a (t/2)) volume ∧
                |∫x in ball a (t/2),inner ℝ (W x) (φ x)|≤
                  C*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)*
                    (∫x in ball a (t/2),(Real.sqrt (hsNormSq (Dφ x)))^s)^(1/s) := by
  have hp : 0<p := zero_lt_one.trans hpOne
  let s := p/(p-1)
  obtain ⟨D,hD,Hpair⟩ := exists_system_cutoff_compensated_pairing_bound n hn p hpOne.le hpTwo A B hA hB
  obtain ⟨F,hF,Henergy⟩ := exists_system_matrix_test_supercritical_energy n hn s hpConj (q*q) q E R
  obtain ⟨S,hS,Hsup⟩ := exists_native_zeroBoundary_supercritical_bound n hn s hpConj
  let Q := ∑j : Fin q,‖PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin q=>ℝ) j‖
  have hQ : 0≤Q := Finset.sum_nonneg fun _ _=>norm_nonneg _
  let C := 2*D*F*(1+Q)
  have hC : 0<C := mul_pos (mul_pos (mul_pos (by norm_num) hD) hF) (by positivity)
  refine ⟨C,hC,?_⟩
  intro N u Du η hu hTarget hη hηOne hCritical χ hχ hcχ hsχ hχA hDχ c v Dv Φ Ψ pConj
    Ω P DP hP hOrth hDPCritical Z hZ hDiv hZCritical a t ht htCap hClosed φ Dφ hφ hDφ W
  let r := t/2
  have hr : 0<r := half_pos ht
  let μ := volume.restrict (ball a r)
  have hSub : ball a r⊆Ω.val := ball_subset_closedBall.trans hClosed
  have ha : a∈Ω.val := hClosed (mem_closedBall_self hr.le)
  have hPBall : MemW12 (ballDomain a r) P DP := hP.memW12_ball hClosed
  have hPBound : ∀ᵐx∂μ,‖P x‖≤Real.sqrt (q : ℝ) :=
    ae_restrict_of_ae_restrict_of_subset hSub (ae_orthogonal_coordinates_bound E R hER hE P hOrth)
  have hOrthBall := ae_restrict_of_ae_restrict_of_subset hSub hOrth
  have hZBall (i : Fin n) : MemLp (fun x=>E (Z x i)) 2 μ :=
    (hZ i).mono_measure (Measure.restrict_mono_set volume hSub)
  obtain ⟨hMoment,hφBound,_hTop⟩ := Hsup q a r φ Dφ hr hφ hDφ
  obtain ⟨_hMoment',_hT,hEnergy⟩ := Henergy a r hr P DP hPBall (Real.sqrt (q : ℝ)) hPBound hOrthBall
    φ Dφ hφ hDφ
  let J := (∫x in ball a r,(Real.sqrt (hsNormSq (Dφ x)))^s)^(1/s)
  have hJ : 0≤J := Real.rpow_nonneg (integral_nonneg fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _) _
  let T := fun (j : Fin q) x=>systemMatrixTestCoefficient E R j (P x) (φ x)
  let DT := fun (j : Fin q) x i=>systemMatrixTestCoefficient E R j (DP x i) (φ x)+
    systemMatrixTestCoefficient E R j (P x) (Dφ x i)
  obtain ⟨_hV,_hT',hWI,hBound⟩ := Hpair q N u Du η hu hTarget hη hCritical χ hχ hcχ hsχ hχA hDχ
    a t ht htCap (q*q) E R hE P DP hPBall (Real.sqrt (q : ℝ)) hPBound Z hZBall (hDiv.mono hSub)
    φ Dφ hφ (S*r^(1-(n : ℝ)/s)*J) hφBound
  obtain ⟨hV,hPsiNonneg,_hGrowth⟩ := cutoff_capped_envelope_lp_growth n hn p hpOne.le hpTwo A B hA hB
    q u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ t ht htCap
  have hPsi : 0≤(Ψ (8*t))^(1/p) := Real.rpow_nonneg hPsiNonneg _
  have hPE := sqrt_integral_hsNormSq_le_of_criticalMorrey DP ha hr (sq_nonneg η)
    (subset_inter le_rfl hSub) hPBall.2.2 hDPCritical
  have hZE := sqrt_integral_hsNormSq_le_of_criticalMorrey (fun x i=>E (Z x i)) ha hr (sq_nonneg η)
    (subset_inter le_rfl hSub) hZBall hZCritical
  rw [Real.sqrt_sq hη] at hPE hZE
  have hFrameRadius : r^((n : ℝ)/2-1)*r^(1-(n : ℝ)/s)=r^((n : ℝ)/2-(n : ℝ)/s) := by
    rw [←Real.rpow_add hr]
    congr 1
    ring
  have hEach (j : Fin q) : Real.sqrt (∫x in ball a r,hsNormSq (DT j x))≤
      (2*F)*r^((n : ℝ)/2-(n : ℝ)/s)*J := by
    calc
      _≤F*(Real.sqrt (∫x in ball a r,hsNormSq (DP x))*r^(1-(n : ℝ)/s)+r^((n : ℝ)/2-(n : ℝ)/s))*J := hEnergy j
      _≤F*((η*r^((n : ℝ)/2-1))*r^(1-(n : ℝ)/s)+r^((n : ℝ)/2-(n : ℝ)/s))*J :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_right hPE (Real.rpow_nonneg hr.le _)) le_rfl) hF.le) hJ
      _=F*((η+1)*r^((n : ℝ)/2-(n : ℝ)/s))*J := by rw [mul_assoc η,hFrameRadius];ring
      _≤F*(2*r^((n : ℝ)/2-(n : ℝ)/s))*J :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by linarith only [hηOne] : η+1≤2) (Real.rpow_nonneg hr.le _)) hF.le) hJ
      _=_ := by ring
  have hSum : (∑j : Fin q,‖PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin q=>ℝ) j‖*
      Real.sqrt (∫x in ball a r,hsNormSq (DT j x)))≤(1+Q)*((2*F)*r^((n : ℝ)/2-(n : ℝ)/s)*J) := by
    calc
      _≤∑j : Fin q,‖PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin q=>ℝ) j‖*((2*F)*r^((n : ℝ)/2-(n : ℝ)/s)*J) :=
        Finset.sum_le_sum fun j _=>mul_le_mul_of_nonneg_left (hEach j) (norm_nonneg _)
      _=Q*((2*F)*r^((n : ℝ)/2-(n : ℝ)/s)*J) := (Finset.sum_mul _ _ _).symm
      _≤_ := mul_le_mul_of_nonneg_right (by linarith : Q≤1+Q)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hF.le) (Real.rpow_nonneg hr.le _)) hJ)
  have hConj : 1/s=1-1/p := by
    dsimp only [s]
    field_simp [hp.ne',(sub_pos.mpr hpOne).ne']
  have hRadiusProduct : r^((n : ℝ)/2-1)*r^((n : ℝ)/2-(n : ℝ)/s)=r^((n : ℝ)/p-1) := by
    rw [←Real.rpow_add hr]
    have hDiv : (n : ℝ)/s=(n : ℝ)*(1-1/p) := by rw [div_eq_mul_inv,←one_div,hConj]
    congr 1
    rw [hDiv]
    ring
  have hnReal : (2 : ℝ)≤n := by exact_mod_cast hn
  have hExponent : 0≤(n : ℝ)/p-1 := sub_nonneg.mpr ((one_le_div hp).mpr (hpTwo.trans hnReal))
  have hRadius : r^((n : ℝ)/p-1)≤t^((n : ℝ)/p-1) :=
    Real.rpow_le_rpow hr.le (by dsimp only [r];linarith only [ht]) hExponent
  refine ⟨hV,hWI,hMoment,hBound.trans ?_⟩
  calc
    _≤D*(Ψ (8*t))^(1/p)*(η*r^((n : ℝ)/2-1))*((1+Q)*((2*F)*r^((n : ℝ)/2-(n : ℝ)/s)*J)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hZE (mul_nonneg hD.le hPsi)) hSum
        (Finset.sum_nonneg fun j _=>mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
        (mul_nonneg (mul_nonneg hD.le hPsi) (mul_nonneg hη (Real.rpow_nonneg hr.le _)))
    _=C*η*(r^((n : ℝ)/2-1)*r^((n : ℝ)/2-(n : ℝ)/s))*(Ψ (8*t))^(1/p)*J := by dsimp only [C];ring
    _=C*η*r^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)*J := by rw [hRadiusProduct]
    _≤C*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)*J :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRadius (mul_nonneg hC.le hη)) hPsi) hJ

def effectiveSystemForcingConstant (n q : ℕ) : ℚ :=
  2*effectiveCompactTargetEnvelopePairingConstant n*
    (effectiveSystemMatrixSupercriticalConstant n q:ℚ)*(1+q)

theorem exists_compact_target_system_forcing_supercritical_bound_effective (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1<p) (hpTwo : p≤2) (hpConj : (n : ℝ)<p/(p-1))
    (hHalf : (1/2:ℝ)≤1-(n:ℝ)/(p/(p-1))) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (A B : ℝ) (hA : 0≤A) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ C=(effectiveSystemForcingConstant n q:ℝ) ∧ ∀(N : CompactC2EmbeddedTarget q)
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
              ∀(φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
                HasZeroBoundaryValues (ballDomain a (t/2)) φ Dφ →
                (∀i,MemLp (fun x=>Dφ x i) (ENNReal.ofReal s) (volume.restrict (ball a (t/2)))) →
                let W := fun x=>∑i : Fin n,Z x i (star (R (P x)) (Dv x i))
                MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv ∧
                IntegrableOn (fun x=>inner ℝ (W x) (φ x)) (ball a (t/2)) volume ∧
                IntegrableOn (fun x=>(Real.sqrt (hsNormSq (Dφ x)))^s) (ball a (t/2)) volume ∧
                |∫x in ball a (t/2),inner ℝ (W x) (φ x)|≤
                  C*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)*
                    (∫x in ball a (t/2),(Real.sqrt (hsNormSq (Dφ x)))^s)^(1/s) := by
  have hp : 0<p := zero_lt_one.trans hpOne
  let s := p/(p-1)
  obtain ⟨D,hD,hDEq,Hpair⟩ := exists_system_cutoff_compensated_pairing_bound_explicit n hn p hpOne.le hpTwo A B hA hB
  obtain ⟨F,hF,hFEq,Henergy⟩ := exists_system_matrix_test_supercritical_energy_effective n hn s hpConj hHalf (q*q) q E R
    (operator_coordinate_encoder_norm_le_dim_add_one q E hE)
    (operator_coordinate_decoder_norm_le_one q E R hER hE)
  obtain ⟨S,hS,_hSEq,Hsup⟩ := exists_native_zeroBoundary_supercritical_bound_uniform_explicit n hn s hpConj hHalf
  let Q : ℝ := (q:ℝ)
  have hQ : 0≤Q := Nat.cast_nonneg q
  have hProj (j : Fin q) : ‖PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin q=>ℝ) j‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    simpa only [PiLp.proj_apply,one_mul] using PiLp.norm_apply_le x j
  have hProjSum : (∑j : Fin q,‖PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin q=>ℝ) j‖)≤Q := by
    calc
      _≤∑_j : Fin q,(1:ℝ) := Finset.sum_le_sum fun j _=>hProj j
      _=Q := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one];rfl
  let C := 2*D*F*(1+Q)
  have hC : 0<C := mul_pos (mul_pos (mul_pos (by norm_num) hD) hF) (by positivity)
  have hCEq : C=(effectiveSystemForcingConstant n q:ℝ) := by
    dsimp only [C,Q,effectiveSystemForcingConstant]
    rw [hDEq,hFEq]
    push_cast
    rfl
  refine ⟨C,hC,hCEq,?_⟩
  intro N u Du η hu hTarget hη hηOne hCritical χ hχ hcχ hsχ hχA hDχ c v Dv Φ Ψ pConj
    Ω P DP hP hOrth hDPCritical Z hZ hDiv hZCritical a t ht htCap hClosed φ Dφ hφ hDφ W
  let r := t/2
  have hr : 0<r := half_pos ht
  let μ := volume.restrict (ball a r)
  have hSub : ball a r⊆Ω.val := ball_subset_closedBall.trans hClosed
  have ha : a∈Ω.val := hClosed (mem_closedBall_self hr.le)
  have hPBall : MemW12 (ballDomain a r) P DP := hP.memW12_ball hClosed
  have hPBound : ∀ᵐx∂μ,‖P x‖≤Real.sqrt (q : ℝ) :=
    ae_restrict_of_ae_restrict_of_subset hSub (ae_orthogonal_coordinates_bound E R hER hE P hOrth)
  have hOrthBall := ae_restrict_of_ae_restrict_of_subset hSub hOrth
  have hZBall (i : Fin n) : MemLp (fun x=>E (Z x i)) 2 μ :=
    (hZ i).mono_measure (Measure.restrict_mono_set volume hSub)
  obtain ⟨hMoment,hφBound,_hTop⟩ := Hsup q a r φ Dφ hr hφ hDφ
  obtain ⟨_hMoment',_hT,hEnergy⟩ := Henergy a r hr P DP hPBall (Real.sqrt (q : ℝ)) hPBound hOrthBall
    φ Dφ hφ hDφ
  let J := (∫x in ball a r,(Real.sqrt (hsNormSq (Dφ x)))^s)^(1/s)
  have hJ : 0≤J := Real.rpow_nonneg (integral_nonneg fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _) _
  let T := fun (j : Fin q) x=>systemMatrixTestCoefficient E R j (P x) (φ x)
  let DT := fun (j : Fin q) x i=>systemMatrixTestCoefficient E R j (DP x i) (φ x)+
    systemMatrixTestCoefficient E R j (P x) (Dφ x i)
  obtain ⟨_hV,_hT',hWI,hBound⟩ := Hpair q N u Du η hu hTarget hη hCritical χ hχ hcχ hsχ hχA hDχ
    a t ht htCap (q*q) E R hE P DP hPBall (Real.sqrt (q : ℝ)) hPBound Z hZBall (hDiv.mono hSub)
    φ Dφ hφ (S*r^(1-(n : ℝ)/s)*J) hφBound
  obtain ⟨hV,hPsiNonneg,_hGrowth⟩ := cutoff_capped_envelope_lp_growth n hn p hpOne.le hpTwo A B hA hB
    q u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ t ht htCap
  have hPsi : 0≤(Ψ (8*t))^(1/p) := Real.rpow_nonneg hPsiNonneg _
  have hPE := sqrt_integral_hsNormSq_le_of_criticalMorrey DP ha hr (sq_nonneg η)
    (subset_inter le_rfl hSub) hPBall.2.2 hDPCritical
  have hZE := sqrt_integral_hsNormSq_le_of_criticalMorrey (fun x i=>E (Z x i)) ha hr (sq_nonneg η)
    (subset_inter le_rfl hSub) hZBall hZCritical
  rw [Real.sqrt_sq hη] at hPE hZE
  have hFrameRadius : r^((n : ℝ)/2-1)*r^(1-(n : ℝ)/s)=r^((n : ℝ)/2-(n : ℝ)/s) := by
    rw [←Real.rpow_add hr]
    congr 1
    ring
  have hEach (j : Fin q) : Real.sqrt (∫x in ball a r,hsNormSq (DT j x))≤
      (2*F)*r^((n : ℝ)/2-(n : ℝ)/s)*J := by
    calc
      _≤F*(Real.sqrt (∫x in ball a r,hsNormSq (DP x))*r^(1-(n : ℝ)/s)+r^((n : ℝ)/2-(n : ℝ)/s))*J := hEnergy j
      _≤F*((η*r^((n : ℝ)/2-1))*r^(1-(n : ℝ)/s)+r^((n : ℝ)/2-(n : ℝ)/s))*J :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_right hPE (Real.rpow_nonneg hr.le _)) le_rfl) hF.le) hJ
      _=F*((η+1)*r^((n : ℝ)/2-(n : ℝ)/s))*J := by rw [mul_assoc η,hFrameRadius];ring
      _≤F*(2*r^((n : ℝ)/2-(n : ℝ)/s))*J :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by linarith only [hηOne] : η+1≤2) (Real.rpow_nonneg hr.le _)) hF.le) hJ
      _=_ := by ring
  have hSum : (∑j : Fin q,‖PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin q=>ℝ) j‖*
      Real.sqrt (∫x in ball a r,hsNormSq (DT j x)))≤(1+Q)*((2*F)*r^((n : ℝ)/2-(n : ℝ)/s)*J) := by
    calc
      _≤∑j : Fin q,‖PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin q=>ℝ) j‖*((2*F)*r^((n : ℝ)/2-(n : ℝ)/s)*J) :=
        Finset.sum_le_sum fun j _=>mul_le_mul_of_nonneg_left (hEach j) (norm_nonneg _)
      _≤Q*((2*F)*r^((n : ℝ)/2-(n : ℝ)/s)*J) := by
        rw [←Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hProjSum (by positivity)
      _≤_ := mul_le_mul_of_nonneg_right (by linarith : Q≤1+Q)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hF.le) (Real.rpow_nonneg hr.le _)) hJ)
  have hConj : 1/s=1-1/p := by
    dsimp only [s]
    field_simp [hp.ne',(sub_pos.mpr hpOne).ne']
  have hRadiusProduct : r^((n : ℝ)/2-1)*r^((n : ℝ)/2-(n : ℝ)/s)=r^((n : ℝ)/p-1) := by
    rw [←Real.rpow_add hr]
    have hDiv : (n : ℝ)/s=(n : ℝ)*(1-1/p) := by rw [div_eq_mul_inv,←one_div,hConj]
    congr 1
    rw [hDiv]
    ring
  have hnReal : (2 : ℝ)≤n := by exact_mod_cast hn
  have hExponent : 0≤(n : ℝ)/p-1 := sub_nonneg.mpr ((one_le_div hp).mpr (hpTwo.trans hnReal))
  have hRadius : r^((n : ℝ)/p-1)≤t^((n : ℝ)/p-1) :=
    Real.rpow_le_rpow hr.le (by dsimp only [r];linarith only [ht]) hExponent
  refine ⟨hV,hWI,hMoment,hBound.trans ?_⟩
  calc
    _≤D*(Ψ (8*t))^(1/p)*(η*r^((n : ℝ)/2-1))*((1+Q)*((2*F)*r^((n : ℝ)/2-(n : ℝ)/s)*J)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hZE (mul_nonneg hD.le hPsi)) hSum
        (Finset.sum_nonneg fun j _=>mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
        (mul_nonneg (mul_nonneg hD.le hPsi) (mul_nonneg hη (Real.rpow_nonneg hr.le _)))
    _=C*η*(r^((n : ℝ)/2-1)*r^((n : ℝ)/2-(n : ℝ)/s))*(Ψ (8*t))^(1/p)*J := by dsimp only [C];ring
    _=C*η*r^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)*J := by rw [hRadiusProduct]
    _≤C*η*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p)*J :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRadius (mul_nonneg hC.le hη)) hPsi) hJ

end StationaryHarmonicMaps.Analysis

end
