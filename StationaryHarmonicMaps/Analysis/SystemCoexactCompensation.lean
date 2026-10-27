module

public import StationaryHarmonicMaps.Analysis.CoexactCompensatedLp
public import StationaryHarmonicMaps.Analysis.CappedEnvelopeValueMoments
public import StationaryHarmonicMaps.Analysis.CompactTargetNativeDivCurl
public import StationaryHarmonicMaps.Analysis.OrthogonalCoefficientBounds
public import HarmonicMaps.Analysis.SobolevLocality

/-!
# Compensation for the same coexact component on the Dirichlet query

The original compact-target cutoff supplies its actual zero-boundary
graph, bound and centered value moment. The original orthogonal frame
supplies its actual derivative energy. The given natural component and
its native gradient complement retain their identity while the genuine
power dual is constructed inside the compensated estimate.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Every same original natural coexact component of P*Dv receives its
compensated bound on the actual half-radius Dirichlet query. No value
moment, dual test or component estimate is an input. -/
theorem exists_same_system_coexact_compensated_bound (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1<p) (hpTwo : p<2) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2) :
    ∃C : ℝ,0<C ∧ ∀(A B : ℝ),0≤A → 0≤B →
      ∀(N : CompactC2EmbeddedTarget q) (u : Domain n → Ambient q)
        (Du : Domain n → Gradient n q) (ηu : ℝ),
        MemW12 (ballDomain (0 : Domain n) 1) u Du →
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),u x∈N.carrierSet) → 0≤ηu →
        criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (ηu^2) →
        ∀χ : Domain n → ℝ,ContDiff ℝ ∞ χ → HasCompactSupport χ →
          tsupport χ⊆closedBall (0 : Domain n) (3/4 : ℝ) →
          (∀x,|χ x|≤A) → (∀(x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) →
          let c := ⨍y in ball (0 : Domain n) 1,u y
          let v := fun x=>χ x • (u x-c)
          let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
          let Φ := fun (x : Domain n) (r : ℝ)=>r^(p-(n : ℝ))*∫y in ball x r,(Real.sqrt (hsNormSq (Dv y)))^p
          let Ψ := fun t : ℝ=>sSup {z : ℝ | ∃x r,0<r ∧ r≤t ∧ z=Φ x r}
          ∀(P : Domain n → Ambient (q*q)) (DP : Domain n → Gradient n (q*q)) (ηg : ℝ),
            MemW12 (ballDomain (0 : Domain n) 1) P DP → 0≤ηg →
            (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (P x))*R (P x)=1) →
            criticalGradientMorreySquare DP (ball (0 : Domain n) 1)≤ENNReal.ofReal (ηg^2) →
            ∀(a : Domain n) (t : ℝ),0<t → t≤1/128 → ball a (t/2)⊆ball (0 : Domain n) 1 →
              ∀(Q : Domain n → Gradient n q) (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
                MemW12 (ballDomain a (t/2)) w Dw →
                (∀i,MemLp (fun x=>Q x i) 2 (volume.restrict (ball a (t/2)))) →
                (∀(ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
                  MemW12 (ballDomain a (t/2)) ψ Dψ →
                  (∫x in ball a (t/2),∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=0) →
                (∀ᵐx∂volume.restrict (ball a (t/2)),∀i,star (R (P x)) (Dv x i)=Dw x i+Q x i) →
                HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) v Dv ∧
                IntegrableOn (fun x=>(hsNormSq (Q x))^(p/2)) (ball a (t/2)) volume ∧
                (∫x in ball a (t/2),(hsNormSq (Q x))^(p/2))^(1/p)≤
                  C*ηg*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p) := by
  let s := 2*p/(2-p)
  obtain ⟨_hr,hs,_hInv⟩ := coexact_three_factor_exponents p hpOne hpTwo
  have hs0 : 0<s := lt_trans (by norm_num) hs
  obtain ⟨D,hD,Hcoexact⟩ := exists_coexact_compensated_lp_bound_ball n hn p hpOne hpTwo
  obtain ⟨G,hG,Hmoment⟩ := exists_capped_envelope_cutoff_real_moment_bound n hn p hpOne.le hpTwo.le s hs0
  let Λ : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q) :=
    (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).toContinuousLinearMap.comp R
  have hΛ (z : Ambient (q*q)) : Λ z=star (R z) := rfl
  let K := D*‖Λ‖*G^(1/s)
  have hK : 0≤K := mul_nonneg (mul_nonneg hD.le (norm_nonneg Λ)) (Real.rpow_nonneg hG.le _)
  let C := 1+K
  refine ⟨C,by dsimp only [C];linarith only [hK],?_⟩
  intro A B hA hB N u Du ηu hu hTarget hηu hDuCritical χ hχ hcχ hsχ hχA hDχ c v Dv Φ Ψ
    P DP ηg hP hηg hOrth hDPCritical a t ht htCap hSub Q w Dw hw hQ hNatural hDecomp
  let r := t/2
  have hr : 0<r := half_pos ht
  let μ := volume.restrict (ball a r)
  let z := ⨍y in ball a (2*t),v y
  have hQuery : ball a r⊆ball a t := ball_subset_ball (by dsimp only [r];linarith only [ht])
  obtain ⟨hPsi,hValueLp,hValueI,hMoment⟩ := Hmoment A B hA hB q u Du ηu hu hηu hDuCritical
    χ hχ hcχ hsχ hχA hDχ a t ht htCap
  have hQueryLp : MemLp (fun x=>v x-z) (ENNReal.ofReal s) μ :=
    hValueLp.mono_measure (Measure.restrict_mono_set volume hQuery)
  have hQueryMoment : (∫x,‖v x-z‖^s ∂μ)≤G*(Ψ (8*t))^(s/p)*t^n :=
    (setIntegral_mono_set hValueI (Eventually.of_forall fun _=>Real.rpow_nonneg (norm_nonneg _) _)
      (Eventually.of_forall fun _ hx=>hQuery hx)).trans hMoment
  obtain ⟨hV,_hPsi,_hGrowth⟩ := cutoff_capped_envelope_lp_growth n hn p hpOne.le hpTwo.le A B hA hB
    q u Du ηu hu hηu hDuCritical χ hχ hcχ hsχ hχA hDχ t ht htCap
  have hVParent : MemW12 (ballDomain (0 : Domain n) 1) v Dv := memW12_of_openDomain_subset hV (subset_univ _)
  have hSupport : tsupport v⊆tsupport χ := by
    apply closure_mono
    intro x hx hz
    apply hx
    change χ x • (u x-c)=0
    rw [hz,zero_smul]
  have hsInside : tsupport χ⊆ball (0 : Domain n) 1 := hsχ.trans (closedBall_subset_ball (by norm_num))
  have hVZero : HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) v Dv :=
    hVParent.zeroBoundary_of_compactSupport_ball (by norm_num) hcχ.smul_right (hSupport.trans hsInside)
  obtain ⟨Nv,_hNv,hVBound⟩ := exists_ae_bound_cutoff_of_compact_target N u hTarget c χ hsInside A hA hχA
  have hPBound : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),‖P x‖≤Real.sqrt (q : ℝ) :=
    ae_orthogonal_coordinates_bound (Ω:=ballDomain (0 : Domain n) 1) E R hER hE P hOrth
  obtain ⟨hQI,hBound⟩ := Hcoexact (q*q) q 0 1 (by norm_num) P DP hP (Real.sqrt (q : ℝ)) hPBound
    Λ v Dv hVZero Nv (ae_restrict_of_ae hVBound) a r hr hSub z hQueryLp Q w Dw hw hQ hNatural
    (by simpa only [hΛ] using hDecomp)
  have ha : a∈ball (0 : Domain n) 1 := hSub (mem_ball_self hr)
  have hDP (i : Fin n) : MemLp (fun x=>DP x i) 2 μ :=
    (hP.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)
  have hEnergy := sqrt_integral_hsNormSq_le_of_criticalMorrey DP ha ht (sq_nonneg ηg)
    (subset_inter hQuery hSub) hDP hDPCritical
  rw [Real.sqrt_sq hηg] at hEnergy
  have hValueRoot : (∫x,‖v x-z‖^s ∂μ)^(1/s)≤G^(1/s)*(Ψ (8*t))^(1/p)*t^((n : ℝ)/s) := by
    have H := Real.rpow_le_rpow (integral_nonneg fun _=>Real.rpow_nonneg (norm_nonneg _) _)
      hQueryMoment (one_div_nonneg.mpr hs0.le)
    rw [Real.mul_rpow (mul_nonneg hG.le (Real.rpow_nonneg hPsi _)) (pow_nonneg ht.le n),
      Real.mul_rpow hG.le (Real.rpow_nonneg hPsi _),←Real.rpow_mul hPsi] at H
    rw [show (s/p)*(1/s)=1/p by field_simp] at H
    have hTPow : (t^n)^(1/s)=t^((n : ℝ)/s) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul ht.le]
      congr 1
      ring
    simpa only [hTPow,mul_assoc] using H
  have hScale : t^((n : ℝ)/2-1)*t^((n : ℝ)/s)=t^((n : ℝ)/p-1) := by
    rw [←Real.rpow_add ht]
    congr 1
    dsimp only [s]
    field_simp
    ring
  refine ⟨hVZero,hQI,hBound.trans ?_⟩
  calc
    _≤D*‖Λ‖*(ηg*t^((n : ℝ)/2-1))*(G^(1/s)*(Ψ (8*t))^(1/p)*t^((n : ℝ)/s)) := by
      have H := mul_le_mul hEnergy hValueRoot
        (Real.rpow_nonneg (integral_nonneg fun _=>Real.rpow_nonneg (norm_nonneg _) _) _)
        (mul_nonneg hηg (Real.rpow_nonneg ht.le _))
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left H (mul_nonneg hD.le (norm_nonneg Λ))
    _=K*ηg*(t^((n : ℝ)/2-1)*t^((n : ℝ)/s))*(Ψ (8*t))^(1/p) := by dsimp only [K];ring
    _=K*ηg*t^((n : ℝ)/p-1)*(Ψ (8*t))^(1/p) := by rw [hScale]
    _≤_ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp only [C];linarith : K≤C) hηg)
      (Real.rpow_nonneg ht.le _)) (Real.rpow_nonneg hPsi _)

end StationaryHarmonicMaps.Analysis

end
