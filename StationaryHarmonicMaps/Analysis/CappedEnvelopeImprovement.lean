module

public import StationaryHarmonicMaps.Analysis.OneBallCompensatedDecay
public import StationaryHarmonicMaps.Analysis.CutoffCappedEnvelope

/-!
# Improvement of the actual all-center finite cutoff envelope

Each original small query either misses the actual cutoff support or
lies in a genuine larger Hodge query contained in the unit ball. Its
one-ball estimate is normalized before taking the original all-center
supremum. Monotonicity and finiteness come from the actual cutoff data.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem closed_hodge_query_of_cutoff_intersection {n : ℕ}
    (S : Set (Domain n)) (hS : S⊆closedBall (0 : Domain n) (3/4 : ℝ))
    (a : Domain n) (r t θ : ℝ) (ht : 0<t) (htCap : t≤1/128)
    (hθ : 0<θ) (hθHalf : θ≤1/2) (hSmall : r≤θ*t/2)
    (hMeet : (ball a r∩S).Nonempty) :
    closedBall a (r/θ)⊆ball (0 : Domain n) 1 := by
  obtain ⟨x,hxa,hxS⟩ := hMeet
  have hx0 : dist x (0 : Domain n)≤3/4 := hS hxS
  have hax : dist a x<r := by simpa only [mem_ball,dist_comm] using hxa
  have hRatio : r/θ≤t/2 := (div_le_iff₀ hθ).mpr (by linarith only [hSmall])
  have hrCap : r≤t/4 := by nlinarith only [hSmall,hθHalf,ht]
  intro y hy
  have hyA : dist y a≤r/θ := hy
  have H1 := dist_triangle y a x
  have H2 := dist_triangle y x (0 : Domain n)
  change dist y (0 : Domain n)<1
  linarith only [H1,H2,hyA,hRatio,hax,hx0,hrCap,htCap]

/-- The original all-center finite envelope improves from the actual
ordered system, with scale and coefficient smallness separated. No
recurrence or finiteness certificate is a source input. -/
theorem exists_compact_target_capped_envelope_improvement
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
            ∀(t θ : ℝ),0<t → t≤1/128 → 0<θ → θ≤1/2 →
              Ψ (θ*t/2)≤C*(η^p*θ^(p-(n : ℝ))+θ^p)*(Ψ (8*t))+
                C*η^p*θ^(p-(n : ℝ))*t^(p*(1-δ)) := by
  have hp : 0<p := zero_lt_one.trans hpOne
  obtain ⟨D,hD,HOneBall⟩ := exists_compact_target_one_ball_compensated_decay
    n hn p hpOne hpTwo hpConj q E R hRE hER hE δ A B L hδ hδOne hA hB hL
  obtain ⟨M,_hM,HEnvelope⟩ := exists_cutoff_capped_envelope n hn p hpOne.le hpTwo.le A B hA hB
  let C := D*(2 : ℝ)^((n : ℝ)-p)
  have hC : 0<C := mul_pos hD (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨C,hC,?_⟩
  intro N u Du η hu hTarget hη hηOne hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
    χ hχ hcχ hsχ hχA hDχ hLap c v Dv Φ Ψ
  obtain ⟨hV,HQuery⟩ := HOneBall N u Du η hu hTarget hη hηOne hCritical P DP hP hOrth hDPCritical
    Ω hΩ hEq hDiv hZCritical χ hχ hcχ hsχ hχA hDχ hLap
  obtain ⟨_hV',Henv⟩ := HEnvelope q u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ
  refine ⟨hV,?_⟩
  intro t θ ht htCap hθ hθHalf
  have hBigCap : 8*t≤1/16 := by linarith only [htCap]
  obtain ⟨hPsi,_hUpper,_hTerm,hMono,_hMean⟩ := Henv (8*t) (by positivity) hBigCap
  have hRight : 0≤C*(η^p*θ^(p-(n : ℝ))+θ^p)*(Ψ (8*t))+C*η^p*θ^(p-(n : ℝ))*t^(p*(1-δ)) := by
    positivity
  have hSmallCap : 0<θ*t/2 := by positivity
  have hNonempty : ({z : ℝ | ∃a r,0<r ∧ r≤θ*t/2 ∧ z=Φ a r}).Nonempty :=
    ⟨Φ (0 : Domain n) (θ*t/2),0,θ*t/2,hSmallCap,le_rfl,rfl⟩
  change sSup {z : ℝ | ∃a r,0<r ∧ r≤θ*t/2 ∧ z=Φ a r}≤_
  apply csSup_le hNonempty
  rintro z ⟨a,r,hr,hrCap,rfl⟩
  by_cases hMeet : (ball a r∩tsupport χ).Nonempty
  · let τ := 2*r/θ
    have hτ : 0<τ := div_pos (mul_pos (by norm_num) hr) hθ
    have hτLe : τ≤t := (div_le_iff₀ hθ).mpr (by linarith only [hrCap])
    have hτCap : τ≤1/128 := hτLe.trans htCap
    have hRadius : θ*(τ/2)=r := by dsimp only [τ];field_simp [hθ.ne']
    have hParentRadius : τ/2=r/θ := by dsimp only [τ];ring_nf
    have hClosed : closedBall a (τ/2)⊆ball (0 : Domain n) 1 := by
      rw [hParentRadius]
      exact closed_hodge_query_of_cutoff_intersection (tsupport χ) hsχ a r t θ ht htCap hθ hθHalf hrCap hMeet
    obtain ⟨_hI,Hlocal⟩ := HQuery a τ hτ hτCap hClosed θ hθ hθHalf
    rw [hRadius] at Hlocal
    have hPsiMono : Ψ (8*τ)≤Ψ (8*t) := hMono (8*τ) (by positivity) (by linarith only [hτLe])
    have hβ : 0<p*(1-δ) := mul_pos hp (sub_pos.mpr hδOne)
    have hErrorMono : τ^(p*(1-δ))≤t^(p*(1-δ)) := Real.rpow_le_rpow hτ.le hτLe hβ.le
    have hRForm : r=(θ/2)*τ := by dsimp only [τ];field_simp [hθ.ne']
    have hCancel : r^(p-(n : ℝ))*τ^((n : ℝ)-p)=(θ/2)^(p-(n : ℝ)) := by
      rw [hRForm,Real.mul_rpow (half_pos hθ).le hτ.le,mul_assoc,←Real.rpow_add hτ]
      rw [show p-(n : ℝ)+((n : ℝ)-p)=0 by ring_nf,Real.rpow_zero,mul_one]
    have hErrorCancel : r^(p-(n : ℝ))*τ^((n : ℝ)-p*δ)=
        (θ/2)^(p-(n : ℝ))*τ^(p*(1-δ)) := by
      rw [hRForm,Real.mul_rpow (half_pos hθ).le hτ.le,mul_assoc,←Real.rpow_add hτ]
      congr 1
      ring_nf
    have hHalfPower : (θ/2)^(p-(n : ℝ))=(2 : ℝ)^((n : ℝ)-p)*θ^(p-(n : ℝ)) := by
      rw [Real.div_rpow hθ.le (by norm_num : (0 : ℝ)≤2),div_eq_mul_inv,←Real.rpow_neg (by norm_num : (0 : ℝ)≤2)]
      rw [show -(p-(n : ℝ))=(n : ℝ)-p by ring_nf]
      ring_nf
    have hThetaPower : θ^(p-(n : ℝ))*θ^n=θ^p := by
      rw [←Real.rpow_natCast,←Real.rpow_add hθ]
      congr 1
      ring_nf
    have hLocalNormalized : Φ a r≤D*((η^p+θ^n)*(Ψ (8*τ))*((θ/2)^(p-(n : ℝ)))+
        η^p*((θ/2)^(p-(n : ℝ)))*τ^(p*(1-δ))) := by
      calc
        Φ a r≤r^(p-(n : ℝ))*(D*((η^p+θ^n)*(Ψ (8*τ))*τ^((n : ℝ)-p)+η^p*τ^((n : ℝ)-p*δ))) :=
          mul_le_mul_of_nonneg_left Hlocal (Real.rpow_nonneg hr.le _)
        _=D*((η^p+θ^n)*(Ψ (8*τ))*(r^(p-(n : ℝ))*τ^((n : ℝ)-p))+
            η^p*(r^(p-(n : ℝ))*τ^((n : ℝ)-p*δ))) := by ring_nf
        _=_ := by rw [hCancel,hErrorCancel];ring_nf
    calc
      Φ a r≤D*((η^p+θ^n)*(Ψ (8*τ))*((θ/2)^(p-(n : ℝ)))+η^p*((θ/2)^(p-(n : ℝ)))*τ^(p*(1-δ))) := hLocalNormalized
      _≤D*((η^p+θ^n)*(Ψ (8*t))*((θ/2)^(p-(n : ℝ)))+η^p*((θ/2)^(p-(n : ℝ)))*t^(p*(1-δ))) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPsiMono (by positivity)) (Real.rpow_nonneg (half_pos hθ).le _))
          (mul_le_mul_of_nonneg_left hErrorMono (by positivity))) hD.le
      _=C*(η^p*θ^(p-(n : ℝ))+θ^(p-(n : ℝ))*θ^n)*(Ψ (8*t))+C*η^p*θ^(p-(n : ℝ))*t^(p*(1-δ)) := by
        rw [hHalfPower]
        dsimp only [C]
        ring_nf
      _=_ := by rw [hThetaPower]
  · have hZero (x : Domain n) (hx : x∈ball a r) : Dv x=0 := by
      have hNot : x∉tsupport χ := fun hxs=>hMeet ⟨x,hx,hxs⟩
      have hχZero : χ x=0 := image_eq_zero_of_notMem_tsupport hNot
      funext i
      change χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)=0
      rw [hχZero,fderiv_of_notMem_tsupport (𝕜:=ℝ) hNot,zero_apply,zero_smul,zero_smul,zero_add]
    have hIntegral : (∫x in ball a r,(Real.sqrt (hsNormSq (Dv x)))^p)=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      rw [hZero x hx]
      simp only [hsNormSq,Pi.zero_apply,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),
        Finset.sum_const_zero,Real.sqrt_zero,Real.zero_rpow hp.ne']
    change r^(p-(n : ℝ))*(∫x in ball a r,(Real.sqrt (hsNormSq (Dv x)))^p)≤_
    rw [hIntegral,mul_zero]
    exact hRight

@[expose] def effectiveCappedEnvelopeImprovementConstant (n q B L : ℕ) : ℚ :=
  effectiveOneBallCompensatedConstant n q B L*2^n

theorem effectiveCappedEnvelopeImprovementConstant_pos (n q B L : ℕ) :
    0<effectiveCappedEnvelopeImprovementConstant n q B L := by
  have H := effectiveOneBallCompensatedConstant_pos n q B L
  unfold effectiveCappedEnvelopeImprovementConstant
  positivity

theorem effective_compact_target_capped_envelope_improvement
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
            ∀(t θ : ℝ),0<t → t≤1/128 → 0<θ → θ≤1/2 →
              Ψ (θ*t/2)≤(effectiveCappedEnvelopeImprovementConstant n q B L : ℝ)*(η^p*θ^(p-(n : ℝ))+θ^p)*(Ψ (8*t))+
                (effectiveCappedEnvelopeImprovementConstant n q B L : ℝ)*η^p*θ^(p-(n : ℝ))*t^(p/2) := by
  have hp : 0<p := zero_lt_one.trans hpOne
  let δ : ℝ := 1/2
  have hδOne : δ<1 := by norm_num [δ]
  have hB : 0≤(B : ℝ) := Nat.cast_nonneg B
  let D : ℝ := effectiveOneBallCompensatedConstant n q B L
  have hD : 0<D := by
    dsimp only [D]
    exact_mod_cast effectiveOneBallCompensatedConstant_pos n q B L
  have HOneBall := effective_compact_target_one_ball_compensated_decay
    n hn p hpOne hpTwo hpConj q E R hRE hER hE A B L hA hConjugate
  obtain ⟨M,_hM,HEnvelope⟩ := exists_cutoff_capped_envelope n hn p hpOne.le hpTwo.le A B hA hB
  let C := D*(2 : ℝ)^((n : ℝ)-p)
  have hC : 0<C := mul_pos hD (Real.rpow_pos_of_pos (by norm_num) _)
  intro N u Du η hu hTarget hη hηOne hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
    χ hχ hcχ hsχ hχA hDχ hLap c v Dv Φ Ψ
  obtain ⟨hV,HQuery⟩ := HOneBall N u Du η hu hTarget hη hηOne hCritical P DP hP hOrth hDPCritical
    Ω hΩ hEq hDiv hZCritical χ hχ hcχ hsχ hχA hDχ hLap
  obtain ⟨_hV',Henv⟩ := HEnvelope q u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ
  refine ⟨hV,?_⟩
  intro t θ ht htCap hθ hθHalf
  have hRaw : Ψ (θ*t/2)≤C*(η^p*θ^(p-(n : ℝ))+θ^p)*(Ψ (8*t))+
      C*η^p*θ^(p-(n : ℝ))*t^(p*(1-δ)) := by
    have hBigCap : 8*t≤1/16 := by linarith only [htCap]
    obtain ⟨hPsi,_hUpper,_hTerm,hMono,_hMean⟩ := Henv (8*t) (by positivity) hBigCap
    have hRight : 0≤C*(η^p*θ^(p-(n : ℝ))+θ^p)*(Ψ (8*t))+C*η^p*θ^(p-(n : ℝ))*t^(p*(1-δ)) := by
      positivity
    have hSmallCap : 0<θ*t/2 := by positivity
    have hNonempty : ({z : ℝ | ∃a r,0<r ∧ r≤θ*t/2 ∧ z=Φ a r}).Nonempty :=
      ⟨Φ (0 : Domain n) (θ*t/2),0,θ*t/2,hSmallCap,le_rfl,rfl⟩
    change sSup {z : ℝ | ∃a r,0<r ∧ r≤θ*t/2 ∧ z=Φ a r}≤_
    apply csSup_le hNonempty
    rintro z ⟨a,r,hr,hrCap,rfl⟩
    by_cases hMeet : (ball a r∩tsupport χ).Nonempty
    · let τ := 2*r/θ
      have hτ : 0<τ := div_pos (mul_pos (by norm_num) hr) hθ
      have hτLe : τ≤t := (div_le_iff₀ hθ).mpr (by linarith only [hrCap])
      have hτCap : τ≤1/128 := hτLe.trans htCap
      have hRadius : θ*(τ/2)=r := by dsimp only [τ];field_simp [hθ.ne']
      have hParentRadius : τ/2=r/θ := by dsimp only [τ];ring_nf
      have hClosed : closedBall a (τ/2)⊆ball (0 : Domain n) 1 := by
        rw [hParentRadius]
        exact closed_hodge_query_of_cutoff_intersection (tsupport χ) hsχ a r t θ ht htCap hθ hθHalf hrCap hMeet
      obtain ⟨_hI,Hlocal⟩ := HQuery a τ hτ hτCap hClosed θ hθ hθHalf
      rw [hRadius] at Hlocal
      have hPsiMono : Ψ (8*τ)≤Ψ (8*t) := hMono (8*τ) (by positivity) (by linarith only [hτLe])
      have hβ : 0<p*(1-δ) := mul_pos hp (sub_pos.mpr hδOne)
      have hErrorMono : τ^(p*(1-δ))≤t^(p*(1-δ)) := Real.rpow_le_rpow hτ.le hτLe hβ.le
      have hRForm : r=(θ/2)*τ := by dsimp only [τ];field_simp [hθ.ne']
      have hCancel : r^(p-(n : ℝ))*τ^((n : ℝ)-p)=(θ/2)^(p-(n : ℝ)) := by
        rw [hRForm,Real.mul_rpow (half_pos hθ).le hτ.le,mul_assoc,←Real.rpow_add hτ]
        rw [show p-(n : ℝ)+((n : ℝ)-p)=0 by ring_nf,Real.rpow_zero,mul_one]
      have hErrorCancel : r^(p-(n : ℝ))*τ^((n : ℝ)-p*δ)=
          (θ/2)^(p-(n : ℝ))*τ^(p*(1-δ)) := by
        rw [hRForm,Real.mul_rpow (half_pos hθ).le hτ.le,mul_assoc,←Real.rpow_add hτ]
        congr 1
        ring_nf
      have hHalfPower : (θ/2)^(p-(n : ℝ))=(2 : ℝ)^((n : ℝ)-p)*θ^(p-(n : ℝ)) := by
        rw [Real.div_rpow hθ.le (by norm_num : (0 : ℝ)≤2),div_eq_mul_inv,←Real.rpow_neg (by norm_num : (0 : ℝ)≤2)]
        rw [show -(p-(n : ℝ))=(n : ℝ)-p by ring_nf]
        ring_nf
      have hThetaPower : θ^(p-(n : ℝ))*θ^n=θ^p := by
        rw [←Real.rpow_natCast,←Real.rpow_add hθ]
        congr 1
        ring_nf
      have hLocalNormalized : Φ a r≤D*((η^p+θ^n)*(Ψ (8*τ))*((θ/2)^(p-(n : ℝ)))+
          η^p*((θ/2)^(p-(n : ℝ)))*τ^(p*(1-δ))) := by
        calc
          Φ a r≤r^(p-(n : ℝ))*(D*((η^p+θ^n)*(Ψ (8*τ))*τ^((n : ℝ)-p)+η^p*τ^((n : ℝ)-p*δ))) :=
            mul_le_mul_of_nonneg_left Hlocal (Real.rpow_nonneg hr.le _)
          _=D*((η^p+θ^n)*(Ψ (8*τ))*(r^(p-(n : ℝ))*τ^((n : ℝ)-p))+
              η^p*(r^(p-(n : ℝ))*τ^((n : ℝ)-p*δ))) := by ring_nf
          _=_ := by rw [hCancel,hErrorCancel];ring_nf
      calc
        Φ a r≤D*((η^p+θ^n)*(Ψ (8*τ))*((θ/2)^(p-(n : ℝ)))+η^p*((θ/2)^(p-(n : ℝ)))*τ^(p*(1-δ))) := hLocalNormalized
        _≤D*((η^p+θ^n)*(Ψ (8*t))*((θ/2)^(p-(n : ℝ)))+η^p*((θ/2)^(p-(n : ℝ)))*t^(p*(1-δ))) :=
          mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPsiMono (by positivity)) (Real.rpow_nonneg (half_pos hθ).le _))
            (mul_le_mul_of_nonneg_left hErrorMono (by positivity))) hD.le
        _=C*(η^p*θ^(p-(n : ℝ))+θ^(p-(n : ℝ))*θ^n)*(Ψ (8*t))+C*η^p*θ^(p-(n : ℝ))*t^(p*(1-δ)) := by
          rw [hHalfPower]
          dsimp only [C]
          ring_nf
        _=_ := by rw [hThetaPower]
    · have hZero (x : Domain n) (hx : x∈ball a r) : Dv x=0 := by
        have hNot : x∉tsupport χ := fun hxs=>hMeet ⟨x,hx,hxs⟩
        have hχZero : χ x=0 := image_eq_zero_of_notMem_tsupport hNot
        funext i
        change χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)=0
        rw [hχZero,fderiv_of_notMem_tsupport (𝕜:=ℝ) hNot,zero_apply,zero_smul,zero_smul,zero_add]
      have hIntegral : (∫x in ball a r,(Real.sqrt (hsNormSq (Dv x)))^p)=0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        rw [hZero x hx]
        simp only [hsNormSq,Pi.zero_apply,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),
          Finset.sum_const_zero,Real.sqrt_zero,Real.zero_rpow hp.ne']
      change r^(p-(n : ℝ))*(∫x in ball a r,(Real.sqrt (hsNormSq (Dv x)))^p)≤_
      rw [hIntegral,mul_zero]
      exact hRight
  have hCNum : C≤(effectiveCappedEnvelopeImprovementConstant n q B L : ℝ) := by
    have hPow : (2 : ℝ)^((n : ℝ)-p)≤(2 : ℝ)^n := by
      have H := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
        (show (n : ℝ)-p≤(n : ℝ) by linarith only [hp])
      simpa only [Real.rpow_natCast] using H
    calc
      _≤D*(2 : ℝ)^n := mul_le_mul_of_nonneg_left hPow hD.le
      _=(effectiveCappedEnvelopeImprovementConstant n q B L : ℝ) := by
        simp only [effectiveCappedEnvelopeImprovementConstant,Rat.cast_mul,Rat.cast_pow,
          Rat.cast_ofNat,D]
  have hPsi : 0≤Ψ (8*t) := (Henv (8*t) (by positivity)
    (by linarith only [htCap] : 8*t≤1/16)).1
  have hMain : 0≤(η^p*θ^(p-(n : ℝ))+θ^p)*(Ψ (8*t)) := by positivity
  have hErr : 0≤η^p*θ^(p-(n : ℝ))*t^(p*(1-δ)) := by positivity
  have hUpgrade := add_le_add (mul_le_mul_of_nonneg_right hCNum hMain)
    (mul_le_mul_of_nonneg_right hCNum hErr)
  have hBound := hRaw.trans (by simpa only [mul_assoc] using hUpgrade)
  simpa only [δ,show p*(1-(1/2 : ℝ))=p/2 by ring,mul_assoc] using hBound

end StationaryHarmonicMaps.Analysis

end
