module

public import StationaryHarmonicMaps.Analysis.CappedEnvelopeImprovement
public import StationaryHarmonicMaps.Analysis.GeometricIteration
public import StationaryHarmonicMaps.Analysis.GeometricRpowIteration

/-!
# Actual improved all-center power growth from the original cutoff system

Scale contraction is fixed before coefficient smallness and original data.
The original finite capped envelope supplies its monotonicity and initial
bound. Its actual improvement rule is iterated internally, and the global
initial cutoff bound extends the stronger growth to every positive radius.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Original system data and a sufficiently small given critical native
Coulomb frame yield the actual cutoff's improved full Lp growth. The
recurrence, finite envelope and all scalar absorption choices are proved. -/
theorem exists_compact_target_cutoff_power_growth
    (n : ℕ) (hn : 2≤n) (p : ℝ) (hpOne : 1<p) (hpTwo : p<2)
    (hpConj : (n : ℝ)<p/(p-1)) (q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (δ A B L : ℝ) (hδ : 0<δ) (hδOne : δ<1) (hA : 0≤A) (hB : 0≤B) (hL : 0≤L) :
    ∃ε C : ℝ,0<ε ∧ ε≤1 ∧ 0<C ∧ ∀(N : CompactC2EmbeddedTarget q)
      (u : Domain n → Ambient q) (Du : Domain n → Gradient n q) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),u x∈N.carrierSet) → 0≤η → η≤ε →
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
            (∀t : ℝ,0<t → t≤1/16 → Ψ t≤C*η^p*t^(p*(1-δ))) ∧
            ∀(a : Domain n) (r : ℝ),0<r →
              IntegrableOn (fun x=>(Real.sqrt (hsNormSq (Dv x)))^p) (ball a r) volume ∧
              (∫x in ball a r,(Real.sqrt (hsNormSq (Dv x)))^p)≤
                C*η^p*r^((n : ℝ)-p+p*(1-δ)) := by
  have hp : 0<p := zero_lt_one.trans hpOne
  let β := p*(1-δ)
  have hβ : 0<β := mul_pos hp (sub_pos.mpr hδOne)
  have hβp : β<p := by dsimp only [β];nlinarith only [hp,hδ]
  obtain ⟨D,hD,HImprove⟩ := exists_compact_target_capped_envelope_improvement
    n hn p hpOne hpTwo hpConj q E R hRE hER hE δ A B L hδ hδOne hA hB hL
  obtain ⟨M,hM,HEnvelope⟩ := exists_cutoff_capped_envelope n hn p hpOne.le hpTwo.le A B hA hB
  obtain ⟨J,hJ,HInitial⟩ := exists_cutoff_lp_envelope_bound n hn p hp hpTwo.le A B hA hB
  let U := (16 : ℝ)^β
  have hU : 0<U := Real.rpow_pos_of_pos (by norm_num) _
  let G := 2*U*D
  have hG : 0<G := mul_pos (mul_pos (by norm_num) hU) hD
  obtain ⟨θ,hθ,hθHalf,hScale⟩ := exists_scale_absorbing_higher_power hG hβp
  obtain ⟨ε,hε,hεOne,hSmall⟩ := exists_smallness_absorbing_morrey_term
    (β:=β) (n:=(n : ℝ)) hG hp hθ
  let σ := θ/16
  have hσ : 0<σ := div_pos hθ (by norm_num)
  have hσOne : σ<1 := by dsimp only [σ];linarith only [hθHalf]
  have hσPow : σ^β=θ^β/U := Real.div_rpow hθ.le (by norm_num : (0 : ℝ)≤16) β
  let ρ := σ^β/2
  have hσβ : 0<σ^β := Real.rpow_pos_of_pos hσ _
  have hρ : 0≤ρ := (half_pos hσβ).le
  have hGap : ρ<σ^β := half_lt_self hσβ
  have hAbsorb (η : ℝ) (hη : 0≤η) (hηle : η≤ε) :
      D*(η^p*θ^(p-(n : ℝ))+θ^p)≤ρ := by
    have Hη := hSmall η hη hηle
    have Hsum : G*(η^p*θ^(p-(n : ℝ))+θ^p)≤θ^β := by nlinarith only [Hη,hScale]
    have Hraw : D*(η^p*θ^(p-(n : ℝ))+θ^p)≤θ^β/(2*U) :=
      (le_div_iff₀ (mul_pos (by norm_num) hU)).mpr (by dsimp only [G] at Hsum;nlinarith only [Hsum])
    exact Hraw.trans_eq (by dsimp only [ρ];rw [hσPow];field_simp)
  let r₀ := (1/16 : ℝ)
  have hr₀ : 0<r₀ := by norm_num [r₀]
  let A₀ := D*θ^(p-(n : ℝ))
  have hA₀ : 0<A₀ := mul_pos hD (Real.rpow_pos_of_pos hθ _)
  let B₀ := M/r₀^β
  have hB₀ : 0<B₀ := div_pos hM (Real.rpow_pos_of_pos hr₀ _)
  let Cs := (B₀+A₀/(σ^β-ρ))/σ^β
  have hCs : 0<Cs := div_pos (add_pos hB₀ (div_pos hA₀ (sub_pos.mpr hGap))) hσβ
  let C := 1+Cs+J*r₀^(-β)
  have hC : 0<C := by dsimp only [C];positivity
  have hCsC : Cs≤C := by
    have HJ : 0≤J*r₀^(-β) := mul_nonneg hJ.le (Real.rpow_nonneg hr₀.le _)
    dsimp only [C]
    linarith only [HJ]
  have hJC : J*r₀^(-β)≤C := by dsimp only [C];linarith only [hCs]
  refine ⟨ε,C,hε,hεOne,hC,?_⟩
  intro N u Du η hu hTarget hη hηle hCritical P DP hP hOrth hDPCritical Ω hΩ hEq Z hDiv hZCritical
    χ hχ hcχ hsχ hχA hDχ hLap c v Dv Φ Ψ
  have hηOne : η≤1 := hηle.trans hεOne
  obtain ⟨hV,HImproveData⟩ := HImprove N u Du η hu hTarget hη hηOne hCritical P DP hP hOrth hDPCritical
    Ω hΩ hEq hDiv hZCritical χ hχ hcχ hsχ hχA hDχ hLap
  obtain ⟨_hVEnv,Henv⟩ := HEnvelope q u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ
  obtain ⟨_hVInitial,Hinit⟩ := HInitial q u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ
  have hηp : 0≤η^p := Real.rpow_nonneg hη _
  have hMono (r s : ℝ) (hr : 0<r) (hrs : r≤s) (hs : s≤r₀) : Ψ r≤Ψ s :=
    (Henv s (hr.trans_le hrs) hs).2.2.2.1 r hr hrs
  have hBase : Ψ r₀≤(B₀*η^p)*r₀^β := by
    have H := (Henv r₀ hr₀ le_rfl).2.1
    exact H.trans_eq (by dsimp only [B₀];field_simp)
  have hStep (s : ℝ) (hs : 0<s) (hsCap : s≤r₀) :
      Ψ (σ*s)≤ρ*Ψ s+(A₀*η^p)*s^β := by
    have hCap : s/8≤1/128 := by dsimp only [r₀] at hsCap;linarith only [hsCap]
    have H := HImproveData (s/8) θ (div_pos hs (by norm_num)) hCap hθ hθHalf
    have hArg : θ*(s/8)/2=σ*s := by dsimp only [σ];ring
    have hOuter : 8*(s/8)=s := by ring
    rw [hArg,hOuter] at H
    have hPsi : 0≤Ψ s := (Henv s hs hsCap).1
    have hErrorScale : (s/8)^β≤s^β := Real.rpow_le_rpow (by positivity)
      (by linarith only [hs]) hβ.le
    have hE : D*η^p*θ^(p-(n : ℝ))*(s/8)^β≤(A₀*η^p)*s^β := by
      calc
        _≤D*η^p*θ^(p-(n : ℝ))*s^β := mul_le_mul_of_nonneg_left hErrorScale (by positivity)
        _=_ := by dsimp only [A₀];ring
    exact H.trans (add_le_add (mul_le_mul_of_nonneg_right (hAbsorb η hη hηle) hPsi) hE)
  have hSmallGrowth : ∀s : ℝ,0<s → s≤r₀ → Ψ s≤Cs*η^p*s^β := by
    have H := all_radius_rpow_bound_of_recurrence Ψ hβ.le hσ hσOne hρ hGap
      (mul_nonneg hA₀.le hηp) (mul_nonneg hB₀.le hηp) hr₀ hMono hBase hStep
    intro s hs hsCap
    exact (H s hs hsCap).trans_eq (by dsimp only [Cs];ring)
  have hGrowth : ∀s : ℝ,0<s → s≤r₀ → Ψ s≤C*η^p*s^β := by
    intro s hs hsCap
    exact (hSmallGrowth s hs hsCap).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCsC hηp) (Real.rpow_nonneg hs.le _))
  refine ⟨hV,hGrowth,?_⟩
  intro a r hr
  obtain ⟨hI,hInitial⟩ := Hinit a r hr
  refine ⟨hI,?_⟩
  have hCancel : r^((n : ℝ)-p)*r^(p-(n : ℝ))=1 := by
    rw [←Real.rpow_add hr]
    rw [show (n : ℝ)-p+(p-(n : ℝ))=0 by ring,Real.rpow_zero]
  by_cases hSmallRadius : r≤r₀
  · have hTerm : Φ a r≤Ψ r := (Henv r hr hSmallRadius).2.2.1 a r hr le_rfl
    calc
      _=r^((n : ℝ)-p)*Φ a r := by change _=r^((n : ℝ)-p)*(r^(p-(n : ℝ))*_);rw [←mul_assoc,hCancel,one_mul]
      _≤r^((n : ℝ)-p)*(C*η^p*r^β) := mul_le_mul_of_nonneg_left
        (hTerm.trans (hGrowth r hr hSmallRadius)) (Real.rpow_nonneg hr.le _)
      _=C*η^p*r^((n : ℝ)-p+β) := by rw [Real.rpow_add hr];ring
  · have hR : r₀≤r := (not_le.mp hSmallRadius).le
    have hPower : r₀^β≤r^β := Real.rpow_le_rpow hr₀.le hR hβ.le
    have hJr : J≤C*r^β := by
      have hZero : r₀^(-β)*r₀^β=1 := by rw [←Real.rpow_add hr₀,neg_add_cancel,Real.rpow_zero]
      calc
        J=(J*r₀^(-β))*r₀^β := by rw [mul_assoc,hZero,mul_one]
        _≤C*r^β := mul_le_mul hJC hPower (Real.rpow_nonneg hr₀.le _) hC.le
    calc
      _=r^((n : ℝ)-p)*Φ a r := by change _=r^((n : ℝ)-p)*(r^(p-(n : ℝ))*_);rw [←mul_assoc,hCancel,one_mul]
      _≤r^((n : ℝ)-p)*(J*η^p) := mul_le_mul_of_nonneg_left hInitial (Real.rpow_nonneg hr.le _)
      _≤r^((n : ℝ)-p)*((C*r^β)*η^p) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hJr hηp) (Real.rpow_nonneg hr.le _)
      _=C*η^p*r^((n : ℝ)-p+β) := by rw [Real.rpow_add hr];ring

end StationaryHarmonicMaps.Analysis

end
