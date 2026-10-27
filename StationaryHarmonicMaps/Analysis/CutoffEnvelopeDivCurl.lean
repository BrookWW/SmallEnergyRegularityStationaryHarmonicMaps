module

public import StationaryHarmonicMaps.Analysis.CutoffCappedEnvelope
public import StationaryHarmonicMaps.Analysis.LocalLpDivCurlPairing

/-!
# Actual capped-envelope growth and ordinary local div--curl integrals

The bounded, nonempty original capped supremum controls every original
ball term. Positive-radius power cancellation yields the actual critical
Lp amplitude from its same value at eight times the reference radius.
The proved raw local div--curl producer then controls the original
ordinary integral against the same native cutoff.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The actual finite cutoff envelope produces the same native graph and genuine all-center gradient growth with amplitude Ψ(8t)^(1/p), including zero amplitude. -/
theorem cutoff_capped_envelope_lp_growth (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hp₁ : 1≤p) (hp₂ : p≤2) (A B : ℝ) (hA : 0≤A) (hB : 0≤B)
    (m : ℕ) (u : Domain n → Ambient m) (Du : Domain n → Gradient n m) (η : ℝ)
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du) (hη : 0≤η)
    (hCritical : criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2))
    (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ⊆Metric.closedBall (0 : Domain n) (3/4 : ℝ))
    (hχA : ∀ x,|χ x|≤A) (hDχB : ∀ (x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B)
    (t : ℝ) (ht : 0<t) (htCap : t≤(1/128 : ℝ)) :
    let c := ⨍ y in Metric.ball (0 : Domain n) 1,u y
    let v := fun x=>χ x • (u x-c)
    let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
    let Φ := fun (x : Domain n) (r : ℝ)=>r^(p-(n : ℝ))*∫ y in Metric.ball x r,(Real.sqrt (hsNormSq (Dv y)))^p
    let Ψ := fun s : ℝ=>sSup {z : ℝ | ∃ x r,0<r ∧ r≤s ∧ z=Φ x r}
    MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) v Dv ∧ 0≤Ψ (8*t) ∧
      ∀ (x : Domain n) (r : ℝ),0<r → r≤8*t →
        (∫ y in Metric.ball x r,(Real.sqrt (hsNormSq (Dv y)))^p)≤
          ((Ψ (8*t))^(1/p))^p*r^((n : ℝ)-p) := by
  intro c v Dv Φ Ψ
  have hp : 0<p := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) hp₁
  obtain ⟨E,_hE,H⟩ := exists_cutoff_capped_envelope n hn p hp₁ hp₂ A B hA hB
  obtain ⟨hW,Henv⟩ := H m u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχB
  obtain ⟨hNonneg,_hUpper,hTerm,_hMono,_hMean⟩ := Henv (8*t) (by positivity) (by linarith only [htCap])
  refine ⟨hW,hNonneg,?_⟩
  intro x r hr hrCap
  have hCancel : r^((n : ℝ)-p)*r^(p-(n : ℝ))=1 := by
    rw [← Real.rpow_add hr]
    have hExp : (n : ℝ)-p+(p-(n : ℝ))=0 := by ring
    rw [hExp,Real.rpow_zero]
  have hGrowth := mul_le_mul_of_nonneg_left (hTerm x r hr hrCap) (Real.rpow_nonneg hr.le ((n : ℝ)-p))
  change r^((n : ℝ)-p)*(r^(p-(n : ℝ))*∫ y in Metric.ball x r,(Real.sqrt (hsNormSq (Dv y)))^p)≤
    r^((n : ℝ)-p)*Ψ (8*t) at hGrowth
  rw [← mul_assoc,hCancel,one_mul] at hGrowth
  rw [one_div,Real.rpow_inv_rpow hNonneg hp.ne']
  exact hGrowth.trans_eq (mul_comm _ _)

/-- Original cutoff and coefficient data yield the ordinary local div--curl bound with the actual capped-envelope factor, without a growth or BMO premise. -/
theorem exists_capped_envelope_divcurl_integral_bound (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hp₁ : 1≤p) (hp₂ : p≤2) (A B : ℝ) (hA : 0≤A) (hB : 0≤B) :
    ∃ C : ℝ,0<C ∧ ∀ (m : ℕ) (u : Domain n → Ambient m) (Du : Domain n → Gradient n m) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
      criticalGradientMorreySquare Du (Metric.ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
      ∀ (χ : Domain n → ℝ),ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ⊆Metric.closedBall (0 : Domain n) (3/4 : ℝ) →
        (∀ x,|χ x|≤A) →
        (∀ (x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) →
        let c := ⨍ y in Metric.ball (0 : Domain n) 1,u y
        let v := fun x=>χ x • (u x-c)
        let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
        let Φ := fun (x : Domain n) (r : ℝ)=>r^(p-(n : ℝ))*∫ y in Metric.ball x r,(Real.sqrt (hsNormSq (Dv y)))^p
        let Ψ := fun s : ℝ=>sSup {z : ℝ | ∃ x r,0<r ∧ r≤s ∧ z=Φ x r}
        ∀ (a : Domain n) (t : ℝ),0<t → t≤(1/128 : ℝ) →
          ∀ (L : Ambient m →L[ℝ] ℝ) (q : ℕ) (Z : Domain n → Gradient n q),
            (∀ i,MemLp (fun x=>Z x i) 2 (volume.restrict (Metric.ball a (t/2)))) →
            HolderToCK.WeakPoissonOn (ballDomain a (t/2)) Z (fun _=>(0 : Ambient q)) →
            ∀ (w : Domain n → Ambient q),ContDiff ℝ ∞ w → HasCompactSupport w →
              tsupport w⊆Metric.ball a (t/2) →
              let Dw := fun x i=>fderiv ℝ w x (EuclideanSpace.single i 1)
              IntegrableOn (fun x=>(∑ i : Fin n,inner ℝ (Z x i) (Dw x i))*L (v x))
                (Metric.ball a (t/2)) volume ∧
              |∫ x in Metric.ball a (t/2),(∑ i : Fin n,inner ℝ (Z x i) (Dw x i))*L (v x)|≤
                C*‖L‖*(Ψ (8*t))^(1/p)*Real.sqrt (∫ x in Metric.ball a (t/2),hsNormSq (Z x))*
                  Real.sqrt (∫ x in Metric.ball a (t/2),hsNormSq (Dw x)) := by
  obtain ⟨C,hC,Hpair⟩ := exists_local_lp_divcurl_integral_bound n hn p hp₁ hp₂
  refine ⟨C,hC,?_⟩
  intro m u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχB c v Dv Φ Ψ a t ht htCap L q Z hZ hDiv w hw hcw hsw Dw
  obtain ⟨hW,hNonneg,hGrowth⟩ := cutoff_capped_envelope_lp_growth n hn p hp₁ hp₂ A B hA hB
    m u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχB t ht htCap
  exact Hpair m a t ht v Dv ((Ψ (8*t))^(1/p)) hW.to_memW12Loc
    (Real.rpow_nonneg hNonneg _) hGrowth L q Z hZ hDiv w hw hcw hsw

end StationaryHarmonicMaps.Analysis

end
