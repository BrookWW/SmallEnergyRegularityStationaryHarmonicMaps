module

public import StationaryHarmonicMaps.Analysis.CriticalLpValueMomentBall
public import StationaryHarmonicMaps.Analysis.CutoffEnvelopeDivCurl

/-!
# Real value moments of the actual cutoff from its finite scale envelope

The actual cutoff produces its all-center local critical Lp growth.
Rescaling the original native graph supplies the same cutoff's moments
on each query ball, centered at its actual double-ball mean. The radius
factor and envelope exponent are retained, including zero envelope.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- Original cutoff data alone give every positive real centered value
moment on every small query, with the genuine capped-envelope amplitude. -/
theorem exists_capped_envelope_cutoff_real_moment_bound (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hpOne : 1≤p) (hpTwo : p≤2) (s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀ (A B : ℝ),0≤A → 0≤B →
      ∀ (m : ℕ) (u : Domain n → Ambient m) (Du : Domain n → Gradient n m) (η : ℝ),
        MemW12 (ballDomain (0 : Domain n) 1) u Du → 0≤η →
        criticalGradientMorreySquare Du (ball (0 : Domain n) 1)≤ENNReal.ofReal (η^2) →
        ∀ (χ : Domain n → ℝ),ContDiff ℝ ∞ χ → HasCompactSupport χ →
          tsupport χ⊆closedBall (0 : Domain n) (3/4 : ℝ) →
          (∀x,|χ x|≤A) → (∀ (x : Domain n) (i : Fin n),|fderiv ℝ χ x (EuclideanSpace.single i 1)|≤B) →
          let c := ⨍y in ball (0 : Domain n) 1,u y
          let v := fun x=>χ x • (u x-c)
          let Dv := fun x i=>χ x • Du x i+fderiv ℝ χ x (EuclideanSpace.single i 1) • (u x-c)
          let Φ := fun (x : Domain n) (r : ℝ)=>r^(p-(n : ℝ))*∫y in ball x r,(Real.sqrt (hsNormSq (Dv y)))^p
          let Ψ := fun t : ℝ=>sSup {z : ℝ | ∃x r,0<r ∧ r≤t ∧ z=Φ x r}
          ∀ (a : Domain n) (t : ℝ),0<t → t≤1/128 →
            let z := ⨍y in ball a (2*t),v y
            0≤Ψ (8*t) ∧
            MemLp (fun x=>v x-z) (ENNReal.ofReal s) (volume.restrict (ball a t)) ∧
            IntegrableOn (fun x=>‖v x-z‖^s) (ball a t) volume ∧
            (∫x in ball a t,‖v x-z‖^s)≤C*(Ψ (8*t))^(s/p)*t^n := by
  obtain ⟨D,hD,HD⟩ := exists_local_real_moment_bound_of_criticalLp_growth n hn p hpOne hpTwo s hs
  refine ⟨D*(2 : ℝ)^n,mul_pos hD (pow_pos (by norm_num) _),?_⟩
  intro A B hA hB m u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ c v Dv Φ Ψ a t ht htCap z
  obtain ⟨hW,hNonneg,hGrowth⟩ := cutoff_capped_envelope_lp_growth n hn p hpOne hpTwo A B hA hB
    m u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχ t ht htCap
  obtain ⟨hf,hI,hMoment⟩ := HD m v Dv ((Ψ (8*t))^(1/p)) a (2*t) hW.to_memW12Loc
    (Real.rpow_nonneg hNonneg _) (by positivity) (fun b r hr hCap=>hGrowth b r hr (by linarith only [hCap,ht]))
  have hSub : ball a t⊆ball a ((7/8 : ℝ)*(2*t)) := ball_subset_ball (by linarith only [ht])
  have hMem := hf.mono_measure (Measure.restrict_mono_set volume hSub)
  have hInt : IntegrableOn (fun x=>‖v x-z‖^s) (ball a t) volume := hI.mono_set hSub
  refine ⟨hNonneg,hMem,hInt,?_⟩
  have H := setIntegral_mono_set hI (Eventually.of_forall fun x=>Real.rpow_nonneg (norm_nonneg _) s)
    (Eventually.of_forall fun _ hx=>hSub hx)
  exact (H.trans hMoment).trans_eq (by
    rw [←Real.rpow_mul hNonneg,mul_pow]
    have hPower : (1/p)*s=s/p := by ring
    rw [hPower]
    ring)

end StationaryHarmonicMaps.Analysis

end
