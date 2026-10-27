module

public import StationaryHarmonicMaps.Foundation.C2Target
public import StationaryHarmonicMaps.Analysis.CutoffEnvelopeDivCurl
public import StationaryHarmonicMaps.Analysis.LocalDivCurlContinuousPairing
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Ordinary native-W0 div--curl pairings for the actual compact target map

Compactness of the original C2 target supplies a genuine essential bound
for the same original centered cutoff. This bound makes the native-W0
contraction product integrable. Its original all-ball BMO estimate and
actual W0 cancellation then give the same envelope bound for the ordinary
integral, with no smoothness or higher-integrability premise on the test.
-/

@[expose] public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The actual compact C2 target and original AE membership produce a global essential bound for the same supported centered cutoff. -/
theorem exists_ae_bound_cutoff_of_compact_target {n m : ℕ}
    (N : CompactC2EmbeddedTarget m) (u : Domain n → Ambient m)
    (hTarget : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),u x∈N.carrierSet)
    (c : Ambient m) (χ : Domain n → ℝ)
    (hsχ : tsupport χ⊆Metric.ball (0 : Domain n) 1)
    (A : ℝ) (hA : 0≤A) (hχA : ∀ x,|χ x|≤A) :
    ∃ M : ℝ,0≤M ∧ ∀ᵐ x ∂volume,‖χ x • (u x-c)‖≤M := by
  obtain ⟨R,hR⟩ := N.isCompact.isBounded.exists_norm_le
  let M := A*(|R|+‖c‖)
  refine ⟨M,by positivity,?_⟩
  filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hTarget] with x hx
  by_cases hxB : x∈Metric.ball (0 : Domain n) 1
  · have huBound : ‖u x‖≤|R| := (hR (u x) (hx hxB)).trans (le_abs_self _)
    calc
      _ = |χ x| *‖u x-c‖ := by rw [norm_smul,Real.norm_eq_abs]
      _ ≤ A*(‖u x‖+‖c‖) := mul_le_mul (hχA x) (norm_sub_le _ _) (norm_nonneg _) hA
      _ ≤ M := mul_le_mul_of_nonneg_left (add_le_add huBound le_rfl) hA
  · have hZero : χ x=0 := by
      by_contra hn
      exact hxB (hsχ (subset_tsupport χ hn))
    rw [hZero,zero_smul,norm_zero]
    positivity

def effectiveCompactTargetEnvelopePairingConstant (n : ℕ) : ℚ :=
  effectiveLocalDivcurlPairingConstant n*(effectiveLocalLpCriticalCutoffConstant n:ℚ)

/-- The actual compact-target cutoff and an arbitrary genuine native W0 test have the ordinary envelope-controlled div--curl pairing; no test smoothness, product integrability or pairing certificate is assumed. -/
theorem exists_compact_target_capped_envelope_native_divcurl_bound_explicit (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hp₁ : 1≤p) (hp₂ : p≤2) (A B : ℝ) (hA : 0≤A) (hB : 0≤B) :
    ∃ C : ℝ,0<C ∧ C=(effectiveCompactTargetEnvelopePairingConstant n:ℝ) ∧ ∀ (m : ℕ) (N : CompactC2EmbeddedTarget m)
      (u : Domain n → Ambient m) (Du : Domain n → Gradient n m) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),u x∈N.carrierSet) → 0≤η →
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
            ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
              HasZeroBoundaryValues (ballDomain a (t/2)) w Dw →
              IntegrableOn (fun x=>(∑ i : Fin n,inner ℝ (Z x i) (Dw x i))*L (v x))
                (Metric.ball a (t/2)) volume ∧
              |∫ x in Metric.ball a (t/2),(∑ i : Fin n,inner ℝ (Z x i) (Dw x i))*L (v x)|≤
                C*‖L‖*(Ψ (8*t))^(1/p)*Real.sqrt (∫ x in Metric.ball a (t/2),hsNormSq (Z x))*
                  Real.sqrt (∫ x in Metric.ball a (t/2),hsNormSq (Dw x)) := by
  obtain ⟨D,hD,hDEq,Hpair⟩ := existsUnique_local_divcurl_continuous_pairing_explicit n hn
  obtain ⟨E,hE,hEEq,Hcut⟩ := exists_local_lp_critical_cutoff_scalar_mean_oscillation_bound_explicit n p hp₁ hp₂
  let C := D*E
  have hCEq : C=(effectiveCompactTargetEnvelopePairingConstant n:ℝ) := by
    dsimp only [C,effectiveCompactTargetEnvelopePairingConstant]
    rw [hDEq,hEEq]
    push_cast
    rfl
  refine ⟨C,mul_pos hD hE,hCEq,?_⟩
  intro m N u Du η hu hTarget hη hCritical χ hχ hcχ hsχ hχA hDχB c v Dv Φ Ψ a t ht htCap L q Z hZ hDiv w Dw hw
  obtain ⟨hW,hNonneg,hGrowth⟩ := cutoff_capped_envelope_lp_growth n hn p hp₁ hp₂ A B hA hB
    m u Du η hu hη hCritical χ hχ hcχ hsχ hχA hDχB t ht htCap
  have hPsi : 0≤(Ψ (8*t))^(1/p) := Real.rpow_nonneg hNonneg _
  have hχInside : tsupport χ⊆Metric.ball (0 : Domain n) 1 := hsχ.trans (Metric.closedBall_subset_ball (by norm_num))
  obtain ⟨M,_hM,hVBound⟩ := exists_ae_bound_cutoff_of_compact_target N u hTarget c χ hχInside A hA hχA
  obtain ⟨κ,_hκ,_hcκ,_hsκ,hOne,_hκBounds,Hb⟩ := Hcut m a t ht v Dv ((Ψ (8*t))^(1/p))
    hW.to_memW12Loc hPsi hGrowth
  let cV := ⨍ y in Metric.ball a (8*t),v y
  let b := fun x=>L (κ x • (v x-cV))
  obtain ⟨hbMeas,hBMO⟩ := Hb L
  let μ := volume.restrict (Metric.ball a (t/2))
  let F := fun x=>∑ i : Fin n,inner ℝ (Z x i) (Dw x i)
  obtain ⟨hFI,hMeanZero⟩ := divergence_free_zeroBoundary_test (ballDomain a (t/2)) Z hZ hDiv hw
  change Integrable F μ at hFI
  change (∫ x,F x ∂μ)=0 at hMeanZero
  have hVLp : MemLp v 2 volume := by
    have H := hW.2.1
    change MemLp v 2 (volume.restrict univ) at H
    rwa [Measure.restrict_univ] at H
  have hObsMeas : AEStronglyMeasurable (fun x=>L (v x)) μ :=
    (L.continuous.comp_aestronglyMeasurable hVLp.aestronglyMeasurable).restrict
  have hObsBound : ∀ᵐ x ∂μ,‖L (v x)‖≤‖L‖*M := by
    filter_upwards [hVBound.filter_mono (ae_mono Measure.restrict_le_self)] with x hx
    exact (L.le_opNorm (v x)).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hOriginalI : Integrable (fun x=>F x*L (v x)) μ := hFI.mul_bdd hObsMeas hObsBound
  have hInside (x : Domain n) (hx : x∈Metric.ball a (t/2)) : b x=L (v x)-L cV := by
    dsimp only [b]
    rw [hOne x (Metric.ball_subset_closedBall hx),one_smul,L.map_sub]
  have hProductEq : (fun x=>F x*b x)=ᵐ[μ](fun x=>F x*L (v x)-F x*L cV) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [hInside x hx]
    ring
  have hProduct : Integrable (fun x=>F x*b x) μ :=
    (hOriginalI.sub (hFI.mul_const (L cV))).congr hProductEq.symm
  have hIntegral : (∫ x,F x*b x ∂μ)=(∫ x,F x*L (v x) ∂μ) := by
    rw [integral_congr_ae hProductEq,integral_sub hOriginalI (hFI.mul_const (L cV)),
      integral_mul_const,hMeanZero,zero_mul,sub_zero]
  obtain ⟨l,⟨_hAllI,_hLimit,hEstimate,hAgree⟩,_hUnique⟩ := Hpair q a (t/2) (half_pos ht)
    Z hZ hDiv w Dw hw b (E*‖L‖*(Ψ (8*t))^(1/p)) hbMeas (by positivity) hBMO
  rw [(hAgree hProduct).trans hIntegral] at hEstimate
  exact ⟨hOriginalI,hEstimate.trans_eq (by dsimp only [C];ring)⟩

theorem exists_compact_target_capped_envelope_native_divcurl_bound (n : ℕ) (hn : 2≤n)
    (p : ℝ) (hp₁ : 1≤p) (hp₂ : p≤2) (A B : ℝ) (hA : 0≤A) (hB : 0≤B) :
    ∃ C : ℝ,0<C ∧ ∀ (m : ℕ) (N : CompactC2EmbeddedTarget m)
      (u : Domain n → Ambient m) (Du : Domain n → Gradient n m) (η : ℝ),
      MemW12 (ballDomain (0 : Domain n) 1) u Du →
      (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),u x∈N.carrierSet) → 0≤η →
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
            ∀ (w : Domain n → Ambient q) (Dw : Domain n → Gradient n q),
              HasZeroBoundaryValues (ballDomain a (t/2)) w Dw →
              IntegrableOn (fun x=>(∑ i : Fin n,inner ℝ (Z x i) (Dw x i))*L (v x))
                (Metric.ball a (t/2)) volume ∧
              |∫ x in Metric.ball a (t/2),(∑ i : Fin n,inner ℝ (Z x i) (Dw x i))*L (v x)|≤
                C*‖L‖*(Ψ (8*t))^(1/p)*Real.sqrt (∫ x in Metric.ball a (t/2),hsNormSq (Z x))*
                  Real.sqrt (∫ x in Metric.ball a (t/2),hsNormSq (Dw x)) := by
  obtain ⟨C,hC,_hCEq,H⟩ := exists_compact_target_capped_envelope_native_divcurl_bound_explicit n hn p hp₁ hp₂ A B hA hB
  exact ⟨C,hC,H⟩

end StationaryHarmonicMaps.Analysis

end
