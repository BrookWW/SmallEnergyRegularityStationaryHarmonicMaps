module

public import StationaryHarmonicMaps.Analysis.SobolevCutoff
public import HolderToCK.Analysis.L2PairingContinuity

/-!
# Actual weak-gradient closure under strong/weak L2 convergence

Compact scalar tests times constant coordinate vectors are genuine L2
tests. Strong convergence of the original maps and weak convergence of
the same derivative columns pass their native negative-sign test identities
to the displayed limit map and columns.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem coordinate_integral_smul_eq_inner {n q : ℕ} {μ : Measure (Domain n)}
    (f : Domain n → Ambient q) (η : Domain n → ℝ)
    (hI : Integrable (fun x => η x • f x) μ) (j : Fin q) :
    (∫ x, η x • f x ∂μ) j = ∫ x, inner ℝ (f x) (η x • EuclideanSpace.single j 1) ∂μ := by
  have H := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).integral_comp_comm hI
  calc
    _ = ∫ x, (η x • f x) j ∂μ := H.symm
    _ = _ := integral_congr_ae (Eventually.of_forall fun x => by
      simp only [inner_smul_right, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
      rfl)

/-- The same strong map limit and weak column limits satisfy the actual native W12 identities. -/
theorem memW12_of_strong_map_weak_gradient_L2 {n q : ℕ} (Ω : OpenDomain n)
    (u : ℕ → Domain n → Ambient q) (Du : ℕ → Domain n → Gradient n q)
    (hseq : ∀ k, MemW12 Ω (u k) (Du k))
    (v : Domain n → Ambient q) (Dv : Domain n → Gradient n q)
    (hv : MemLp v 2 (volume.restrict Ω.val))
    (hDv : ∀ i, MemLp (fun x => Dv x i) 2 (volume.restrict Ω.val))
    (hstrong : Tendsto (fun k => eLpNorm (u k - v) 2 (volume.restrict Ω.val)) atTop (𝓝 0))
    (hweak : ∀ (i : Fin n) (g : Domain n → Ambient q), MemLp g 2 (volume.restrict Ω.val) →
      Tendsto (fun k => ∫ x in Ω.val, inner ℝ (Du k x i) (g x)) atTop
        (𝓝 (∫ x in Ω.val, inner ℝ (Dv x i) (g x)))) :
    MemW12 Ω v Dv := by
  have hvloc : LocallyIntegrableOn v Ω.val volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hv.locallyIntegrable (by norm_num))
  have hDvloc (i : Fin n) : LocallyIntegrableOn (fun x => Dv x i) Ω.val volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict ((hDv i).locallyIntegrable (by norm_num))
  refine ⟨⟨hvloc, hDvloc, ?_⟩, hv, hDv⟩
  intro i φ hφ hcφ hsφ
  let dφ := coordinateDerivative φ hφ i
  have hdφ : Continuous dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdφ : HasCompactSupport dφ := hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hsdφ : tsupport dφ ⊆ Ω.val :=
    (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hsφ
  have hLeftI : IntegrableOn (fun x => dφ x • v x) Ω.val volume :=
    (integrable_compact_smul_of_locallyIntegrableOn hvloc hdφ hcdφ hsdφ).integrableOn
  have hRightI : IntegrableOn (fun x => φ x • Dv x i) Ω.val volume :=
    (integrable_compact_smul_of_locallyIntegrableOn (hDvloc i) hφ.continuous hcφ hsφ).integrableOn
  ext j
  change (∫ x in Ω.val, dφ x • v x) j = -(∫ x in Ω.val, φ x • Dv x i) j
  rw [coordinate_integral_smul_eq_inner _ _ hLeftI, coordinate_integral_smul_eq_inner _ _ hRightI]
  let e : Ambient q := EuclideanSpace.single j 1
  have hGL : MemLp (fun x => dφ x • e) 2 (volume.restrict Ω.val) :=
    ((hdφ.smul continuous_const).memLp_of_hasCompactSupport hcdφ.smul_right).restrict _
  have hGR : MemLp (fun x => φ x • e) 2 (volume.restrict Ω.val) :=
    ((hφ.continuous.smul continuous_const).memLp_of_hasCompactSupport hcφ.smul_right).restrict _
  have hL : Tendsto (fun k => ∫ x in Ω.val, inner ℝ (u k x) (dφ x • e)) atTop
      (𝓝 (∫ x in Ω.val, inner ℝ (v x) (dφ x • e))) := by
    simpa only [real_inner_comm] using HolderToCK.tendsto_integral_inner_of_L2
      (fun k => (hseq k).2.1) hv hGL hstrong
  have hR := hweak i (fun x => φ x • e) hGR
  have heq (k : ℕ) : (∫ x in Ω.val, inner ℝ (u k x) (dφ x • e)) =
      -(∫ x in Ω.val, inner ℝ (Du k x i) (φ x • e)) := by
    have H := congrArg (fun w : Ambient q => w j) ((hseq k).1.2.2 i φ hφ hcφ hsφ)
    change (∫ x in Ω.val, dφ x • u k x) j = -(∫ x in Ω.val, φ x • Du k x i) j at H
    rw [coordinate_integral_smul_eq_inner _ _ ((hseq k).1.integrable_test_derivative i hφ hcφ hsφ),
      coordinate_integral_smul_eq_inner _ _ ((hseq k).1.integrable_test_gradient i hφ hcφ hsφ)] at H
    exact H
  exact tendsto_nhds_unique hL (hR.neg.congr' (Eventually.of_forall fun k => (heq k).symm))

end StationaryHarmonicMaps.Analysis

end
