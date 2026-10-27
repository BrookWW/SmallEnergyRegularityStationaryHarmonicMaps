module

public import StationaryHarmonicMaps.Analysis.C1MixedPostcomposition
public import HarmonicMaps.Analysis.SobolevAECongruence
public import HarmonicMaps.Analysis.SobolevLocality
public import HarmonicMaps.SobolevRestriction
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual operator-field Sobolev tests

A compact target cutoff agrees with the given linear operator field on a
neighborhood of the essential range. The mixed chain rule and a.e. Sobolev
congruence produce the original product map and its actual weak columns.
Interior compact support gives genuine bounded zero-boundary test data.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

private theorem exists_compact_operator_cutoff {m q : ℕ}
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q)) (M : ℝ) :
    ∃ A : Ambient m → (Ambient q →L[ℝ] Ambient q),
      ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧
      ∀ z, ‖z‖ ≤ M → A z = R z ∧ fderiv ℝ A z = R := by
  let χ : ContDiffBump (0 : Ambient m) :=
    { rIn := |M| + 1, rOut := |M| + 2,
      rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let A : Ambient m → (Ambient q →L[ℝ] Ambient q) := fun z => χ z • R z
  have hA : ContDiff ℝ ∞ A := χ.contDiff.smul R.contDiff
  have htsA : tsupport A ⊆ tsupport (χ : Ambient m → ℝ) := by
    apply closure_mono
    intro z hz hzero
    change χ z = (0 : ℝ) at hzero
    apply hz
    change χ z • R z = 0
    rw [hzero]
    exact zero_smul ℝ (R z)
  have hcA : HasCompactSupport A :=
    χ.hasCompactSupport.of_isClosed_subset (isClosed_tsupport A) htsA
  refine ⟨A, hA, hcA, ?_⟩
  intro z hz
  have hball : z ∈ Metric.ball (0 : Ambient m) χ.rIn := by
    change dist z 0 < |M| + 1
    rw [dist_zero_right]
    exact lt_of_le_of_lt (hz.trans (le_abs_self M)) (lt_add_one _)
  have hEq : A =ᶠ[𝓝 z] R :=
    (χ.eventuallyEq_one_of_mem_ball hball).mono (fun y hy => by
      change χ y = (1 : ℝ) at hy
      change χ y • R y = R y
      rw [hy, one_smul])
  exact ⟨hEq.eq_of_nhds, hEq.fderiv_eq.trans R.fderiv⟩

private theorem compact_operator_test_support {n m q : ℕ}
    (A : Ambient m → (Ambient q →L[ℝ] Ambient q)) (hcA : HasCompactSupport A)
    (ψ : Domain n → Ambient q) (hcψ : HasCompactSupport ψ) :
    HasCompactSupport (fun z : Domain n × Ambient m => A z.2 (ψ z.1)) ∧
      Prod.fst '' tsupport (fun z : Domain n × Ambient m => A z.2 (ψ z.1)) ⊆ tsupport ψ := by
  let V : Domain n × Ambient m → Ambient q := fun z => A z.2 (ψ z.1)
  have hts : tsupport V ⊆ tsupport ψ ×ˢ tsupport A := by
    apply closure_minimal _ ((isClosed_tsupport ψ).prod (isClosed_tsupport A))
    intro z hz
    have hψnz : ψ z.1 ≠ 0 := by
      intro hzero
      exact hz (by change A z.2 (ψ z.1) = 0; rw [hzero, map_zero])
    have hAnz : A z.2 ≠ 0 := by
      intro hzero
      exact hz (by change A z.2 (ψ z.1) = 0; rw [hzero]; rfl)
    exact ⟨subset_tsupport ψ hψnz, subset_tsupport A hAnz⟩
  refine ⟨(hcψ.prod hcA).of_isClosed_subset (isClosed_tsupport V) hts, ?_⟩
  rintro x ⟨z, hz, rfl⟩
  exact (hts hz).1

/-- A compact smooth mixed field agrees with the operator product and derivative near the range. -/
theorem exists_smooth_compact_operator_test {n m q : ℕ}
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q)) (M : ℝ)
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ∃ V : Domain n × Ambient m → Ambient q,
      ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
      Prod.fst '' tsupport V ⊆ tsupport ψ ∧
      ∀ (x : Domain n) (z : Ambient m), ‖z‖ ≤ M →
        V (x, z) = R z (ψ x) ∧ ∀ (a : Domain n) (b : Ambient m),
          fderiv ℝ V (x, z) (a, b) = R b (ψ x) + R z (fderiv ℝ ψ x a) := by
  obtain ⟨A, hA, hcA, hEq⟩ := exists_compact_operator_cutoff R M
  let V : Domain n × Ambient m → Ambient q := fun z => A z.2 (ψ z.1)
  have hV : ContDiff ℝ ∞ V :=
    (hA.comp contDiff_snd).clm_apply (hψ.comp contDiff_fst)
  obtain ⟨hcV, hsV⟩ := compact_operator_test_support A hcA ψ hcψ
  refine ⟨V, hV, hcV, hsV, ?_⟩
  intro x z hz
  obtain ⟨hAz, hDA⟩ := hEq z hz
  refine ⟨by change A z (ψ x) = _; rw [hAz], ?_⟩
  intro a b
  have hdA : HasFDerivAt (fun w : Domain n × Ambient m => A w.2)
      ((fderiv ℝ A z).comp (ContinuousLinearMap.snd ℝ (Domain n) (Ambient m))) (x, z) :=
    (hA.differentiable (by simp) z).hasFDerivAt.comp (x, z) hasFDerivAt_snd
  have hdψ : HasFDerivAt (fun w : Domain n × Ambient m => ψ w.1)
      ((fderiv ℝ ψ x).comp (ContinuousLinearMap.fst ℝ (Domain n) (Ambient m))) (x, z) :=
    (hψ.differentiable (by simp) x).hasFDerivAt.comp (x, z) hasFDerivAt_fst
  have H := congrArg (fun D : (Domain n × Ambient m) →L[ℝ] Ambient q => D (a, b))
    (hdA.clm_apply hdψ).fderiv
  change fderiv ℝ V (x, z) (a, b) = A z (fderiv ℝ ψ x a) + fderiv ℝ A z b (ψ x) at H
  rw [hAz, hDA] at H
  exact H.trans (add_comm _ _)

/-- The original operator product has the displayed local weak product gradient. -/
theorem memW12Loc_operator_test {n m q : ℕ} {Ω : OpenDomain n}
    {p : Domain n → Ambient m} {Dp : Domain n → Gradient n m}
    (hp : MemW12Loc Ω p Dp) {M : ℝ}
    (hb : ∀ᵐ x ∂volume.restrict Ω.val, ‖p x‖ ≤ M)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    MemW12Loc Ω (fun x => R (p x) (ψ x)) (fun x i =>
      R (Dp x i) (ψ x) + R (p x) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
  obtain ⟨V, hV, hcV, _hsV, hEq⟩ := exists_smooth_compact_operator_test R M ψ hψ hcψ
  obtain ⟨L, hL⟩ := (hcV.fderiv ℝ).exists_bound_of_continuous
    (hV.continuous_fderiv (by simp))
  have hW := memW12Loc_mixed_postcompose_c1 hp V (hV.of_le (by simp)) hL
  apply hW.congr_ae
  · exact hb.mono (fun x hx => (hEq x (p x) hx).1)
  · filter_upwards [hb] with x hx
    funext i
    exact (hEq x (p x) hx).2 _ _

/-- The actual product is a bounded W₀¹,² test on every interior ball containing the test support. -/
theorem operator_test_zeroBoundary_ball {n m q : ℕ} {Ω : OpenDomain n}
    {p : Domain n → Ambient m} {Dp : Domain n → Gradient n m}
    (hp : MemW12Loc Ω p Dp) {M : ℝ}
    (hb : ∀ᵐ x ∂volume.restrict Ω.val, ‖p x‖ ≤ M)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    {a : Domain n} {r : ℝ} (hr : 0 < r) (hclosed : Metric.closedBall a r ⊆ Ω.val)
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Metric.ball a r) :
    HasZeroBoundaryValues (ballDomain a r) (fun x => R (p x) (ψ x))
      (fun x i => R (Dp x i) (ψ x) + R (p x) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂volume.restrict (Metric.ball a r), ‖R (p x) (ψ x)‖ ≤ C := by
  have hW := (memW12Loc_operator_test hp hb R ψ hψ hcψ).memW12_ball hclosed
  have hts : tsupport (fun x => R (p x) (ψ x)) ⊆ tsupport ψ := by
    apply closure_mono
    intro x hx hz
    exact hx (by change R (p x) (ψ x) = 0; rw [hz, map_zero])
  have hc : HasCompactSupport (fun x => R (p x) (ψ x)) :=
    hcψ.of_isClosed_subset (isClosed_tsupport _) hts
  obtain ⟨B, hB⟩ := hcψ.exists_bound_of_continuous hψ.continuous
  have hBnonneg : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨hW.zeroBoundary_of_compactSupport_ball hr hc (hts.trans hsψ),
    ‖R‖ * |M| * B, by positivity, ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (Metric.ball_subset_closedBall.trans hclosed) hb] with x hx
  calc
    ‖R (p x) (ψ x)‖ ≤ ‖R (p x)‖ * ‖ψ x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖R‖ * ‖p x‖) * ‖ψ x‖ :=
      mul_le_mul_of_nonneg_right (R.le_opNorm _) (norm_nonneg _)
    _ ≤ _ := by gcongr; exact hx.trans (le_abs_self M); exact hB x

end StationaryHarmonicMaps.Analysis

end
