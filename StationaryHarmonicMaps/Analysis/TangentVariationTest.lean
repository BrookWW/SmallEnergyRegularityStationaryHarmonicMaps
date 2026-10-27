module

public import HarmonicMaps.Sobolev
public import StationaryHarmonicMaps.Geometry.NormalProjectionProperties
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Actual compact tangent variations

A cutoff equal to one near the compact target turns the tangent projection of
an ambient vector into a compact C¹ tangent field. Its derivative on the target
is the negative derivative of the ambient normal-projection extension.
-/

public section

open HarmonicMaps Set Filter Topology
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- A normal-projection extension supplies genuine compact C¹ tangent fields. -/
theorem exists_compact_tangent_field {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (G : Ambient q → Ambient q →L[ℝ] Ambient q) (hG : ContDiff ℝ 1 G)
    (hGN : ∀ p : N.Carrier, G p.val = N.normalProjection p) (v : Ambient q) :
    ∃ Y : Ambient q → Ambient q, ContDiff ℝ 1 Y ∧ HasCompactSupport Y ∧
      (∀ p : N.Carrier, Y p.val = v - G p.val v) ∧
      (∀ p : N.Carrier, Y p.val ∈ N.tangentImage p) ∧
      ∀ (p : N.Carrier) (w : Ambient q),
        fderiv ℝ Y p.val w = -(fderiv ℝ G p.val w v) := by
  obtain ⟨R, hR, hbound⟩ := N.isCompact.isBounded.exists_pos_norm_le
  let χ : ContDiffBump (0 : Ambient q) :=
    { rIn := R + 1, rOut := R + 2,
      rIn_pos := lt_trans hR (lt_add_one R), rIn_lt_rOut := by linarith }
  have hχ : ContDiff ℝ 1 (χ : Ambient q → ℝ) := χ.contDiff
  have hpball (p : N.Carrier) : p.val ∈ Metric.ball (0 : Ambient q) χ.rIn := by
    change dist p.val 0 < R + 1
    rw [dist_zero_right]
    exact lt_of_le_of_lt (hbound p.val p.property) (lt_add_one R)
  have hχp (p : N.Carrier) : χ p.val = 1 :=
    χ.one_of_mem_closedBall (Metric.ball_subset_closedBall (hpball p))
  have hDχ (p : N.Carrier) : fderiv ℝ (χ : Ambient q → ℝ) p.val = 0 :=
    (χ.eventuallyEq_one_of_mem_ball (hpball p)).fderiv_eq.trans
      (hasFDerivAt_const (1 : ℝ) p.val).fderiv
  let Z : Ambient q → Ambient q := fun y => v - G y v
  let Y : Ambient q → Ambient q := fun y => χ y • Z y
  have hZ : ContDiff ℝ 1 Z := contDiff_const.sub (hG.clm_apply contDiff_const)
  have hY : ContDiff ℝ 1 Y := hχ.smul hZ
  have hYN (p : N.Carrier) : Y p.val = v - G p.val v := by
    change χ p.val • (v - G p.val v) = v - G p.val v
    rw [hχp p, one_smul]
  refine ⟨Y, hY, χ.hasCompactSupport.smul_right, hYN, ?_, ?_⟩
  · intro p
    rw [hYN p, hGN p]
    exact N.sub_normalProjection_apply_mem p v
  · intro p w
    have heval := (ContinuousLinearMap.apply ℝ (Ambient q) v).hasFDerivAt.comp p.val
      (hG.differentiable one_ne_zero p.val).hasFDerivAt
    have hDZ := congrArg (fun D : Ambient q →L[ℝ] Ambient q => D w)
      ((hasFDerivAt_const v p.val).sub heval).fderiv
    have hZfun : (fun _ : Ambient q => v) -
        ((ContinuousLinearMap.apply ℝ (Ambient q) v) ∘ G) = Z := by
      funext y
      simp only [Z, Pi.sub_apply, Function.comp_apply, ContinuousLinearMap.apply_apply]
    rw [hZfun] at hDZ
    have hDZ' : fderiv ℝ Z p.val w = -(fderiv ℝ G p.val w v) := by
      simpa only [Z, Pi.sub_apply, Function.comp_apply, sub_apply, zero_apply,
        zero_sub, neg_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply] using hDZ
    have hDY := congrArg (fun D : Ambient q →L[ℝ] Ambient q => D w)
      (fderiv_fun_smul (hχ.differentiable one_ne_zero p.val)
        (hZ.differentiable one_ne_zero p.val))
    simpa only [Y, add_apply, smul_apply, hχp p, one_smul, hDχ p,
      ContinuousLinearMap.smulRight_apply, zero_apply, zero_smul, add_zero, hDZ'] using hDY

/-- The literal separated map variation is compact and supported inside the domain. -/
theorem tangent_product_variation {n q : ℕ} (N : CompactC2EmbeddedTarget q)
    (Ω : OpenDomain n) (η : Domain n → ℝ) (hη : ContDiff ℝ 1 η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ Ω.val)
    (Y : Ambient q → Ambient q) (hY : ContDiff ℝ 1 Y) (hcY : HasCompactSupport Y)
    (hYN : ∀ p : N.Carrier, Y p.val ∈ N.tangentImage p) :
    ContDiff ℝ 1 (fun z : Domain n × Ambient q => η z.1 • Y z.2) ∧
      HasCompactSupport (fun z : Domain n × Ambient q => η z.1 • Y z.2) ∧
      tsupport (fun z : Domain n × Ambient q => η z.1 • Y z.2) ⊆
        Ω.val ×ˢ (Set.univ : Set (Ambient q)) ∧
      ∀ (x : Domain n) (p : N.Carrier), η x • Y p.val ∈ N.tangentImage p := by
  have hsupp : Function.support (fun z : Domain n × Ambient q => η z.1 • Y z.2) ⊆
      tsupport η ×ˢ tsupport Y := by
    intro z hz
    exact ⟨subset_tsupport η (left_ne_zero_of_smul hz),
      subset_tsupport Y (right_ne_zero_of_smul hz)⟩
  have htsupp : tsupport (fun z : Domain n × Ambient q => η z.1 • Y z.2) ⊆
      tsupport η ×ˢ tsupport Y :=
    closure_minimal hsupp ((isClosed_tsupport η).prod (isClosed_tsupport Y))
  refine ⟨(hη.comp contDiff_fst).smul (hY.comp contDiff_snd),
    (hcη.prod hcY).of_isClosed_subset (isClosed_tsupport _) htsupp,
    fun z hz => ⟨hsη (htsupp hz).1, mem_univ _⟩, ?_⟩
  intro x p
  exact (N.tangentImage p).smul_mem (η x) (hYN p)

/-- The actual derivative of the separated test is the two-variable product rule. -/
theorem fderiv_tangent_product_variation {n q : ℕ}
    (η : Domain n → ℝ) (hη : ContDiff ℝ 1 η)
    (Y : Ambient q → Ambient q) (hY : ContDiff ℝ 1 Y)
    (x : Domain n) (y : Ambient q) (a : Domain n) (b : Ambient q) :
    fderiv ℝ (fun z : Domain n × Ambient q => η z.1 • Y z.2) (x, y) (a, b) =
      η x • fderiv ℝ Y y b + fderiv ℝ η x a • Y y := by
  have hη' : HasFDerivAt (fun z : Domain n × Ambient q => η z.1)
      ((fderiv ℝ η x).comp (ContinuousLinearMap.fst ℝ (Domain n) (Ambient q))) (x, y) :=
    (hη.differentiable one_ne_zero x).hasFDerivAt.comp (x, y) hasFDerivAt_fst
  have hY' : HasFDerivAt (fun z : Domain n × Ambient q => Y z.2)
      ((fderiv ℝ Y y).comp (ContinuousLinearMap.snd ℝ (Domain n) (Ambient q))) (x, y) :=
    (hY.differentiable one_ne_zero y).hasFDerivAt.comp (x, y) hasFDerivAt_snd
  have h := congrArg (fun D : (Domain n × Ambient q) →L[ℝ] Ambient q => D (a, b))
    (hη'.smul hY').fderiv
  have hfun : (fun z : Domain n × Ambient q => η z.1) •
      (fun z : Domain n × Ambient q => Y z.2) =
      (fun z : Domain n × Ambient q => η z.1 • Y z.2) := rfl
  rw [hfun] at h
  simpa only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.smulRight_apply, Function.comp_apply] using h

end StationaryHarmonicMaps.Analysis

end
