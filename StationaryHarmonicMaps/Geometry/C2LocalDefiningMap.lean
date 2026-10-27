module

public import StationaryHarmonicMaps.Geometry.C2LocalRetraction
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Compact local defining maps for a C² target

A cutoff of the displacement from a local retraction vanishes on the entire
target. Near its center, the kernel of its actual derivative is contained in
the target tangent subspace. The defining maps are global C¹ functions with
compact support.
-/

public section

open Filter Set Topology
open scoped ContDiff

namespace StationaryHarmonicMaps.CompactC2EmbeddedTarget

/-- A genuine compact C¹ defining map detects tangent vectors near each target point. -/
theorem exists_compact_local_defining_map {q : ℕ} (N : CompactC2EmbeddedTarget q)
    (p : N.Carrier) :
    ∃ (O : Set (EuclideanSpace ℝ (Fin q)))
      (F : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin q)),
      IsOpen O ∧ p.val ∈ O ∧ ContDiff ℝ 1 F ∧ HasCompactSupport F ∧
      (∀ y : N.Carrier, F y.val = 0) ∧
      ∀ y : N.Carrier, y.val ∈ O → ∀ v : EuclideanSpace ℝ (Fin q),
        fderiv ℝ F y.val v = 0 → v ∈ N.tangentImage y := by
  obtain ⟨V, R, hVo, hpV, hR, _hRmem, hfix, hDRt⟩ :=
    N.exists_local_c2_ambient_retraction p
  obtain ⟨χ, hsχ, hcχ, hχ, _hχrange, hχp⟩ :=
    exists_contDiff_tsupport_subset (n := (1 : ℕ∞)) (hVo.mem_nhds hpV)
  let F : EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin q) :=
    fun z => χ z • (z - R z)
  have hFC1 : ContDiff ℝ 1 F := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport χ
    · have hRz : ContDiffAt ℝ 1 R z :=
        (hR.contDiffAt (hVo.mem_nhds (hsχ hz))).of_le one_le_two
      exact hχ.contDiffAt.smul (contDiffAt_id.sub hRz)
    · apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
      change χ y • (y - R y) = 0
      simp only [hy, Pi.zero_apply, zero_smul]
  have hFN (y : N.Carrier) : F y.val = 0 := by
    by_cases hyχ : χ y.val = 0
    · simp only [F, hyχ, zero_smul]
    · have hyV : y.val ∈ V := hsχ (subset_tsupport χ hyχ)
      simp only [F, hfix y hyV, sub_self, smul_zero]
  refine ⟨Function.support χ, F, hχ.continuous.isOpen_support, ?_, hFC1,
    hcχ.smul_right, hFN, ?_⟩
  · change χ p.val ≠ 0
    rw [hχp]
    exact one_ne_zero
  · intro y hy v hv
    have hyχ : χ y.val ≠ 0 := hy
    have hyV : y.val ∈ V := hsχ (subset_tsupport χ hyχ)
    have hRd : DifferentiableAt ℝ R y.val :=
      (hR.contDiffAt (hVo.mem_nhds hyV)).differentiableAt two_ne_zero
    have hsub : fderiv ℝ (fun z => z - R z) y.val =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin q)) - fderiv ℝ R y.val :=
      ((hasFDerivAt_id y.val).sub hRd.hasFDerivAt).fderiv
    have hDF : fderiv ℝ F y.val = χ y.val •
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin q)) - fderiv ℝ R y.val) := by
      have h := fderiv_fun_smul (c := χ) (f := fun z => z - R z)
        (hχ.differentiable one_ne_zero y.val)
        (differentiableAt_id.sub hRd)
      simpa only [F, hsub, hfix y hyV, sub_self,
        ContinuousLinearMap.smulRight_zero, add_zero] using h
    have hzero : χ y.val • (v - fderiv ℝ R y.val v) = 0 := by
      simpa only [hDF, smul_apply, sub_apply,
        ContinuousLinearMap.id_apply] using hv
    have hvR : v = fderiv ℝ R y.val v :=
      sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left hyχ)
    rw [hvR]
    exact hDRt y hyV v

end StationaryHarmonicMaps.CompactC2EmbeddedTarget

end
