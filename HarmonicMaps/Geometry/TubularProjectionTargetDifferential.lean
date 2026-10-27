module
public import HarmonicMaps.Geometry.TubularProjectionCharacterization
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Mul
public section
open Filter Set Topology
open scoped ContDiff
namespace HarmonicMaps
theorem tubularProjection_atTarget_differential {q : ℕ}
    (N : CompactSmoothEmbeddedTarget q) (p : N.Carrier) :
    ∀ (V : Set (Ambient q)) (g : Ambient q → Ambient q),
      IsOpen V → p.val ∈ V → V ⊆ tubularTube q N →
      ContDiffOn ℝ ∞ g V →
      (∀ w : tubularTube q N, w.val ∈ V →
        g w.val = (tubularProjection q N w).val) →
      (∀ v w : Ambient q,
        inner ℝ (v - fderiv ℝ g p.val v) (fderiv ℝ g p.val w) = 0) ∧
      ‖fderiv ℝ g p.val‖ ≤ 1 ∧
      (∀ v w : Ambient q,
        inner ℝ (fderiv ℝ g p.val v) w =
          inner ℝ v (fderiv ℝ g p.val w)) ∧
      (fderiv ℝ g p.val).comp (fderiv ℝ g p.val) = fderiv ℝ g p.val := by
  intro V g hV hpV hVU hg hgP
  have hSpec := (tubularProjection_characterization q N).2
  have hgp : g p.val = p.val := by
    obtain ⟨hp, hP⟩ := hSpec.2.2.1 p
    have h := hgP ⟨p.val, hp⟩ hpV
    simpa only [hP] using h
  have hNormal : ∀ z ∈ V, ∀ w : Ambient q,
      inner ℝ (z - g z) (fderiv ℝ g z w) = 0 := by
    intro z hz w
    have hzU := hVU hz
    have hMin := (hSpec.2.1 ⟨z, hzU⟩).1
    have hzg := hgP ⟨z, hzU⟩ hz
    have hDiff : DifferentiableAt ℝ g z :=
      (hg.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)
    have hmin : IsLocalMin (fun y => ‖z - g y‖ ^ 2) z := by
      filter_upwards [hV.mem_nhds hz] with y hy
      have hyN : g y ∈ N.carrierSet := by
        rw [hgP ⟨y, hVU hy⟩ hy]
        exact (tubularProjection q N ⟨y, hVU hy⟩).property
      have hDist := hMin ⟨g y, hyN⟩
      rw [← hzg] at hDist
      exact pow_le_pow_left₀ (norm_nonneg _) (by
        simpa only [dist_eq_norm] using hDist) 2
    have hsq := ((hasFDerivAt_const z z).sub hDiff.hasFDerivAt).norm_sq
    have heq := congrArg (fun L => L w) (hmin.hasFDerivAt_eq_zero hsq)
    simp only [smul_apply, ContinuousLinearMap.comp_apply, zero_apply,
      Pi.sub_apply, innerSL_apply_apply, neg_apply, zero_sub, inner_neg_right,
      nsmul_eq_mul, Nat.cast_ofNat] at heq
    exact neg_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left two_ne_zero)
  have hDiff : DifferentiableAt ℝ g p.val :=
    (hg.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)
  have hJetSmooth : ContDiffOn ℝ ∞ (fderiv ℝ g) V :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hV).1 hg).2
  have hDDiff : DifferentiableAt ℝ (fderiv ℝ g) p.val :=
    (hJetSmooth.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)
  have hOrth : ∀ v w : Ambient q,
      inner ℝ (v - fderiv ℝ g p.val v) (fderiv ℝ g p.val w) = 0 := by
    intro v w
    have he : (fun z => inner ℝ (z - g z) (fderiv ℝ g z w)) =ᶠ[𝓝 p.val]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hV.mem_nhds hpV] with z hz
      exact hNormal z hz w
    have hLeft : DifferentiableAt ℝ (fun z => z - g z) p.val :=
      differentiableAt_id.sub hDiff
    have hRight : DifferentiableAt ℝ (fun z => fderiv ℝ g z w) p.val :=
      hDDiff.clm_apply (differentiableAt_const w)
    have hd : fderiv ℝ (fun z => inner ℝ (z - g z) (fderiv ℝ g z w)) p.val v = 0 := by
      rw [he.fderiv_eq]
      simpa only [zero_apply] using
        congrArg (fun L : Ambient q →L[ℝ] ℝ => L v)
          (hasFDerivAt_const (0 : ℝ) p.val).fderiv
    rw [fderiv_inner_apply ℝ hLeft hRight, hgp, sub_self, inner_zero_left, zero_add] at hd
    have hfd : fderiv ℝ (fun z : Ambient q => z - g z) p.val =
        ContinuousLinearMap.id ℝ (Ambient q) - fderiv ℝ g p.val :=
      ((hasFDerivAt_id p.val).sub hDiff.hasFDerivAt).fderiv
    rw [hfd] at hd
    simpa only [sub_apply, ContinuousLinearMap.id_apply] using hd
  have hInner : ∀ v w : Ambient q,
      inner ℝ v (fderiv ℝ g p.val w) =
        inner ℝ (fderiv ℝ g p.val v) (fderiv ℝ g p.val w) := by
    intro v w
    have h := hOrth v w
    rw [inner_sub_left] at h
    exact sub_eq_zero.mp h
  have hNorm : ‖fderiv ℝ g p.val‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    have hi := hInner v v
    rw [real_inner_self_eq_norm_sq] at hi
    have hn := norm_sub_sq_real v (fderiv ℝ g p.val v)
    rw [hi] at hn
    simp only [one_mul]
    nlinarith only [hn, sq_nonneg ‖v - fderiv ℝ g p.val v‖,
      norm_nonneg v, norm_nonneg (fderiv ℝ g p.val v)]
  have hSym : ∀ v w : Ambient q,
      inner ℝ (fderiv ℝ g p.val v) w =
        inner ℝ v (fderiv ℝ g p.val w) := by
    intro v w
    calc
      inner ℝ (fderiv ℝ g p.val v) w = inner ℝ w (fderiv ℝ g p.val v) :=
        real_inner_comm _ _
      _ = inner ℝ (fderiv ℝ g p.val w) (fderiv ℝ g p.val v) := hInner w v
      _ = inner ℝ (fderiv ℝ g p.val v) (fderiv ℝ g p.val w) := real_inner_comm _ _
      _ = inner ℝ v (fderiv ℝ g p.val w) := (hInner v w).symm
  refine ⟨hOrth, hNorm, hSym, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  change inner ℝ (fderiv ℝ g p.val (fderiv ℝ g p.val v)) w =
    inner ℝ (fderiv ℝ g p.val v) w
  exact (hSym (fderiv ℝ g p.val v) w).trans ((hInner v w).symm.trans (hSym v w).symm)
end HarmonicMaps
