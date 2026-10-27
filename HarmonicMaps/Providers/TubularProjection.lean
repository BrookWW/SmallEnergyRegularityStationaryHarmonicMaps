module
public import HarmonicMaps.Geometry.TubularProjectionDerivativeCharacterization
public import HarmonicMaps.Geometry.TubularProjectionSecondDerivativeCharacterization
public import HarmonicMaps.Geometry.TubularProjectionTargetDifferential
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
public import HarmonicMaps.Geometry.TubularProjectionCharacterization
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Normed.Group.Bounded
public section
open Filter Set Topology
open scoped ContDiff Manifold
namespace HarmonicMaps
open scoped Manifold ContDiff
private theorem tubularProjection_atTarget_tangentProjection (q : ℕ) (N : CompactSmoothEmbeddedTarget q) (p : N.Carrier) :
  ∀ (V : Set (Ambient q)) (g : Ambient q → Ambient q),
    IsOpen V → p.val ∈ V → V ⊆ tubularTube q N →
    ContDiffOn ℝ ∞ g V →
    (∀ w : tubularTube q N, w.val ∈ V →
      g w.val = (tubularProjection q N w).val) →
    fderiv ℝ g p.val =
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) 𝓘(ℝ, Ambient q)
        (Subtype.val : N.Carrier → Ambient q) p).range.starProjection :=
by
  classical
  intro V g hV hpV hVU hg hgP
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension))
  let J := 𝓘(ℝ, Ambient q)
  let incl : N.Carrier → Ambient q := Subtype.val
  let A := mfderiv I J incl p
  have hSpec := (tubularProjection_characterization q N).2
  have hInclDiff : MDifferentiableAt I J incl p :=
    (N.isSmoothEmbedding.contMDiff p).mdifferentiableAt (by simp)
  have hgSmooth : ContDiffAt ℝ ∞ g p.val := hg.contDiffAt (hV.mem_nhds hpV)
  have hgDiff : DifferentiableAt ℝ g p.val := hgSmooth.differentiableAt (by simp)
  have hFix : (g ∘ incl) =ᶠ[𝓝 p] incl := by
    filter_upwards [continuousAt_subtype_val.preimage_mem_nhds (hV.mem_nhds hpV)] with p' hp'
    obtain ⟨hp'U, hP⟩ := hSpec.2.2.1 p'
    have h := hgP ⟨p'.val, hp'U⟩ hp'
    simpa only [hP, Function.comp_def, incl] using h
  have hFixDer : mfderiv I J (g ∘ incl) p = A := hFix.mfderiv_eq
  have hFixComp : (fderiv ℝ g p.val).comp A = A := by
    have h := mfderiv_comp p hgDiff.mdifferentiableAt hInclDiff
    rw [mfderiv_eq_fderiv] at h
    exact h.symm.trans hFixDer
  let lift : Ambient q → N.Carrier := fun x =>
    if hx : x ∈ V then tubularProjection q N ⟨x, hVU hx⟩ else p
  have hLiftAmbient : (incl ∘ lift) =ᶠ[𝓝 p.val] g := by
    filter_upwards [hV.mem_nhds hpV] with x hx
    dsimp only [Function.comp_def, incl, lift]
    rw [dif_pos hx]
    exact (hgP ⟨x, hVU hx⟩ hx).symm
  have hLiftp : lift p.val = p := by
    dsimp only [lift]
    rw [dif_pos hpV]
    obtain ⟨hpU, hP⟩ := hSpec.2.2.1 p
    exact hP
  have hCompositeSmooth : ContMDiffAt J J ∞ (incl ∘ lift) p.val :=
    hgSmooth.contMDiffAt.congr_of_eventuallyEq hLiftAmbient
  have hLiftCont : ContinuousAt lift p.val :=
    IsInducing.subtypeVal.continuousAt_iff.mpr hCompositeSmooth.continuousAt
  have hLiftSmooth : ContMDiffAt J I ∞ lift p.val :=
    (ContMDiffAt.iff_comp_isImmersionAt
      (N.isSmoothEmbedding.isImmersion.isImmersionAt (lift p.val))).mpr ⟨hLiftCont, hCompositeSmooth⟩
  have hLiftDiff : MDifferentiableAt J I lift p.val :=
    hLiftSmooth.mdifferentiableAt (by simp)
  have hFactor : fderiv ℝ g p.val = A.comp (mfderiv J I lift p.val) := by
    have h := mfderiv_comp p.val
      ((N.isSmoothEmbedding.contMDiff (lift p.val)).mdifferentiableAt (by simp)) hLiftDiff
    rw [hLiftp] at h
    have hEq : mfderiv J J (incl ∘ lift) p.val = fderiv ℝ g p.val := by
      simpa only [J, mfderiv_eq_fderiv] using
        (hLiftAmbient.mfderiv_eq (I := J) (I' := J))
    exact hEq.symm.trans h
  have hRangeTo : (fderiv ℝ g p.val).range ≤ A.range := by
    rintro v ⟨w, rfl⟩
    refine ⟨mfderiv J I lift p.val w, ?_⟩
    rw [hFactor]
    rfl
  have hRangeFrom : A.range ≤ (fderiv ℝ g p.val).range := by
    rintro v ⟨w, rfl⟩
    exact ⟨A w, congrArg (fun T : EuclideanSpace ℝ (Fin N.dimension) →L[ℝ] Ambient q => T w) hFixComp⟩
  have hOrtho := (tubularProjection_atTarget_differential N p V g hV hpV hVU hg hgP).1
  apply ContinuousLinearMap.ext
  intro v
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hRangeTo ⟨v, rfl⟩
  · intro w hw
    obtain ⟨u, rfl⟩ := hRangeFrom hw
    exact hOrtho v u


end HarmonicMaps

namespace HarmonicMaps

private theorem tubularProjectionDerivative_atTarget (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    ∀ (p : N.Carrier) (hp : p.val ∈ tubularTube q N),
      tubularProjectionDerivative q N ⟨p.val, hp⟩ =
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) 𝓘(ℝ, Ambient q)
          (Subtype.val : N.Carrier → Ambient q) p).range.starProjection ∧
      ‖tubularProjectionDerivative q N ⟨p.val, hp⟩‖ ≤ 1 := by
  intro p hp
  obtain ⟨V, hV, hpV, hVU, g, hg, hgP⟩ :=
    (tubularProjection_characterization q N).2.2.2.2.1 ⟨p.val, hp⟩
  have hD := (tubularProjectionDerivative_characterization q N).1
    ⟨p.val, hp⟩ V g hV hpV hVU hg hgP
  rw [← hD]
  exact ⟨tubularProjection_atTarget_tangentProjection q N p V g hV hpV hVU hg hgP,
    (tubularProjection_atTarget_differential N p V g hV hpV hVU hg hgP).2.1⟩

private theorem tubularProjectionDerivative_continuous (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    Continuous (tubularProjectionDerivative q N) := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨V, hV, hzV, _, g, _, _, hgD, hD⟩ :=
    (tubularProjectionDerivative_characterization q N).2.1 z
  have hCont : ContinuousAt (fun w : tubularTube q N => fderiv ℝ g w.val) z :=
    (hgD.contDiffAt (hV.mem_nhds hzV)).continuousAt.comp continuousAt_subtype_val
  apply hCont.congr
  filter_upwards [continuousAt_subtype_val.preimage_mem_nhds (hV.mem_nhds hzV)] with w hw
  exact hD w hw

private theorem tubularProjectionSecondDerivative_continuous (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    Continuous (tubularProjectionSecondDerivative q N) := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨V, hV, hzV, _, g, _, _, hgH, hH⟩ :=
    (tubularProjectionSecondDerivative_characterization q N).2.1 z
  have hCont : ContinuousAt (fun w : tubularTube q N => fderiv ℝ (fderiv ℝ g) w.val) z :=
    (hgH.contDiffAt (hV.mem_nhds hzV)).continuousAt.comp continuousAt_subtype_val
  apply hCont.congr
  filter_upwards [continuousAt_subtype_val.preimage_mem_nhds (hV.mem_nhds hzV)] with w hw
  exact hH w hw

private theorem tubularProjectionDerivative_radiusReduction (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ tubularBaseRadius q N ∧
      ∀ z : Ambient q, Metric.infDist z N.carrierSet < 2 * rho →
        ∃ hz : z ∈ tubularTube q N, ‖tubularProjectionDerivative q N ⟨z, hz⟩‖ ≤ 2 := by
  let V : Set (tubularTube q N) := {w | ‖tubularProjectionDerivative q N w‖ < 2}
  let O : Set (Ambient q) := Subtype.val '' V
  have hV : IsOpen V := isOpen_lt
    (tubularProjectionDerivative_continuous q N).norm continuous_const
  have hO : IsOpen O := (tubularProjection_characterization q N).2.1.isOpenMap_subtype_val V hV
  have hNO : N.carrierSet ⊆ O := by
    intro p hp
    obtain ⟨hpU, _⟩ := (tubularProjection_characterization q N).2.2.2.1 ⟨p, hp⟩
    refine ⟨⟨p, hpU⟩, ?_, rfl⟩
    exact (tubularProjectionDerivative_atTarget q N ⟨p, hp⟩ hpU).2.trans_lt (by norm_num)
  obtain ⟨delta, hdelta, hthick⟩ := N.isCompact.exists_thickening_subset_open hO hNO
  let rho := min (tubularBaseRadius q N) (delta / 2)
  have hrho : 0 < rho := lt_min (tubularProjection_characterization q N).1 (half_pos hdelta)
  refine ⟨rho, hrho, min_le_left _ _, ?_⟩
  intro z hz
  have hzdelta : Metric.infDist z N.carrierSet < delta :=
    hz.trans_le (by dsimp only [rho]; linarith only [min_le_right (tubularBaseRadius q N) (delta / 2)])
  have hzO := hthick ((Metric.mem_thickening_iff_infDist_lt N.nonempty).2 hzdelta)
  obtain ⟨w, hw, hwz⟩ := hzO
  subst z
  exact ⟨w.property, le_of_lt hw⟩

private theorem tubularProjectionSecondDerivative_targetNormSup (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    let S : Set ℝ := {r | ∃ p : N.Carrier, ∃ hp : p.val ∈ tubularTube q N,
      r = ‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖}
    BddAbove S ∧ 0 ≤ sSup S ∧
      (∀ (p : N.Carrier) (hp : p.val ∈ tubularTube q N),
        ‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖ ≤ sSup S) ∧
      ∃ (p : N.Carrier) (hp : p.val ∈ tubularTube q N),
        ‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖ = sSup S := by
  classical
  dsimp only
  let inclusion : N.Carrier → tubularTube q N := fun p =>
    ⟨p.val, ((tubularProjection_characterization q N).2.2.2.1 p).choose⟩
  let f : N.Carrier → ℝ := fun p => ‖tubularProjectionSecondDerivative q N (inclusion p)‖
  have hI : Continuous inclusion := continuous_subtype_val.subtype_mk _
  have hH : Continuous (fun p : N.Carrier => tubularProjectionSecondDerivative q N (inclusion p)) :=
    (tubularProjectionSecondDerivative_continuous q N).comp hI
  have hf : Continuous f := by
    change Continuous (fun p : N.Carrier => ‖tubularProjectionSecondDerivative q N (inclusion p)‖)
    exact (continuous_norm (E := Ambient q →L[ℝ] (Ambient q →L[ℝ] Ambient q))).comp hH
  have hSet : {r : ℝ | ∃ p : N.Carrier, ∃ hp : p.val ∈ tubularTube q N,
      r = ‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖} = range f := by
    ext r
    constructor
    · rintro ⟨p, hp, hr⟩
      exact ⟨p, hr.symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p, (inclusion p).property, rfl⟩
  have hCompact : IsCompact (range f) := isCompact_range hf
  have hBdd := hCompact.bddAbove
  have hNonempty : (range f).Nonempty := range_nonempty f
  obtain ⟨p, hpSup⟩ := hCompact.sSup_mem hNonempty
  rw [hSet]
  refine ⟨hBdd, ?_, ?_, ?_⟩
  · rw [← hpSup]
    change 0 ≤ ‖tubularProjectionSecondDerivative q N (inclusion p)‖
    exact norm_nonneg (tubularProjectionSecondDerivative q N (inclusion p))
  · intro p' hp'
    exact le_csSup hBdd ⟨p', rfl⟩
  · exact ⟨p, (inclusion p).property, hpSup⟩

end HarmonicMaps

namespace HarmonicMaps

private theorem exists_projection_cutoff (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    ∃ χ : Ambient q → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ tubularTube q N ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ x, Metric.infDist x N.carrierSet < ε → χ x = 1 := by
  have hBase := tubularProjection_characterization q N
  have hU := hBase.2.1
  have hNU : N.carrierSet ⊆ tubularTube q N := by
    intro p hp
    obtain ⟨h, _⟩ := hBase.2.2.2.1 ⟨p, hp⟩
    exact h
  obtain ⟨K, hK, hNK, hKU⟩ := exists_compact_between N.isCompact hU hNU
  obtain ⟨χ, hχ1, hχ0, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, Ambient q)
      N.isClosed hNK (n := (⊤ : ℕ∞))
  have hχsupport : tsupport χ ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hxK
    exact hx (hχ0 x hxK)
  have hχcompact : HasCompactSupport χ :=
    hK.of_isClosed_subset (isClosed_tsupport _) hχsupport
  obtain ⟨ε, hε, hεχ⟩ := (Metric.hasBasis_nhdsSet_thickening N.isCompact).mem_iff.mp hχ1
  refine ⟨χ, χ.contMDiff.contDiff, hχcompact, hχsupport.trans hKU, ε, hε, ?_⟩
  intro x hx
  exact hεχ ((Metric.mem_thickening_iff_infDist_lt N.nonempty).mpr hx)

private theorem projection_cutoff_smooth (q : ℕ) (N : CompactSmoothEmbeddedTarget q)
    (p0 : Ambient q) (χ : Ambient q → ℝ) (A : Ambient q → Ambient q)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχsupport : tsupport χ ⊆ tubularTube q N)
    (hAP : ∀ z : tubularTube q N, A z.val = (tubularProjection q N z).val) :
    ContDiff ℝ ∞ (fun x => χ x • (A x - p0)) := by
  classical
  let R : Ambient q → Ambient q := fun x => χ x • (A x - p0)
  change ContDiff ℝ ∞ R
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · have hxU := hχsupport hx
    obtain ⟨V, hV, hxV, hVU, g, hg, hgP⟩ :=
      (tubularProjection_characterization q N).2.2.2.2.1 ⟨x, hxU⟩
    have hEq : R =ᶠ[𝓝 x] (fun y => χ y • (g y - p0)) := by
      filter_upwards [hV.mem_nhds hxV] with y hy
      have hyU := hVU hy
      dsimp only [R]
      rw [hAP ⟨y, hyU⟩, hgP ⟨y, hyU⟩ hy]
    exact (hχsmooth.contDiffAt.smul
      ((hg.contDiffAt (hV.mem_nhds hxV)).sub contDiffAt_const)).congr_of_eventuallyEq hEq
  · have hEq : R =ᶠ[𝓝 x] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      dsimp only [R]
      simp only [hy, Pi.zero_apply, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq hEq

private theorem compact_perturbation_derivative_bounds {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (R : E → E)
    (p0 : E) (hRsmooth : ContDiff ℝ ∞ R) (hRcompact : HasCompactSupport R) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      (∀ z, ‖fderiv ℝ (fun x => R x + p0) z‖ ≤ C₁) ∧
      ∀ z, ‖fderiv ℝ (fderiv ℝ (fun x => R x + p0)) z‖ ≤ C₂ := by
  have hDRsmooth : ContDiff ℝ ∞ (fderiv ℝ R) := (contDiff_infty_iff_fderiv.mp hRsmooth).2
  have hDDRcontinuous : Continuous (fderiv ℝ (fderiv ℝ R)) :=
    ((contDiff_infty_iff_fderiv.mp hDRsmooth).2).continuous
  obtain ⟨C₁, hC₁⟩ := (hRcompact.fderiv ℝ).exists_bound_of_continuous hDRsmooth.continuous
  obtain ⟨C₂, hC₂⟩ := ((hRcompact.fderiv ℝ).fderiv ℝ).exists_bound_of_continuous hDDRcontinuous
  have hDQ : fderiv ℝ (fun x => R x + p0) = fderiv ℝ R := by
    funext z
    exact fderiv_add_const p0
  refine ⟨max C₁ 1, max C₂ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_, ?_⟩
  · intro z
    rw [hDQ]
    exact (hC₁ z).trans (le_max_left _ _)
  · intro z
    rw [hDQ]
    exact (hC₂ z).trans (le_max_left _ _)

private theorem tubularProjection_exists_global_extension (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ tubularBaseRadius q N ∧
      ∃ Q : Ambient q → Ambient q, ContDiff ℝ ∞ Q ∧
        (∀ z : tubularTube q N, Metric.infDist z.val N.carrierSet < ρ →
          Q z.val = (tubularProjection q N z).val) ∧
        ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
          (∀ z, ‖fderiv ℝ Q z‖ ≤ C₁) ∧
          ∀ z, ‖fderiv ℝ (fderiv ℝ Q) z‖ ≤ C₂ := by
  classical
  obtain ⟨χ, hχsmooth, hχcompact, hχsupport, ε, hε, hεχ⟩ := exists_projection_cutoff q N
  let ρ := min ε (tubularBaseRadius q N)
  have hρ : 0 < ρ := lt_min hε (tubularProjection_characterization q N).1
  obtain ⟨p0, hp0⟩ := N.nonempty
  let A : Ambient q → Ambient q := fun x =>
    if hx : x ∈ tubularTube q N then (tubularProjection q N ⟨x, hx⟩).val else p0
  have hAP : ∀ z : tubularTube q N, A z.val = (tubularProjection q N z).val := by
    intro z
    dsimp only [A]
    rw [dif_pos z.property]
  let R : Ambient q → Ambient q := fun x => χ x • (A x - p0)
  let Q : Ambient q → Ambient q := fun x => R x + p0
  have hRsmooth : ContDiff ℝ ∞ R := projection_cutoff_smooth q N p0 χ A hχsmooth hχsupport hAP
  have hRcompact : HasCompactSupport R := hχcompact.smul_right
  refine ⟨ρ, hρ, min_le_right _ _, Q, hRsmooth.add contDiff_const, ?_,
    compact_perturbation_derivative_bounds R p0 hRsmooth hRcompact⟩
  intro z hz
  have hχz : χ z.val = 1 := hεχ z.val (lt_of_lt_of_le hz (min_le_left _ _))
  dsimp only [Q, R]
  rw [hχz, one_smul, hAP z, sub_add_cancel]

end HarmonicMaps

namespace HarmonicMaps.Providers.TubularProjection
theorem result (q : ℕ) (N : CompactSmoothEmbeddedTarget q) :
  ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ tubularBaseRadius q N ∧
  let U : Set (Ambient q) := {z | Metric.infDist z N.carrierSet < 2 * ρ}
  ∃ hsub : U ⊆ tubularTube q N,
    IsOpen U ∧
    (∀ z : U,
      (∀ p : N.Carrier,
        dist z.val (tubularProjection q N ⟨z.val, hsub z.property⟩).val ≤
          dist z.val p.val) ∧
      ∀ p : N.Carrier,
        (∀ p' : N.Carrier, dist z.val p.val ≤ dist z.val p'.val) →
        p = tubularProjection q N ⟨z.val, hsub z.property⟩) ∧
    (∀ p : N.Carrier, ∃ hp : p.val ∈ U,
      tubularProjection q N ⟨p.val, hsub hp⟩ = p ∧
      tubularProjectionDerivative q N ⟨p.val, hsub hp⟩ =
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin N.dimension)) 𝓘(ℝ, Ambient q)
          (Subtype.val : N.Carrier → Ambient q) p).range.starProjection) ∧
    (∀ z : U, ∃ V : Set (Ambient q), IsOpen V ∧ z.val ∈ V ∧ V ⊆ U ∧
      ∃ g : Ambient q → Ambient q, ContDiffOn ℝ ∞ g V ∧
        ∀ w : U, w.val ∈ V →
          g w.val = (tubularProjection q N ⟨w.val, hsub w.property⟩).val) ∧
    (∀ z : U, ‖tubularProjectionDerivative q N ⟨z.val, hsub z.property⟩‖ ≤ 2) ∧
    let S : Set ℝ := {k | ∃ p : N.Carrier, ∃ hp : p.val ∈ tubularTube q N,
      k = ‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖}
    S.Nonempty ∧ BddAbove S ∧ 0 ≤ sSup S ∧
    (∀ (p : N.Carrier) (hp : p.val ∈ tubularTube q N),
      ‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖ ≤ sSup S) ∧
    ∃ Q : Ambient q → Ambient q, ContDiff ℝ ∞ Q ∧
      (∀ z : tubularTube q N, Metric.infDist z.val N.carrierSet < ρ →
        Q z.val = (tubularProjection q N z).val) ∧
      ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
        (∀ z, ‖fderiv ℝ Q z‖ ≤ C₁) ∧
        ∀ z, ‖fderiv ℝ (fderiv ℝ Q) z‖ ≤ C₂ :=
by
  classical
  obtain ⟨rd, hrd, hrdbase, hD⟩ := tubularProjectionDerivative_radiusReduction q N
  obtain ⟨re, hre, hrebase, Q, hQ, hQP, C₁, C₂, hC₁, hC₂, hQD, hQH⟩ :=
    tubularProjection_exists_global_extension q N
  let ρ := min rd re
  have hρ : 0 < ρ := lt_min hrd hre
  have hρrd : ρ ≤ rd := min_le_left rd re
  have hρre : ρ ≤ re := min_le_right rd re
  have hρbase : ρ ≤ tubularBaseRadius q N := hρrd.trans hrdbase
  refine ⟨ρ, hρ, hρbase, ?_⟩
  let U : Set (Ambient q) := {z | Metric.infDist z N.carrierSet < 2 * ρ}
  have hsub : U ⊆ tubularTube q N := by
    intro z hz
    change Metric.infDist z N.carrierSet < 2 * tubularBaseRadius q N
    exact hz.trans_le (mul_le_mul_of_nonneg_left hρbase (by norm_num))
  have hU : IsOpen U := isOpen_lt (Metric.continuous_infDist_pt N.carrierSet) continuous_const
  refine ⟨hsub, hU, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    exact (tubularProjection_characterization q N).2.2.1 ⟨z.val, hsub z.property⟩
  · intro p
    have hp : p.val ∈ U := by
      change Metric.infDist p.val N.carrierSet < 2 * ρ
      rw [Metric.infDist_zero_of_mem p.property]
      exact mul_pos (by norm_num) hρ
    have hP : tubularProjection q N ⟨p.val, hsub hp⟩ = p := by
      obtain ⟨hpbase, hfixed⟩ := (tubularProjection_characterization q N).2.2.2.1 p
      exact hfixed
    exact ⟨hp, hP, (tubularProjectionDerivative_atTarget q N p (hsub hp)).1⟩
  · intro z
    obtain ⟨V, hV, hzV, hVbase, g, hg, hgP⟩ :=
      (tubularProjection_characterization q N).2.2.2.2.1 ⟨z.val, hsub z.property⟩
    refine ⟨V ∩ U, hV.inter hU, ⟨hzV, z.property⟩, inter_subset_right,
      g, hg.mono inter_subset_left, ?_⟩
    intro w hw
    exact hgP ⟨w.val, hsub w.property⟩ hw.1
  · intro z
    have hzrd : Metric.infDist z.val N.carrierSet < 2 * rd :=
      z.property.trans_le (mul_le_mul_of_nonneg_left hρrd (by norm_num))
    obtain ⟨hzbase, hnorm⟩ := hD z.val hzrd
    exact hnorm
  · have hSup := tubularProjectionSecondDerivative_targetNormSup q N
    obtain ⟨p, hp, hMax⟩ := hSup.2.2.2
    refine ⟨⟨‖tubularProjectionSecondDerivative q N ⟨p.val, hp⟩‖, p, hp, rfl⟩,
      hSup.1, hSup.2.1, hSup.2.2.1, Q, hQ, ?_, C₁, C₂, hC₁, hC₂, hQD, hQH⟩
    intro z hz
    exact hQP z (hz.trans_le hρre)

end HarmonicMaps.Providers.TubularProjection
end
