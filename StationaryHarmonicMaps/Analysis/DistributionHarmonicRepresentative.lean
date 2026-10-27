module

public import StationaryHarmonicMaps.Analysis.DistributionHarmonicMollification
public import HarmonicMaps.Analysis.InteriorSobolevApproximation
import HolderToCK.Analysis.Harmonic.RadialMollifier
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Smooth representatives of distribution-harmonic L² fields

Actual harmonic interior mollifications reproduce under a fixed radial
kernel. Commutation of the two actual convolutions and L² approximation
identify a locally fixed smooth convolution with the original field almost
everywhere on the entire open domain.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology Convolution

namespace StationaryHarmonicMaps.Analysis

/-- Two actual smooth compact scalar kernels commute on integrable vector data. -/
theorem compact_kernelConvolution_commute {n q : ℕ}
    (u : Domain n → Ambient q) (hu : Integrable u volume)
    {χ ψ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (x : Domain n) :
    (∫ z, χ z • (∫ w, ψ w • u (x - z - w))) =
      ∫ z, ψ z • (∫ w, χ w • u (x - z - w)) := by
  let M := ContinuousLinearMap.mul ℝ ℝ
  let S := ContinuousLinearMap.lsmul ℝ ℝ (E := Ambient q)
  have hassoc {f g : Domain n → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
      (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) :
      (f ⋆[M, volume] g) ⋆[S, volume] u = f ⋆[S, volume] (g ⋆[S, volume] u) := by
    have hgI : Integrable g volume := hg.continuous.integrable_of_hasCompactSupport hcg
    have hnormI : Integrable ((fun y => ‖g y‖) ⋆[M, volume] fun y => ‖u y‖) volume :=
      hgI.norm.integrable_convolution M hu.norm
    funext y
    apply convolution_assoc M S S S (fun a b c => by exact mul_smul a b c)
      hf.continuous.aestronglyMeasurable hg.continuous.aestronglyMeasurable hu.aestronglyMeasurable
    · exact Eventually.of_forall (hcf.convolutionExists_left M hf.continuous hgI.locallyIntegrable)
    · exact Eventually.of_forall (hcg.norm.convolutionExists_left M hg.continuous.norm hu.norm.locallyIntegrable)
    · exact hcf.norm.convolutionExists_left M hf.continuous.norm hnormI.locallyIntegrable y
  have hflip : M.flip = M := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact mul_comm b a
  have hcomm : χ ⋆[M, volume] ψ = ψ ⋆[M, volume] χ := by
    rw [← convolution_flip, hflip]
  have H : χ ⋆[S, volume] (ψ ⋆[S, volume] u) = ψ ⋆[S, volume] (χ ⋆[S, volume] u) := by
    rw [← hassoc hχ hcχ hψ hcψ, hcomm, hassoc hψ hcψ hχ hcχ]
  exact congrFun H x

private theorem scaled_kernelConvolution_tendsto {n q : ℕ}
    (v : Domain n → Ambient q) (hv : Continuous v)
    (ε : ℕ → PositiveRadius) (hε : Tendsto (fun k => (ε k).val) atTop (𝓝 (0 : ℝ)))
    (x : Domain n) :
    Tendsto (fun k => ∫ z, scaledMollifierKernel n (ε k) z • v (x - z))
      atTop (𝓝 (v x)) := by
  have hsupport : Tendsto (fun k => Function.support (scaledMollifierKernel n (ε k)))
      atTop (𝓝 (0 : Domain n)).smallSets := by
    rw [tendsto_smallSets_iff]
    intro U hU
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
    filter_upwards [hε.eventually (gt_mem_nhds hδ)] with k hk
    intro z hz
    apply hδU
    have hnorm : ‖z‖ ≤ (ε k).val / 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        scaledMollifierKernel_tsupport_subset_halfBall n (ε k) (subset_tsupport _ hz)
    change dist z 0 < δ
    rw [dist_zero_right]
    linarith only [hnorm, hk, (ε k).property]
  exact convolution_tendsto_right
    (Eventually.of_forall fun k => scaledMollifierKernel_nonneg n (ε k))
    (Eventually.of_forall fun k => HolderToCK.scaledMollifierKernel_integral_one n (ε k)) hsupport
    (Eventually.of_forall fun _ => hv.aestronglyMeasurable)
    (hv.continuousAt.tendsto.comp tendsto_snd) tendsto_const_nhds

private theorem harmonic_mollification_fixed_kernel_identity {n q : ℕ} (hn : 2 ≤ n)
    (Ω : OpenDomain n) (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val volume)
    (hharm : ∀ (η : Domain n → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ω.val → (∫ z in Ω.val, Laplacian.laplacian η z • u z) = 0)
    (a : Domain n) {R : ℝ} (hR : 0 < R) (hball : Metric.ball a R ⊆ Ω.val)
    (ε : PositiveRadius) (hε : ε.val ≤ R / 4) (y : Domain n) (hy : y ∈ Metric.ball a (R / 8)) :
    let τ : PositiveRadius := ⟨R / 8, div_pos hR (by norm_num)⟩
    let m := fun (h : PositiveRadius) (x : Domain n) =>
      ∫ z, scaledMollifierKernel n h z • zeroExtensionOn Ω u (x - z)
    m ε y = ∫ z, scaledMollifierKernel n ε z • m τ (y - z) := by
  intro τ m
  have hm : ContDiff ℝ ∞ (m ε) :=
    kernelConvolution_contDiff Ω u hu (scaledMollifierKernel_contDiff n ε)
      (scaledMollifierKernel_hasCompactSupport n ε)
  have hHarm (x : Domain n) (hx : x ∈ Metric.ball a (R / 2)) :
      Laplacian.laplacian (m ε) x = 0 := by
    apply distribution_harmonic_kernelConvolution Ω u hu hharm
      (scaledMollifierKernel_contDiff n ε) (scaledMollifierKernel_hasCompactSupport n ε) x
    intro z hz
    apply hball
    have hnorm : ‖z‖ ≤ ε.val / 2 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        scaledMollifierKernel_tsupport_subset_halfBall n ε hz
    have hx' : dist x a < R / 2 := hx
    have hdist : dist (x - z) x = ‖z‖ := by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
    exact lt_of_le_of_lt (dist_triangle (x - z) x a)
      (by rw [hdist]; linarith only [hnorm, hx', hε, hR])
  have hclosed : Metric.closedBall y τ.val ⊆ Metric.ball a (R / 2) := by
    intro z hz
    have hzy : dist z y ≤ R / 8 := hz
    have hya : dist y a < R / 8 := hy
    exact lt_of_le_of_lt (dist_triangle z y a) (by linarith only [hzy, hya, hR])
  have H := HolderToCK.harmonic_scaledMollifier_integral_eq hn y τ
    (Metric.ball a (R / 2)) Metric.isOpen_ball hclosed (m ε) hm.contDiffOn hHarm
  calc
    m ε y = ∫ z, scaledMollifierKernel n τ z • m ε (y - z) := H.symm
    _ = _ := compact_kernelConvolution_commute (zeroExtensionOn Ω u)
      (zeroExtensionOn_integrable Ω u hu)
      (scaledMollifierKernel_contDiff n τ) (scaledMollifierKernel_hasCompactSupport n τ)
      (scaledMollifierKernel_contDiff n ε) (scaledMollifierKernel_hasCompactSupport n ε) y

/-- Actual integrable L² distribution-harmonic data have a smooth a.e. representative on the open domain. -/
theorem exists_smooth_representative_of_distribution_harmonic_L2 {n q : ℕ} (hn : 2 ≤ n)
    (Ω : OpenDomain n) (u : Domain n → Ambient q)
    (hI : IntegrableOn u Ω.val volume) (hL2 : MemLp u 2 (volume.restrict Ω.val))
    (hharm : ∀ (η : Domain n → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Ω.val → (∫ z in Ω.val, Laplacian.laplacian η z • u z) = 0) :
    ∃ v : Domain n → Ambient q, ContDiffOn ℝ ∞ v Ω.val ∧
      v =ᵐ[volume.restrict Ω.val] u ∧
      ∀ x ∈ Ω.val, Laplacian.laplacian v x = 0 := by
  let ε : ℕ → PositiveRadius := fun k => ⟨1 / ((k : ℝ) + 1), by positivity⟩
  have hε : Tendsto (fun k => (ε k).val) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let m := fun (h : PositiveRadius) (x : Domain n) =>
    ∫ z, scaledMollifierKernel n h z • zeroExtensionOn Ω u (x - z)
  have hm (h : PositiveRadius) : ContDiff ℝ ∞ (m h) :=
    kernelConvolution_contDiff Ω u hI (scaledMollifierKernel_contDiff n h)
      (scaledMollifierKernel_hasCompactSupport n h)
  have hlocal (a : Domain n) {R : ℝ} (hR : 0 < R) (hball : Metric.ball a R ⊆ Ω.val) :
      let τ : PositiveRadius := ⟨R / 8, div_pos hR (by norm_num)⟩
      ∀ y ∈ Metric.ball a (R / 8), Tendsto (fun k => m (ε k) y) atTop (𝓝 (m τ y)) := by
    intro τ y hy
    have H := scaled_kernelConvolution_tendsto (m τ) (hm τ).continuous ε hε y
    apply H.congr'
    filter_upwards [hε.eventually (gt_mem_nhds (div_pos hR (by norm_num : (0 : ℝ) < 4)))] with k hk
    exact (harmonic_mollification_fixed_kernel_identity hn Ω u hI hharm a hR hball (ε k) hk.le y hy).symm
  let v := fun x => limUnder atTop (fun k => m (ε k) x)
  have hveq (a : Domain n) {R : ℝ} (hR : 0 < R) (hball : Metric.ball a R ⊆ Ω.val) :
      let τ : PositiveRadius := ⟨R / 8, div_pos hR (by norm_num)⟩
      EqOn v (m τ) (Metric.ball a (R / 8)) := by
    intro τ y hy
    exact (hlocal a hR hball y hy).limUnder_eq
  have hpoint (x : Domain n) (hx : x ∈ Ω.val) :
      ContDiffAt ℝ ∞ v x ∧ Laplacian.laplacian v x = 0 ∧
      Tendsto (fun k => m (ε k) x) atTop (𝓝 (v x)) := by
    obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (Ω.property.mem_nhds hx)
    let τ : PositiveRadius := ⟨R / 8, div_pos hR (by norm_num)⟩
    have hEq := hveq x hR hball
    have hxinner : x ∈ Metric.ball x (R / 8) := Metric.mem_ball_self (div_pos hR (by norm_num))
    have hEqnhds : v =ᶠ[𝓝 x] m τ := Filter.eventuallyEq_of_mem
      (Metric.isOpen_ball.mem_nhds hxinner) hEq
    refine ⟨(hm τ).contDiffAt.congr_of_eventuallyEq hEqnhds, ?_, ?_⟩
    · rw [(InnerProductSpace.laplacian_congr_nhds hEqnhds).self_of_nhds]
      apply distribution_harmonic_kernelConvolution Ω u hI hharm
        (scaledMollifierKernel_contDiff n τ) (scaledMollifierKernel_hasCompactSupport n τ) x
      intro z hz
      apply hball
      have hnorm : ‖z‖ ≤ τ.val / 2 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          scaledMollifierKernel_tsupport_subset_halfBall n τ hz
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
      change ‖z‖ < R
      dsimp only [τ] at hnorm
      linarith only [hnorm, hR]
    · rw [hEq hxinner]
      exact hlocal x hR hball x hxinner
  have hnorm : Tendsto (fun k => eLpNorm (m (ε k) - u) 2 (volume.restrict Ω.val)) atTop (𝓝 0) := by
    have H := tendsto_eLpNorm_euclideanMollification_sub Ω u hI hL2 Ω.property.measurableSet (Subset.refl _)
    have hs : Tendsto ε atTop (comap (fun h : PositiveRadius => h.val) (𝓝 (0 : ℝ))) :=
      tendsto_comap_iff.mpr hε
    exact H.comp hs
  have hmeasure : TendstoInMeasure (volume.restrict Ω.val) (fun k => m (ε k)) atTop u :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (fun k => (hm (ε k)).continuous.aestronglyMeasurable)
      hL2.aestronglyMeasurable hnorm
  obtain ⟨s, hs, hseq⟩ := hmeasure.exists_seq_tendsto_ae
  refine ⟨v, fun x hx => (hpoint x hx).1.contDiffWithinAt, ?_, fun x hx => (hpoint x hx).2.1⟩
  filter_upwards [hseq, ae_restrict_mem Ω.property.measurableSet] with x hseqx hx
  exact tendsto_nhds_unique (((hpoint x hx).2.2).comp hs.tendsto_atTop) hseqx

/-- Actual ball L² data alone supply the integrability needed for the distributional Weyl lemma. -/
theorem memLp_two_distribution_harmonic_smooth_representative_ball {n q : ℕ} (hn : 2 ≤ n)
    (a : Domain n) (R : ℝ) (u : Domain n → Ambient q)
    (hu : MemLp u 2 (volume.restrict (Metric.ball a R)))
    (hharm : ∀ (η : Domain n → ℝ), ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ Metric.ball a R →
        (∫ z in Metric.ball a R, Laplacian.laplacian η z • u z) = 0) :
    ∃ v : Domain n → Ambient q, ContDiffOn ℝ ∞ v (Metric.ball a R) ∧
      v =ᵐ[volume.restrict (Metric.ball a R)] u ∧
      ∀ x ∈ Metric.ball a R, Laplacian.laplacian v x = 0 := by
  have hI : IntegrableOn u (Metric.ball a R) volume := by
    letI : IsFiniteMeasure (volume.restrict (Metric.ball a R)) :=
      isFiniteMeasure_restrict.mpr measure_ball_ne_top
    exact hu.integrable (by norm_num)
  exact exists_smooth_representative_of_distribution_harmonic_L2 hn (ballDomain a R) u hI hu hharm

end StationaryHarmonicMaps.Analysis

end
