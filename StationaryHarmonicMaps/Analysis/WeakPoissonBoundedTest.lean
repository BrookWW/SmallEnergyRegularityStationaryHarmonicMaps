module

public import StationaryHarmonicMaps.Analysis.BoundedSobolevTestApproximation
public import HolderToCK.Foundation.WeakPoisson
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded Sobolev tests for an L¹ Poisson forcing

The actual bounded smooth zero-boundary approximation controls the L¹
forcing pairing by dominated convergence. Strong L² convergence of its
actual gradient columns controls the left pairing. No bounded-density
hypothesis is added to the Poisson equation.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem inner_integrable_of_memLp_two {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

private theorem integral_inner_eq_inner_toLp {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, inner ℝ (f x) (g x) ∂μ) = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

private theorem tendsto_integral_inner_of_l2 {n q : ℕ} {μ : Measure (Domain n)}
    {f : ℕ → Domain n → Ambient q} {u g : Domain n → Ambient q}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, inner ℝ (g x) (f k x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (g x) (u x) ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hlim
  have hconst : Tendsto (fun _ : ℕ => hg.toLp g) atTop (𝓝 (hg.toLp g)) :=
    tendsto_const_nhds
  have hinner := hconst.inner (𝕜 := ℝ) hLp
  simp_rw [integral_inner_eq_inner_toLp hg (hf _), integral_inner_eq_inner_toLp hg hu]
  exact hinner

/-- An L¹ Poisson forcing admits every actual essentially bounded W₀¹,² test. -/
theorem weakPoissonOn_bounded_zeroBoundary_test {n q : ℕ}
    {Ω : OpenDomain n} {Du : Domain n → Gradient n q} {F : Domain n → Ambient q}
    (hpoisson : HolderToCK.WeakPoissonOn Ω Du F)
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 (volume.restrict Ω.val))
    (hF : IntegrableOn F Ω.val volume)
    {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : HasZeroBoundaryValues Ω w Dw) {M : ℝ}
    (hb : ∀ᵐ x ∂volume.restrict Ω.val, ‖w x‖ ≤ M) :
    IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (Du x i) (Dw x i)) Ω.val volume ∧
    IntegrableOn (fun x => inner ℝ (F x) (w x)) Ω.val volume ∧
    (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (Du x i) (Dw x i)) =
      -(∫ x in Ω.val, inner ℝ (F x) (w x)) := by
  let μ := volume.restrict Ω.val
  obtain ⟨C, ψ, hC, hψ, hcψ, hbound, haelim, _hmaplim, hgradlim⟩ :=
    exists_bounded_smooth_zeroBoundary_approximation Ω hw hb
  have hDψ (j : ℕ) (i : Fin n) :
      MemLp (fun x => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) 2 μ :=
    ((hψ j).continuous_fderiv (by simp) |>.clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hcψ j).1.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hleft (i : Fin n) : Integrable (fun x => inner ℝ (Du x i) (Dw x i)) μ :=
    inner_integrable_of_memLp_two (hDu i) (hw.1.2.2 i)
  have hright : Integrable (fun x => inner ℝ (F x) (w x)) μ := by
    apply (hF.norm.mul_const M).mono'
      (hF.aestronglyMeasurable.inner hw.1.2.1.aestronglyMeasurable)
    filter_upwards [hb] with x hx
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hleftlim : Tendsto (fun j => ∑ i : Fin n,
      ∫ x, inner ℝ (Du x i) (fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) ∂μ) atTop
      (𝓝 (∑ i : Fin n, ∫ x, inner ℝ (Du x i) (Dw x i) ∂μ)) :=
    tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_integral_inner_of_l2 (fun j => hDψ j i) (hw.1.2.2 i) (hDu i) (hgradlim i))
  have hrightlim : Tendsto (fun j => ∫ x, inner ℝ (F x) (ψ j x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (F x) (w x) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖F x‖ * C)
      (fun j => hF.aestronglyMeasurable.inner (hψ j).continuous.aestronglyMeasurable)
      (hF.norm.mul_const C)
    · intro j
      exact Eventually.of_forall (fun x => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hbound j x) (norm_nonneg _)))
    · filter_upwards [haelim] with x hx
      exact tendsto_const_nhds.inner (𝕜 := ℝ) hx
  have hseq (j : ℕ) : (∑ i : Fin n,
      ∫ x, inner ℝ (Du x i) (fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) ∂μ) =
      -(∫ x, inner ℝ (F x) (ψ j x) ∂μ) := by
    rw [← integral_finsetSum _ (fun i _ => inner_integrable_of_memLp_two (hDu i) (hDψ j i))]
    exact (hpoisson.2 (ψ j) (hψ j) (hcψ j).1 (hcψ j).2).2.2
  refine ⟨integrable_finsetSum _ (fun i _ => hleft i), hright, ?_⟩
  rw [integral_finsetSum _ (fun i _ => hleft i)]
  exact tendsto_nhds_unique hleftlim (hrightlim.neg.congr'
    (Eventually.of_forall fun j => (hseq j).symm))

end StationaryHarmonicMaps.Analysis

end
