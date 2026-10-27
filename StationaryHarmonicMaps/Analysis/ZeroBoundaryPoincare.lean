module

public import StationaryHarmonicMaps.Analysis.SupportedPoincare
public import HarmonicMaps.Analysis.SobolevDifference
import HolderToCK.Analysis.L2PairingContinuity
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Coercive Poincaré on the native zero-boundary Sobolev space

The actual compact smooth graph approximation transfers the coercive
estimate with its unchanged constant. Zero gradient energy then forces
the map to vanish almost everywhere inside the ball.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Squared norm integrals are continuous under actual L² convergence. -/
theorem tendsto_integral_norm_sq_of_L2 {n q : ℕ} {μ : Measure (Domain n)}
    {f : ℕ → Domain n → Ambient q} {u : Domain n → Ambient q}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖f k x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x, ‖u x‖ ^ 2 ∂μ)) := by
  have hnorm (g : Domain n → Ambient q) (hg : MemLp g 2 μ) :
      (∫ x, ‖g x‖ ^ 2 ∂μ) = ‖hg.toLp g‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa only [real_inner_self_eq_norm_sq] using HolderToCK.integral_inner_eq_L2_inner hg hg
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hconv
  simpa only [← hnorm] using hLp.norm.pow 2

/-- The actual HS energy integral is continuous under columnwise L² convergence. -/
theorem tendsto_integral_hsNormSq_of_columns_L2 {n q : ℕ}
    {μ : Measure (Domain n)} {D : ℕ → Domain n → Gradient n q}
    {Du : Domain n → Gradient n q}
    (hD : ∀ k (i : Fin n), MemLp (fun x => D k x i) 2 μ)
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 μ)
    (hconv : ∀ i : Fin n, Tendsto
      (fun k => eLpNorm (fun x => D k x i - Du x i) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, hsNormSq (D k x) ∂μ) atTop
      (𝓝 (∫ x, hsNormSq (Du x) ∂μ)) := by
  have hsum := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_integral_norm_sq_of_L2 (fun k => hD k i) (hDu i) (hconv i))
  have hEq (k : ℕ) : (∫ x, hsNormSq (D k x) ∂μ) =
      ∑ i : Fin n, ∫ x, ‖D k x i‖ ^ 2 ∂μ :=
    integral_finsetSum _ (fun i _ => (hD k i).integrable_norm_pow (by decide))
  have hEqU : (∫ x, hsNormSq (Du x) ∂μ) =
      ∑ i : Fin n, ∫ x, ‖Du x i‖ ^ 2 ∂μ :=
    integral_finsetSum _ (fun i _ => (hDu i).integrable_norm_pow (by decide))
  simpa only [hEq, hEqU] using hsum

/-- Every native W₀¹,² map satisfies the actual compact-test coercive estimate. -/
theorem zeroBoundary_poincare {n q : ℕ} (hn : 1 ≤ n)
    (a : Domain n) {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : HasZeroBoundaryValues (ballDomain a R) u Du) :
    (∫ x in Metric.ball a R, ‖u x‖ ^ 2) ≤
      (24 * (2 : ℝ) ^ (n + 1)) * R ^ 2 *
        ∫ x in Metric.ball a R, hsNormSq (Du x) := by
  obtain ⟨hW, f, hf, hc, hlim, hDlim⟩ := hu
  let μ := volume.restrict (Metric.ball a R)
  have hmap (k : ℕ) : MemLp (f k) 2 μ :=
    (hf k).continuous.memLp_of_hasCompactSupport (hc k).1
  have hD (k : ℕ) (i : Fin n) : MemLp (coordinateDerivative (f k) (hf k) i) 2 μ :=
    ((hf k).continuous_fderiv (by simp) |>.clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hc k).1.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hleft := tendsto_integral_norm_sq_of_L2 hmap hW.2.1 hlim
  have hright := tendsto_integral_hsNormSq_of_columns_L2 hD hW.2.2 hDlim
  exact le_of_tendsto_of_tendsto hleft
    (hright.const_mul ((24 * (2 : ℝ) ^ (n + 1)) * R ^ 2))
    (Eventually.of_forall fun k => compactSmooth_zeroBoundary_poincare hn a hR
      (f k) (hf k) (hc k).1 (hc k).2)

/-- Zero gradient energy forces a native zero-boundary map to vanish inside the ball. -/
theorem zeroBoundary_ae_eq_zero_of_energy_eq_zero {n q : ℕ} (hn : 1 ≤ n)
    (a : Domain n) {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : HasZeroBoundaryValues (ballDomain a R) u Du)
    (henergy : (∫ x in Metric.ball a R, hsNormSq (Du x)) = 0) :
    u =ᵐ[volume.restrict (Metric.ball a R)] 0 := by
  have hb := zeroBoundary_poincare hn a hR hu
  rw [henergy, mul_zero] at hb
  have hnorm : (∫ x in Metric.ball a R, ‖u x‖ ^ 2) = 0 :=
    le_antisymm hb (integral_nonneg fun x => sq_nonneg ‖u x‖)
  have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖u x‖)
    (hu.1.2.1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))).mp hnorm
  filter_upwards [hz] with x hx
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- Subtracting two native zero-boundary maps retains an actual compact smooth graph approximation. -/
theorem zeroBoundary_sub {n q : ℕ} {Ω : OpenDomain n}
    {u v : Domain n → Ambient q} {Du Dv : Domain n → Gradient n q}
    (hu : HasZeroBoundaryValues Ω u Du) (hv : HasZeroBoundaryValues Ω v Dv) :
    HasZeroBoundaryValues Ω (u - v) (fun x i => Du x i - Dv x i) := by
  obtain ⟨huW, f, hf, hc, hlim, hDlim⟩ := hu
  obtain ⟨hvW, g, hg, hd, hlim', hDlim'⟩ := hv
  let μ := volume.restrict Ω.val
  have hs (k : ℕ) : ContDiff ℝ ∞ (f k - g k) := (hf k).sub (hg k)
  refine ⟨huW.sub hvW, (fun k => f k - g k), hs, ?_, ?_, ?_⟩
  · intro k
    exact ⟨(hc k).1.sub (hd k).1,
      (tsupport_sub _ _).trans (union_subset (hc k).2 (hd k).2)⟩
  · have hsum : Tendsto (fun k => eLpNorm (f k - u) 2 μ + eLpNorm (g k - v) 2 μ)
        atTop (𝓝 0) := by simpa only [add_zero] using hlim.add hlim'
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le)
    intro k
    have heq : f k - g k - (u - v) = (f k - u) - (g k - v) := by
      funext x
      simp only [Pi.sub_apply]
      abel_nf
    dsimp only
    rw [heq]
    exact eLpNorm_sub_le
      ((hf k).continuous.aestronglyMeasurable.sub huW.2.1.aestronglyMeasurable)
      ((hg k).continuous.aestronglyMeasurable.sub hvW.2.1.aestronglyMeasurable) (by norm_num)
  · intro i
    have hsum : Tendsto (fun k =>
        eLpNorm (fun x => coordinateDerivative (f k) (hf k) i x - Du x i) 2 μ +
        eLpNorm (fun x => coordinateDerivative (g k) (hg k) i x - Dv x i) 2 μ)
        atTop (𝓝 0) := by simpa only [add_zero] using (hDlim i).add (hDlim' i)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le)
    intro k
    have heq : (fun x => coordinateDerivative (f k - g k) (hs k) i x -
        (Du x i - Dv x i)) =
        (fun x => coordinateDerivative (f k) (hf k) i x - Du x i) -
        (fun x => coordinateDerivative (g k) (hg k) i x - Dv x i) := by
      funext x
      simp only [coordinateDerivative, fderiv_sub ((hf k).differentiable (by simp) x)
        ((hg k).differentiable (by simp) x), sub_apply, Pi.sub_apply]
      abel_nf
    dsimp only
    rw [heq]
    exact eLpNorm_sub_le
      (((hf k).continuous_fderiv (by simp) |>.clm_apply continuous_const).aestronglyMeasurable.sub
        (huW.2.2 i).aestronglyMeasurable)
      (((hg k).continuous_fderiv (by simp) |>.clm_apply continuous_const).aestronglyMeasurable.sub
        (hvW.2.2 i).aestronglyMeasurable) (by norm_num)

end StationaryHarmonicMaps.Analysis

end
