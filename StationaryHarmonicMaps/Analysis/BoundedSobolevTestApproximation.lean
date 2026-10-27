module

public import StationaryHarmonicMaps.Analysis.PostcompositionColumnLimit
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Bounded smooth approximation of bounded zero-boundary Sobolev maps

A smooth compact target cutoff fixes a neighborhood of the essential range.
Composing the genuine zero-boundary density sequence with that cutoff gives
uniformly bounded compact smooth tests. A subsequence converges almost
everywhere and the actual derivative columns converge strongly in L².
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- A compact smooth target map fixes the prescribed ball and has bounded derivative. -/
theorem exists_smooth_bounded_identity {q : ℕ} (M : ℝ) :
    ∃ (H : Ambient q → Ambient q) (C L : ℝ),
      ContDiff ℝ ∞ H ∧ H 0 = 0 ∧ 0 ≤ C ∧ 0 ≤ L ∧
      (∀ y, ‖H y‖ ≤ C) ∧ (∀ y, ‖fderiv ℝ H y‖ ≤ L) ∧
      ∀ y, ‖y‖ < |M| + 1 →
        H y = y ∧ fderiv ℝ H y = ContinuousLinearMap.id ℝ (Ambient q) := by
  let χ : ContDiffBump (0 : Ambient q) :=
    { rIn := |M| + 1, rOut := |M| + 2,
      rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  let H : Ambient q → Ambient q := fun y => χ y • y
  have hH : ContDiff ℝ ∞ H := χ.contDiff.smul contDiff_id
  have hcH : HasCompactSupport H := χ.hasCompactSupport.smul_right
  obtain ⟨C, hC⟩ := hcH.exists_bound_of_continuous hH.continuous
  obtain ⟨L, hL⟩ := (hcH.fderiv ℝ).exists_bound_of_continuous
    (hH.continuous_fderiv (by simp))
  refine ⟨H, C, L, hH, by simp [H], (norm_nonneg _).trans (hC 0),
    (norm_nonneg _).trans (hL 0), hC, hL, ?_⟩
  intro y hy
  have hball : y ∈ Metric.ball (0 : Ambient q) χ.rIn := by
    simpa only [Metric.mem_ball, dist_zero_right] using hy
  have heq : H =ᶠ[𝓝 y] id :=
    (χ.eventuallyEq_one_of_mem_ball hball).mono (fun z hz => by
      change χ z = (1 : ℝ) at hz
      change χ z • z = z
      rw [hz, one_smul])
  exact ⟨heq.eq_of_nhds, heq.fderiv_eq.trans fderiv_id⟩

/-- Bounded W₀¹,² maps admit actual uniformly bounded smooth compact approximations. -/
theorem exists_bounded_smooth_zeroBoundary_approximation {n q : ℕ}
    (Ω : OpenDomain n) {w : Domain n → Ambient q} {Dw : Domain n → Gradient n q}
    (hw : HasZeroBoundaryValues Ω w Dw) {M : ℝ}
    (hb : ∀ᵐ x ∂volume.restrict Ω.val, ‖w x‖ ≤ M) :
    ∃ (C : ℝ) (ψ : ℕ → Domain n → Ambient q), 0 ≤ C ∧
      (∀ j, ContDiff ℝ ∞ (ψ j)) ∧
      (∀ j, HasCompactSupport (ψ j) ∧ tsupport (ψ j) ⊆ Ω.val) ∧
      (∀ j x, ‖ψ j x‖ ≤ C) ∧
      (∀ᵐ x ∂volume.restrict Ω.val, Tendsto (fun j => ψ j x) atTop (𝓝 (w x))) ∧
      Tendsto (fun j => eLpNorm (ψ j - w) 2 (volume.restrict Ω.val)) atTop (𝓝 0) ∧
      ∀ i : Fin n, Tendsto (fun j => eLpNorm
        (fun x => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1) - Dw x i)
        2 (volume.restrict Ω.val)) atTop (𝓝 0) := by
  obtain ⟨m, hm, hmc, hmconv, hDmconv⟩ := hw.2
  let μ := volume.restrict Ω.val
  have hmL (j : ℕ) : MemLp (m j) 2 μ :=
    (hm j).continuous.memLp_of_hasCompactSupport (hmc j).1
  have hDmL (j : ℕ) (i : Fin n) :
      MemLp (coordinateDerivative (m j) (hm j) i) 2 μ :=
    ((hm j).continuous_fderiv (by simp) |>.clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hmc j).1.fderiv_apply ℝ (EuclideanSpace.single i 1))
  obtain ⟨s, hs, hsae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num :
    (2 : ℝ≥0∞) ≠ 0) (fun j => (hmL j).aestronglyMeasurable)
      hw.1.2.1.aestronglyMeasurable hmconv).exists_seq_tendsto_ae
  obtain ⟨H, C, L, hH, hH0, hC, hL, hbound, hDH, hfix⟩ :=
    exists_smooth_bounded_identity (q := q) M
  let ψ (j : ℕ) := H ∘ m (s j)
  have hψ (j : ℕ) : ContDiff ℝ ∞ (ψ j) := hH.comp (hm (s j))
  have hψc (j : ℕ) : HasCompactSupport (ψ j) := (hmc (s j)).1.comp_left hH0
  have hψs (j : ℕ) : tsupport (ψ j) ⊆ Ω.val := by
    apply Subset.trans _ (hmc (s j)).2
    apply closure_mono
    intro x hx hz
    exact hx (by change H (m (s j) x) = 0; rw [hz, hH0])
  have hfixw : ∀ᵐ x ∂μ,
      H (w x) = w x ∧ fderiv ℝ H (w x) = ContinuousLinearMap.id ℝ (Ambient q) := by
    filter_upwards [hb] with x hx
    exact hfix (w x) (lt_of_le_of_lt (hx.trans (le_abs_self M)) (lt_add_one _))
  have hmaplim : Tendsto (fun j => eLpNorm (ψ j - w) 2 μ) atTop (𝓝 0) := by
    have Hlim := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal L)
      (hmconv.comp hs.tendsto_atTop) (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using Hlim) (fun _ => zero_le)
    intro j
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (p := 2)
    filter_upwards [hfixw] with x hx
    change ‖H (m (s j) x) - w x‖ ≤ L * ‖m (s j) x - w x‖
    calc
      ‖H (m (s j) x) - w x‖ = ‖H (m (s j) x) - H (w x)‖ := by rw [hx.1]
      _ ≤ _ := postcomposition_norm_sub_le hH hDH _ _
  have hgradlim (i : Fin n) : Tendsto (fun j => eLpNorm
      (fun x => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1) - Dw x i) 2 μ)
      atTop (𝓝 0) := by
    have Hlim := tendsto_postcomposition_column_l2
      (fun j => (hmL (s j)).aestronglyMeasurable) hw.1.2.1.aestronglyMeasurable
      (fun j => hDmL (s j) i) (hw.1.2.2 i) hsae
      ((hDmconv i).comp hs.tendsto_atTop) (hH.of_le (by simp)) hDH
    have heq (j : ℕ) :
        (fun x => fderiv ℝ H (m (s j) x)
          (coordinateDerivative (m (s j)) (hm (s j)) i x) -
            fderiv ℝ H (w x) (Dw x i)) =ᵐ[μ]
        (fun x => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1) - Dw x i) := by
      filter_upwards [hfixw] with x hx
      rw [hx.2, ContinuousLinearMap.id_apply]
      congr 1
      simp only [ψ, fderiv_comp x (hH.differentiable (by simp) _)
        ((hm (s j)).differentiable (by simp) x),
        ContinuousLinearMap.comp_apply, coordinateDerivative]
    exact Hlim.congr (fun j => eLpNorm_congr_ae (heq j))
  refine ⟨C, ψ, hC, hψ, fun j => ⟨hψc j, hψs j⟩,
    (fun j x => hbound (m (s j) x)), ?_, hmaplim, hgradlim⟩
  filter_upwards [hsae, hfixw] with x hx hfixx
  have Hlim : Tendsto (fun j => H (m (s j) x)) atTop (𝓝 (H (w x))) :=
    hH.continuous.continuousAt.tendsto.comp hx
  rw [hfixx.1] at Hlim
  exact Hlim

end StationaryHarmonicMaps.Analysis

end
