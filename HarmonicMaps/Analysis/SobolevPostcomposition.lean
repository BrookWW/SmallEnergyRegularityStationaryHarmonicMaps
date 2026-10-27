module

public import HarmonicMaps.Analysis.SobolevPostcompositionBasic
import HarmonicMaps.Analysis.SobolevSmoothDensity
import HarmonicMaps.Analysis.SobolevL2Closure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Weak target chain rule on Euclidean balls

Whole-ball smooth density, an almost-everywhere convergent subsequence and
dominated convergence identify the actual columns of the postcomposed map.
Closure of the weak Sobolev graph then gives finite W1,2 membership on every
positive-radius ball.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff

namespace HarmonicMaps

/-- The classical target chain rule in the displayed coordinate columns. -/
theorem coordinateDerivative_postcomposition {n q k : ℕ}
    {m : Domain n → Ambient q} (hm : ContDiff ℝ ∞ m)
    {F : Ambient q → Ambient k} (hF : ContDiff ℝ ∞ F) (i : Fin n) (x : Domain n) :
    coordinateDerivative (F ∘ m) (hF.comp hm) i x =
      fderiv ℝ F (m x) (coordinateDerivative m hm i x) := by
  simp only [coordinateDerivative,
    fderiv_comp x (hF.differentiable (by simp) (m x))
      (hm.differentiable (by simp) x), ContinuousLinearMap.comp_apply]

private theorem tendsto_postcomposition_column {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {q k : ℕ} {m v : ℕ → α → Ambient q} {u w : α → Ambient q}
    (hm : ∀ j, AEStronglyMeasurable (m j) μ) (hu : AEStronglyMeasurable u μ)
    (hv : ∀ j, MemLp (v j) 2 μ) (hw : MemLp w 2 μ)
    (hmae : ∀ᵐ x ∂μ, Tendsto (fun j => m j x) atTop (𝓝 (u x)))
    (hconv : Tendsto (fun j => eLpNorm (v j - w) 2 μ) atTop (𝓝 0))
    {F : Ambient q → Ambient k} (hF : ContDiff ℝ ∞ F)
    {L : ℝ} (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) :
    Tendsto (fun j => eLpNorm
      (fun x => fderiv ℝ F (m j x) (v j x) - fderiv ℝ F (u x) (w x)) 2 μ)
      atTop (𝓝 0) := by
  let A : ℕ → α → Ambient k := fun j x => fderiv ℝ F (m j x) (v j x - w x)
  let B : ℕ → α → Ambient k := fun j x =>
    (fderiv ℝ F (m j x) - fderiv ℝ F (u x)) (w x)
  have hA : ∀ j, MemLp (A j) 2 μ := fun j =>
    memLp_postcomposition_column (hm j) ((hv j).sub hw) hF hDF
  have hB : ∀ j, AEStronglyMeasurable (B j) μ := fun j =>
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((((hF.continuous_fderiv (by simp)).comp_aestronglyMeasurable (hm j)).sub
        ((hF.continuous_fderiv (by simp)).comp_aestronglyMeasurable hu)).prodMk
          hw.aestronglyMeasurable)
  have hbB : ∀ j, ∀ᵐ x ∂μ, ‖B j x‖ ≤ (2 * L) * ‖w x‖ := by
    intro j
    filter_upwards [] with x
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith only [hDF (m j x), hDF (u x)])
  have hlimB : Tendsto (fun j => eLpNorm (B j) 2 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_zero_of_dominated hB hw hbB
    filter_upwards [hmae] with x hx
    have hd := (hF.continuous_fderiv (by simp)).continuousAt.tendsto.comp hx
    have hzero : Tendsto (fun j => fderiv ℝ F (m j x) - fderiv ℝ F (u x))
        atTop (𝓝 0) := by
      simpa only [sub_self, Function.comp_def] using
        hd.sub (tendsto_const_nhds (x := fderiv ℝ F (u x)))
    have he := (ContinuousLinearMap.apply ℝ (Ambient k) (w x)).continuous.tendsto 0
      |>.comp hzero
    simpa only [B, Function.comp_def, ContinuousLinearMap.apply_apply,
      zero_apply] using he
  have hlimA : Tendsto (fun j => eLpNorm (A j) 2 μ) atTop (𝓝 0) := by
    have H := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal L) hconv
      (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using H) (fun _ => zero_le)
    intro j
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (p := 2)
    filter_upwards [] with x
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hDF (m j x)) (norm_nonneg _))
  have hsplit (j : ℕ) :
      (fun x => fderiv ℝ F (m j x) (v j x) - fderiv ℝ F (u x) (w x)) = A j + B j := by
    funext x
    simp only [A, B, Pi.add_apply, map_sub, sub_apply]
    abel
  have H := hlimA.add hlimB
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using H) (fun _ => zero_le)
  intro j
  dsimp only
  rw [hsplit]
  exact eLpNorm_add_le (hA j).aestronglyMeasurable (hB j) (by norm_num)

/-- Smooth target maps with globally bounded derivative preserve finite W1,2
on a positive-radius ball, with the actual weak chain-rule columns. -/
theorem MemW12.postcompose {n q k : ℕ} {a : Domain n} {R : ℝ} (hR : 0 < R)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du)
    (F : Ambient q → Ambient k) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hDF : ∀ z, ‖fderiv ℝ F z‖ ≤ L) :
    MemW12 (ballDomain a R) (F ∘ u)
      (fun x i => fderiv ℝ F (u x) (Du x i)) := by
  let μ := volume.restrict (ballDomain a R).val
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  obtain ⟨m, hm, hmW, hmconv, hDmconv⟩ := hu.smoothDensity_memW12_ball hR
  obtain ⟨s, hs, hsae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num :
    (2 : ℝ≥0∞) ≠ 0) (fun j => (hmW j).2.1.aestronglyMeasurable)
      hu.2.1.aestronglyMeasurable hmconv).exists_seq_tendsto_ae
  have hcomp (j : ℕ) : MemW12 (ballDomain a R) (F ∘ m (s j))
      (fun x i => fderiv ℝ F (m (s j) x)
        (coordinateDerivative (m (s j)) (hm (s j)) i x)) := by
    have hmap : MemLp (F ∘ m (s j)) 2 μ :=
      memLp_postcomposition (hmW (s j)).2.1 hF hDF
    have hcol (i : Fin n) : MemLp
        (coordinateDerivative (F ∘ m (s j)) (hF.comp (hm (s j))) i) 2 μ := by
      apply (memLp_postcomposition_column (hmW (s j)).2.1.aestronglyMeasurable
        ((hmW (s j)).2.2 i) hF hDF).ae_eq
      filter_upwards [] with x
      exact (coordinateDerivative_postcomposition (hm (s j)) hF i x).symm
    have H := memW12_of_contDiff (ballDomain a R) (hF.comp (hm (s j))) hmap hcol
    have heq : (fun x i => coordinateDerivative (F ∘ m (s j))
        (hF.comp (hm (s j))) i x) =
        (fun x i => fderiv ℝ F (m (s j) x)
          (coordinateDerivative (m (s j)) (hm (s j)) i x)) := by
      funext x i
      exact coordinateDerivative_postcomposition (hm (s j)) hF i x
    rw [heq] at H
    exact H
  apply MemW12.of_L2_limit_ball a R hcomp
    (memLp_postcomposition hu.2.1 hF hDF)
    (fun i => memLp_postcomposition_column hu.2.1.aestronglyMeasurable (hu.2.2 i) hF hDF)
  · have H := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal L) (hmconv.comp hs.tendsto_atTop)
      (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using H) (fun _ => zero_le)
    intro j
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (p := 2)
    filter_upwards [] with x
    exact postcomposition_norm_sub_le hF hDF _ _
  · intro i
    exact tendsto_postcomposition_column
      (fun j => (hmW (s j)).2.1.aestronglyMeasurable) hu.2.1.aestronglyMeasurable
      (fun j => (hmW (s j)).2.2 i) (hu.2.2 i) hsae
      ((hDmconv i).comp hs.tendsto_atTop) hF hDF

end HarmonicMaps
