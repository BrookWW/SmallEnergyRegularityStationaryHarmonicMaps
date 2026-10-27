module

public import HolderToCK.Analysis.HolderMollificationDerivative
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # The classical derivative of the same Holder Sobolev map

The actual mollifications and their full derivatives converge uniformly on
each inner ball. Uniform limits of derivatives identify the original function's
Fréchet derivative with the linear map carrying its displayed weak columns.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology

namespace HolderToCK

theorem holder_weakGradient_hasFDerivAt {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (hΩ : volume Ω.val ≠ ⊤)
    {α β H H₁ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hH : 0 ≤ H) (hH₁ : 0 ≤ H₁)
    (hHolder : HolderBoundOn Ω.val u α H)
    (hGradientHolder : ∀ i : Fin n, HolderBoundOn Ω.val (fun x => Du x i) β H₁)
    {x : Domain n} (hx : x ∈ Ω.val) :
    HasFDerivAt u
      (∑ i : Fin n, (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).smulRight (Du x i)) x := by
  obtain ⟨ρ, hρ, hBall⟩ := Metric.mem_nhds_iff.mp (Ω.property.mem_nhds hx)
  let W := Metric.ball x (ρ / 4)
  have hMargin : ∀ y ∈ W, Metric.ball y (ρ / 2) ⊆ Ω.val := by
    intro y hy z hz
    apply hBall
    have hyx : dist y x < ρ / 4 := hy
    have hzy : dist z y < ρ / 2 := hz
    change dist z x < ρ
    exact lt_of_le_of_lt (dist_triangle z y x) (by linarith only [hyx, hzy, hρ])
  let h : ℕ → PositiveRadius := fun k => ⟨1 / ((k : ℝ) + 1), by positivity⟩
  have hh : Tendsto (fun k => (h k).val) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hValue := euclideanMollification_tendstoUniformlyOn_of_holder Ω u
    (hu.integrable_domain hΩ) hα hH hHolder W (half_pos hρ) hMargin h hh
  have hDerivative := MemW12.holderMollification_fderiv_tendstoUniformlyOn Ω hu hΩ
    hβ hH₁ hGradientHolder W (half_pos hρ) hMargin h hh
  apply hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hDerivative
  · intro k y _
    have hm := euclideanMollification_contDiff Ω u (hu.integrable_domain hΩ) (h k)
    exact (hm.differentiable (by simp)).differentiableAt.hasFDerivAt
  · intro y hy
    exact hValue.tendsto_at hy
  · exact Metric.mem_ball_self (by positivity : 0 < ρ / 4)

theorem holder_weakGradient_contDiffOn_one {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (hΩ : volume Ω.val ≠ ⊤)
    {α β H H₁ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hH : 0 ≤ H) (hH₁ : 0 ≤ H₁)
    (hHolder : HolderBoundOn Ω.val u α H)
    (hGradientHolder : ∀ i : Fin n, HolderBoundOn Ω.val (fun x => Du x i) β H₁) :
    ContDiffOn ℝ 1 u Ω.val ∧
    ∀ x ∈ Ω.val, fderiv ℝ u x =
      ∑ i : Fin n, (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).smulRight (Du x i) := by
  have hDerivative (x : Domain n) (hx : x ∈ Ω.val) :=
    holder_weakGradient_hasFDerivAt Ω hu hΩ hα hβ hH hH₁ hHolder hGradientHolder hx
  have hGradient : ContinuousOn (fderiv ℝ u) Ω.val := by
    apply (columnLinearMap_continuousOn (fun i => (hGradientHolder i).continuousOn hβ)).congr
    intro x hx
    exact (hDerivative x hx).fderiv
  refine ⟨?_, fun x hx => (hDerivative x hx).fderiv⟩
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) Ω.property).mpr
  refine ⟨?_, ?_, contDiffOn_zero.mpr hGradient⟩
  · intro x hx
    exact (hDerivative x hx).differentiableAt.differentiableWithinAt
  · intro hzero
    cases hzero

theorem holder_weakGradient_firstDerivative_bounds {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (hΩ : volume Ω.val ≠ ⊤)
    {α β H H₁ M : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hH : 0 ≤ H) (hH₁ : 0 ≤ H₁) (hM : 0 ≤ M)
    (hHolder : HolderBoundOn Ω.val u α H)
    (hGradientHolder : ∀ i : Fin n, HolderBoundOn Ω.val (fun x => Du x i) β H₁)
    (hGradientBound : ∀ x ∈ Ω.val, ∀ i : Fin n, ‖Du x i‖ ≤ M) :
    ContDiffOn ℝ 1 u Ω.val ∧
    (∀ x ∈ Ω.val, ‖fderiv ℝ u x‖ ≤ Real.sqrt (n : ℝ) * M) ∧
    HolderBoundOn Ω.val (fderiv ℝ u) β (Real.sqrt (n : ℝ) * H₁) := by
  obtain ⟨hSmooth, hDerivative⟩ :=
    holder_weakGradient_contDiffOn_one Ω hu hΩ hα hβ hH hH₁ hHolder hGradientHolder
  refine ⟨hSmooth, ?_, ?_⟩
  · intro x hx
    apply norm_linearMap_le_of_columns_bound (fderiv ℝ u x) hM
    intro i
    rw [hDerivative x hx, columnLinearMap_single]
    exact hGradientBound x hx i
  · intro x hx y hy
    have hbound (i : Fin n) :
        ‖(fderiv ℝ u x - fderiv ℝ u y) (EuclideanSpace.single i 1)‖ ≤
          H₁ * Real.rpow (dist x y) β := by
      rw [sub_apply, hDerivative x hx, hDerivative y hy, columnLinearMap_single,
        columnLinearMap_single]
      exact hGradientHolder i x hx y hy
    have hnonneg : 0 ≤ H₁ * Real.rpow (dist x y) β :=
      mul_nonneg hH₁ (Real.rpow_nonneg dist_nonneg _)
    simpa only [mul_assoc] using
      norm_linearMap_le_of_columns_bound (fderiv ℝ u x - fderiv ℝ u y) hnonneg hbound

end HolderToCK
end
