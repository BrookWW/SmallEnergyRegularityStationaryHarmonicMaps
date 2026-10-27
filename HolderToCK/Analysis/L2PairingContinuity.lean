module

public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Actual integrals and continuity of L2 inner-product pairings -/

public section

open HarmonicMaps MeasureTheory Filter
open scoped Topology

namespace HolderToCK

theorem integrable_inner_of_memLp_two {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

theorem integral_inner_eq_L2_inner {n q : ℕ} {μ : Measure (Domain n)}
    {f g : Domain n → Ambient q} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, inner ℝ (f x) (g x) ∂μ) = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

theorem tendsto_integral_inner_of_L2 {n q : ℕ} {μ : Measure (Domain n)}
    {f : ℕ → Domain n → Ambient q} {u g : Domain n → Ambient q}
    (hf : ∀ k, MemLp (f k) 2 μ) (hu : MemLp u 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun k => eLpNorm (f k - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, inner ℝ (g x) (f k x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (g x) (u x) ∂μ)) := by
  have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf u hu).mpr hlim
  have hconst : Tendsto (fun _ : ℕ => hg.toLp g) atTop (𝓝 (hg.toLp g)) :=
    tendsto_const_nhds
  have hinner := hconst.inner (𝕜 := ℝ) hLp
  simp_rw [integral_inner_eq_L2_inner hg (hf _), integral_inner_eq_L2_inner hg hu]
  exact hinner

end HolderToCK
end
