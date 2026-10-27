module

public import HolderToCK.Analysis.ContinuousWeakDerivative
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The actual segment identity for the same classical representative -/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK

theorem c1_segment_integral {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} (hu : ContDiffOn ℝ 1 u Ω.val) (x y : Domain n)
    (hSegment : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ Ω.val) :
    u y - u x = ∫ t in (0 : ℝ)..1, fderiv ℝ u (x + t • (y - x)) (y - x) := by
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) t := by
    simpa only [Pi.add_def, id_eq, zero_add, one_smul] using
      (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const (y - x))
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => u (x + s • (y - x)))
        (fderiv ℝ u (x + t • (y - x)) (y - x)) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have hdiff := (hu.contDiffAt (Ω.property.mem_nhds (hSegment t ht'))).differentiableAt one_ne_zero
    exact hdiff.hasFDerivAt.comp_hasDerivAt t (hline t)
  have hcont : ContinuousOn (fun t : ℝ => fderiv ℝ u (x + t • (y - x)) (y - x))
      (Icc (0 : ℝ) 1) :=
    (((hu.continuousOn_fderiv_of_isOpen Ω.property le_rfl).comp
      ((continuous_const.add (continuous_id.smul continuous_const)).continuousOn) hSegment).clm_apply
        continuousOn_const)
  have hInt : IntervalIntegrable
      (fun t : ℝ => fderiv ℝ u (x + t • (y - x)) (y - x)) volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one
  simpa only [zero_smul, add_zero, one_smul, add_sub_cancel] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt).symm

theorem holder_weakGradient_segment_integral {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 Ω u Du) (hΩ : volume Ω.val ≠ ⊤)
    {α β H H₁ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hH : 0 ≤ H) (hH₁ : 0 ≤ H₁)
    (hHolder : HolderBoundOn Ω.val u α H)
    (hGradientHolder : ∀ i : Fin n, HolderBoundOn Ω.val (fun x => Du x i) β H₁)
    (x y : Domain n) (hSegment : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ Ω.val) :
    u y - u x = ∫ t in (0 : ℝ)..1,
      (∑ i : Fin n, (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).smulRight
        (Du (x + t • (y - x)) i)) (y - x) := by
  obtain ⟨hSmooth, hDerivative⟩ :=
    holder_weakGradient_contDiffOn_one Ω hu hΩ hα hβ hH hH₁ hHolder hGradientHolder
  rw [c1_segment_integral Ω hSmooth x y hSegment]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  dsimp only
  rw [hDerivative _ (hSegment t ht')]

end HolderToCK
end
