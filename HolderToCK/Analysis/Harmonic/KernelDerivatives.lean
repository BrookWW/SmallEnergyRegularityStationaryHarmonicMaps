module

public import HolderToCK.Analysis.ConvolutionDerivatives
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Actual iterated derivatives of compact-kernel convolutions

Evaluation of the native iterated Fréchet derivative commutes with convolution
against integrable domain data. Every derivative falls on the compact smooth
kernel, with the original domain zero extension preserved.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff Topology

namespace HolderToCK

noncomputable section

theorem iteratedFDeriv_apply_contDiff {n : ℕ} {χ : Domain n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (k : ℕ) (v : Fin k → Domain n) :
    ContDiff ℝ ∞ (fun z => iteratedFDeriv ℝ k χ z v) := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Domain n) ℝ v
  exact L.contDiff.comp (hχ.iteratedFDeriv_right (by exact le_rfl))

theorem iteratedFDeriv_apply_hasCompactSupport {n : ℕ} {χ : Domain n → ℝ}
    (hcχ : HasCompactSupport χ) (k : ℕ) (v : Fin k → Domain n) :
    HasCompactSupport (fun z => iteratedFDeriv ℝ k χ z v) := by
  exact (hcχ.iteratedFDeriv k).comp_left
    (g := fun p : ContinuousMultilinearMap ℝ (fun _ : Fin k => Domain n) ℝ => p v)
    (by simp only [zero_apply])

theorem kernelConvolution_iteratedFDeriv_apply {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val)
    {χ : Domain n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (k : ℕ) (x : Domain n) (v : Fin k → Domain n) :
    iteratedFDeriv ℝ k (fun x => ∫ z, χ z • zeroExtensionOn Ω u (x - z)) x v =
      ∫ z, iteratedFDeriv ℝ k χ (x - z) v • zeroExtensionOn Ω u z := by
  induction k generalizing x with
  | zero =>
      simp only [iteratedFDeriv_zero_apply]
      rw [← integral_sub_left_eq_self
        (fun z => χ z • zeroExtensionOn Ω u (x - z)) volume x]
      simp only [sub_sub_cancel]
  | succ k ih =>
      let χk : Domain n → ℝ := fun z => iteratedFDeriv ℝ k χ z (Fin.tail v)
      have hk : ContDiff ℝ ∞ χk := iteratedFDeriv_apply_contDiff hχ k (Fin.tail v)
      have hck : HasCompactSupport χk :=
        iteratedFDeriv_apply_hasCompactSupport hcχ k (Fin.tail v)
      have hsmooth := kernelConvolution_contDiff Ω u hu hχ hcχ
      have hdiff := (hsmooth.contDiffAt (x := x)).differentiableAt_iteratedFDeriv
        (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top k))
      rw [hdiff.iteratedFDeriv_succ_apply_left']
      have hprev : (fun y => iteratedFDeriv ℝ k
          (fun x => ∫ z, χ z • zeroExtensionOn Ω u (x - z)) y (Fin.tail v)) =
          fun y => ∫ z, χk z • zeroExtensionOn Ω u (y - z) := by
        funext y
        rw [ih]
        rw [← integral_sub_left_eq_self
          (fun z => χk z • zeroExtensionOn Ω u (y - z)) volume y]
        simp only [sub_sub_cancel]
        rfl
      rw [hprev, kernelConvolution_fderiv Ω u hu hk hck]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      dsimp only
      have hdχ := (hχ.contDiffAt (x := x - z)).differentiableAt_iteratedFDeriv
        (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top k))
      rw [hdχ.iteratedFDeriv_succ_apply_left']

end
end HolderToCK
end
