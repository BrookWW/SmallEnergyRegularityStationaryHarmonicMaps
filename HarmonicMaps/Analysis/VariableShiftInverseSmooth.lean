module

public import HarmonicMaps.Analysis.VariableShiftCalculus
public import HarmonicMaps.Analysis.VariableShiftDerivativeInvertible
public import HarmonicMaps.Analysis.VariableShiftMetric
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Smoothness of the inverse variable translation

The local inverse from the inverse function theorem agrees near each target
point with any global right inverse of an injective variable translation.
Its smoothness therefore gives smoothness of the existing global inverse.
-/

public section

open Filter Topology
open scoped ContDiff

namespace HarmonicMaps

private theorem contDiffAt_inverse_of_injective {n : ℕ}
    {f g : Domain n → Domain n} {a : Domain n} {e : Domain n ≃L[ℝ] Domain n}
    (hf : ContDiffAt ℝ ∞ f a) (hf' : HasFDerivAt f (e : Domain n →L[ℝ] Domain n) a)
    (hfi : Function.Injective f) (hg : ∀ z, f (g z) = z) :
    ContDiffAt ℝ ∞ g (f a) := by
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hright : ∀ᶠ z in 𝓝 (f a), f (hf.localInverse hf' hn z) = z :=
    (hf.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  have heq : g =ᶠ[𝓝 (f a)] hf.localInverse hf' hn := by
    filter_upwards [hright] with z hz
    exact hfi ((hg z).trans hz.symm)
  exact (hf.to_localInverse hf' hn).congr_of_eventuallyEq heq

/-- Every global inverse characterized by the translation equation is smooth. -/
theorem variableShift_contDiff_inverse {n : ℕ} {s : Domain n → ℝ} {L : ℝ}
    (hs : ContDiff ℝ ∞ s) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL0 : 0 ≤ L)
    (hL : L ≤ 1 / 4) {y : Domain n} (hy : y ∈ Metric.ball 0 1)
    (g : Domain n → Domain n) (hg : ∀ z, variableShift s y (g z) = z) :
    ContDiff ℝ ∞ g := by
  have hfi := (variableShift_bijective hs hDs hL0 hL hy).1
  apply contDiff_iff_contDiffAt.2
  intro z
  obtain ⟨e, he⟩ :=
    variableShift_exists_continuousLinearEquiv_hasFDerivAt hs hDs hL y hy (g z)
  have hinv := contDiffAt_inverse_of_injective
    (contDiff_variableShift hs y).contDiffAt he hfi hg
  rw [hg z] at hinv
  exact hinv

end HarmonicMaps
