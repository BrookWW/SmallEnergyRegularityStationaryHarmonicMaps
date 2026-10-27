module

public import HarmonicMaps.EnergyLemmas
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring

/-!
# Hilbert--Schmidt energy algebra

The coordinate-column norm identity retains the source normalization: energy
is the sum of squared column norms without a factor of one half.
-/

public section

open scoped BigOperators

namespace HarmonicMaps

/-- The exact squared-gradient expansion with the displayed difference
columns and coefficient two on the mixed term. -/
theorem hsNormSq_sub_orthogonality {n q : ℕ} (A B : Gradient n q) :
    hsNormSq A = hsNormSq B + hsNormSq (A - B) +
      2 * ∑ i : Fin n, inner ℝ (B i) ((A - B) i) := by
  have hpoint (a b : Ambient q) :
      ‖a‖ ^ 2 = ‖b‖ ^ 2 + ‖a - b‖ ^ 2 + 2 * inner ℝ b (a - b) := by
    have h := norm_add_sq_real b (a - b)
    have heq : b + (a - b) = a := by abel
    rw [heq] at h
    linarith only [h]
  simp only [hsNormSq, Pi.sub_apply]
  calc
    (∑ i : Fin n, ‖A i‖ ^ 2) =
        ∑ i : Fin n, (‖B i‖ ^ 2 + ‖A i - B i‖ ^ 2 +
          2 * inner ℝ (B i) (A i - B i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hpoint (A i) (B i)
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

end HarmonicMaps
end
