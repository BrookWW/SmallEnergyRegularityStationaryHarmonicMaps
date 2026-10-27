/-
MIT License

Copyright (c) 2026 LeanStationaryHarmonicMaps contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import HarmonicMaps.Analysis.RadialStressBasic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Algebra of the radial stress contraction

The identities expand the squared radial derivative and contract an arbitrary
gradient matrix with the coordinate expression of a radial field derivative.
The energy uses the existing squared Hilbert--Schmidt norm.
-/

public section

open scoped BigOperators

namespace HarmonicMaps

noncomputable section

/-- The square norm of a finite real linear combination as a double sum. -/
theorem norm_sq_sum_smul {n q : ℕ}
    (a : Fin n → ℝ) (v : Fin n → Ambient q) :
    ‖(∑ i : Fin n, a i • v i)‖ ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n,
        a i * a j * inner ℝ (v i) (v j) := by
  refine (real_inner_self_eq_norm_sq (∑ i : Fin n, a i • v i)).symm.trans ?_
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-- The squared radial derivative is the radial double contraction. -/
theorem gradientRadialDerivative_norm_sq_eq_sum {n q : ℕ}
    (A : Gradient n q) (x : {x : Domain n // x ≠ 0}) :
    ‖gradientRadialDerivative A x‖ ^ 2 =
      (‖x.val‖⁻¹) ^ 2 *
        (∑ i : Fin n, ∑ j : Fin n,
          x.val i * x.val j * inner ℝ (A i) (A j)) := by
  change ‖‖x.val‖⁻¹ • (∑ i : Fin n, x.val i • A i)‖ ^ 2 = _
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x.val)),
    mul_pow, norm_sq_sum_smul]

/-- Contracting the diagonal and radial parts with an arbitrary gradient. -/
theorem radialStressContraction_algebra {n q : ℕ}
    (A : Gradient n q) (x : Domain n) (hx : x ≠ 0) (c d : ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ (A i) (A j) *
        (c * (EuclideanSpace.single i (1 : ℝ)) j + d * (x i * x j / ‖x‖))) =
      c * hsNormSq A + ‖x‖ * d * ‖gradientRadialDerivative A ⟨x, hx⟩‖ ^ 2 := by
  have hfirst :
      (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (A i) (A j) * (c * (EuclideanSpace.single i (1 : ℝ)) j)) =
        c * hsNormSq A := by
    calc
      _ = ∑ i : Fin n, c * ‖A i‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_eq_single i]
        · simp only [PiLp.single_apply, ite_true, mul_one,
            real_inner_self_eq_norm_sq, mul_comm]
        · intro j _ hji
          simp only [PiLp.single_apply, if_neg hji, mul_zero]
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
      _ = c * hsNormSq A := by
        rw [hsNormSq, Finset.mul_sum]
  have hsecond :
      (∑ i : Fin n, ∑ j : Fin n,
        inner ℝ (A i) (A j) * (d * (x i * x j / ‖x‖))) =
        d * ((∑ i : Fin n, ∑ j : Fin n,
          x i * x j * inner ℝ (A i) (A j)) / ‖x‖) := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n,
          d * (x i * x j * inner ℝ (A i) (A j) / ‖x‖) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_div]
  have hradial := gradientRadialDerivative_norm_sq_eq_sum A ⟨x, hx⟩
  have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hradial_term :
      d * ((∑ i : Fin n, ∑ j : Fin n,
        x i * x j * inner ℝ (A i) (A j)) / ‖x‖) =
        ‖x‖ * d * ‖gradientRadialDerivative A ⟨x, hx⟩‖ ^ 2 := by
    rw [hradial]
    field_simp [hnorm_ne]
  calc
    _ = c * hsNormSq A +
        d * ((∑ i : Fin n, ∑ j : Fin n,
          x i * x j * inner ℝ (A i) (A j)) / ‖x‖) := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [hfirst, hsecond]
    _ = _ := by rw [hradial_term]

/-- The pure contraction of the radial derivative-coordinate expression. -/
theorem gradientRadialStressContractionFormula {n q : ℕ}
    (A : Gradient n q) (eta : ℝ → ℝ) {x : Domain n} (hx : x ≠ 0) :
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ (A i) (A j) *
        (eta ‖x‖ * (EuclideanSpace.single i (1 : ℝ)) j +
          deriv eta ‖x‖ * (x i * x j / ‖x‖))) =
      eta ‖x‖ * hsNormSq A +
        ‖x‖ * deriv eta ‖x‖ * ‖gradientRadialDerivative A ⟨x, hx⟩‖ ^ 2 :=
  radialStressContraction_algebra A x hx (eta ‖x‖) (deriv eta ‖x‖)

end
end HarmonicMaps

end
