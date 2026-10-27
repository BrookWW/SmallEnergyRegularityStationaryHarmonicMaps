module

public import HolderToCK.Analysis.Bootstrap.CoordinateWords
public import HolderToCK.Analysis.GradientLinearAlgebra

/-! # Native regularity from actual finite coordinate derivatives

The derivative of a Euclidean map is the finite sum of its actual coordinate
columns. Regularity of those columns therefore gives regularity of the native
Fréchet derivative. Iterating this identity combines regularity of all words
of a fixed length into higher regularity of the same original map.
-/

public section

open HarmonicMaps Set
open scoped ContDiff

namespace HolderToCK

/-- Regularity of every actual coordinate column reconstructs the native
Fréchet derivative field on an open domain. -/
theorem contDiffOn_fderiv_of_coordinate_columns {n q : ℕ}
    (Ω : OpenDomain n) {u : Domain n → Ambient q} (k : ℕ)
    (hcolumns : ∀ i : Fin n, ContDiffOn ℝ k
      (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) Ω.val) :
    ContDiffOn ℝ k (fderiv ℝ u) Ω.val := by
  have hsum : ContDiffOn ℝ k
      (fun x => ∑ i : Fin n,
        (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).smulRight
          (fderiv ℝ u x (EuclideanSpace.single i 1))) Ω.val := by
    apply ContDiffOn.sum
    intro i _
    exact (((ContinuousLinearMap.smulRightL ℝ (Domain n) (Ambient q))
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i)).contDiff.comp_contDiffOn
        (hcolumns i))
  exact hsum.congr (fun x _ => linearMap_eq_columnSum (fderiv ℝ u x))

/-- A C1 map whose actual first coordinate derivatives are Ck is C(k+1). -/
theorem contDiffOn_succ_of_coordinate_columns {n q : ℕ}
    (Ω : OpenDomain n) {u : Domain n → Ambient q} (k : ℕ)
    (hu : ContDiffOn ℝ 1 u Ω.val)
    (hcolumns : ∀ i : Fin n, ContDiffOn ℝ k
      (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) Ω.val) :
    ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) u Ω.val := by
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := (k : ℕ∞ω)) Ω.property).mpr
  refine ⟨hu.differentiableOn_one, ?_,
    contDiffOn_fderiv_of_coordinate_columns Ω k hcolumns⟩
  intro hk
  cases hk

/-- Combining C(r) coordinate words of length k raises the native regularity
of a Ck map to C(k+r), without replacing that map or its derivatives. -/
theorem contDiffOn_add_of_coordinate_words {n q : ℕ}
    (Ω : OpenDomain n) {u : Domain n → Ambient q} (k r : ℕ)
    (hu : ContDiffOn ℝ k u Ω.val)
    (hwords : ∀ w : List (Fin n), w.length = k →
      ContDiffOn ℝ r (coordinateWord u w) Ω.val) :
    ContDiffOn ℝ ((k + r : ℕ) : ℕ∞ω) u Ω.val := by
  induction k generalizing u with
  | zero =>
      simpa only [Nat.zero_add, coordinateWord_nil] using hwords [] rfl
  | succ k ih =>
      have huOne : ContDiffOn ℝ 1 u Ω.val :=
        hu.of_le (by exact_mod_cast Nat.succ_pos k)
      have hcolumns : ∀ i : Fin n, ContDiffOn ℝ ((k + r : ℕ) : ℕ∞ω)
          (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) Ω.val := by
        intro i
        have hcolumn : ContDiffOn ℝ k
            (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) Ω.val :=
          (hu.fderiv_of_isOpen Ω.property (by norm_cast)).clm_apply contDiffOn_const
        apply ih hcolumn
        intro w hw
        have happend : (w ++ [i]).length = k + 1 := by
          simp only [List.length_append, List.length_singleton, hw]
        simpa only [coordinateWord_append, coordinateWord_cons, coordinateWord_nil] using
          hwords (w ++ [i]) happend
      have hfull := contDiffOn_succ_of_coordinate_columns Ω (k + r) huOne hcolumns
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 r] using hfull

/-- The finite coordinate combination used after a C2 estimate for every word
of length m-1 on a smaller open domain. -/
theorem contDiffOn_succ_of_coordinate_words_two {n q : ℕ}
    (Ω : OpenDomain n) {u : Domain n → Ambient q} (m : ℕ) (hm : 1 ≤ m)
    (hu : ContDiffOn ℝ m u Ω.val)
    (hwords : ∀ w : List (Fin n), w.length = m - 1 →
      ContDiffOn ℝ 2 (coordinateWord u w) Ω.val) :
    ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) u Ω.val := by
  have huLower : ContDiffOn ℝ (m - 1 : ℕ) u Ω.val :=
    hu.of_le (by exact_mod_cast Nat.sub_le m 1)
  have hfull := contDiffOn_add_of_coordinate_words Ω (m - 1) 2 huLower hwords
  have horder : m - 1 + 2 = m + 1 := by omega
  simpa only [horder] using hfull

end HolderToCK
end
