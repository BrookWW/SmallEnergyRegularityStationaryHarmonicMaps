module

public import HolderToCK.Foundation.HolderBounds
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! # Uniform Holder bounds from short segments

Equal subdivision of a segment in a convex carrier turns a uniform local
Holder estimate into a global one, with factor m^(1-alpha).
-/

public section

open HarmonicMaps Set AffineMap

namespace HolderToCK

theorem holderBoundOn_of_uniform_short_segments {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {s : Set (Domain n)} {f : Domain n → E}
    {α H ρ d : ℝ} (hs : Convex ℝ s) (m : ℕ) (hm : 0 < m)
    (hdiam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ d) (hsize : d < (m : ℝ) * ρ)
    (hlocal : ∀ x ∈ s, ∀ y ∈ s, dist x y < ρ →
      ‖f x - f y‖ ≤ H * Real.rpow (dist x y) α) :
    HolderBoundOn s f α (H * Real.rpow (m : ℝ) (1 - α)) := by
  have hmreal : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  intro x hx y hy
  let z : ℕ → Domain n := fun k => lineMap x y ((k : ℝ) / m)
  have hzmem (k : ℕ) (hk : k ≤ m) : z k ∈ s := by
    apply hs.lineMap_mem hx hy
    exact ⟨div_nonneg (Nat.cast_nonneg _) hmreal.le,
      (div_le_one hmreal).mpr (by exact_mod_cast hk)⟩
  have hzdist (k : ℕ) : dist (z k) (z (k + 1)) = (m : ℝ)⁻¹ * dist x y := by
    dsimp only [z]
    rw [dist_lineMap_lineMap, Real.dist_eq, Nat.cast_add, Nat.cast_one]
    have heq : (k : ℝ) / m - ((k : ℝ) + 1) / m = -(m : ℝ)⁻¹ := by ring
    rw [heq, abs_neg, abs_of_pos (inv_pos.mpr hmreal)]
  have hzdshort (k : ℕ) : dist (z k) (z (k + 1)) < ρ := by
    rw [hzdist, ← div_eq_inv_mul, div_lt_iff₀ hmreal]
    exact (hdiam x hx y hy).trans_lt (by simpa only [mul_comm] using hsize)
  have hstep (k : ℕ) (hk : k < m) : dist (f (z k)) (f (z (k + 1))) ≤
      H * Real.rpow ((m : ℝ)⁻¹ * dist x y) α := by
    rw [dist_eq_norm]
    simpa only [hzdist] using hlocal (z k) (hzmem k hk.le) (z (k + 1))
      (hzmem (k + 1) (by omega)) (hzdshort k)
  have hchain := dist_le_range_sum_of_dist_le (f := fun k => f (z k)) m
    (d := fun _ => H * Real.rpow ((m : ℝ)⁻¹ * dist x y) α) (fun {k} hk => hstep k hk)
  have hz0 : z 0 = x := by simp only [z, Nat.cast_zero, zero_div, lineMap_apply_zero]
  have hzm : z m = y := by simp only [z, div_self hmreal.ne', lineMap_apply_one]
  rw [hz0, hzm, dist_eq_norm, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hchain
  have hcoeff : (m : ℝ) * (H * Real.rpow ((m : ℝ)⁻¹ * dist x y) α) =
      (H * Real.rpow (m : ℝ) (1 - α)) * Real.rpow (dist x y) α := by
    change (m : ℝ) * (H * (((m : ℝ)⁻¹ * dist x y) ^ α)) =
      (H * (m : ℝ) ^ (1 - α)) * (dist x y) ^ α
    rw [Real.mul_rpow (inv_nonneg.mpr hmreal.le) dist_nonneg, Real.inv_rpow hmreal.le,
      Real.rpow_sub hmreal, Real.rpow_one]
    ring
  exact hchain.trans_eq hcoeff

end HolderToCK
end
