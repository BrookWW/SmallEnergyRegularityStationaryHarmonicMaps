module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Linear growth from a geometric recurrence

A recurrence whose coefficient is smaller than the radius contraction gives
a linear bound at every geometric radius. Monotonicity transfers the bound
to all positive radii below the reference radius. The real-power specialization
and the scale-then-smallness choice apply to the Morrey-envelope recurrence.
-/

public section

namespace StationaryHarmonicMaps

/-- The recurrence gives a linear bound at every geometric radius. -/
theorem geometric_radius_linear_bound (f : ℝ → ℝ)
    {θ ρ A B r₀ : ℝ} (hθ : 0 < θ) (hθOne : θ < 1)
    (hρ : 0 ≤ ρ) (hρθ : ρ < θ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hr₀ : 0 < r₀) (hbase : f r₀ ≤ B * r₀)
    (hstep : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      f (θ * r) ≤ ρ * f r + A * r) :
    ∀ k : ℕ, f (θ ^ k * r₀) ≤
      (B + A / (θ - ρ)) * (θ ^ k * r₀) := by
  let C := B + A / (θ - ρ)
  have hgap : 0 < θ - ρ := sub_pos.mpr hρθ
  have hBC : B ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_right (div_nonneg hA hgap.le)
  have habsorb : ρ * C + A ≤ θ * C := by
    have hcancel : (θ - ρ) * (A / (θ - ρ)) = A := by
      field_simp [hgap.ne']
    have hprod : 0 ≤ (θ - ρ) * B := mul_nonneg hgap.le hB
    dsimp only [C]
    nlinarith only [hcancel, hprod]
  intro k
  induction k with
  | zero =>
      simp only [pow_zero, one_mul]
      exact hbase.trans (mul_le_mul_of_nonneg_right hBC hr₀.le)
  | succ k ih =>
      have hkr : 0 < θ ^ k * r₀ := mul_pos (pow_pos hθ k) hr₀
      have hkr₀ : θ ^ k * r₀ ≤ r₀ :=
        mul_le_of_le_one_left hr₀.le (pow_le_one₀ hθ.le hθOne.le)
      have hnext : θ ^ (k + 1) * r₀ = θ * (θ ^ k * r₀) := by
        rw [pow_succ]
        ring
      rw [hnext]
      calc
        f (θ * (θ ^ k * r₀)) ≤ ρ * f (θ ^ k * r₀) + A * (θ ^ k * r₀) :=
          hstep _ hkr hkr₀
        _ ≤ ρ * (C * (θ ^ k * r₀)) + A * (θ ^ k * r₀) :=
          add_le_add (mul_le_mul_of_nonneg_left ih hρ) le_rfl
        _ = (ρ * C + A) * (θ ^ k * r₀) := by ring
        _ ≤ (θ * C) * (θ ^ k * r₀) :=
          mul_le_mul_of_nonneg_right habsorb hkr.le
        _ = C * (θ * (θ ^ k * r₀)) := by ring

/-- Monotonicity transfers geometric linear growth to every inner radius. -/
theorem all_radius_linear_bound_of_recurrence (f : ℝ → ℝ)
    {θ ρ A B r₀ : ℝ} (hθ : 0 < θ) (hθOne : θ < 1)
    (hρ : 0 ≤ ρ) (hρθ : ρ < θ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hr₀ : 0 < r₀)
    (hmono : ∀ r s : ℝ, 0 < r → r ≤ s → s ≤ r₀ → f r ≤ f s)
    (hbase : f r₀ ≤ B * r₀)
    (hstep : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      f (θ * r) ≤ ρ * f r + A * r) :
    ∀ r : ℝ, 0 < r → r ≤ r₀ →
      f r ≤ ((B + A / (θ - ρ)) / θ) * r := by
  intro r hr hrr₀
  let C := B + A / (θ - ρ)
  have hC : 0 ≤ C := add_nonneg hB (div_nonneg hA (sub_pos.mpr hρθ).le)
  obtain ⟨k, hLower, hUpper⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr hr₀) ((div_le_one hr₀).mpr hrr₀) hθ hθOne
  have hkr : 0 < θ ^ k * r₀ := mul_pos (pow_pos hθ k) hr₀
  have hrk : r ≤ θ ^ k * r₀ := (div_le_iff₀ hr₀).mp hUpper
  have hk₀ : θ ^ k * r₀ ≤ r₀ :=
    mul_le_of_le_one_left hr₀.le (pow_le_one₀ hθ.le hθOne.le)
  have hbracket : θ * (θ ^ k * r₀) < r := by
    have hl := (lt_div_iff₀ hr₀).mp hLower
    rw [pow_succ] at hl
    nlinarith only [hl]
  have hscale : θ ^ k * r₀ ≤ r / θ := by
    exact (le_div_iff₀ hθ).mpr (by nlinarith only [hbracket])
  calc
    f r ≤ f (θ ^ k * r₀) := hmono _ _ hr hrk hk₀
    _ ≤ C * (θ ^ k * r₀) :=
      geometric_radius_linear_bound f hθ hθOne hρ hρθ hA hB hr₀ hbase hstep k
    _ ≤ C * (r / θ) := mul_le_mul_of_nonneg_left hscale hC
    _ = (C / θ) * r := by ring

/-- A real-power contraction with exponent greater than one has linear growth. -/
theorem all_radius_linear_bound_of_rpow_recurrence (f : ℝ → ℝ)
    {θ β A B r₀ : ℝ} (hθ : 0 < θ) (hθOne : θ < 1)
    (hβ : 1 < β) (hA : 0 ≤ A) (hB : 0 ≤ B) (hr₀ : 0 < r₀)
    (hmono : ∀ r s : ℝ, 0 < r → r ≤ s → s ≤ r₀ → f r ≤ f s)
    (hbase : f r₀ ≤ B * r₀)
    (hstep : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      f (θ * r) ≤ θ ^ β * f r + A * r) :
    ∀ r : ℝ, 0 < r → r ≤ r₀ →
      f r ≤ ((B + A / (θ - θ ^ β)) / θ) * r := by
  exact all_radius_linear_bound_of_recurrence f hθ hθOne
    (Real.rpow_nonneg hθ.le _) (Real.rpow_lt_self_of_lt_one hθ hθOne hβ)
    hA hB hr₀ hmono hbase hstep

/-- Positive real powers can be made small while respecting a prescribed cap. -/
theorem exists_positive_rpow_bound {C p a cap : ℝ}
    (hC : 0 < C) (hp : 0 < p) (ha : 0 < a) (hcap : 0 < cap) :
    ∃ t : ℝ, 0 < t ∧ t ≤ cap ∧ C * t ^ p ≤ a := by
  let root := (a / C) ^ p⁻¹
  have hroot : 0 < root := Real.rpow_pos_of_pos (div_pos ha hC) _
  have hpower : root ^ p = a / C :=
    Real.rpow_inv_rpow (div_pos ha hC).le hp.ne'
  refine ⟨min cap root, lt_min hcap hroot, min_le_left _ _, ?_⟩
  have hmono := Real.rpow_le_rpow (lt_min hcap hroot).le
    (min_le_right cap root) hp.le
  have hmul := mul_le_mul_of_nonneg_left hmono hC.le
  rw [hpower] at hmul
  have hcancel : C * (a / C) = a := by field_simp [hC.ne']
  exact hmul.trans_eq hcancel

/-- The radius contraction can be fixed before the Morrey smallness threshold. -/
theorem exists_scale_absorbing_higher_power {C p β : ℝ}
    (hC : 0 < C) (hβp : β < p) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
      C * θ ^ p ≤ (1 / 2 : ℝ) * θ ^ β := by
  obtain ⟨θ, hθ, hθcap, hsmall⟩ := exists_positive_rpow_bound
    hC (sub_pos.mpr hβp) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨θ, hθ, hθcap, ?_⟩
  have hsplit : θ ^ p = θ ^ (p - β) * θ ^ β := by
    rw [← Real.rpow_add hθ]
    congr 1
    ring
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hθ.le β)

/-- Once the radius is fixed, one positive threshold absorbs all smaller data. -/
theorem exists_smallness_absorbing_morrey_term {C p β n θ : ℝ}
    (hC : 0 < C) (hp : 0 < p) (hθ : 0 < θ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ η : ℝ, 0 ≤ η → η ≤ η₀ →
        C * η ^ p * θ ^ (p - n) ≤ (1 / 2 : ℝ) * θ ^ β := by
  have hcoef : 0 < C * θ ^ (p - n) :=
    mul_pos hC (Real.rpow_pos_of_pos hθ _)
  have hrhs : 0 < (1 / 2 : ℝ) * θ ^ β :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hθ _)
  obtain ⟨η₀, hη₀, hηcap, hsmall⟩ :=
    exists_positive_rpow_bound hcoef hp hrhs (by norm_num : (0 : ℝ) < 1)
  refine ⟨η₀, hη₀, hηcap, ?_⟩
  intro η hη hηle
  have hpower := Real.rpow_le_rpow hη hηle hp.le
  calc
    C * η ^ p * θ ^ (p - n) = (C * θ ^ (p - n)) * η ^ p := by ring
    _ ≤ (C * θ ^ (p - n)) * η₀ ^ p :=
      mul_le_mul_of_nonneg_left hpower hcoef.le
    _ ≤ (1 / 2 : ℝ) * θ ^ β := hsmall

/-- A single source constant admits the ordered scale and smallness choices. -/
theorem exists_scale_then_smallness {C p β n : ℝ}
    (hC : 0 < C) (hβ : 1 < β) (hβp : β < p) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
      C * θ ^ p ≤ (1 / 2 : ℝ) * θ ^ β ∧
      ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
        ∀ η : ℝ, 0 ≤ η → η ≤ η₀ →
          C * θ ^ p + C * η ^ p * θ ^ (p - n) ≤ θ ^ β := by
  obtain ⟨θ, hθ, hθcap, hscale⟩ :=
    exists_scale_absorbing_higher_power hC hβp
  obtain ⟨η₀, hη₀, hηcap, hsmall⟩ :=
    exists_smallness_absorbing_morrey_term (β := β) (n := n) hC
      (lt_trans (by norm_num : (0 : ℝ) < 1) (lt_trans hβ hβp)) hθ
  refine ⟨θ, hθ, hθcap, hscale, η₀, hη₀, hηcap, ?_⟩
  intro η hη hηle
  have herr := hsmall η hη hηle
  linarith only [hscale, herr]

end StationaryHarmonicMaps

end
