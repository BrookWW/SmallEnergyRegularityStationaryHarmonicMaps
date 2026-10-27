module

public import HarmonicMaps.Energy
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# A genuine weak measure bound for centered ball superlevels

A disjoint Vitali subfamily covers every selected center after fivefold
radius enlargement. Summing its actual lower integrals gives the weak
measure estimate with the explicit Euclidean coefficient 5^n.
-/

public section

open HarmonicMaps MeasureTheory Set Metric
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Fivefold ball enlargement multiplies the actual extended volume by 5^n. -/
theorem volume_ball_five_mul {n : ℕ} (x : Domain n) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball x (5 * r)) = ENNReal.ofReal ((5 : ℝ) ^ n) * volume (Metric.ball x r) := by
  rw [Measure.addHaar_ball_of_pos volume x (by positivity : 0 < 5 * r),
    Measure.addHaar_ball_of_pos volume x hr]
  simp only [finrank_euclideanSpace, Fintype.card_fin, mul_pow,
    ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5) n), mul_assoc]

/-- Real ball-average superlevels satisfy the actual scaled weak measure inequality. -/
theorem centered_ball_superlevel_measure_bound {n : ℕ}
    (f : Domain n → ℝ≥0∞) (S : Set (Domain n)) (R level : ℝ) (_hlevel : 0 < level)
    (hS : ∀ x ∈ S, ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      ENNReal.ofReal level * volume (Metric.ball x r) ≤ ∫⁻ y in Metric.ball x r, f y) :
    ENNReal.ofReal level * volume S ≤ ENNReal.ofReal ((5 : ℝ) ^ n) * ∫⁻ y, f y := by
  classical
  let T : Set (Domain n × PositiveRadius) := {a | a.1 ∈ S ∧ a.2.val ≤ R ∧
    ENNReal.ofReal level * volume (Metric.ball a.1 a.2.val) ≤
      ∫⁻ y in Metric.ball a.1 a.2.val, f y}
  obtain ⟨U, hUT, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball T
      (fun a => a.1) (fun a => a.2.val) R (fun a ha => ha.2.1) 5 (by norm_num)
  have hcount : U.Countable := hdisj.countable_of_isOpen
    (fun _ _ => Metric.isOpen_ball) (fun a _ => ⟨a.1, Metric.mem_ball_self a.2.property⟩)
  letI : Countable U := hcount.to_subtype
  have hScover : S ⊆ ⋃ a : U, Metric.ball a.val.1 (5 * a.val.2.val) := by
    intro x hx
    obtain ⟨r, hr, hcap, hbig⟩ := hS x hx
    let a : Domain n × PositiveRadius := (x, ⟨r, hr⟩)
    have ha : a ∈ T := ⟨hx, hcap, hbig⟩
    obtain ⟨b, hb, hsub⟩ := hcover a ha
    exact mem_iUnion_of_mem (⟨b, hb⟩ : U) (hsub (Metric.mem_ball_self hr))
  have hmeasure : volume S ≤ ∑' a : U, volume (Metric.ball a.val.1 (5 * a.val.2.val)) :=
    (measure_mono hScover).trans (measure_iUnion_le _)
  have hsmallDisj : Pairwise (fun a b : U => Disjoint
      (Metric.ball a.val.1 a.val.2.val) (Metric.ball b.val.1 b.val.2.val)) := hdisj.subtype
  have hIntegral : (∑' a : U, ∫⁻ y in Metric.ball a.val.1 a.val.2.val, f y) ≤ ∫⁻ y, f y := by
    rw [← lintegral_iUnion (fun _ => measurableSet_ball) hsmallDisj]
    simpa only [Measure.restrict_univ] using
      (lintegral_mono_set (f := f) (μ := volume) (subset_univ
        (⋃ a : U, Metric.ball a.val.1 a.val.2.val)))
  calc
    _ ≤ ENNReal.ofReal level * ∑' a : U,
        volume (Metric.ball a.val.1 (5 * a.val.2.val)) := mul_le_mul_right hmeasure _
    _ = ENNReal.ofReal ((5 : ℝ) ^ n) * ∑' a : U,
        ENNReal.ofReal level * volume (Metric.ball a.val.1 a.val.2.val) := by
      simp_rw [volume_ball_five_mul _ (Subtype.property _)]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      ac_rfl
    _ ≤ ENNReal.ofReal ((5 : ℝ) ^ n) *
        ∑' a : U, ∫⁻ y in Metric.ball a.val.1 a.val.2.val, f y :=
      mul_le_mul_right (ENNReal.tsum_le_tsum fun a => (hUT a.property).2.2) _
    _ ≤ _ := mul_le_mul_right hIntegral _

/-- The positive-level weak bound has the usual inverse-level measure factor. -/
theorem centered_ball_superlevel_measure_le {n : ℕ}
    (f : Domain n → ℝ≥0∞) (S : Set (Domain n)) (R level : ℝ) (hlevel : 0 < level)
    (hS : ∀ x ∈ S, ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      ENNReal.ofReal level * volume (Metric.ball x r) ≤ ∫⁻ y in Metric.ball x r, f y) :
    volume S ≤ ENNReal.ofReal ((5 : ℝ) ^ n / level) * ∫⁻ y, f y := by
  have H := mul_le_mul_right (centered_ball_superlevel_measure_bound f S R level hlevel hS)
    (ENNReal.ofReal level⁻¹)
  have hcancel : ENNReal.ofReal level⁻¹ * ENNReal.ofReal level = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hlevel.le), inv_mul_cancel₀ hlevel.ne',
      ENNReal.ofReal_one]
  have hcoef : ENNReal.ofReal level⁻¹ * ENNReal.ofReal ((5 : ℝ) ^ n) =
      ENNReal.ofReal ((5 : ℝ) ^ n / level) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hlevel.le), div_eq_mul_inv, mul_comm]
  rwa [← mul_assoc, hcancel, one_mul, ← mul_assoc, hcoef] at H

end StationaryHarmonicMaps.Analysis

end
