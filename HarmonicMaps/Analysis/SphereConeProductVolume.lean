module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Volume of a cone in product coordinates

Horizontal sections of a positive truncated cone are scalar multiples of its
tangent base. Fubini and Haar scaling give the exact product-volume formula,
including bases of infinite measure.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Pointwise

namespace HarmonicMaps

/-- The product-coordinate cone with positive height b has volume
b^(dim H+1)/(dim H+1) times the volume of its measurable tangent base. -/
theorem sphereCone_product_volume {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    (b : ℝ) (hb : 0 < b) (S : Set H) (hS : MeasurableSet S) :
    (volume : Measure (ℝ × H)) {p | p.1 ∈ Ioo 0 b ∧ p.1⁻¹ • p.2 ∈ S} =
      ENNReal.ofReal (b ^ (Module.finrank ℝ H + 1) / (Module.finrank ℝ H + 1)) *
        (volume : Measure H) S := by
  have hcone : MeasurableSet {p : ℝ × H | p.1 ∈ Ioo 0 b ∧ p.1⁻¹ • p.2 ∈ S} :=
    (measurableSet_Ioo.preimage measurable_fst).inter
      (hS.preimage (measurable_fst.inv.smul measurable_snd))
  have hsection (t : ℝ) :
      (volume : Measure H) ((Prod.mk t) ⁻¹'
        {p : ℝ × H | p.1 ∈ Ioo 0 b ∧ p.1⁻¹ • p.2 ∈ S}) =
      (Ioo 0 b).indicator
        (fun t : ℝ => ENNReal.ofReal (t ^ Module.finrank ℝ H) * (volume : Measure H) S) t := by
    by_cases ht : t ∈ Ioo 0 b
    · have heq : (Prod.mk t) ⁻¹'
          {p : ℝ × H | p.1 ∈ Ioo 0 b ∧ p.1⁻¹ • p.2 ∈ S} = t • S := by
        ext y
        simp only [mem_preimage, mem_setOf_eq, ht, true_and,
          mem_smul_set_iff_inv_smul_mem₀ ht.1.ne']
      rw [heq, indicator_of_mem ht, Measure.addHaar_smul_of_nonneg volume ht.1.le]
    · have heq : (Prod.mk t) ⁻¹'
          {p : ℝ × H | p.1 ∈ Ioo 0 b ∧ p.1⁻¹ • p.2 ∈ S} = ∅ := by
        ext y
        simp only [mem_preimage, mem_setOf_eq, ht, false_and, mem_empty_iff_false]
      rw [heq, measure_empty, indicator_of_notMem ht]
  have hpower (d : ℕ) :
      (∫⁻ t in Ioo (0 : ℝ) b, ENNReal.ofReal (t ^ d)) =
        ENNReal.ofReal (b ^ (d + 1) / (d + 1)) := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
      ← ofReal_integral_eq_lintegral_ofReal (intervalIntegral.intervalIntegrable_pow d).1,
      ← intervalIntegral.integral_of_le hb.le, integral_pow]
    · simp only [zero_pow (Nat.succ_ne_zero d), sub_zero]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact pow_nonneg ht.1.le d
  rw [Measure.volume_eq_prod, Measure.prod_apply hcone]
  simp_rw [hsection]
  rw [lintegral_indicator measurableSet_Ioo,
    lintegral_mul_const _ (by fun_prop), hpower]

end HarmonicMaps
end
