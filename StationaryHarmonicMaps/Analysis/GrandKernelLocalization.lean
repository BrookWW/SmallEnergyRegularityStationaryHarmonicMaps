module

public import StationaryHarmonicMaps.Analysis.SmoothGrandMaximalMeasurability

/-!
# Actual localized tests controlled by the smooth grand maximal field

A compact test with its actual derivative bound is divided by its
positive scale factor. The resulting literal kernel is admissible in
the original grand supremum. Restoring the factor gives the localized
pairing estimate used for Calderon--Zygmund cutoff averages.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original grand kernel field controls each actual compact smooth test after its genuine derivative normalization. -/
theorem smooth_grand_kernel_localized_pairing_le {n : ℕ} (f : Domain n → ℝ) :
    let J := fun a => ⨆ r : PositiveRadius, ⨆ κ : Domain n → ℝ,
      ⨆ (_ : ContDiff ℝ ∞ κ), ⨆ (_ : HasCompactSupport κ),
      ⨆ (_ : tsupport κ⊆Metric.ball a r.val),
      ⨆ (_ : ∀ x∈Metric.ball a r.val,∀ i : Fin n,
        |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤r.val^(-(n : ℝ)-1)),
        ENNReal.ofReal |∫ x,κ x*f x|
    ∀ (a : Domain n) (r B : ℝ),0<r → 0<B →
      ∀ (κ : Domain n → ℝ),ContDiff ℝ ∞ κ → HasCompactSupport κ →
        tsupport κ⊆Metric.ball a r →
        (∀ x∈Metric.ball a r,∀ i : Fin n,
          |fderiv ℝ κ x (EuclideanSpace.single i 1)|≤B) →
        ENNReal.ofReal |∫ x,κ x*f x|≤ENNReal.ofReal (B*r^(n+1))*J a := by
  intro J a r B hr hB κ hκ hcκ hsκ hDκ
  let A : ℝ := B*r^(n+1)
  have hA : 0<A := mul_pos hB (pow_pos hr _)
  let φ := fun x=>A⁻¹*κ x
  have hφ : ContDiff ℝ ∞ φ := contDiff_const.mul hκ
  have hcφ : HasCompactSupport φ := hcκ.mul_left (f := fun _ : Domain n=>A⁻¹)
  have hsφ : tsupport φ⊆Metric.ball a r := (tsupport_mul_subset_right (f := fun _ : Domain n=>A⁻¹) (g := κ)).trans hsκ
  have hExponent : r^(-(n : ℝ)-1)=(r^(n+1))⁻¹ := by
    rw [show -(n : ℝ)-1=-((n+1 : ℕ) : ℝ) by push_cast;ring,
      Real.rpow_neg hr.le,Real.rpow_natCast]
  have hDφ (x : Domain n) (hx : x∈Metric.ball a r) (i : Fin n) :
      |fderiv ℝ φ x (EuclideanSpace.single i 1)|≤r^(-(n : ℝ)-1) := by
    rw [fderiv_const_mul (hκ.differentiable (by simp) x) A⁻¹]
    change |A⁻¹*fderiv ℝ κ x (EuclideanSpace.single i 1)|≤_
    rw [abs_mul,abs_inv,abs_of_pos hA,hExponent]
    calc
      _ ≤ A⁻¹*B := mul_le_mul_of_nonneg_left (hDκ x hx i) (inv_nonneg.mpr hA.le)
      _ = _ := by dsimp only [A];field_simp [hB.ne',hr.ne']
  have hEntry : ENNReal.ofReal |∫ x,φ x*f x|≤J a :=
    le_iSup_of_le (⟨r,hr⟩ : PositiveRadius) (le_iSup_of_le φ (le_iSup_of_le hφ
      (le_iSup_of_le hcφ (le_iSup_of_le hsφ (le_iSup_of_le hDφ le_rfl)))))
  have hInt : (∫ x,φ x*f x)=A⁻¹*(∫ x,κ x*f x) := by
    dsimp only [φ]
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  have hRestore : ENNReal.ofReal A*ENNReal.ofReal |∫ x,φ x*f x|=
      ENNReal.ofReal |∫ x,κ x*f x| := by
    rw [hInt,abs_mul,abs_inv,abs_of_pos hA,← ENNReal.ofReal_mul hA.le]
    congr 1
    rw [← mul_assoc,mul_inv_cancel₀ hA.ne',one_mul]
  rw [← hRestore]
  exact mul_le_mul_of_nonneg_left hEntry zero_le

end StationaryHarmonicMaps.Analysis

end
