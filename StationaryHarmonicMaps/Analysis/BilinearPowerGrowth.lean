module

public import StationaryHarmonicMaps.Analysis.BoundedNativeBilinearProduct
public import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds
import StationaryHarmonicMaps.Analysis.BoundedBilinearWeakL2
import HolderToCK.Analysis.Harmonic.GradientVariance

/-!
# Actual power growth of bounded native bilinear products

The same literal Leibniz graph has its quantitative full-HS energy bound
on every original truncated query. Its coefficient is explicit and does
not depend on a Euclidean encoding or on the target dimensions.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

private theorem bounded_bilinear_HS_energy {X : Type*} [MeasurableSpace X]
    {n m k q : ℕ} (μ : Measure X)
    (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q))
    (u : X → Ambient m) (hu : AEStronglyMeasurable u μ) (M : ℝ)
    (hBound : ∀ᵐ x ∂μ, ‖u x‖ ≤ M)
    (F : X → Gradient n k) (hF : ∀ i, MemLp (fun x => F x i) 2 μ) :
    (∀ i, MemLp (fun x => B (u x) (F x i)) 2 μ) ∧
    (∫ x, hsNormSq (fun i => B (u x) (F x i)) ∂μ) ≤
      (‖B‖ * |M|)^2 * (∫ x, hsNormSq (F x) ∂μ) := by
  have hColumn (i : Fin n) := bounded_bilinear_L2_energy μ B u hu hBound (fun x => F x i) (hF i)
  refine ⟨fun i => (hColumn i).1, ?_⟩
  change (∫ x, ∑ i : Fin n, ‖B (u x) (F x i)‖^2 ∂μ) ≤
    (‖B‖ * |M|)^2 * (∫ x, ∑ i : Fin n, ‖F x i‖^2 ∂μ)
  rw [integral_finsetSum _ (fun i _ => (hColumn i).1.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)),
    integral_finsetSum _ (fun i _ => (hF i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)),
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => (hColumn i).2)

/-- The actual bounded native bilinear product has its literal Leibniz
gradient, an original-value bound and the quantitative all-query power
growth coefficient `2*‖B‖²*(Mu²*Kv+Mv²*Ku)`. -/
theorem bounded_native_bilinear_power_growth_ball {n m k q : ℕ}
    (a : Domain n) (r : ℝ) (hr : 0 < r)
    (u : Domain n → Ambient m) (Du : Domain n → Gradient n m)
    (hu : MemW12 (ballDomain a r) u Du) (Mu : ℝ)
    (huBound : ∀ᵐ x ∂volume.restrict (ball a r), ‖u x‖ ≤ Mu)
    (v : Domain n → Ambient k) (Dv : Domain n → Gradient n k)
    (hv : MemW12 (ballDomain a r) v Dv) (Mv : ℝ)
    (hvBound : ∀ᵐ x ∂volume.restrict (ball a r), ‖v x‖ ≤ Mv)
    (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q))
    (ν Ku Kv : ℝ) (hKu : 0 ≤ Ku) (hKv : 0 ≤ Kv)
    (hGrowthU : ∀ x, x ∈ ball a r → ∀ s : ℝ, 0 < s →
      (∫ y in ball x s ∩ ball a r, hsNormSq (Du y)) ≤ Ku * s^ν)
    (hGrowthV : ∀ x, x ∈ ball a r → ∀ s : ℝ, 0 < s →
      (∫ y in ball x s ∩ ball a r, hsNormSq (Dv y)) ≤ Kv * s^ν) :
    let W := fun x => B (u x) (v x)
    let DW := fun x i => B (Du x i) (v x) + B (u x) (Dv x i)
    MemW12 (ballDomain a r) W DW ∧
      (∀ᵐ x ∂volume.restrict (ball a r), ‖W x‖ ≤ ‖B‖ * |Mu| * |Mv|) ∧
      0 ≤ 2 * ‖B‖^2 * (Mu^2 * Kv + Mv^2 * Ku) ∧
      ∀ x, x ∈ ball a r → ∀ s : ℝ, 0 < s →
        IntegrableOn (fun y => hsNormSq (DW y)) (ball x s ∩ ball a r) volume ∧
        (∫ y in ball x s ∩ ball a r, hsNormSq (DW y)) ≤
          (2 * ‖B‖^2 * (Mu^2 * Kv + Mv^2 * Ku)) * s^ν := by
  intro W DW
  have hW : MemW12 (ballDomain a r) W DW :=
    memW12_bounded_bilinear_product_ball a r hr u Du hu Mu huBound v Dv hv Mv hvBound B
  refine ⟨hW, ?_, ?_, ?_⟩
  · filter_upwards [huBound,hvBound] with x hx hy
    change ‖B (u x) (v x)‖ ≤ _
    calc
      _ ≤ ‖B (u x)‖ * ‖v x‖ := (B (u x)).le_opNorm _
      _ ≤ (‖B‖ * |Mu|) * |Mv| := mul_le_mul
        ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hx.trans (le_abs_self Mu)) (norm_nonneg B)))
        (hy.trans (le_abs_self Mv)) (norm_nonneg (v x)) (mul_nonneg (norm_nonneg B) (abs_nonneg Mu))
  · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (add_nonneg (mul_nonneg (sq_nonneg _) hKv) (mul_nonneg (sq_nonneg _) hKu))
  · intro x hx s hs
    let S := ball x s ∩ ball a r
    let μ := volume.restrict S
    have hSub : S ⊆ ball a r := inter_subset_right
    have hUM : MemLp u 2 μ := hu.2.1.mono_measure (Measure.restrict_mono_set volume hSub)
    have hVM : MemLp v 2 μ := hv.2.1.mono_measure (Measure.restrict_mono_set volume hSub)
    have hDu (i : Fin n) : MemLp (fun y => Du y i) 2 μ :=
      (hu.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)
    have hDv (i : Fin n) : MemLp (fun y => Dv y i) 2 μ :=
      (hv.2.2 i).mono_measure (Measure.restrict_mono_set volume hSub)
    have hUB : ∀ᵐ y ∂μ, ‖u y‖ ≤ Mu :=
      huBound.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub))
    have hVB : ∀ᵐ y ∂μ, ‖v y‖ ≤ Mv :=
      hvBound.filter_mono (ae_mono (Measure.restrict_mono_set volume hSub))
    let X := fun y i => B (Du y i) (v y)
    let Y := fun y i => B (u y) (Dv y i)
    have hX : (∀ i, MemLp (fun y => X y i) 2 μ) ∧
        (∫ y, hsNormSq (X y) ∂μ) ≤ (‖B‖ * |Mv|)^2 * (∫ y, hsNormSq (Du y) ∂μ) := by
      simpa only [ContinuousLinearMap.flip_apply,ContinuousLinearMap.opNorm_flip] using
        bounded_bilinear_HS_energy μ B.flip v hVM.aestronglyMeasurable Mv hVB Du hDu
    have hY := bounded_bilinear_HS_energy μ B u hUM.aestronglyMeasurable Mu hUB Dv hDv
    have hXI : Integrable (fun y => hsNormSq (X y)) μ := integrable_hsNormSq_of_columns X hX.1
    have hYI : Integrable (fun y => hsNormSq (Y y)) μ := integrable_hsNormSq_of_columns Y hY.1
    have hWI : IntegrableOn (fun y => hsNormSq (DW y)) S volume := hW.integrable_hsNormSq.mono_set hSub
    refine ⟨hWI, ?_⟩
    calc
      _ ≤ ∫ y, 2 * hsNormSq (X y) + 2 * hsNormSq (Y y) ∂μ :=
        integral_mono hWI ((hXI.const_mul 2).add (hYI.const_mul 2))
          (fun y => HolderToCK.hsNormSq_add_le (X y) (Y y))
      _ = 2 * (∫ y, hsNormSq (X y) ∂μ) + 2 * (∫ y, hsNormSq (Y y) ∂μ) := by
        rw [integral_add (hXI.const_mul 2) (hYI.const_mul 2),integral_const_mul,integral_const_mul]
      _ ≤ 2 * ((‖B‖ * |Mv|)^2 * (∫ y, hsNormSq (Du y) ∂μ)) +
          2 * ((‖B‖ * |Mu|)^2 * (∫ y, hsNormSq (Dv y) ∂μ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hX.2 (by norm_num))
          (mul_le_mul_of_nonneg_left hY.2 (by norm_num))
      _ ≤ 2 * ((‖B‖ * |Mv|)^2 * (Ku * s^ν)) + 2 * ((‖B‖ * |Mu|)^2 * (Kv * s^ν)) :=
        add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hGrowthU x hx s hs) (sq_nonneg _)) (by norm_num))
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hGrowthV x hx s hs) (sq_nonneg _)) (by norm_num))
      _ = _ := by rw [mul_pow,mul_pow,sq_abs,sq_abs]; ring

end StationaryHarmonicMaps.Analysis

end
