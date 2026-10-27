module

public import StationaryHarmonicMaps.Analysis.BoundedL2MultiplierContinuity
public import StationaryHarmonicMaps.Analysis.WeakStrongPairing
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Weak L² products with bounded strongly convergent coefficients

A genuine continuous bilinear map acts on a bounded strong L² coefficient
and an energy-bounded weak L² field. Its transpose transforms every fixed
L² test into a strongly convergent L² test. The resulting product therefore
converges against every actual L² field.
-/

public section

open HarmonicMaps MeasureTheory Filter
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- A genuine bounded coefficient gives the actual L² product and its squared-energy bound. -/
theorem bounded_bilinear_L2_energy {X : Type*} [MeasurableSpace X] {m d e : ℕ}
    (μ : Measure X) (T : Ambient m →L[ℝ] (Ambient d →L[ℝ] Ambient e))
    (p : X → Ambient m) (hp : AEStronglyMeasurable p μ)
    {B : ℝ} (hb : ∀ᵐ x ∂μ, ‖p x‖ ≤ B)
    (f : X → Ambient d) (hf : MemLp f 2 μ) :
    MemLp (fun x => T (p x) (f x)) 2 μ ∧
      (∫ x, ‖T (p x) (f x)‖ ^ 2 ∂μ) ≤
        (‖T‖ * |B|) ^ 2 * (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  have hm := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    ((T.continuous.comp_aestronglyMeasurable hp).prodMk hf.aestronglyMeasurable)
  have hbound : ∀ᵐ x ∂μ, ‖T (p x) (f x)‖ ≤ (‖T‖ * |B|) * ‖f x‖ := by
    filter_upwards [hb] with x hx
    calc
      _ ≤ ‖T (p x)‖ * ‖f x‖ := (T (p x)).le_opNorm _
      _ ≤ (‖T‖ * ‖p x‖) * ‖f x‖ :=
        mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
      _ ≤ (‖T‖ * |B|) * ‖f x‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hx.trans (le_abs_self B)) (norm_nonneg T)) (norm_nonneg (f x))
  have hprod : MemLp (fun x => T (p x) (f x)) 2 μ := hf.of_le_mul hm hbound
  refine ⟨hprod, ?_⟩
  rw [← integral_const_mul]
  apply integral_mono_ae
    (hprod.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
    ((hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul _)
  filter_upwards [hbound] with x hx
  exact (pow_le_pow_left₀ (norm_nonneg _) hx 2).trans_eq (mul_pow _ _ _)

/-- A bounded strong coefficient and an energy-bounded weak field give the same bilinear weak limit. -/
theorem bounded_bilinear_weak_L2_limit {n m d e : ℕ} (μ : Measure (Domain n))
    (P : ℕ → Domain n → Ambient m) (Q : Domain n → Ambient m)
    (hP : ∀ k, MemLp (P k) 2 μ) (hQ : MemLp Q 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (P k - Q) 2 μ) atTop (𝓝 0))
    {B : ℝ} (hbound : ∀ k, ∀ᵐ x ∂μ, ‖P k x‖ ≤ B)
    (T : Ambient m →L[ℝ] (Ambient d →L[ℝ] Ambient e))
    (F : ℕ → Domain n → Ambient d) (f : Domain n → Ambient d)
    (hF : ∀ k, MemLp (F k) 2 μ) (hf : MemLp f 2 μ)
    (hweak : ∀ b : Domain n → Ambient d, MemLp b 2 μ →
      Tendsto (fun k => ∫ x, inner ℝ (F k x) (b x) ∂μ) atTop
        (𝓝 (∫ x, inner ℝ (f x) (b x) ∂μ)))
    {M : ℝ} (henergy : ∀ k, (∫ x, ‖F k x‖ ^ 2 ∂μ) ≤ M) :
    MemLp (fun x => T (Q x) (f x)) 2 μ ∧
      (∀ k, MemLp (fun x => T (P k x) (F k x)) 2 μ) ∧
      ∀ b : Domain n → Ambient e, MemLp b 2 μ →
        Tendsto (fun k => ∫ x, inner ℝ (T (P k x) (F k x)) (b x) ∂μ) atTop
          (𝓝 (∫ x, inner ℝ (T (Q x) (f x)) (b x) ∂μ)) := by
  have hQbound := ae_norm_le_of_bounded_L2_limit μ P Q hP hQ hconv hbound
  have hproduct (p : Domain n → Ambient m) (hp : MemLp p 2 μ)
      (hb : ∀ᵐ x ∂μ, ‖p x‖ ≤ B) (v : Domain n → Ambient d) (hv : MemLp v 2 μ) :
      MemLp (fun x => T (p x) (v x)) 2 μ := by
    exact (bounded_bilinear_L2_energy μ T p hp.aestronglyMeasurable hb v hv).1
  refine ⟨hproduct Q hQ hQbound f hf,
    fun k => hproduct (P k) (hP k) (hbound k) (F k) (hF k), ?_⟩
  intro b hb
  let A : (Ambient d →L[ℝ] Ambient e) →ₗ[ℝ] (Ambient e →L[ℝ] Ambient d) :=
    { toFun := fun C => C.adjoint
      map_add' := by intro C D; exact map_add ContinuousLinearMap.adjoint C D
      map_smul' := by
        intro c C
        simpa only [starRingEnd_apply, star_trivial, RingHom.id_apply] using
          (map_smulₛₗ (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Ambient d)
            (F := Ambient e)) c C) }
  let L := (A.toContinuousLinearMap.comp T).flip
  have hL (v : Ambient e) (p : Ambient m) : L v p = (T p).adjoint v := rfl
  have hA : MemLp (fun x => L (b x)) 2 μ := L.lipschitz.comp_memLp (map_zero L) hb
  obtain ⟨_hQb, hg, hG, _hDiff, hstrong⟩ := bounded_L2_limit_fixed_operator_L2
    μ P Q hP hQ hconv hbound (fun x => L (b x)) hA
  simp only [map_sub] at hstrong
  have H := tendsto_integral_inner_of_weak_and_strong_L2 μ F
    (fun k x => L (b x) (P k x)) f (fun x => L (b x) (Q x)) hF hG hf hg hweak hstrong henergy
  simpa only [hL, ContinuousLinearMap.adjoint_inner_right] using H

end StationaryHarmonicMaps.Analysis

end
