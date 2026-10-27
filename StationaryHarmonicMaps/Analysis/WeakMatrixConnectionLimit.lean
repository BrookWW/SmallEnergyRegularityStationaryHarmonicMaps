module

public import StationaryHarmonicMaps.Analysis.BoundedBilinearWeakL2
public import StationaryHarmonicMaps.Analysis.OperatorCoefficientCoordinates
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Weak limits of actual encoded matrix connections

The same continuous decoder and encoder carry the products throughout.
Bounded strong frame coefficients and actual energy-bounded weak derivative
and potential coefficients produce the weak limit of the encoded connection.
The intermediate right product has its energy bound proved from the actual
bilinear operator and the original potential energy.
-/

public section

open HarmonicMaps MeasureTheory Filter
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- Actual encoded connections have the expected weak L² limit under bounded strong frame convergence. -/
theorem weak_L2_limit_matrix_connection_encoding {n m q : ℕ} (μ : Measure (Domain n))
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient m)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀ T, R (E T) = T)
    (P : ℕ → Domain n → Ambient m) (Q : Domain n → Ambient m)
    (hP : ∀ k, MemLp (P k) 2 μ) (hQ : MemLp Q 2 μ)
    (hconv : Tendsto (fun k => eLpNorm (P k - Q) 2 μ) atTop (𝓝 0))
    {B : ℝ} (hbound : ∀ k, ∀ᵐ x ∂μ, ‖P k x‖ ≤ B)
    (D A : ℕ → Domain n → Ambient m) (d a : Domain n → Ambient m)
    (hD : ∀ k, MemLp (D k) 2 μ) (hd : MemLp d 2 μ)
    (hA : ∀ k, MemLp (A k) 2 μ) (ha : MemLp a 2 μ)
    (hweakD : ∀ b : Domain n → Ambient m, MemLp b 2 μ →
      Tendsto (fun k => ∫ x, inner ℝ (D k x) (b x) ∂μ) atTop
        (𝓝 (∫ x, inner ℝ (d x) (b x) ∂μ)))
    (hweakA : ∀ b : Domain n → Ambient m, MemLp b 2 μ →
      Tendsto (fun k => ∫ x, inner ℝ (A k x) (b x) ∂μ) atTop
        (𝓝 (∫ x, inner ℝ (a x) (b x) ∂μ)))
    {MD MA : ℝ} (henergyD : ∀ k, (∫ x, ‖D k x‖ ^ 2 ∂μ) ≤ MD)
    (henergyA : ∀ k, (∫ x, ‖A k x‖ ^ 2 ∂μ) ≤ MA) :
    MemLp (fun x => E (star (R (Q x)) * R (d x) +
      star (R (Q x)) * R (a x) * R (Q x))) 2 μ ∧
    (∀ k, MemLp (fun x => E (star (R (P k x)) * R (D k x) +
      star (R (P k x)) * R (A k x) * R (P k x))) 2 μ) ∧
    ∀ b : Domain n → Ambient m, MemLp b 2 μ →
      Tendsto (fun k => ∫ x, inner ℝ
        (E (star (R (P k x)) * R (D k x) +
          star (R (P k x)) * R (A k x) * R (P k x))) (b x) ∂μ) atTop
        (𝓝 (∫ x, inner ℝ (E (star (R (Q x)) * R (d x) +
          star (R (Q x)) * R (a x) * R (Q x))) (b x) ∂μ)) := by
  let V := Ambient q →L[ℝ] Ambient q
  let C : V →L[ℝ] (V →L[ℝ] V) :=
    ContinuousLinearMap.compL ℝ (Ambient q) (Ambient q) (Ambient q)
  let Adj : V →ₗ[ℝ] V :=
    { toFun := fun S => S.adjoint
      map_add' := by intro S T; exact map_add ContinuousLinearMap.adjoint S T
      map_smul' := by
        intro c S
        simpa only [starRingEnd_apply, star_trivial, RingHom.id_apply] using
          (map_smulₛₗ (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Ambient q)
            (F := Ambient q)) c S) }
  let K : (V →L[ℝ] V) →L[ℝ] (Ambient m →L[ℝ] Ambient m) :=
    ((ContinuousLinearMap.compL ℝ (Ambient m) V (Ambient m)) E).comp
      ((ContinuousLinearMap.compL ℝ (Ambient m) V V).flip R)
  let TL := K.comp (C.comp (Adj.toContinuousLinearMap.comp R))
  let TR := K.comp (C.flip.comp R)
  have hTL (p z : Ambient m) : TL p z = E (star (R p) * R z) := rfl
  have hTR (p z : Ambient m) : TR p z = E (R z * R p) := rfl
  have hleft := bounded_bilinear_weak_L2_limit μ P Q hP hQ hconv hbound
    TL D d hD hd hweakD henergyD
  simp only [hTL] at hleft
  let U (k : ℕ) (x : Domain n) := E (R (A k x) * R (P k x))
  let u (x : Domain n) := E (R (a x) * R (Q x))
  have hright : MemLp u 2 μ ∧ (∀ k, MemLp (U k) 2 μ) ∧
      ∀ b : Domain n → Ambient m, MemLp b 2 μ →
        Tendsto (fun k => ∫ x, inner ℝ (U k x) (b x) ∂μ) atTop
          (𝓝 (∫ x, inner ℝ (u x) (b x) ∂μ)) := by
    simpa only [hTR] using bounded_bilinear_weak_L2_limit μ P Q hP hQ hconv hbound
      TR A a hA ha hweakA henergyA
  have henergyU (k : ℕ) : (∫ x, ‖U k x‖ ^ 2 ∂μ) ≤ (‖TR‖ * |B|) ^ 2 * MA := by
    have H := (bounded_bilinear_L2_energy μ TR (P k) (hP k).aestronglyMeasurable
      (hbound k) (A k) (hA k)).2
    simp only [hTR] at H
    exact H.trans (mul_le_mul_of_nonneg_left (henergyA k) (sq_nonneg _))
  have hconj := bounded_bilinear_weak_L2_limit μ P Q hP hQ hconv hbound
    TL U u hright.2.1 hright.1 hright.2.2 henergyU
  simp only [hTL, U, u, hRE, ← mul_assoc] at hconj
  have hsum : MemLp (fun x => E (star (R (Q x)) * R (d x) +
      star (R (Q x)) * R (a x) * R (Q x))) 2 μ := by
    exact MemLp.ae_eq (Eventually.of_forall fun x => (map_add E _ _).symm)
      (hleft.1.add hconj.1)
  have hsums (k : ℕ) : MemLp (fun x => E (star (R (P k x)) * R (D k x) +
      star (R (P k x)) * R (A k x) * R (P k x))) 2 μ := by
    exact MemLp.ae_eq (Eventually.of_forall fun x => (map_add E _ _).symm)
      ((hleft.2.1 k).add (hconj.2.1 k))
  refine ⟨hsum, hsums, ?_⟩
  intro b hb
  have heq (S T : Domain n → Ambient m) (hS : MemLp S 2 μ) (hT : MemLp T 2 μ) :
      (∫ x, inner ℝ (S x + T x) (b x) ∂μ) =
        (∫ x, inner ℝ (S x) (b x) ∂μ) + (∫ x, inner ℝ (T x) (b x) ∂μ) := by
    simp_rw [inner_add_left]
    exact integral_add (HolderToCK.integrable_inner_of_memLp_two hS hb)
      (HolderToCK.integrable_inner_of_memLp_two hT hb)
  have H := (hleft.2.2 b hb).add (hconj.2.2 b hb)
  simp only [map_add]
  simpa only [heq _ _ (hleft.2.1 _) (hconj.2.1 _), heq _ _ hleft.1 hconj.1] using H

end StationaryHarmonicMaps.Analysis

end
