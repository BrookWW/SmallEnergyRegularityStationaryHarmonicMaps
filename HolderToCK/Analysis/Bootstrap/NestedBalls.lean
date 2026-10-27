module

public import HolderToCK.Analysis.Poisson.InteriorLocalization
public import HolderToCK.Analysis.Bootstrap.QuadraticComposition
public import HolderToCK.Analysis.Bootstrap.CoordinateRegularity
public import HolderToCK.Analysis.Bootstrap.CoordinateNorms

/-! # One quantitative derivative upgrade of the same quadratic Poisson map

The actual weak equation gives every differentiated coordinate equation.
Schauder estimates raise their regularity by two orders. Combining the same
coordinate words recovers native derivatives with the original Holder exponent.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK

theorem quadratic_poisson_nested_step (n q m : ℕ) (hn : 2 ≤ n) (hm : 1 ≤ m)
    (γ : ℝ) (hγ : 0 < γ) (hγOne : γ < 1)
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    (hA : ContDiff ℝ ∞ A) (c : Ambient q) (R s t M : ℝ)
    (hs : 0 < s) (hst : s < t) (hM : 0 ≤ M) :
    ∃ M' : ℝ, 0 ≤ M' ∧ M ≤ M' ∧ ∀ (u : Domain n → Ambient q) (δ : ℝ),
      0 ≤ δ → δ ≤ 1 →
      ContDiffOn ℝ m u (Metric.ball (0 : Domain n) t) →
      MapsTo u (Metric.ball (0 : Domain n) t) (Metric.closedBall c R) →
      WeakPoissonOn (ballDomain (0 : Domain n) t)
        (fun x i => fderiv ℝ u x (EuclideanSpace.single i 1)) (classicalQuadraticForcing A u) →
      (∀ x ∈ Metric.ball (0 : Domain n) t, ‖u x - u 0‖ ≤ M * δ) →
      (∀ x ∈ Metric.ball (0 : Domain n) t, ∀ j : ℕ, 1 ≤ j → j ≤ m →
        ‖iteratedFDeriv ℝ j u x‖ ≤ M * δ) →
      HolderBoundOn (Metric.ball (0 : Domain n) t) (iteratedFDeriv ℝ m u) γ (M * δ) →
      ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) u (Metric.ball (0 : Domain n) s) ∧
      (∀ x ∈ Metric.ball (0 : Domain n) s, ‖u x - u 0‖ ≤ M' * δ) ∧
      (∀ x ∈ Metric.ball (0 : Domain n) s, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 →
        ‖iteratedFDeriv ℝ j u x‖ ≤ M' * δ) ∧
      HolderBoundOn (Metric.ball (0 : Domain n) s) (iteratedFDeriv ℝ (m + 1) u) γ (M' * δ) := by
  obtain ⟨B, hB⟩ := classicalQuadraticForcing_compact_bounds (n := n) A hA c R
  obtain ⟨S, hS, hSch⟩ := poissonInteriorSchauder_nested n q hn γ hγ hγOne s t hs hst
  let D : ℝ := (2 * t) ^ (1 - γ)
  let M₀ : ℝ := M * max 1 D
  let P₀ := quadraticDerivativeBoundConstant n (m - 1) (B (m - 1) : ℝ) M₀
  let P₁ := quadraticHolderBoundConstant n (m - 1) (B (m - 1) : ℝ) M₀ (M * D)
  have ht : 0 < t := hs.trans hst
  have hD : 0 ≤ D := Real.rpow_nonneg (by positivity) _
  have hM₀ : 0 ≤ M₀ := mul_nonneg hM (le_trans zero_le_one (le_max_left _ _))
  have hP₀ : 0 ≤ P₀ := quadraticDerivativeBoundConstant_nonneg n (m - 1) (B _).property
  have hP₁ : 0 ≤ P₁ := quadraticHolderBoundConstant_nonneg n (m - 1) (B _).property hM₀
    (mul_nonneg hM hD)
  let K : ℝ := S * (M + P₀ + P₁)
  have hK : 0 ≤ K := by positivity
  let M' : ℝ := M + (n : ℝ) ^ (m + 1) * K
  have hM' : 0 ≤ M' := by positivity
  have hMM' : M ≤ M' := by
    dsimp only [M']
    exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) _) hK)
  have hKM' : (n : ℝ) ^ (m + 1) * K ≤ M' := by
    dsimp only [M']; exact le_add_of_nonneg_left hM
  refine ⟨M', hM', hMM', ?_⟩
  intro u δ hδ hδOne hu hRange hEq hzero hderiv hHighest
  let Ω : OpenDomain n := ballDomain (0 : Domain n) t
  let Ω' : OpenDomain n := ballDomain (0 : Domain n) s
  have hsub : Ω'.val ⊆ Ω.val := Metric.ball_subset_ball hst.le
  have horder : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have huLow : ContDiffOn ℝ ((m - 1 + 1 : ℕ) : ℕ∞ω) u Ω.val := by
    simpa only [horder, Ω, ballDomain] using hu
  have hF : ContDiffOn ℝ ((m - 1 : ℕ) : ℕ∞ω) (classicalQuadraticForcing A u) Ω.val :=
    contDiffOn_classicalQuadraticForcing Ω (m - 1)
      (hA.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top _)))) huLow
  have hdiameter : ∀ x ∈ Ω.val, ∀ y ∈ Ω.val, dist x y ≤ 2 * t := by
    intro x hx y hy
    have hx0 : dist x 0 < t := by simpa only [Ω, ballDomain, Metric.mem_ball] using hx
    have h0y : dist 0 y < t := by
      simpa only [Ω, ballDomain, Metric.mem_ball, dist_comm] using hy
    exact (dist_triangle x 0 y).trans (by linarith only [hx0, h0y])
  obtain ⟨hForceNorm, hForceHolder⟩ := hB (m - 1) Ω u huLow (convex_ball 0 t)
    hRange M (2 * t) δ γ hM (by positivity) hδ hδOne hγ.le hγOne.le hdiameter
    (by simpa only [horder, Ω, ballDomain] using hderiv)
    (by rw [horder]; exact hHighest)
    (m - 1) le_rfl
  have hδsq : δ ^ 2 ≤ δ := by nlinarith only [hδ, hδOne]
  have hAmp : S * (M * δ + P₀ * δ ^ 2 + P₁ * δ ^ 2) ≤ K * δ := by
    calc
      _ ≤ S * (M * δ + P₀ * δ + P₁ * δ) := mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hδsq hP₀))
          (mul_le_mul_of_nonneg_left hδsq hP₁)) hS
      _ = _ := by dsimp only [K]; ring
  have hwords : ∀ w : List (Fin n), w.length = m - 1 →
      ContDiffOn ℝ 2 (coordinateWord u w) Ω'.val ∧
      (∀ x ∈ Ω'.val, ‖iteratedFDeriv ℝ 2 (coordinateWord u w) x‖ ≤ K * δ) ∧
      HolderBoundOn Ω'.val (iteratedFDeriv ℝ 2 (coordinateWord u w)) γ (K * δ) := by
    intro w hw
    obtain ⟨hw1, hwW, hwEq⟩ := hEq.coordinate_words Ω huLow hF w hw.le
    have hFw : ContDiffOn ℝ w.length (classicalQuadraticForcing A u) Ω.val := by
      simpa only [hw] using hF
    have hForcew : ∀ x ∈ Ω.val, ‖coordinateWord (classicalQuadraticForcing A u) w x‖ ≤ P₀ * δ ^ 2 := by
      intro x hx
      have h := norm_coordinateWord_le_iteratedFDeriv Ω w hFw x hx
      rw [hw] at h
      exact h.trans (hForceNorm x hx)
    have hHolderw : HolderBoundOn Ω.val (coordinateWord (classicalQuadraticForcing A u) w) γ
        (P₁ * δ ^ 2) := by
      intro x hx y hy
      have h := norm_coordinateWord_sub_le_iteratedFDeriv_sub Ω w hFw x y hx hy
      rw [hw] at h
      exact h.trans (hForceHolder x hx y hy)
    let center : Ambient q := if m = 1 then u 0 else 0
    have hwBound : ∀ x ∈ Ω.val, ‖coordinateWord u w x - center‖ ≤ M * δ := by
      intro x hx
      by_cases hmOne : m = 1
      · have hwNil : w = [] := List.length_eq_zero_iff.mp (by omega)
        rw [hwNil, coordinateWord_nil]
        simpa only [center, if_pos hmOne] using hzero x hx
      · have hmw : 1 ≤ w.length := by omega
        have huWord : ContDiffOn ℝ w.length u Ω.val := hu.of_le (by exact_mod_cast (by omega : w.length ≤ m))
        simp only [center, if_neg hmOne, sub_zero]
        exact (norm_coordinateWord_le_iteratedFDeriv Ω w huWord x hx).trans
          (hderiv x hx w.length hmw (by omega))
    obtain ⟨hw2, hwSup, hwHolder, _⟩ := hSch (coordinateWord u w)
      (fun x i => fderiv ℝ (coordinateWord u w) x (EuclideanSpace.single i 1))
      (coordinateWord (classicalQuadraticForcing A u) w) center
      (M * δ) (P₀ * δ ^ 2) (P₁ * δ ^ 2) hwW hw1.continuousOn hwEq
      (mul_nonneg hM hδ) hwBound (mul_nonneg hP₀ (sq_nonneg δ)) hForcew
      (mul_nonneg hP₁ (sq_nonneg δ)) hHolderw
    have hcentered (x : Domain n) (hx : x ∈ Ω'.val) :
        iteratedFDeriv ℝ 2 (fun y => coordinateWord u w y - center) x =
          iteratedFDeriv ℝ 2 (coordinateWord u w) x := by
      rw [fun_iteratedFDeriv_sub_apply (hw2.contDiffAt (Ω'.property.mem_nhds hx)) contDiffAt_const,
        iteratedFDeriv_const_of_ne two_ne_zero, Pi.zero_apply, sub_zero]
    refine ⟨hw2, ?_, ?_⟩
    · intro x hx
      rw [← hcentered x hx]
      exact (hwSup 2 le_rfl x hx).trans hAmp
    · intro x hx y hy
      exact (hwHolder x hx y hy).trans
        (mul_le_mul_of_nonneg_right hAmp (Real.rpow_nonneg dist_nonneg _))
  have huNext : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) u Ω'.val :=
    contDiffOn_succ_of_coordinate_words_two Ω' m hm (hu.mono hsub)
      (fun w hw => (hwords w hw).1)
  have hlong : ∀ w : List (Fin n), w.length = m + 1 →
      (∀ x ∈ Ω'.val, ‖coordinateWord u w x‖ ≤ K * δ) ∧
      HolderBoundOn Ω'.val (coordinateWord u w) γ (K * δ) := by
    intro w hw
    let v := w.take 2
    let z := w.drop 2
    have hv : v.length = 2 := by dsimp only [v]; rw [List.length_take, hw]; omega
    have hz : z.length = m - 1 := by dsimp only [z]; rw [List.length_drop, hw]; omega
    have heq : w = v ++ z := (List.take_append_drop 2 w).symm
    obtain ⟨hz2, hzSup, hzHolder⟩ := hwords z hz
    have hzv : ContDiffOn ℝ v.length (coordinateWord u z) Ω'.val := by
      simpa only [hv, Nat.cast_ofNat] using hz2
    rw [heq, coordinateWord_append]
    refine ⟨?_, ?_⟩
    · intro x hx
      have h := norm_coordinateWord_le_iteratedFDeriv Ω' v hzv x hx
      rw [hv] at h
      exact h.trans (hzSup x hx)
    · intro x hx y hy
      have h := norm_coordinateWord_sub_le_iteratedFDeriv_sub Ω' v hzv x y hx hy
      rw [hv] at h
      exact h.trans (hzHolder x hx y hy)
  refine ⟨huNext, ?_, ?_, ?_⟩
  · intro x hx
    exact (hzero x (hsub hx)).trans (mul_le_mul_of_nonneg_right hMM' hδ)
  · intro x hx j hj hjm
    rcases Nat.eq_or_lt_of_le hjm with rfl | hjlt
    · exact (norm_iteratedFDeriv_le_of_coordinate_words Ω' (m + 1) huNext
        (mul_nonneg hK hδ) x hx (fun w hw => (hlong w hw).1 x hx)).trans
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hKM' hδ)
    · exact (hderiv x (hsub hx) j hj (by omega)).trans (mul_le_mul_of_nonneg_right hMM' hδ)
  · have h := iteratedFDeriv_holderBoundOn_of_coordinate_words Ω' (m + 1) huNext
      (mul_nonneg hK hδ) (fun w hw => (hlong w hw).2)
    intro x hx y hy
    exact (h x hx y hy).trans (mul_le_mul_of_nonneg_right
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hKM' hδ)
      (Real.rpow_nonneg dist_nonneg _))

end HolderToCK
end
