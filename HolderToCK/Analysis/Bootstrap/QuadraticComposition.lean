module

public import HolderToCK.Analysis.Bootstrap.DerivativeProducts
public import HolderToCK.Analysis.Bootstrap.CoordinateWords
public import HolderToCK.Analysis.Bootstrap.CoefficientBounds

/-! # All-order bounds for the classical quadratic forcing

The forcing uses the actual coordinate columns of the derivative of one map.
Each product estimate retains both gradient factors. Its order-k derivative
is consequently bounded by a finite constant times `delta ^ 2`, under the
same condition `0 <= delta <= 1` at every order.
-/

public section

open HarmonicMaps Set
open scoped ContDiff NNReal

namespace HolderToCK

/-- The quadratic forcing formed from the classical gradient of the map. -/
@[expose] noncomputable def classicalQuadraticForcing {n q : ℕ}
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    (u : Domain n → Ambient q) (x : Domain n) : Ambient q :=
  ∑ i : Fin n, A (u x) (fderiv ℝ u x (EuclideanSpace.single i 1))
    (fderiv ℝ u x (EuclideanSpace.single i 1))

/-- A finite derivative bound, with C bounding the coefficient derivatives
through order k. The maximum permits all nonnegative sizes of M. -/
@[expose] def quadraticDerivativeBoundConstant (n k : ℕ) (C M : ℝ) : ℝ :=
  (n : ℝ) * (4 : ℝ) ^ k * (k.factorial : ℝ) * C * (max 1 M) ^ k * M ^ 2

theorem quadraticDerivativeBoundConstant_nonneg (n k : ℕ) {C M : ℝ}
    (hC : 0 ≤ C) : 0 ≤ quadraticDerivativeBoundConstant n k C M := by
  unfold quadraticDerivativeBoundConstant
  positivity

theorem compact_coefficient_uniform_bounds {q : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Ambient q → E) (hA : ContDiff ℝ ∞ A) (c : Ambient q) (R : ℝ) :
    ∃ C : ℕ → ℝ≥0,
      (∀ k : ℕ, ∀ j, j ≤ k → ∀ z ∈ Metric.closedBall c R,
        ‖iteratedFDeriv ℝ j A z‖ ≤ (C k : ℝ)) ∧
      ∀ k : ℕ, ∀ j, j ≤ k → ∀ x ∈ Metric.closedBall c R,
        ∀ y ∈ Metric.closedBall c R,
        ‖iteratedFDeriv ℝ j A x - iteratedFDeriv ℝ j A y‖ ≤
          (C k : ℝ) * ‖x - y‖ := by
  obtain ⟨b, hb, hLip⟩ := compact_coefficient_derivative_bounds A hA c R
  let C : ℕ → ℝ≥0 := fun k => ∑ i ∈ Finset.range (k + 2), b i
  have hentry (k j : ℕ) (hj : j < k + 2) : (b j : ℝ) ≤ (C k : ℝ) := by
    dsimp only [C]
    simp only [NNReal.coe_sum]
    exact Finset.single_le_sum (fun i _ => (b i).property)
      (Finset.mem_range.mpr hj)
  refine ⟨C, ?_, ?_⟩
  · intro k j hj z hz
    exact (hb j z hz).trans (hentry k j (by omega))
  · intro k j hj x hx y hy
    exact (hLip j x hx y hy).trans
      (mul_le_mul_of_nonneg_right (hentry k (j + 1) (by omega)) (norm_nonneg _))

theorem contDiffOn_classicalQuadraticForcing {n q : ℕ} (Ω : OpenDomain n)
    {A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q}
    {u : Domain n → Ambient q} (k : ℕ) (hA : ContDiff ℝ k A)
    (hu : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) u Ω.val) :
    ContDiffOn ℝ k (classicalQuadraticForcing A u) Ω.val := by
  have hco : ContDiffOn ℝ k (A ∘ u) Ω.val :=
    hA.comp_contDiffOn (hu.of_le (by exact_mod_cast Nat.le_succ k))
  have hcol (i : Fin n) : ContDiffOn ℝ k
      (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) Ω.val :=
    (hu.fderiv_of_isOpen Ω.property (by norm_cast)).clm_apply contDiffOn_const
  exact ContDiffOn.sum (fun i _ => (hco.clm_apply (hcol i)).clm_apply (hcol i))

theorem norm_iteratedFDeriv_coefficient_comp_le_uniform {n q : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : OpenDomain n) {A : Ambient q → E} {u : Domain n → Ambient q}
    (k : ℕ) (hA : ContDiff ℝ k A) (hu : ContDiffOn ℝ k u Ω.val)
    (x : Domain n) (hx : x ∈ Ω.val) {C M δ : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hδone : δ ≤ 1)
    (hAderiv : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i A (u x)‖ ≤ C)
    (huderiv : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i u x‖ ≤ M * δ) :
    ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i (A ∘ u) x‖ ≤
      (k.factorial : ℝ) * C * (max 1 M) ^ k := by
  intro i hik
  have hD : 1 ≤ max 1 M := le_max_left _ _
  have hMi : ∀ j, 1 ≤ j → j ≤ i → ‖iteratedFDeriv ℝ j u x‖ ≤ (max 1 M) ^ j := by
    intro j hj hji
    calc
      _ ≤ M * δ := huderiv j hj (hji.trans hik)
      _ ≤ M := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hδone hM
      _ ≤ max 1 M := le_max_right _ _
      _ ≤ (max 1 M) ^ j := by simpa only [pow_one] using pow_le_pow_right₀ hD hj
  calc
    _ ≤ (i.factorial : ℝ) * C * (max 1 M) ^ i :=
      norm_iteratedFDeriv_comp_on_open Ω i
        (hA.of_le (by exact_mod_cast hik)) (hu.of_le (by exact_mod_cast hik)) x hx
        (fun j hj => hAderiv j (hj.trans hik)) hMi
    _ ≤ (k.factorial : ℝ) * C * (max 1 M) ^ k :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hik) hC)
        (pow_le_pow_right₀ hD hik) (by positivity) (by positivity)

/-- A uniform Holder constant for the coefficient composition through order k.
The recurrence contains only finite sums and products of the displayed data. -/
@[expose] def coefficientCompositionHolderConstant (C M L : ℝ) : ℕ → ℝ
  | 0 => C * L
  | k + 1 => coefficientCompositionHolderConstant C M L k +
      (2 : ℝ) ^ k * M * (coefficientCompositionHolderConstant C M L k +
        (k.factorial : ℝ) * C * (max 1 M) ^ k)

theorem coefficientCompositionHolderConstant_nonneg {C M L : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hL : 0 ≤ L) (k : ℕ) :
    0 ≤ coefficientCompositionHolderConstant C M L k := by
  induction k with
  | zero => exact mul_nonneg hC hL
  | succ k ih =>
      change 0 ≤ coefficientCompositionHolderConstant C M L k + _
      positivity

theorem coefficientCompositionHolderConstant_mono {C M L : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    Monotone (coefficientCompositionHolderConstant C M L) := by
  apply monotone_nat_of_le_succ
  intro k
  change coefficientCompositionHolderConstant C M L k ≤
    coefficientCompositionHolderConstant C M L k + _
  apply le_add_of_nonneg_right
  have hH := coefficientCompositionHolderConstant_nonneg hC hM hL k
  positivity

theorem iteratedFDeriv_coefficient_comp_holderBoundOn {n q : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : OpenDomain n) {A : Ambient q → E} {u : Domain n → Ambient q}
    (k : ℕ) (hA : ContDiff ℝ k A) (hu : ContDiffOn ℝ k u Ω.val)
    {C M L δ γ : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hAderiv : ∀ x ∈ Ω.val, ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i A (u x)‖ ≤ C)
    (hALip : ∀ x ∈ Ω.val, ∀ y ∈ Ω.val, ∀ i, i ≤ k →
      ‖iteratedFDeriv ℝ i A (u x) - iteratedFDeriv ℝ i A (u y)‖ ≤ C * ‖u x - u y‖)
    (huderiv : ∀ x ∈ Ω.val, ∀ i, 1 ≤ i → i ≤ k →
      ‖iteratedFDeriv ℝ i u x‖ ≤ M * δ)
    (huHolder : HolderBoundOn Ω.val u γ (L * δ))
    (huderivHolder : ∀ i, 1 ≤ i → i ≤ k →
      HolderBoundOn Ω.val (iteratedFDeriv ℝ i u) γ (M * δ)) :
    ∀ i, i ≤ k → HolderBoundOn Ω.val (iteratedFDeriv ℝ i (A ∘ u)) γ
      (coefficientCompositionHolderConstant C M L k * δ) := by
  induction k generalizing E with
  | zero =>
      intro i hi x hx y hy
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      rw [norm_iteratedFDeriv_zero_sub]
      calc
        _ ≤ C * ‖u x - u y‖ := by
          simpa only [norm_iteratedFDeriv_zero_sub, Function.comp_apply] using hALip x hx y hy 0 le_rfl
        _ ≤ C * ((L * δ) * Real.rpow (dist x y) γ) :=
          mul_le_mul_of_nonneg_left (huHolder x hx y hy) hC
        _ = _ := by
          change C * ((L * δ) * (dist x y) ^ γ) = (C * L * δ) * (dist x y) ^ γ
          ring
  | succ k ih =>
      have huLow : ContDiffOn ℝ k u Ω.val := hu.of_le (by exact_mod_cast Nat.le_succ k)
      have hAlow : ContDiff ℝ k A := hA.of_le (by exact_mod_cast Nat.le_succ k)
      have hA' : ContDiff ℝ k (fderiv ℝ A) := hA.fderiv_right (by norm_cast)
      have hdu : ContDiffOn ℝ k (fderiv ℝ u) Ω.val :=
        hu.fderiv_of_isOpen Ω.property (by norm_cast)
      have hA'Bound : ∀ x ∈ Ω.val, ∀ j, j ≤ k →
          ‖iteratedFDeriv ℝ j (fderiv ℝ A) (u x)‖ ≤ C := by
        intro x hx j hj
        rw [norm_iteratedFDeriv_fderiv]
        exact hAderiv x hx (j + 1) (Nat.add_le_add_right hj 1)
      have hA'Lip : ∀ x ∈ Ω.val, ∀ y ∈ Ω.val, ∀ j, j ≤ k →
          ‖iteratedFDeriv ℝ j (fderiv ℝ A) (u x) -
            iteratedFDeriv ℝ j (fderiv ℝ A) (u y)‖ ≤ C * ‖u x - u y‖ := by
        intro x hx y hy j hj
        rw [norm_iteratedFDeriv_fderiv_sub]
        exact hALip x hx y hy (j + 1) (Nat.add_le_add_right hj 1)
      have hcoHolder : ∀ j, j ≤ k →
          HolderBoundOn Ω.val (iteratedFDeriv ℝ j ((fderiv ℝ A) ∘ u)) γ
            (coefficientCompositionHolderConstant C M L k * δ) := by
        apply ih hA' huLow hA'Bound hA'Lip
        · exact fun x hx j hj hjk => huderiv x hx j hj (hjk.trans (Nat.le_succ k))
        · exact fun j hj hjk => huderivHolder j hj (hjk.trans (Nat.le_succ k))
      let K : ℝ := (k.factorial : ℝ) * C * (max 1 M) ^ k
      let H : ℝ := coefficientCompositionHolderConstant C M L k
      have hK : 0 ≤ K := by dsimp only [K]; positivity
      have hH : 0 ≤ H := coefficientCompositionHolderConstant_nonneg hC hM hL k
      have hcoBound : ∀ x ∈ Ω.val, ∀ j, j ≤ k →
          ‖iteratedFDeriv ℝ j ((fderiv ℝ A) ∘ u) x‖ ≤ K := by
        intro x hx
        exact norm_iteratedFDeriv_coefficient_comp_le_uniform Ω k hA' huLow x hx
          hC hM hδone (hA'Bound x hx)
          (fun j hj hjk => huderiv x hx j hj (hjk.trans (Nat.le_succ k)))
      have hduBound : ∀ x ∈ Ω.val, ∀ j, j ≤ k →
          ‖iteratedFDeriv ℝ j (fderiv ℝ u) x‖ ≤ M * δ := by
        intro x hx j hj
        rw [norm_iteratedFDeriv_fderiv]
        exact huderiv x hx (j + 1) (Nat.succ_le_succ (Nat.zero_le _))
          (Nat.add_le_add_right hj 1)
      have hduHolder : ∀ j, j ≤ k → HolderBoundOn Ω.val
          (iteratedFDeriv ℝ j (fderiv ℝ u)) γ (M * δ) := by
        intro j hj x hx y hy
        rw [norm_iteratedFDeriv_fderiv_sub]
        exact huderivHolder (j + 1) (Nat.succ_le_succ (Nat.zero_le _))
          (Nat.add_le_add_right hj 1) x hx y hy
      have hprod := iteratedFDeriv_bilinear_holderBoundOn Ω
        (ContinuousLinearMap.compL ℝ (Domain n) (Ambient q) E)
        (ContinuousLinearMap.norm_compL_le _ _ _ _) k
        (hA'.comp_contDiffOn huLow) hdu hK (mul_nonneg hH hδ)
        hcoBound hduBound hcoHolder hduHolder
      have hlocal (x : Domain n) (hx : x ∈ Ω.val) : fderiv ℝ (A ∘ u) =ᶠ[nhds x]
          (fun z => (fderiv ℝ A (u z)).comp (fderiv ℝ u z)) := by
        filter_upwards [Ω.property.eventually_mem hx] with z hz
        exact fderiv_comp z (hA.differentiable (by norm_cast)).differentiableAt
          ((hu.contDiffAt (Ω.property.mem_nhds hz)).differentiableAt (by norm_cast))
      have htop : HolderBoundOn Ω.val (iteratedFDeriv ℝ (k + 1) (A ∘ u)) γ
          (coefficientCompositionHolderConstant C M L (k + 1) * δ) := by
        intro x hx y hy
        rw [← norm_iteratedFDeriv_fderiv_sub]
        rw [(hlocal x hx).iteratedFDeriv ℝ k |>.eq_of_nhds,
          (hlocal y hy).iteratedFDeriv ℝ k |>.eq_of_nhds]
        have hp := hprod x hx y hy
        simp only [ContinuousLinearMap.compL_apply, Function.comp_apply] at hp
        apply hp.trans
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
        have hδsq : δ ^ 2 ≤ δ := by
          simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hδone hδ
        calc
          (2 : ℝ) ^ k * ((H * δ) * (M * δ) + K * (M * δ)) =
              (2 : ℝ) ^ k * M * H * δ ^ 2 + (2 : ℝ) ^ k * M * K * δ := by ring
          _ ≤ (2 : ℝ) ^ k * M * H * δ + (2 : ℝ) ^ k * M * K * δ :=
            add_le_add (mul_le_mul_of_nonneg_left hδsq (by positivity)) le_rfl
          _ ≤ coefficientCompositionHolderConstant C M L (k + 1) * δ := by
            change _ ≤ (H + (2 : ℝ) ^ k * M * (H + K)) * δ
            nlinarith only [mul_nonneg hH hδ]
      intro j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hjlt
      · exact htop
      · have hjk : j ≤ k := Nat.le_of_lt_succ hjlt
        have hlower : HolderBoundOn Ω.val (iteratedFDeriv ℝ j (A ∘ u)) γ (H * δ) := by
          apply ih hAlow huLow
          · exact fun x hx i hi => hAderiv x hx i (hi.trans (Nat.le_succ k))
          · exact fun x hx y hy i hi => hALip x hx y hy i (hi.trans (Nat.le_succ k))
          · exact fun x hx i hi hik => huderiv x hx i hi (hik.trans (Nat.le_succ k))
          · exact fun i hi hik => huderivHolder i hi (hik.trans (Nat.le_succ k))
          · exact hjk
        intro x hx y hy
        exact (hlower x hx y hy).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (coefficientCompositionHolderConstant_mono hC hM hL (Nat.le_succ k)) hδ)
          (Real.rpow_nonneg dist_nonneg _))

theorem norm_iteratedFDeriv_classicalQuadraticForcing_le {n q : ℕ} (Ω : OpenDomain n)
    {A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q}
    {u : Domain n → Ambient q} (k : ℕ) (hA : ContDiff ℝ k A)
    (hu : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) u Ω.val)
    {C M δ : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hAderiv : ∀ x ∈ Ω.val, ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i A (u x)‖ ≤ C)
    (huderiv : ∀ x ∈ Ω.val, ∀ j, 1 ≤ j → j ≤ k + 1 →
      ‖iteratedFDeriv ℝ j u x‖ ≤ M * δ) :
    ∀ x ∈ Ω.val, ‖iteratedFDeriv ℝ k (classicalQuadraticForcing A u) x‖ ≤
      quadraticDerivativeBoundConstant n k C M * δ ^ 2 := by
  intro x hx
  let K : ℝ := (k.factorial : ℝ) * C * (max 1 M) ^ k
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let P (i : Fin n) : Domain n → Ambient q :=
    fun y => fderiv ℝ u y (EuclideanSpace.single i 1)
  have huLow : ContDiffOn ℝ k u Ω.val := hu.of_le (by exact_mod_cast Nat.le_succ k)
  have hco : ContDiffOn ℝ k (A ∘ u) Ω.val := hA.comp_contDiffOn huLow
  have hdu : ContDiffOn ℝ k (fderiv ℝ u) Ω.val :=
    hu.fderiv_of_isOpen Ω.property (by norm_cast)
  have hcol (i : Fin n) : ContDiffOn ℝ k (P i) Ω.val :=
    hdu.clm_apply contDiffOn_const
  have hcolBound (i : Fin n) (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (P i) x‖ ≤ M * δ := by
    calc
      _ ≤ ‖EuclideanSpace.single i (1 : ℝ)‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ u) x‖ :=
        norm_iteratedFDeriv_clm_apply_const_on_open Ω j
          (hdu.of_le (by exact_mod_cast hj)) _ x hx
      _ = ‖iteratedFDeriv ℝ (j + 1) u x‖ := by
        rw [PiLp.norm_single, norm_one, one_mul, norm_iteratedFDeriv_fderiv]
      _ ≤ M * δ := huderiv x hx (j + 1) (Nat.succ_le_succ (Nat.zero_le _))
        (Nat.add_le_add_right hj 1)
  have hcoBound : ∀ j, j ≤ k → ‖iteratedFDeriv ℝ j (A ∘ u) x‖ ≤ K :=
    norm_iteratedFDeriv_coefficient_comp_le_uniform Ω k hA huLow x hx hC hM hδone
      (hAderiv x hx) (fun j hj hjk => huderiv x hx j hj (hjk.trans (Nat.le_succ k)))
  have hfirstBound (i : Fin n) (j : ℕ) (hj : j ≤ k) :
      ‖iteratedFDeriv ℝ j (fun y => A (u y) (P i y)) x‖ ≤
        (2 : ℝ) ^ k * K * (M * δ) := by
    calc
      _ ≤ (2 : ℝ) ^ j * K * (M * δ) :=
        norm_iteratedFDeriv_clm_apply_le_uniform Ω j
          (hco.of_le (by exact_mod_cast hj)) ((hcol i).of_le (by exact_mod_cast hj))
          x hx hK (fun l hl => hcoBound l (hl.trans hj))
          (fun l hl => hcolBound i l (hl.trans hj))
      _ ≤ (2 : ℝ) ^ k * K * (M * δ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hK)
          (mul_nonneg hM hδ)
  have hterm (i : Fin n) :
      ‖iteratedFDeriv ℝ k (fun y => A (u y) (P i y) (P i y)) x‖ ≤
        (4 : ℝ) ^ k * K * M ^ 2 * δ ^ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ k * ((2 : ℝ) ^ k * K * (M * δ)) * (M * δ) :=
        norm_iteratedFDeriv_clm_apply_le_uniform Ω k (hco.clm_apply (hcol i)) (hcol i)
          x hx (by positivity) (hfirstBound i) (hcolBound i)
      _ = _ := by rw [show (4 : ℝ) ^ k = (2 : ℝ) ^ k * (2 : ℝ) ^ k by
        rw [← mul_pow]; norm_num]; ring
  change ‖iteratedFDeriv ℝ k (fun y => ∑ i : Fin n, A (u y) (P i y) (P i y)) x‖ ≤ _
  have hsum := iteratedFDeriv_fun_sum_apply (u := Finset.univ)
    (f := fun i y => A (u y) (P i y) (P i y)) (fun i _ =>
      ((hco.clm_apply (hcol i)).clm_apply (hcol i)).contDiffAt (Ω.property.mem_nhds hx))
  rw [hsum]
  calc
    _ ≤ ∑ i : Fin n, ‖iteratedFDeriv ℝ k (fun y => A (u y) (P i y) (P i y)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (4 : ℝ) ^ k * K * M ^ 2 * δ ^ 2 :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = quadraticDerivativeBoundConstant n k C M * δ ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp only [K, quadraticDerivativeBoundConstant]
      ring

/-- A finite Holder bound for the order-k forcing derivative. -/
@[expose] def quadraticHolderBoundConstant (n k : ℕ) (C M L : ℝ) : ℝ :=
  (n : ℝ) * (4 : ℝ) ^ k * M ^ 2 *
    (coefficientCompositionHolderConstant C M L k +
      2 * (k.factorial : ℝ) * C * (max 1 M) ^ k)

theorem quadraticHolderBoundConstant_nonneg (n k : ℕ) {C M L : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    0 ≤ quadraticHolderBoundConstant n k C M L := by
  unfold quadraticHolderBoundConstant
  have hH := coefficientCompositionHolderConstant_nonneg hC hM hL k
  positivity

theorem iteratedFDeriv_classicalQuadraticForcing_holderBoundOn {n q : ℕ}
    (Ω : OpenDomain n)
    {A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q}
    {u : Domain n → Ambient q} (k : ℕ) (hA : ContDiff ℝ k A)
    (hu : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) u Ω.val)
    {C M L δ γ : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hAderiv : ∀ x ∈ Ω.val, ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i A (u x)‖ ≤ C)
    (hALip : ∀ x ∈ Ω.val, ∀ y ∈ Ω.val, ∀ i, i ≤ k →
      ‖iteratedFDeriv ℝ i A (u x) - iteratedFDeriv ℝ i A (u y)‖ ≤ C * ‖u x - u y‖)
    (huderiv : ∀ x ∈ Ω.val, ∀ i, 1 ≤ i → i ≤ k + 1 →
      ‖iteratedFDeriv ℝ i u x‖ ≤ M * δ)
    (huHolder : HolderBoundOn Ω.val u γ (L * δ))
    (huderivHolder : ∀ i, 1 ≤ i → i ≤ k + 1 →
      HolderBoundOn Ω.val (iteratedFDeriv ℝ i u) γ (M * δ)) :
    HolderBoundOn Ω.val (iteratedFDeriv ℝ k (classicalQuadraticForcing A u)) γ
      (quadraticHolderBoundConstant n k C M L * δ ^ 2) := by
  let K : ℝ := (k.factorial : ℝ) * C * (max 1 M) ^ k
  let H : ℝ := coefficientCompositionHolderConstant C M L k
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hH : 0 ≤ H := coefficientCompositionHolderConstant_nonneg hC hM hL k
  have hδsq : δ ^ 2 ≤ δ := by
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hδone hδ
  let P (i : Fin n) : Domain n → Ambient q :=
    fun y => fderiv ℝ u y (EuclideanSpace.single i 1)
  have huLow : ContDiffOn ℝ k u Ω.val := hu.of_le (by exact_mod_cast Nat.le_succ k)
  have hco : ContDiffOn ℝ k (A ∘ u) Ω.val := hA.comp_contDiffOn huLow
  have hdu : ContDiffOn ℝ k (fderiv ℝ u) Ω.val :=
    hu.fderiv_of_isOpen Ω.property (by norm_cast)
  have hcol (i : Fin n) : ContDiffOn ℝ k (P i) Ω.val :=
    hdu.clm_apply contDiffOn_const
  have hcoBound : ∀ x ∈ Ω.val, ∀ j, j ≤ k →
      ‖iteratedFDeriv ℝ j (A ∘ u) x‖ ≤ K := by
    intro x hx
    exact norm_iteratedFDeriv_coefficient_comp_le_uniform Ω k hA huLow x hx hC hM hδone
      (hAderiv x hx) (fun j hj hjk => huderiv x hx j hj (hjk.trans (Nat.le_succ k)))
  have hcoHolder : ∀ j, j ≤ k →
      HolderBoundOn Ω.val (iteratedFDeriv ℝ j (A ∘ u)) γ (H * δ) :=
    iteratedFDeriv_coefficient_comp_holderBoundOn Ω k hA huLow hC hM hL hδ hδone
      hAderiv hALip (fun x hx j hj hjk => huderiv x hx j hj (hjk.trans (Nat.le_succ k)))
      huHolder (fun j hj hjk => huderivHolder j hj (hjk.trans (Nat.le_succ k)))
  have hcolBound (i : Fin n) : ∀ x ∈ Ω.val, ∀ j, j ≤ k →
      ‖iteratedFDeriv ℝ j (P i) x‖ ≤ M * δ := by
    intro x hx j hj
    have hp := norm_iteratedFDeriv_clm_apply_const_on_open Ω j
      (hdu.of_le (by exact_mod_cast hj)) (EuclideanSpace.single i 1) x hx
    rw [PiLp.norm_single, norm_one, one_mul, norm_iteratedFDeriv_fderiv] at hp
    exact hp.trans (huderiv x hx (j + 1) (Nat.succ_le_succ (Nat.zero_le _))
      (Nat.add_le_add_right hj 1))
  have hcolHolder (i : Fin n) : ∀ j, j ≤ k →
      HolderBoundOn Ω.val (iteratedFDeriv ℝ j (P i)) γ (M * δ) := by
    intro j hj x hx y hy
    have hp := norm_iteratedFDeriv_clm_apply_const_sub_le Ω j
      (hdu.of_le (by exact_mod_cast hj)) (EuclideanSpace.single i 1) x y hx hy
    rw [PiLp.norm_single, norm_one, one_mul, norm_iteratedFDeriv_fderiv_sub] at hp
    exact hp.trans (huderivHolder (j + 1) (Nat.succ_le_succ (Nat.zero_le _))
      (Nat.add_le_add_right hj 1) x hx y hy)
  have hfirstBound (i : Fin n) : ∀ x ∈ Ω.val, ∀ j, j ≤ k →
      ‖iteratedFDeriv ℝ j (fun y => A (u y) (P i y)) x‖ ≤
        (2 : ℝ) ^ k * K * (M * δ) := by
    intro x hx j hj
    have hp := norm_iteratedFDeriv_clm_apply_le_uniform Ω j
      (hco.of_le (by exact_mod_cast hj)) ((hcol i).of_le (by exact_mod_cast hj))
      x hx hK (fun l hl => hcoBound x hx l (hl.trans hj))
      (fun l hl => hcolBound i x hx l (hl.trans hj))
    exact hp.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hK)
      (mul_nonneg hM hδ))
  have hfirstHolder (i : Fin n) : ∀ j, j ≤ k →
      HolderBoundOn Ω.val (iteratedFDeriv ℝ j (fun y => A (u y) (P i y))) γ
        ((2 : ℝ) ^ k * M * (H + K) * δ) := by
    intro j hj x hx y hy
    have hp := iteratedFDeriv_clm_apply_holderBoundOn Ω j
      (hco.of_le (by exact_mod_cast hj)) ((hcol i).of_le (by exact_mod_cast hj))
      hK (mul_nonneg hH hδ)
      (fun z hz l hl => hcoBound z hz l (hl.trans hj))
      (fun z hz l hl => hcolBound i z hz l (hl.trans hj))
      (fun l hl => hcoHolder l (hl.trans hj))
      (fun l hl => hcolHolder i l (hl.trans hj)) x hx y hy
    apply hp.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
    calc
      (2 : ℝ) ^ j * ((H * δ) * (M * δ) + K * (M * δ)) ≤
          (2 : ℝ) ^ k * ((H * δ) * (M * δ) + K * (M * δ)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (by positivity)
      _ = (2 : ℝ) ^ k * M * H * δ ^ 2 + (2 : ℝ) ^ k * M * K * δ := by ring
      _ ≤ (2 : ℝ) ^ k * M * H * δ + (2 : ℝ) ^ k * M * K * δ :=
        add_le_add (mul_le_mul_of_nonneg_left hδsq (by positivity)) le_rfl
      _ = _ := by ring
  have htermHolder (i : Fin n) :
      HolderBoundOn Ω.val (iteratedFDeriv ℝ k (fun y => A (u y) (P i y) (P i y))) γ
        ((4 : ℝ) ^ k * M ^ 2 * (H + 2 * K) * δ ^ 2) := by
    have hp := iteratedFDeriv_clm_apply_holderBoundOn Ω k
      (hco.clm_apply (hcol i)) (hcol i) (by positivity) (by positivity)
      (hfirstBound i) (hcolBound i) (hfirstHolder i) (hcolHolder i)
    intro x hx y hy
    apply (hp x hx y hy).trans_eq
    change (2 : ℝ) ^ k * (((2 : ℝ) ^ k * M * (H + K) * δ) * (M * δ) +
      ((2 : ℝ) ^ k * K * (M * δ)) * (M * δ)) * (dist x y) ^ γ =
      ((4 : ℝ) ^ k * M ^ 2 * (H + 2 * K) * δ ^ 2) * (dist x y) ^ γ
    rw [show (4 : ℝ) ^ k = (2 : ℝ) ^ k * (2 : ℝ) ^ k by rw [← mul_pow]; norm_num]
    ring
  intro x hx y hy
  change ‖iteratedFDeriv ℝ k (fun z => ∑ i : Fin n, A (u z) (P i z) (P i z)) x -
    iteratedFDeriv ℝ k (fun z => ∑ i : Fin n, A (u z) (P i z) (P i z)) y‖ ≤ _
  have hsum (z : Domain n) (hz : z ∈ Ω.val) := iteratedFDeriv_fun_sum_apply
    (u := Finset.univ) (f := fun i t => A (u t) (P i t) (P i t)) (fun i _ =>
      ((hco.clm_apply (hcol i)).clm_apply (hcol i)).contDiffAt (Ω.property.mem_nhds hz))
  rw [hsum x hx, hsum y hy, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin n, ‖iteratedFDeriv ℝ k (fun z => A (u z) (P i z) (P i z)) x -
        iteratedFDeriv ℝ k (fun z => A (u z) (P i z) (P i z)) y‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ((4 : ℝ) ^ k * M ^ 2 * (H + 2 * K) * δ ^ 2) *
        Real.rpow (dist x y) γ := Finset.sum_le_sum (fun i _ => htermHolder i x hx y hy)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (n : ℝ) * (((4 : ℝ) ^ k * M ^ 2 * (H + 2 * K) * δ ^ 2) * (dist x y) ^ γ) =
        (quadraticHolderBoundConstant n k C M L * δ ^ 2) * (dist x y) ^ γ
      dsimp only [K, H, quadraticHolderBoundConstant]
      ring

theorem classicalQuadraticForcing_bounds_of_highest_holder {n q : ℕ}
    (Ω : OpenDomain n)
    {A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q}
    {u : Domain n → Ambient q} (k : ℕ) (hA : ContDiff ℝ k A)
    (hu : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) u Ω.val)
    (hConvex : Convex ℝ Ω.val) {C M D δ γ : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hγ : 0 ≤ γ) (hγone : γ ≤ 1)
    (hD : 0 ≤ D)
    (hDiameter : ∀ x ∈ Ω.val, ∀ y ∈ Ω.val, dist x y ≤ D)
    (hAderiv : ∀ x ∈ Ω.val, ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i A (u x)‖ ≤ C)
    (hALip : ∀ x ∈ Ω.val, ∀ y ∈ Ω.val, ∀ i, i ≤ k →
      ‖iteratedFDeriv ℝ i A (u x) - iteratedFDeriv ℝ i A (u y)‖ ≤ C * ‖u x - u y‖)
    (huderiv : ∀ x ∈ Ω.val, ∀ i, 1 ≤ i → i ≤ k + 1 →
      ‖iteratedFDeriv ℝ i u x‖ ≤ M * δ)
    (hHighest : HolderBoundOn Ω.val (iteratedFDeriv ℝ (k + 1) u) γ (M * δ)) :
    let T := Real.rpow D (1 - γ)
    let M' := M * max 1 T
    ∀ j, j ≤ k →
      (∀ x ∈ Ω.val, ‖iteratedFDeriv ℝ j (classicalQuadraticForcing A u) x‖ ≤
        quadraticDerivativeBoundConstant n j C M' * δ ^ 2) ∧
      HolderBoundOn Ω.val (iteratedFDeriv ℝ j (classicalQuadraticForcing A u)) γ
        (quadraticHolderBoundConstant n j C M' (M * T) * δ ^ 2) := by
  dsimp only
  let T := Real.rpow D (1 - γ)
  let M' := M * max 1 T
  have hT : 0 ≤ T := Real.rpow_nonneg hD _
  have hM' : 0 ≤ M' := mul_nonneg hM (le_trans zero_le_one (le_max_left _ _))
  have hMM' : M ≤ M' := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (le_max_left 1 T) hM
  have hMδ : M * δ ≤ M' * δ := mul_le_mul_of_nonneg_right hMM' hδ
  have huHolder : HolderBoundOn Ω.val u γ ((M * T) * δ) := by
    have hzero := iteratedFDeriv_holderBoundOn_of_next_derivative Ω 0
      (hu.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))) hConvex
      (mul_nonneg hM hδ) hγ hγone
      (fun x hx => huderiv x hx 1 le_rfl (Nat.succ_le_succ (Nat.zero_le _))) hDiameter
    intro x hx y hy
    have hh := hzero x hx y hy
    rw [norm_iteratedFDeriv_zero_sub] at hh
    exact hh.trans_eq (by
      change (M * δ * T) * (dist x y) ^ γ = ((M * T) * δ) * (dist x y) ^ γ
      ring)
  have hAllHolder : ∀ i, 1 ≤ i → i ≤ k + 1 →
      HolderBoundOn Ω.val (iteratedFDeriv ℝ i u) γ (M' * δ) := by
    intro i _ hi x hx y hy
    rcases Nat.eq_or_lt_of_le hi with rfl | hilt
    · exact (hHighest x hx y hy).trans
        (mul_le_mul_of_nonneg_right hMδ (Real.rpow_nonneg dist_nonneg _))
    · have hnext : i + 1 ≤ k + 1 := Nat.succ_le_of_lt hilt
      have hlower := iteratedFDeriv_holderBoundOn_of_next_derivative Ω i
        (hu.of_le (by exact_mod_cast hnext)) hConvex (mul_nonneg hM hδ) hγ hγone
        (fun z hz => huderiv z hz (i + 1) (Nat.succ_le_succ (Nat.zero_le _)) hnext)
        hDiameter
      apply (hlower x hx y hy).trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
      calc
        (M * δ) * T ≤ (M * δ) * max 1 T :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg hM hδ)
        _ = M' * δ := by dsimp only [M']; ring
  intro j hj
  have huj : ContDiffOn ℝ ((j + 1 : ℕ) : ℕ∞ω) u Ω.val :=
    hu.of_le (by exact_mod_cast Nat.add_le_add_right hj 1)
  have hAj : ContDiff ℝ j A := hA.of_le (by exact_mod_cast hj)
  have hAjBound : ∀ x ∈ Ω.val, ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i A (u x)‖ ≤ C :=
    fun x hx i hi => hAderiv x hx i (hi.trans hj)
  have hujBound : ∀ x ∈ Ω.val, ∀ i, 1 ≤ i → i ≤ j + 1 →
      ‖iteratedFDeriv ℝ i u x‖ ≤ M' * δ :=
    fun x hx i hi hij => (huderiv x hx i hi (hij.trans (Nat.add_le_add_right hj 1))).trans hMδ
  refine ⟨norm_iteratedFDeriv_classicalQuadraticForcing_le Ω j hAj huj
    hC hM' hδ hδone hAjBound hujBound, ?_⟩
  exact iteratedFDeriv_classicalQuadraticForcing_holderBoundOn Ω j hAj huj hC hM'
    (mul_nonneg hM hT) hδ hδone hAjBound
    (fun x hx y hy i hi => hALip x hx y hy i (hi.trans hj)) hujBound huHolder
    (fun i hi hij => hAllHolder i hi (hij.trans (Nat.add_le_add_right hj 1)))

theorem classicalQuadraticForcing_compact_bounds {n q : ℕ}
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    (hA : ContDiff ℝ ∞ A) (c : Ambient q) (R : ℝ) :
    ∃ C : ℕ → ℝ≥0, ∀ k : ℕ, ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q),
      ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) u Ω.val → Convex ℝ Ω.val →
      MapsTo u Ω.val (Metric.closedBall c R) →
      ∀ M D δ γ : ℝ, 0 ≤ M → 0 ≤ D → 0 ≤ δ → δ ≤ 1 → 0 ≤ γ → γ ≤ 1 →
      (∀ x ∈ Ω.val, ∀ y ∈ Ω.val, dist x y ≤ D) →
      (∀ x ∈ Ω.val, ∀ i, 1 ≤ i → i ≤ k + 1 →
        ‖iteratedFDeriv ℝ i u x‖ ≤ M * δ) →
      HolderBoundOn Ω.val (iteratedFDeriv ℝ (k + 1) u) γ (M * δ) →
      let T := Real.rpow D (1 - γ)
      let M' := M * max 1 T
      ∀ j, j ≤ k →
        (∀ x ∈ Ω.val, ‖iteratedFDeriv ℝ j (classicalQuadraticForcing A u) x‖ ≤
          quadraticDerivativeBoundConstant n j (C k : ℝ) M' * δ ^ 2) ∧
        HolderBoundOn Ω.val (iteratedFDeriv ℝ j (classicalQuadraticForcing A u)) γ
          (quadraticHolderBoundConstant n j (C k : ℝ) M' (M * T) * δ ^ 2) := by
  obtain ⟨C, hC, hCLip⟩ := compact_coefficient_uniform_bounds A hA c R
  refine ⟨C, ?_⟩
  intro k Ω u hu hConvex huRange M D δ γ hM hD hδ hδone hγ hγone hDiameter huderiv hHighest
  exact classicalQuadraticForcing_bounds_of_highest_holder Ω k
    (hA.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top k)))) hu
    hConvex (C k).property hM hδ hδone hγ hγone hD hDiameter
    (fun x hx j hj => hC k j hj (u x) (huRange hx))
    (fun x hx y hy j hj => hCLip k j hj (u x) (huRange hx) (u y) (huRange hy))
    huderiv hHighest

end HolderToCK
end
