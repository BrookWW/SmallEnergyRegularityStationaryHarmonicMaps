module

public import HolderToCK.Analysis.Bootstrap.WeakDifferentiation
public import HolderToCK.Analysis.WeakPoissonLocality
public import Mathlib.Data.List.OfFn

/-! # Finite coordinate derivatives of one weak Poisson solution

Coordinate words act by repeated classical directional derivatives in the
Euclidean coordinate basis. Finite regularity of the original solution and
forcing supplies the classical regularity, native local Sobolev data, and
signed weak equation for every word. Restriction uses the same functions on
each smaller open domain.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK

/-- The classical derivative associated with a finite coordinate word. The
head coordinate differentiates the function associated with the tail. -/
@[expose] noncomputable def coordinateWord {n q : ℕ} (u : Domain n → Ambient q) :
    List (Fin n) → Domain n → Ambient q
  | [] => u
  | i :: w => fun x => fderiv ℝ (coordinateWord u w) x (EuclideanSpace.single i 1)

@[simp] theorem coordinateWord_nil {n q : ℕ} (u : Domain n → Ambient q) :
    coordinateWord u [] = u := rfl

@[simp] theorem coordinateWord_cons {n q : ℕ} (u : Domain n → Ambient q)
    (i : Fin n) (w : List (Fin n)) :
    coordinateWord u (i :: w) =
      fun x => fderiv ℝ (coordinateWord u w) x (EuclideanSpace.single i 1) := rfl

theorem coordinateWord_append {n q : ℕ} (u : Domain n → Ambient q)
    (v w : List (Fin n)) :
    coordinateWord u (v ++ w) = coordinateWord (coordinateWord u w) v := by
  induction v with
  | nil => rfl
  | cons i v ih =>
      simp only [List.cons_append, coordinateWord_cons, ih]

/-- The coordinate basis vectors, in the order of a finite coordinate word. -/
@[expose] noncomputable def coordinateWordDirections {n : ℕ} (w : List (Fin n)) :
    Fin w.length → Domain n := fun j => EuclideanSpace.single (w.get j) 1

theorem coordinateWordDirections_cons {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    coordinateWordDirections (i :: w) =
      Fin.cons (EuclideanSpace.single i 1) (coordinateWordDirections w) := by
  funext j
  exact Fin.cases rfl (fun _ => rfl) j

theorem coordinateWordDirections_ofFn {n k : ℕ} (I : Fin k → Fin n) :
    coordinateWordDirections (List.ofFn I) =
      fun j => EuclideanSpace.single (I (Fin.cast (List.length_ofFn (f := I)) j)) 1 := by
  funext j
  exact congrArg (fun i => EuclideanSpace.single i (1 : ℝ)) (List.get_ofFn I j)

theorem contDiffOn_coordinateWord {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} (w : List (Fin n)) (r : ℕ)
    (hu : ContDiffOn ℝ ((w.length + r : ℕ) : ℕ∞ω) u Ω.val) :
    ContDiffOn ℝ r (coordinateWord u w) Ω.val := by
  induction w generalizing r with
  | nil => simpa only [List.length_nil, Nat.zero_add, coordinateWord_nil] using hu
  | cons i w ih =>
      have htail : ContDiffOn ℝ ((r + 1 : ℕ) : ℕ∞ω) (coordinateWord u w) Ω.val := by
        apply ih (r + 1)
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 r] using hu
      exact (htail.fderiv_of_isOpen Ω.property (by norm_cast)).clm_apply contDiffOn_const

theorem coordinateWord_eq_iteratedFDeriv {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} (w : List (Fin n))
    (hu : ContDiffOn ℝ w.length u Ω.val) (x : Domain n) (hx : x ∈ Ω.val) :
    coordinateWord u w x = iteratedFDeriv ℝ w.length u x (coordinateWordDirections w) := by
  induction w generalizing x with
  | nil => exact (iteratedFDeriv_zero_apply _).symm
  | cons i w ih =>
      have huTail : ContDiffOn ℝ w.length u Ω.val :=
        hu.of_le (by exact_mod_cast Nat.le_succ w.length)
      have hlocal : coordinateWord u w =ᶠ[nhds x]
          fun z => iteratedFDeriv ℝ w.length u z (coordinateWordDirections w) := by
        filter_upwards [Ω.property.eventually_mem hx] with y hy
        exact ih huTail y hy
      rw [coordinateWord_cons]
      change fderiv ℝ (coordinateWord u w) x (EuclideanSpace.single i 1) = _
      rw [hlocal.fderiv_eq]
      have hdu : DifferentiableAt ℝ (iteratedFDeriv ℝ w.length u) x :=
        (hu.contDiffAt (Ω.property.mem_nhds hx)).differentiableAt_iteratedFDeriv
          (by exact_mod_cast Nat.lt_succ_self w.length)
      simpa only [coordinateWordDirections_cons, List.length_cons, Fin.tail_cons, Fin.cons_zero] using
        (hdu.iteratedFDeriv_succ_apply_left'
          (m := coordinateWordDirections (i :: w))).symm

theorem coordinateWord_ofFn_eq_iteratedFDeriv {n q k : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} (I : Fin k → Fin n)
    (hu : ContDiffOn ℝ k u Ω.val) (x : Domain n) (hx : x ∈ Ω.val) :
    coordinateWord u (List.ofFn I) x =
      iteratedFDeriv ℝ k u x (fun j => EuclideanSpace.single (I j) 1) := by
  induction k generalizing x with
  | zero =>
      rw [List.ofFn_zero, coordinateWord_nil, iteratedFDeriv_zero_apply]
  | succ k ih =>
      have huTail : ContDiffOn ℝ k u Ω.val :=
        hu.of_le (by exact_mod_cast Nat.le_succ k)
      have hlocal : coordinateWord u (List.ofFn (Fin.tail I)) =ᶠ[nhds x]
          fun z => iteratedFDeriv ℝ k u z
            (fun j => EuclideanSpace.single (I j.succ) 1) := by
        filter_upwards [Ω.property.eventually_mem hx] with y hy
        exact ih (Fin.tail I) huTail y hy
      rw [List.ofFn_succ, coordinateWord_cons]
      change fderiv ℝ (coordinateWord u (List.ofFn (Fin.tail I))) x
        (EuclideanSpace.single (I 0) 1) = _
      rw [hlocal.fderiv_eq]
      have hdu : DifferentiableAt ℝ (iteratedFDeriv ℝ k u) x :=
        (hu.contDiffAt (Ω.property.mem_nhds hx)).differentiableAt_iteratedFDeriv
          (by exact_mod_cast Nat.lt_succ_self k)
      exact (hdu.iteratedFDeriv_succ_apply_left'
        (m := fun j => EuclideanSpace.single (I j) 1)).symm

theorem coordinateWord_congr_nhds {n q : ℕ} {u v : Domain n → Ambient q}
    {x : Domain n} (huv : u =ᶠ[nhds x] v) (w : List (Fin n)) :
    coordinateWord u w =ᶠ[nhds x] coordinateWord v w := by
  induction w with
  | nil => exact huv
  | cons i w ih =>
      change (fun y => fderiv ℝ (coordinateWord u w) y (EuclideanSpace.single i 1)) =ᶠ[nhds x]
        (fun y => fderiv ℝ (coordinateWord v w) y (EuclideanSpace.single i 1))
      exact (ih.fderiv (𝕜 := ℝ)).mono
        (fun _ h => congrArg (fun A => A (EuclideanSpace.single i 1)) h)

theorem coordinateWord_eq_of_perm {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} {v w : List (Fin n)} (hvw : v.Perm w)
    (hu : ContDiffOn ℝ v.length u Ω.val) :
    EqOn (coordinateWord u v) (coordinateWord u w) Ω.val := by
  induction hvw with
  | nil => exact fun _ _ => rfl
  | @cons i v w hperm ih =>
      have huTail : ContDiffOn ℝ v.length u Ω.val :=
        hu.of_le (by exact_mod_cast Nat.le_succ v.length)
      intro x hx
      have hlocal : coordinateWord u v =ᶠ[nhds x] coordinateWord u w := by
        filter_upwards [Ω.property.eventually_mem hx] with y hy
        exact ih huTail hy
      exact congrArg (fun A => A (EuclideanSpace.single i 1)) (hlocal.fderiv_eq (𝕜 := ℝ))
  | swap i j w =>
      have htail : ContDiffOn ℝ 2 (coordinateWord u w) Ω.val := by
        apply contDiffOn_coordinateWord Ω w 2
        simpa only [List.length_cons, Nat.add_assoc] using hu
      intro x hx
      exact fderiv_direction_swap_of_contDiffAt_two (coordinateWord u w) x
        (htail.contDiffAt (Ω.property.mem_nhds hx)) _ _
  | trans h₁ h₂ ih₁ ih₂ =>
      exact (ih₁ hu).trans (ih₂ (by simpa only [h₁.length_eq] using hu))

theorem coordinateWord_reverse_eq {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} (w : List (Fin n))
    (hu : ContDiffOn ℝ w.length u Ω.val) :
    EqOn (coordinateWord u w.reverse) (coordinateWord u w) Ω.val :=
  coordinateWord_eq_of_perm Ω w.reverse_perm
    (by simpa only [List.length_reverse] using hu)

theorem norm_coordinateWord_le_iteratedFDeriv {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} (w : List (Fin n))
    (hu : ContDiffOn ℝ w.length u Ω.val) (x : Domain n) (hx : x ∈ Ω.val) :
    ‖coordinateWord u w x‖ ≤ ‖iteratedFDeriv ℝ w.length u x‖ := by
  rw [coordinateWord_eq_iteratedFDeriv Ω w hu x hx]
  simpa only [coordinateWordDirections, PiLp.norm_single, norm_one,
    Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ w.length u x).le_opNorm (coordinateWordDirections w)

theorem norm_coordinateWord_sub_le_iteratedFDeriv_sub {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} (w : List (Fin n))
    (hu : ContDiffOn ℝ w.length u Ω.val) (x y : Domain n)
    (hx : x ∈ Ω.val) (hy : y ∈ Ω.val) :
    ‖coordinateWord u w x - coordinateWord u w y‖ ≤
      ‖iteratedFDeriv ℝ w.length u x - iteratedFDeriv ℝ w.length u y‖ := by
  rw [coordinateWord_eq_iteratedFDeriv Ω w hu x hx,
    coordinateWord_eq_iteratedFDeriv Ω w hu y hy]
  simpa only [sub_apply, coordinateWordDirections,
    PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ w.length u x - iteratedFDeriv ℝ w.length u y).le_opNorm
      (coordinateWordDirections w)

theorem contDiff_coordinateWord {n q : ℕ} {ψ : Domain n → Ambient q}
    (hψ : ContDiff ℝ ∞ ψ) (w : List (Fin n)) :
    ContDiff ℝ ∞ (coordinateWord ψ w) := by
  induction w with
  | nil => exact hψ
  | cons i w ih => exact contDiff_fderiv_apply ih (EuclideanSpace.single i 1)

theorem hasCompactSupport_coordinateWord {n q : ℕ} {ψ : Domain n → Ambient q}
    (hcψ : HasCompactSupport ψ) (w : List (Fin n)) :
    HasCompactSupport (coordinateWord ψ w) := by
  induction w with
  | nil => exact hcψ
  | cons i w ih => exact ih.fderiv_apply ℝ (EuclideanSpace.single i 1)

theorem tsupport_coordinateWord_subset {n q : ℕ} (ψ : Domain n → Ambient q)
    (w : List (Fin n)) : tsupport (coordinateWord ψ w) ⊆ tsupport ψ := by
  induction w with
  | nil => exact Subset.rfl
  | cons i w ih =>
      exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans ih

theorem compact_test_inner_coordinateWord_integral {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} (w : List (Fin n))
    (hu : ContDiffOn ℝ w.length u Ω.val)
    {ψ : Domain n → Ambient q} (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Ω.val) :
    IntegrableOn (fun x => inner ℝ (coordinateWord u w x) (ψ x)) Ω.val ∧
    IntegrableOn (fun x => inner ℝ (u x) (coordinateWord ψ w.reverse x)) Ω.val ∧
    (∫ x in Ω.val, inner ℝ (coordinateWord u w x) (ψ x)) =
      (-1 : ℝ) ^ w.length *
        (∫ x in Ω.val, inner ℝ (u x) (coordinateWord ψ w.reverse x)) := by
  induction w generalizing ψ with
  | nil =>
      have hI : IntegrableOn (fun x => inner ℝ (u x) (ψ x)) Ω.val :=
        (compact_inner_integrable hu.continuousOn hψ.continuous hcψ hsψ).integrableOn
      refine ⟨hI, hI, ?_⟩
      simp only [List.length_nil, List.reverse_nil, coordinateWord_nil, pow_zero, one_mul]
  | cons i w ih =>
      have hwu : ContDiffOn ℝ 1 (coordinateWord u w) Ω.val :=
        contDiffOn_coordinateWord Ω w 1 hu
      have huTail : ContDiffOn ℝ w.length u Ω.val :=
        hu.of_le (by exact_mod_cast Nat.le_succ w.length)
      have hdψ : ContDiff ℝ ∞ (coordinateWord ψ [i]) := contDiff_coordinateWord hψ [i]
      have hcdψ : HasCompactSupport (coordinateWord ψ [i]) :=
        hasCompactSupport_coordinateWord hcψ [i]
      have hsdψ : tsupport (coordinateWord ψ [i]) ⊆ Ω.val :=
        (tsupport_coordinateWord_subset ψ [i]).trans hsψ
      have hpair := compact_test_inner_fderiv_integral Ω hwu hψ hcψ hsψ i
      have hword := ih huTail hdψ hcdψ hsdψ
      have hreverse : coordinateWord ψ (i :: w).reverse =
          coordinateWord (coordinateWord ψ [i]) w.reverse := by
        rw [List.reverse_cons, coordinateWord_append]
      refine ⟨hpair.1, ?_, ?_⟩
      · simpa only [hreverse] using hword.2.1
      · rw [coordinateWord_cons, hpair.2.2]
        change -(∫ x in Ω.val, inner ℝ (coordinateWord u w x) (coordinateWord ψ [i] x)) = _
        rw [hword.2.2, hreverse, List.length_cons, pow_succ]
        ring

theorem compact_test_inner_coordinateWord_integral_same_order {n q : ℕ}
    (Ω : OpenDomain n) {u : Domain n → Ambient q} (w : List (Fin n))
    (hu : ContDiffOn ℝ w.length u Ω.val)
    {ψ : Domain n → Ambient q} (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Ω.val) :
    IntegrableOn (fun x => inner ℝ (coordinateWord u w x) (ψ x)) Ω.val ∧
    IntegrableOn (fun x => inner ℝ (u x) (coordinateWord ψ w x)) Ω.val ∧
    (∫ x in Ω.val, inner ℝ (coordinateWord u w x) (ψ x)) =
      (-1 : ℝ) ^ w.length *
        (∫ x in Ω.val, inner ℝ (u x) (coordinateWord ψ w x)) := by
  have hword := compact_test_inner_coordinateWord_integral Ω w hu hψ hcψ hsψ
  have hψword : ContDiffOn ℝ w.length ψ Ω.val := hψ.contDiffOn.of_le
    (le_of_lt (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top w.length)))
  have hreverse := coordinateWord_reverse_eq Ω w hψword
  have hrightEq : (fun x => inner ℝ (u x) (coordinateWord ψ w.reverse x)) =ᵐ[
      volume.restrict Ω.val] (fun x => inner ℝ (u x) (coordinateWord ψ w x)) := by
    filter_upwards [ae_restrict_mem Ω.property.measurableSet] with x hx
    rw [hreverse hx]
  refine ⟨hword.1, hword.2.1.congr hrightEq, ?_⟩
  rw [hword.2.2, integral_congr_ae hrightEq]

theorem memW12Loc_coordinateWord {n q : ℕ} (Ω : OpenDomain n)
    {u : Domain n → Ambient q} (w : List (Fin n))
    (hu : ContDiffOn ℝ ((w.length + 1 : ℕ) : ℕ∞ω) u Ω.val) :
    MemW12Loc Ω (coordinateWord u w)
      (fun x i => fderiv ℝ (coordinateWord u w) x (EuclideanSpace.single i 1)) :=
  memW12Loc_of_contDiffOn_one Ω (contDiffOn_coordinateWord Ω w 1 hu)

theorem WeakPoissonOn.coordinate_word {n q : ℕ} (Ω : OpenDomain n)
    {u F : Domain n → Ambient q} (w : List (Fin n))
    (hu : ContDiffOn ℝ ((w.length + 1 : ℕ) : ℕ∞ω) u Ω.val)
    (hF : ContDiffOn ℝ w.length F Ω.val)
    (hEq : WeakPoissonOn Ω
      (fun x i => fderiv ℝ u x (EuclideanSpace.single i 1)) F) :
    MemW12Loc Ω (coordinateWord u w)
      (fun x i => fderiv ℝ (coordinateWord u w) x (EuclideanSpace.single i 1)) ∧
    WeakPoissonOn Ω
      (fun x i => fderiv ℝ (coordinateWord u w) x (EuclideanSpace.single i 1))
      (coordinateWord F w) := by
  induction w with
  | nil =>
      refine ⟨memW12Loc_coordinateWord Ω [] hu, ?_⟩
      exact hEq
  | cons i w ih =>
      have huTail : ContDiffOn ℝ ((w.length + 1 : ℕ) : ℕ∞ω) u Ω.val :=
        hu.of_le (by exact_mod_cast Nat.le_succ (w.length + 1))
      have hFTail : ContDiffOn ℝ w.length F Ω.val :=
        hF.of_le (by exact_mod_cast Nat.le_succ w.length)
      have htailEq := (ih huTail hFTail).2
      have hwu : ContDiffOn ℝ 2 (coordinateWord u w) Ω.val := by
        apply contDiffOn_coordinateWord Ω w 2
        simpa only [List.length_cons, Nat.add_assoc] using hu
      have hwF : ContDiffOn ℝ 1 (coordinateWord F w) Ω.val :=
        contDiffOn_coordinateWord Ω w 1 hF
      exact htailEq.coordinateDerivative Ω hwu hwF i

theorem WeakPoissonOn.coordinate_word_of_length_le {n q k : ℕ} (Ω : OpenDomain n)
    {u F : Domain n → Ambient q}
    (hu : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) u Ω.val) (hF : ContDiffOn ℝ k F Ω.val)
    (hEq : WeakPoissonOn Ω
      (fun x i => fderiv ℝ u x (EuclideanSpace.single i 1)) F)
    (w : List (Fin n)) (hw : w.length ≤ k) :
    MemW12Loc Ω (coordinateWord u w)
      (fun x i => fderiv ℝ (coordinateWord u w) x (EuclideanSpace.single i 1)) ∧
    WeakPoissonOn Ω
      (fun x i => fderiv ℝ (coordinateWord u w) x (EuclideanSpace.single i 1))
      (coordinateWord F w) :=
  hEq.coordinate_word Ω w (hu.of_le (by exact_mod_cast Nat.add_le_add_right hw 1))
    (hF.of_le (by exact_mod_cast hw))

theorem WeakPoissonOn.coordinate_word_on_subset {n q k : ℕ} {Ω Ω' : OpenDomain n}
    {u F : Domain n → Ambient q} (hsub : Ω'.val ⊆ Ω.val)
    (hu : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) u Ω.val) (hF : ContDiffOn ℝ k F Ω.val)
    (hEq : WeakPoissonOn Ω
      (fun x i => fderiv ℝ u x (EuclideanSpace.single i 1)) F)
    (w : List (Fin n)) (hw : w.length ≤ k) :
    MemW12Loc Ω' (coordinateWord u w)
      (fun x i => fderiv ℝ (coordinateWord u w) x (EuclideanSpace.single i 1)) ∧
    WeakPoissonOn Ω'
      (fun x i => fderiv ℝ (coordinateWord u w) x (EuclideanSpace.single i 1))
      (coordinateWord F w) :=
  (hEq.mono hsub).coordinate_word_of_length_le Ω' (hu.mono hsub) (hF.mono hsub) w hw

theorem WeakPoissonOn.coordinate_words {n q k : ℕ} (Ω : OpenDomain n)
    {u F : Domain n → Ambient q}
    (hu : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) u Ω.val) (hF : ContDiffOn ℝ k F Ω.val)
    (hEq : WeakPoissonOn Ω
      (fun x i => fderiv ℝ u x (EuclideanSpace.single i 1)) F) :
    ∀ w : List (Fin n), w.length ≤ k →
      ContDiffOn ℝ 1 (coordinateWord u w) Ω.val ∧
      MemW12Loc Ω (coordinateWord u w)
        (fun x i => fderiv ℝ (coordinateWord u w) x (EuclideanSpace.single i 1)) ∧
      WeakPoissonOn Ω
        (fun x i => fderiv ℝ (coordinateWord u w) x (EuclideanSpace.single i 1))
        (coordinateWord F w) := by
  intro w hw
  refine ⟨contDiffOn_coordinateWord Ω w 1
    (hu.of_le (by exact_mod_cast Nat.add_le_add_right hw 1)), ?_⟩
  exact hEq.coordinate_word_of_length_le Ω hu hF w hw

theorem WeakPoissonOn.coordinate_word_ofFn {n q k : ℕ} (Ω : OpenDomain n)
    {u F : Domain n → Ambient q}
    (hu : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) u Ω.val) (hF : ContDiffOn ℝ k F Ω.val)
    (hEq : WeakPoissonOn Ω
      (fun x i => fderiv ℝ u x (EuclideanSpace.single i 1)) F)
    (I : Fin k → Fin n) :
    ContDiffOn ℝ 1 (coordinateWord u (List.ofFn I)) Ω.val ∧
    MemW12Loc Ω (coordinateWord u (List.ofFn I))
      (fun x i => fderiv ℝ (coordinateWord u (List.ofFn I)) x (EuclideanSpace.single i 1)) ∧
    WeakPoissonOn Ω
      (fun x i => fderiv ℝ (coordinateWord u (List.ofFn I)) x (EuclideanSpace.single i 1))
      (coordinateWord F (List.ofFn I)) :=
  hEq.coordinate_words Ω hu hF (List.ofFn I) (by rw [List.length_ofFn])

end HolderToCK
end
