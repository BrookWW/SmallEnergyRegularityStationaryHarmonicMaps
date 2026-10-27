module

public import HolderToCK.Foundation.HolderBounds
public import HolderToCK.Analysis.Bootstrap.FirstDerivativeHolder
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Data.Nat.Choose.Sum

/-! # Derivative bounds for products on an open Euclidean domain

The estimates apply to the actual iterated Frechet derivatives. A uniform
bound on each factor through order k gives a factor `2 ^ k` for a bilinear
product. Evaluation of a continuous linear map is treated as a bilinear
product of norm at most one. Two-point differences give Holder estimates
for the same derivative maps; next derivatives supply the lower-order
Holder bounds on bounded convex domains.
-/

public section

open HarmonicMaps Set
open scoped ContDiff

namespace HolderToCK

theorem norm_iteratedFDeriv_clm_apply_on_open {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω : OpenDomain n) {f : Domain n → E →L[ℝ] F} {g : Domain n → E}
    (k : ℕ) (hf : ContDiffOn ℝ k f Ω.val) (hg : ContDiffOn ℝ k g Ω.val)
    (x : Domain n) (hx : x ∈ Ω.val) :
    ‖iteratedFDeriv ℝ k (fun y => f y (g y)) x‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖ := by
  have h := norm_iteratedFDerivWithin_clm_apply hf hg Ω.property.uniqueDiffOn hx le_rfl
  simpa only [iteratedFDerivWithin_of_isOpen _ Ω.property hx] using h

theorem norm_iteratedFDeriv_clm_apply_const_on_open {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω : OpenDomain n) {f : Domain n → E →L[ℝ] F}
    (k : ℕ) (hf : ContDiffOn ℝ k f Ω.val) (v : E)
    (x : Domain n) (hx : x ∈ Ω.val) :
    ‖iteratedFDeriv ℝ k (fun y => f y v) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ k f x‖ := by
  exact norm_iteratedFDeriv_clm_apply_const (hf.contDiffAt (Ω.property.mem_nhds hx)) le_rfl

theorem real_sum_range_choose (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = (2 : ℝ) ^ k := by
  exact_mod_cast Nat.sum_range_choose k

theorem norm_iteratedFDeriv_clm_apply_le_uniform {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω : OpenDomain n) {f : Domain n → E →L[ℝ] F} {g : Domain n → E}
    (k : ℕ) (hf : ContDiffOn ℝ k f Ω.val) (hg : ContDiffOn ℝ k g Ω.val)
    (x : Domain n) (hx : x ∈ Ω.val) {C D : ℝ} (hC : 0 ≤ C)
    (hfBound : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (hgBound : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ k (fun y => f y (g y)) x‖ ≤ (2 : ℝ) ^ k * C * D := by
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖ :=
      norm_iteratedFDeriv_clm_apply_on_open Ω k hf hg x hx
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfBound i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
          (Nat.cast_nonneg _))
        (hgBound (k - i) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, real_sum_range_choose]

theorem norm_iteratedFDeriv_comp_on_open {n q : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : OpenDomain n) {A : Ambient q → E} {u : Domain n → Ambient q}
    (k : ℕ) (hA : ContDiff ℝ k A) (hu : ContDiffOn ℝ k u Ω.val)
    (x : Domain n) (hx : x ∈ Ω.val) {C D : ℝ}
    (hAderiv : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i A (u x)‖ ≤ C)
    (huderiv : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i u x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ k (A ∘ u) x‖ ≤ (k.factorial : ℝ) * C * D ^ k := by
  have h := norm_iteratedFDerivWithin_comp_le hA.contDiffOn hu le_rfl
    uniqueDiffOn_univ Ω.property.uniqueDiffOn (fun _ _ => mem_univ _) hx
    (by simpa only [iteratedFDerivWithin_univ] using hAderiv)
    (by simpa only [iteratedFDerivWithin_of_isOpen _ Ω.property hx] using huderiv)
  simpa only [iteratedFDerivWithin_of_isOpen _ Ω.property hx] using h

theorem norm_iteratedFDeriv_bilinear_le_uniform {n : ℕ} {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Ω : OpenDomain n) (B : E →L[ℝ] F →L[ℝ] G) (hB : ‖B‖ ≤ 1)
    {f : Domain n → E} {g : Domain n → F} (k : ℕ)
    (hf : ContDiffOn ℝ k f Ω.val) (hg : ContDiffOn ℝ k g Ω.val)
    (x : Domain n) (hx : x ∈ Ω.val) {C D : ℝ} (hC : 0 ≤ C)
    (hfBound : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (hgBound : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ k (fun y => B (f y) (g y)) x‖ ≤ (2 : ℝ) ^ k * C * D := by
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
    hf hg Ω.property.uniqueDiffOn hx le_rfl hB
  simp only [iteratedFDerivWithin_of_isOpen _ Ω.property hx] at h
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖ := h
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfBound i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
          (Nat.cast_nonneg _))
        (hgBound (k - i) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hC)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, real_sum_range_choose]

theorem norm_iteratedFDeriv_zero_sub {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Domain n → E) (x y : Domain n) :
    ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 f y‖ = ‖f x - f y‖ := by
  rw [iteratedFDeriv_zero_eq_comp]
  simp only [Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map]

theorem norm_iteratedFDeriv_fderiv_sub {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Domain n → E) (k : ℕ) (x y : Domain n) :
    ‖iteratedFDeriv ℝ k (fderiv ℝ f) x - iteratedFDeriv ℝ k (fderiv ℝ f) y‖ =
      ‖iteratedFDeriv ℝ (k + 1) f x - iteratedFDeriv ℝ (k + 1) f y‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply]
  rw [← (continuousMultilinearCurryRightEquiv' ℝ k (Domain n) E).symm.map_sub,
    LinearIsometryEquiv.norm_map]

theorem norm_iteratedFDeriv_bilinear_sub_le_uniform {n : ℕ} {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Ω : OpenDomain n) (B : E →L[ℝ] F →L[ℝ] G) (hB : ‖B‖ ≤ 1)
    {f : Domain n → E} {g : Domain n → F} (k : ℕ)
    (hf : ContDiffOn ℝ k f Ω.val) (hg : ContDiffOn ℝ k g Ω.val)
    (x y : Domain n) (hx : x ∈ Ω.val) (hy : y ∈ Ω.val)
    {C D H J : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hfBound : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i f y‖ ≤ C)
    (hgBound : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i g x‖ ≤ D)
    (hfSub : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ ≤ H)
    (hgSub : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i g x - iteratedFDeriv ℝ i g y‖ ≤ J) :
    ‖iteratedFDeriv ℝ k (fun z => B (f z) (g z)) x -
      iteratedFDeriv ℝ k (fun z => B (f z) (g z)) y‖ ≤
      (2 : ℝ) ^ k * (H * D + C * J) := by
  let Ωxy : OpenDomain n := ⟨(fun z => x + z) ⁻¹' Ω.val ∩
      (fun z => y + z) ⁻¹' Ω.val,
    (Ω.property.preimage (continuous_const.add continuous_id)).inter
      (Ω.property.preimage (continuous_const.add continuous_id))⟩
  have hzero : (0 : Domain n) ∈ Ωxy.val :=
    ⟨by simpa only [mem_preimage, add_zero] using hx,
      by simpa only [mem_preimage, add_zero] using hy⟩
  let fx : Domain n → E := fun z => f (x + z)
  let fy : Domain n → E := fun z => f (y + z)
  let gx : Domain n → F := fun z => g (x + z)
  let gy : Domain n → F := fun z => g (y + z)
  have hfx : ContDiffOn ℝ k fx Ωxy.val :=
    hf.comp (contDiffOn_const.add contDiffOn_id) (fun _ hz => hz.1)
  have hfy : ContDiffOn ℝ k fy Ωxy.val :=
    hf.comp (contDiffOn_const.add contDiffOn_id) (fun _ hz => hz.2)
  have hgx : ContDiffOn ℝ k gx Ωxy.val :=
    hg.comp (contDiffOn_const.add contDiffOn_id) (fun _ hz => hz.1)
  have hgy : ContDiffOn ℝ k gy Ωxy.val :=
    hg.comp (contDiffOn_const.add contDiffOn_id) (fun _ hz => hz.2)
  have hfDiff : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i (fun z => fx z - fy z) 0‖ ≤ H := by
    intro i hi
    rw [fun_iteratedFDeriv_sub_apply
      ((hfx.of_le (by exact_mod_cast hi)).contDiffAt (Ωxy.property.mem_nhds hzero))
      ((hfy.of_le (by exact_mod_cast hi)).contDiffAt (Ωxy.property.mem_nhds hzero))]
    simpa only [fx, fy, iteratedFDeriv_comp_add_left, add_zero] using hfSub i hi
  have hgDiff : ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i (fun z => gx z - gy z) 0‖ ≤ J := by
    intro i hi
    rw [fun_iteratedFDeriv_sub_apply
      ((hgx.of_le (by exact_mod_cast hi)).contDiffAt (Ωxy.property.mem_nhds hzero))
      ((hgy.of_le (by exact_mod_cast hi)).contDiffAt (Ωxy.property.mem_nhds hzero))]
    simpa only [gx, gy, iteratedFDeriv_comp_add_left, add_zero] using hgSub i hi
  have hfirst := norm_iteratedFDeriv_bilinear_le_uniform Ωxy B hB k (hfx.sub hfy) hgx
    0 hzero hH hfDiff
    (by simpa only [gx, iteratedFDeriv_comp_add_left, add_zero] using hgBound)
  have hsecond := norm_iteratedFDeriv_bilinear_le_uniform Ωxy B hB k hfy (hgx.sub hgy)
    0 hzero hC
    (by simpa only [fy, iteratedFDeriv_comp_add_left, add_zero] using hfBound) hgDiff
  have hprodX := B.isBoundedBilinearMap.contDiff.comp₂_contDiffOn hfx hgx
  have hprodY := B.isBoundedBilinearMap.contDiff.comp₂_contDiffOn hfy hgy
  have heq : (fun z => B (fx z) (gx z) - B (fy z) (gy z)) =
      (fun z => B (fx z - fy z) (gx z) + B (fy z) (gx z - gy z)) := by
    funext z
    simp only [map_sub, sub_apply]
    abel
  have hsub := fun_iteratedFDeriv_sub_apply
    (hprodX.contDiffAt (Ωxy.property.mem_nhds hzero))
    (hprodY.contDiffAt (Ωxy.property.mem_nhds hzero))
  have hleft : iteratedFDeriv ℝ k (fun z => B (fx z) (gx z)) 0 =
      iteratedFDeriv ℝ k (fun z => B (f z) (g z)) x := by
    exact (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := fun z => B (f z) (g z)) k x 0).trans
      (by rw [add_zero])
  have hright : iteratedFDeriv ℝ k (fun z => B (fy z) (gy z)) 0 =
      iteratedFDeriv ℝ k (fun z => B (f z) (g z)) y := by
    exact (iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := fun z => B (f z) (g z)) k y 0).trans
      (by rw [add_zero])
  rw [← hleft, ← hright, ← hsub, heq,
    fun_iteratedFDeriv_add_apply
      ((B.isBoundedBilinearMap.contDiff.comp₂_contDiffOn (hfx.sub hfy) hgx).contDiffAt
        (Ωxy.property.mem_nhds hzero))
      ((B.isBoundedBilinearMap.contDiff.comp₂_contDiffOn hfy (hgx.sub hgy)).contDiffAt
        (Ωxy.property.mem_nhds hzero))]
  exact (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

theorem iteratedFDeriv_bilinear_holderBoundOn {n : ℕ} {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Ω : OpenDomain n) (B : E →L[ℝ] F →L[ℝ] G) (hB : ‖B‖ ≤ 1)
    {f : Domain n → E} {g : Domain n → F} (k : ℕ)
    (hf : ContDiffOn ℝ k f Ω.val) (hg : ContDiffOn ℝ k g Ω.val)
    {C D H J γ : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hfBound : ∀ x ∈ Ω.val, ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (hgBound : ∀ x ∈ Ω.val, ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i g x‖ ≤ D)
    (hfHolder : ∀ i, i ≤ k → HolderBoundOn Ω.val (iteratedFDeriv ℝ i f) γ H)
    (hgHolder : ∀ i, i ≤ k → HolderBoundOn Ω.val (iteratedFDeriv ℝ i g) γ J) :
    HolderBoundOn Ω.val (iteratedFDeriv ℝ k (fun z => B (f z) (g z))) γ
      ((2 : ℝ) ^ k * (H * D + C * J)) := by
  intro x hx y hy
  have h := norm_iteratedFDeriv_bilinear_sub_le_uniform Ω B hB k hf hg x y hx hy hC
    (mul_nonneg hH (Real.rpow_nonneg dist_nonneg _)) (hfBound y hy) (hgBound x hx)
    (fun i hi => hfHolder i hi x hx y hy) (fun i hi => hgHolder i hi x hx y hy)
  exact h.trans_eq (by
    change (2 : ℝ) ^ k * (H * (dist x y) ^ γ * D + C * (J * (dist x y) ^ γ)) =
      ((2 : ℝ) ^ k * (H * D + C * J)) * (dist x y) ^ γ
    ring)

theorem iteratedFDeriv_clm_apply_holderBoundOn {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω : OpenDomain n) {f : Domain n → E →L[ℝ] F} {g : Domain n → E}
    (k : ℕ) (hf : ContDiffOn ℝ k f Ω.val) (hg : ContDiffOn ℝ k g Ω.val)
    {C D H J γ : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hfBound : ∀ x ∈ Ω.val, ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (hgBound : ∀ x ∈ Ω.val, ∀ i, i ≤ k → ‖iteratedFDeriv ℝ i g x‖ ≤ D)
    (hfHolder : ∀ i, i ≤ k → HolderBoundOn Ω.val (iteratedFDeriv ℝ i f) γ H)
    (hgHolder : ∀ i, i ≤ k → HolderBoundOn Ω.val (iteratedFDeriv ℝ i g) γ J) :
    HolderBoundOn Ω.val (iteratedFDeriv ℝ k (fun z => f z (g z))) γ
      ((2 : ℝ) ^ k * (H * D + C * J)) := by
  let B : (E →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ F)
  have hB : ‖B‖ ≤ 1 := by
    simp only [B, ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.apply]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
    simp only [ContinuousLinearMap.coe_id', id, one_mul]
    rfl
  exact iteratedFDeriv_bilinear_holderBoundOn Ω B hB k hf hg hC hH
    hfBound hgBound hfHolder hgHolder

theorem norm_iteratedFDeriv_clm_apply_const_sub_le {n : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω : OpenDomain n) {f : Domain n → E →L[ℝ] F} (k : ℕ)
    (hf : ContDiffOn ℝ k f Ω.val) (v : E)
    (x y : Domain n) (hx : x ∈ Ω.val) (hy : y ∈ Ω.val) :
    ‖iteratedFDeriv ℝ k (fun z => f z v) x - iteratedFDeriv ℝ k (fun z => f z v) y‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ := by
  let L : (E →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F v
  have hL : ‖L‖ ≤ ‖v‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro T
    exact (T.le_opNorm v).trans_eq (mul_comm _ _)
  change ‖iteratedFDeriv ℝ k (L ∘ f) x - iteratedFDeriv ℝ k (L ∘ f) y‖ ≤ _
  rw [L.iteratedFDeriv_comp_left (hf.contDiffAt (Ω.property.mem_nhds hx)) le_rfl,
    L.iteratedFDeriv_comp_left (hf.contDiffAt (Ω.property.mem_nhds hy)) le_rfl]
  have heq : L.compContinuousMultilinearMap (iteratedFDeriv ℝ k f x) -
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ k f y) =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y) := by
    ext z
    exact (map_sub L _ _).symm
  rw [heq]
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

theorem iteratedFDeriv_holderBoundOn_of_next_derivative {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : OpenDomain n) {u : Domain n → E} (k : ℕ)
    (hu : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞ω) u Ω.val) (hConvex : Convex ℝ Ω.val)
    {C D γ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ) (hγone : γ ≤ 1)
    (hderiv : ∀ x ∈ Ω.val, ‖iteratedFDeriv ℝ (k + 1) u x‖ ≤ C)
    (hDiameter : ∀ x ∈ Ω.val, ∀ y ∈ Ω.val, dist x y ≤ D) :
    HolderBoundOn Ω.val (iteratedFDeriv ℝ k u) γ (C * Real.rpow D (1 - γ)) := by
  intro x hx y hy
  have hLip := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hu.contDiffAt (Ω.property.mem_nhds hz)).differentiableAt_iteratedFDeriv
      (by exact_mod_cast Nat.lt_succ_self k))
    (fun z hz => by rw [norm_fderiv_iteratedFDeriv]; exact hderiv z hz)
    hConvex hy hx
  have hpower := dist_le_diameter_factor_rpow x y (hDiameter x hx y hy) hγ hγone
  calc
    _ ≤ C * dist x y := by simpa only [dist_eq_norm] using hLip
    _ ≤ C * (Real.rpow D (1 - γ) * Real.rpow (dist x y) γ) :=
      mul_le_mul_of_nonneg_left hpower hC
    _ = _ := (mul_assoc _ _ _).symm

end HolderToCK
end
