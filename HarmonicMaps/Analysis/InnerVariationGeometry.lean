module

public import HarmonicMaps.Analysis.VariableShiftInverseSmooth
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Geometry of compactly supported inner variations

A smooth compactly supported vector field generates global smooth bijections
`x ↦ x + t • ζ x` on a two-sided interval about zero. The differential bound
comes from compact support. A ball containing the support is preserved.
-/

public section

open Set Filter Topology
open scoped ContDiff

namespace HarmonicMaps

/-- Compact support and smoothness give a strictly positive global derivative bound. -/
theorem innerVariation_exists_derivative_bound {n : ℕ} {ζ : Domain n → Domain n}
    (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ) :
    ∃ L : ℝ, 0 < L ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ L := by
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hζ.continuous_fderiv (by simp))
  exact ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun x => (hC x).trans (le_max_right _ _)⟩

/-- The differential of the literal inner variation. -/
theorem innerVariation_hasFDerivAt {n : ℕ} {ζ : Domain n → Domain n}
    (hζ : ContDiff ℝ ∞ ζ) (t : ℝ) (x : Domain n) :
    HasFDerivAt (fun y => y + t • ζ y)
      (ContinuousLinearMap.id ℝ (Domain n) + t • fderiv ℝ ζ x) x := by
  exact (hasFDerivAt_id x).add
    ((hζ.differentiable (by simp) x).hasFDerivAt.const_smul t)

/-- A small bounded derivative gives both metric bounds for an inner variation. -/
theorem innerVariation_norm_sub_bounds {n : ℕ} {ζ : Domain n → Domain n}
    (hζ : ContDiff ℝ ∞ ζ) {L : ℝ} (hL : 0 ≤ L)
    (hD : ∀ x, ‖fderiv ℝ ζ x‖ ≤ L) (t : ℝ) (x y : Domain n) :
    (1 - |t| * L) * ‖x - y‖ ≤ ‖(x + t • ζ x) - (y + t • ζ y)‖ ∧
    ‖(x + t • ζ x) - (y + t • ζ y)‖ ≤ (1 + |t| * L) * ‖x - y‖ := by
  have hlip : LipschitzWith ⟨L, hL⟩ ζ := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hζ.differentiable (by simp))
    intro z
    exact_mod_cast hD z
  have hb : ‖t • (ζ x - ζ y)‖ ≤ (|t| * L) * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hlip.norm_sub_le x y) (abs_nonneg t)
  have heq : (x + t • ζ x) - (y + t • ζ y) = (x - y) + t • (ζ x - ζ y) := by
    rw [smul_sub]
    abel
  rw [heq]
  constructor
  · have hn := norm_sub_norm_le (x - y) (-(t • (ζ x - ζ y)))
    rw [norm_neg, sub_neg_eq_add] at hn
    nlinarith only [hn, hb]
  · have hn := norm_add_le (x - y) (t • (ζ x - ζ y))
    nlinarith only [hn, hb]

/-- A small derivative perturbation of the identity is a global bijection. -/
theorem innerVariation_bijective {n : ℕ} {ζ : Domain n → Domain n}
    (hζ : ContDiff ℝ ∞ ζ) {L : ℝ} (hL : 0 ≤ L)
    (hD : ∀ x, ‖fderiv ℝ ζ x‖ ≤ L) {t : ℝ} (ht : |t| * L < 1) :
    Function.Bijective (fun x => x + t • ζ x) := by
  have hlip : LipschitzWith ⟨L, hL⟩ ζ := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hζ.differentiable (by simp))
    intro z
    exact_mod_cast hD z
  constructor
  · intro x y hxy
    dsimp only at hxy
    have hb := (innerVariation_norm_sub_bounds hζ hL hD t x y).1
    rw [hxy, sub_self, norm_zero] at hb
    have hz : ‖x - y‖ = 0 := by
      nlinarith only [hb, ht, norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro z
    have hcontract : ContractingWith ⟨|t| * L, mul_nonneg (abs_nonneg _) hL⟩
        (fun x => z - t • ζ x) := by
      refine ⟨ht, LipschitzWith.of_dist_le_mul ?_⟩
      intro x y
      change dist (z - t • ζ x) (z - t • ζ y) ≤ (|t| * L) * dist x y
      rw [dist_sub_left, dist_smul₀, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hlip.dist_le_mul x y) (abs_nonneg t)
    refine ⟨hcontract.fixedPoint, ?_⟩
    have hf := hcontract.fixedPoint_isFixedPt
    change z - t • ζ hcontract.fixedPoint = hcontract.fixedPoint at hf
    exact (eq_sub_iff_add_eq.mp hf.symm)

private theorem innerVariation_contDiff_inverse {n : ℕ} {ζ : Domain n → Domain n}
    (hζ : ContDiff ℝ ∞ ζ) {L : ℝ} (hL : 0 ≤ L)
    (hD : ∀ x, ‖fderiv ℝ ζ x‖ ≤ L) {t : ℝ} (ht : |t| * L < 1)
    {g : Domain n → Domain n} (hg : ∀ z, g z + t • ζ (g z) = z) :
    ContDiff ℝ ∞ g := by
  have hfi := (innerVariation_bijective hζ hL hD ht).1
  have hs : ContDiff ℝ ∞ (fun x => x + t • ζ x) := contDiff_id.add (hζ.const_smul t)
  apply contDiff_iff_contDiffAt.2
  intro z
  let A := ContinuousLinearMap.id ℝ (Domain n) + t • fderiv ℝ ζ (g z)
  have hsmall : ‖-(t • fderiv ℝ ζ (g z))‖ < 1 := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hD (g z)) (abs_nonneg t)).trans_lt ht
  have hu : IsUnit A := by
    change IsUnit (1 + t • fderiv ℝ ζ (g z))
    rw [← sub_neg_eq_add]
    exact isUnit_one_sub_of_norm_lt_one hsmall
  have hb := ContinuousLinearMap.isUnit_iff_bijective.mp hu
  let e := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have he : HasFDerivAt (fun x => x + t • ζ x)
      (e : Domain n →L[ℝ] Domain n) (g z) := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact innerVariation_hasFDerivAt hζ t (g z)
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hright := (hs.contDiffAt.hasStrictFDerivAt' he hn).eventually_right_inverse
  have heq : g =ᶠ[𝓝 (g z + t • ζ (g z))] hs.contDiffAt.localInverse he hn := by
    filter_upwards [hright] with w hw
    exact hfi ((hg w).trans hw.symm)
  have hi := (hs.contDiffAt.to_localInverse he hn).congr_of_eventuallyEq heq
  rw [hg z] at hi
  exact hi

/-- The unique global inverse is smooth and obeys a quantitative distance bound. -/
theorem innerVariation_existsUnique_smooth_inverse {n : ℕ} {ζ : Domain n → Domain n}
    (hζ : ContDiff ℝ ∞ ζ) {L : ℝ} (hL : 0 ≤ L)
    (hD : ∀ x, ‖fderiv ℝ ζ x‖ ≤ L) {t : ℝ} (ht : |t| * L < 1) :
    ∃! g : Domain n → Domain n,
      (∀ z, g z + t • ζ (g z) = z) ∧
      (∀ x, g (x + t • ζ x) = x) ∧ ContDiff ℝ ∞ g ∧
      (∀ z w, ‖g z - g w‖ ≤ (1 / (1 - |t| * L)) * ‖z - w‖) := by
  classical
  have hb := innerVariation_bijective hζ hL hD ht
  let e := Equiv.ofBijective (fun x => x + t • ζ x) hb
  have hr : ∀ z, e.symm z + t • ζ (e.symm z) = z := e.apply_symm_apply
  have hl : ∀ x, e.symm (x + t • ζ x) = x := e.symm_apply_apply
  refine ⟨e.symm, ⟨hr, hl, innerVariation_contDiff_inverse hζ hL hD ht hr, ?_⟩, ?_⟩
  · intro z w
    have hbnd := (innerVariation_norm_sub_bounds hζ hL hD t (e.symm z) (e.symm w)).1
    rw [hr z, hr w] at hbnd
    rw [one_div, ← div_eq_inv_mul]
    exact (le_div_iff₀ (sub_pos.mpr ht)).mpr (by simpa only [mul_comm] using hbnd)
  · intro g hg
    funext z
    exact hb.1 ((hg.1 z).trans (hr z).symm)

/-- Both maps and their derivatives have uniform bound two when the perturbation
has derivative norm at most one half. The inverse equations are the only data
required of the already constructed inverse. -/
theorem innerVariation_uniform_bounds {n : ℕ} {ζ : Domain n → Domain n}
    (hζ : ContDiff ℝ ∞ ζ) {L : ℝ} (hL : 0 ≤ L)
    (hD : ∀ x, ‖fderiv ℝ ζ x‖ ≤ L) {t : ℝ} (ht : |t| * L ≤ 1 / 2)
    {g : Domain n → Domain n} (hg : ∀ z, g z + t • ζ (g z) = z) :
    LipschitzWith 2 (fun x => x + t • ζ x) ∧ LipschitzWith 2 g ∧
    (∀ x, ‖fderiv ℝ (fun y => y + t • ζ y) x‖ ≤ 2) ∧
    (∀ z, ‖fderiv ℝ g z‖ ≤ 2) := by
  have hf : LipschitzWith 2 (fun x => x + t • ζ x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (x + t • ζ x) (y + t • ζ y) ≤ (2 : ℝ) * dist x y
    rw [dist_eq_norm, dist_eq_norm]
    have hb := (innerVariation_norm_sub_bounds hζ hL hD t x y).2
    have hn := norm_nonneg (x - y)
    nlinarith only [hb, ht, hn]
  have hi : LipschitzWith 2 g := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    change dist (g z) (g w) ≤ (2 : ℝ) * dist z w
    rw [dist_eq_norm, dist_eq_norm]
    have hb := (innerVariation_norm_sub_bounds hζ hL hD t (g z) (g w)).1
    rw [hg z, hg w] at hb
    have hn := norm_nonneg (g z - g w)
    nlinarith only [hb, ht, hn]
  exact ⟨hf, hi, fun _ => norm_fderiv_le_of_lipschitz ℝ hf,
    fun _ => norm_fderiv_le_of_lipschitz ℝ hi⟩

/-- A bijection fixed off a set preserves that set exactly. -/
theorem innerVariation_image_eq_of_fixed_compl {α : Type*} {f : α → α}
    (hf : Function.Bijective f) {s : Set α} (hoff : ∀ x ∉ s, f x = x) :
    f '' s = s := by
  apply Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    by_contra hz
    have hxx := hf.1 (hoff (f x) hz)
    exact hz (hxx.symm ▸ hx)
  · intro z hz
    obtain ⟨x, hx⟩ := hf.2 z
    refine ⟨x, ?_, hx⟩
    by_contra hnot
    rw [hoff x hnot] at hx
    exact hnot (hx ▸ hz)

/-- The source inner variation is a smooth diffeomorphism for every sufficiently
small positive or negative parameter, and preserves its support-containing ball. -/
theorem innerVariation_diffeomorphism {n : ℕ} {ζ : Domain n → Domain n}
    (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ)
    {a : Domain n} {R : ℝ} (hsupp : tsupport ζ ⊆ Metric.ball a R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      ContDiff ℝ ∞ (fun x => x + t • ζ x) ∧
      Function.Bijective (fun x => x + t • ζ x) ∧
      (∃! g : Domain n → Domain n,
        (∀ z, g z + t • ζ (g z) = z) ∧
        (∀ x, g (x + t • ζ x) = x) ∧ ContDiff ℝ ∞ g) ∧
      ((fun x => x + t • ζ x) '' Metric.ball a R = Metric.ball a R) ∧
      (∀ x ∉ Metric.ball a R, x + t • ζ x = x) := by
  obtain ⟨L, hL, hD⟩ := innerVariation_exists_derivative_bound hζ hc
  refine ⟨1 / (2 * L), by positivity, ?_⟩
  intro t ht
  have hsmall : |t| * L < 1 := by
    have ht' := (lt_div_iff₀ (by positivity : 0 < 2 * L)).mp ht
    nlinarith only [ht']
  have hb := innerVariation_bijective hζ hL.le hD hsmall
  have hoff : ∀ x ∉ Metric.ball a R, x + t • ζ x = x := by
    intro x hx
    have hx' : x ∉ tsupport ζ := fun h => hx (hsupp h)
    rw [image_eq_zero_of_notMem_tsupport hx', smul_zero, add_zero]
  refine ⟨contDiff_id.add (hζ.const_smul t), hb, ?_,
    innerVariation_image_eq_of_fixed_compl hb hoff, hoff⟩
  obtain ⟨g, hg, _⟩ := innerVariation_existsUnique_smooth_inverse hζ hL.le hD hsmall
  refine ⟨g, ⟨hg.1, hg.2.1, hg.2.2.1⟩, ?_⟩
  intro k hk
  funext z
  exact hb.1 ((hk.1 z).trans (hg.1 z).symm)

end HarmonicMaps
