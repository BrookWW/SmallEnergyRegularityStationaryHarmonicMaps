module

public import HolderToCK.Analysis.WeakPoissonMollification
public import HolderToCK.Analysis.WeakPoissonLocality
public import HolderToCK.Foundation.HolderBounds
public import HarmonicMaps.Analysis.AffineBallSobolev
public import HarmonicMaps.Analysis.AffineEnergyScaling

/-! # Actual signed weak Poisson data under positive affine changes

The pullback has weak columns multiplied by the dilation and forcing multiplied
by its square. Compact tests and the two signed integral pairings are transported
through the same inverse affine map. The quadratic constant remains unchanged;
the original Holder coefficient is multiplied by the exact radius power.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace HolderToCK

theorem integrable_affineBall {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (a b : Domain n) {t : ℝ} (ht : 0 < t) (r : ℝ) {f : Domain n → E}
    (hf : IntegrableOn f (Metric.ball a r) volume) :
    IntegrableOn (fun x => f (a + t • (x - b))) (Metric.ball b (r / t)) volume := by
  have hf' := hf.smul_measure (c := ENNReal.ofReal ((t ^ n)⁻¹)) ENNReal.ofReal_ne_top
  rw [← affineBall_map_restrict a b ht r] at hf'
  exact hf'.comp_measurable (affineBall_measurableEmbedding a b ht.ne').measurable

theorem WeakPoissonOn.affineBall_pullback {n q : ℕ}
    {a : Domain n} {r : ℝ} {u F : Domain n → Ambient q}
    {Du : Domain n → Gradient n q}
    (hEq : WeakPoissonOn (ballDomain a r) Du F)
    (hu : MemW12 (ballDomain a r) u Du) (K : ℝ)
    (hBound : ∀ᵐ x ∂volume.restrict (Metric.ball a r), ‖F x‖ ≤ K * hsNormSq (Du x))
    (b : Domain n) {t : ℝ} (ht : 0 < t) :
    WeakPoissonOn (ballDomain b (r / t))
      (fun x i => t • Du (a + t • (x - b)) i)
      (fun x => t ^ 2 • F (a + t • (x - b))) := by
  have hF := hEq.integrable_of_quadratic_bound hu K hBound
  have hF' : IntegrableOn (fun x => t ^ 2 • F (a + t • (x - b)))
      (Metric.ball b (r / t)) volume := by
    change Integrable (t ^ 2 • (fun x => F (a + t • (x - b))))
      (volume.restrict (Metric.ball b (r / t)))
    exact (integrable_affineBall a b ht r hF).smul (t ^ 2)
  refine ⟨hF'.locallyIntegrableOn, ?_⟩
  intro ψ hψ hcψ hsψ
  let Ψ : Domain n → Ambient q := fun z => ψ (b + t⁻¹ • (z - a))
  have hΨ : ContDiff ℝ ∞ Ψ := hψ.comp (affineBall_contDiff b a t⁻¹)
  have hcΨ : HasCompactSupport Ψ :=
    affineBallTest_hasCompactSupport hcψ b a (inv_ne_zero ht.ne')
  have hratio : r / t / t⁻¹ = r := by field_simp
  have hsΨ : tsupport Ψ ⊆ (ballDomain a r).val := by
    simpa only [hratio, Ψ, ballDomain] using
      affineBallTest_tsupport_subset b a (inv_pos.mpr ht) (r / t) hsψ
  have hder (x : Domain n) (i : Fin n) :
      fderiv ℝ Ψ (a + t • (x - b)) (EuclideanSpace.single i 1) =
        t⁻¹ • fderiv ℝ ψ x (EuclideanSpace.single i 1) := by
    simpa only [coordinateDerivative, Ψ, affineBall_inverse a b ht.ne'] using
      affineBallTest_coordinateDerivative hψ b a t⁻¹ i (a + t • (x - b))
  obtain ⟨hleft, hright, heq⟩ := hEq.2 Ψ hΨ hcΨ hsΨ
  let A : Domain n → ℝ := fun z => ∑ i : Fin n,
    inner ℝ (Du z i) (fderiv ℝ Ψ z (EuclideanSpace.single i 1))
  let B : Domain n → ℝ := fun z => inner ℝ (F z) (Ψ z)
  have hA (x : Domain n) : (∑ i : Fin n,
      inner ℝ (t • Du (a + t • (x - b)) i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        t ^ 2 * A (a + t • (x - b)) := by
    simp only [A, hder, real_inner_smul_left, real_inner_smul_right, ← Finset.mul_sum]
    field_simp
  have hB (x : Domain n) : inner ℝ (t ^ 2 • F (a + t • (x - b))) (ψ x) =
      t ^ 2 * B (a + t • (x - b)) := by
    simp only [B, Ψ, affineBall_inverse a b ht.ne', real_inner_smul_left]
  have hleft' : IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (t • Du (a + t • (x - b)) i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))
      (Metric.ball b (r / t)) volume :=
    ((integrable_affineBall a b ht r hleft).const_mul (t ^ 2)).congr
      (Eventually.of_forall fun x => (hA x).symm)
  have hright' : IntegrableOn (fun x => inner ℝ (t ^ 2 • F (a + t • (x - b))) (ψ x))
      (Metric.ball b (r / t)) volume :=
    ((integrable_affineBall a b ht r hright).const_mul (t ^ 2)).congr
      (Eventually.of_forall fun x => (hB x).symm)
  have hleftEq : (∫ x in Metric.ball b (r / t), ∑ i : Fin n,
      inner ℝ (t • Du (a + t • (x - b)) i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      t ^ 2 * ((t ^ n)⁻¹ * ∫ z in Metric.ball a r, A z) := by
    calc
      _ = ∫ x in Metric.ball b (r / t), t ^ 2 * A (a + t • (x - b)) :=
        setIntegral_congr_fun measurableSet_ball (fun x _ => hA x)
      _ = t ^ 2 * ∫ x in Metric.ball b (r / t), A (a + t • (x - b)) := integral_const_mul _ _
      _ = _ := by rw [integral_affineBall a b ht r A, smul_eq_mul]
  have hrightEq : (∫ x in Metric.ball b (r / t), inner ℝ (t ^ 2 • F (a + t • (x - b))) (ψ x)) =
      t ^ 2 * ((t ^ n)⁻¹ * ∫ z in Metric.ball a r, B z) := by
    calc
      _ = ∫ x in Metric.ball b (r / t), t ^ 2 * B (a + t • (x - b)) :=
        setIntegral_congr_fun measurableSet_ball (fun x _ => hB x)
      _ = t ^ 2 * ∫ x in Metric.ball b (r / t), B (a + t • (x - b)) := integral_const_mul _ _
      _ = _ := by rw [integral_affineBall a b ht r B, smul_eq_mul]
  refine ⟨hleft', hright', ?_⟩
  dsimp only [ballDomain]
  rw [hleftEq, hrightEq]
  change (∫ z in Metric.ball a r, A z) = -(∫ z in Metric.ball a r, B z) at heq
  rw [heq, mul_neg, mul_neg]

theorem quadratic_forcing_bound_affineBall {n q : ℕ}
    (a b : Domain n) {r t K : ℝ} (ht : 0 < t)
    {F : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hBound : ∀ᵐ x ∂volume.restrict (Metric.ball a r), ‖F x‖ ≤ K * hsNormSq (Du x)) :
    ∀ᵐ x ∂volume.restrict (Metric.ball b (r / t)),
      ‖t ^ 2 • F (a + t • (x - b))‖ ≤
        K * hsNormSq (fun i => t • Du (a + t • (x - b)) i) := by
  filter_upwards [ae_affineBall a b ht r hBound] with x hx
  rw [norm_smul, Real.norm_of_nonneg (sq_nonneg t), hsNormSq_const_smul]
  exact (mul_le_mul_of_nonneg_left hx (sq_nonneg t)).trans_eq (by ring)

theorem HolderBoundOn.affineBall_pullback {n q : ℕ}
    {a : Domain n} {r α H : ℝ} {u : Domain n → Ambient q}
    (hHolder : HolderBoundOn (Metric.ball a r) u α H)
    (b : Domain n) {t : ℝ} (ht : 0 < t) :
    HolderBoundOn (Metric.ball b (r / t)) (fun x => u (a + t • (x - b))) α
      (H * Real.rpow t α) := by
  intro x hx y hy
  have hdist : dist (a + t • (x - b)) (a + t • (y - b)) = t * dist x y := by
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, sub_sub_sub_cancel_right,
      norm_smul, Real.norm_of_nonneg ht.le, dist_eq_norm]
  calc
    _ ≤ H * Real.rpow (dist (a + t • (x - b)) (a + t • (y - b))) α :=
      hHolder _ ((affineBall_mem_ball_iff a b ht r x).mpr hx)
        _ ((affineBall_mem_ball_iff a b ht r y).mpr hy)
    _ = _ := by
      rw [hdist]
      simp only [Real.rpow_eq_pow]
      rw [Real.mul_rpow ht.le dist_nonneg]
      ring

theorem quadratic_poisson_affine_unit_data {n q : ℕ}
    (a : Domain n) (R : PositiveRadius)
    {u F : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R.val) u Du)
    (hEq : WeakPoissonOn (ballDomain a R.val) Du F)
    {α H K : ℝ} (hHolder : HolderBoundOn (Metric.ball a R.val) u α H)
    (hBound : ∀ᵐ x ∂volume.restrict (Metric.ball a R.val), ‖F x‖ ≤ K * hsNormSq (Du x)) :
    MemW12 (ballDomain (0 : Domain n) 1) (fun z => u (a + R.val • z))
      (fun z i => R.val • Du (a + R.val • z) i) ∧
    WeakPoissonOn (ballDomain (0 : Domain n) 1)
      (fun z i => R.val • Du (a + R.val • z) i)
      (fun z => R.val ^ 2 • F (a + R.val • z)) ∧
    HolderBoundOn (Metric.ball (0 : Domain n) 1) (fun z => u (a + R.val • z)) α
      (H * Real.rpow R.val α) ∧
    (∀ᵐ z ∂volume.restrict (Metric.ball (0 : Domain n) 1),
      ‖R.val ^ 2 • F (a + R.val • z)‖ ≤
        K * hsNormSq (fun i => R.val • Du (a + R.val • z) i)) := by
  have hu' := hu.affineBall_pullback (0 : Domain n) R.property
  have hEq' := hEq.affineBall_pullback hu K hBound (0 : Domain n) R.property
  have hHolder' := hHolder.affineBall_pullback (0 : Domain n) R.property
  have hBound' := quadratic_forcing_bound_affineBall a (0 : Domain n) R.property hBound
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [div_self R.property.ne', sub_zero] using hu'
  · simpa only [div_self R.property.ne', sub_zero] using hEq'
  · simpa only [div_self R.property.ne', sub_zero] using hHolder'
  · simpa only [div_self R.property.ne', sub_zero] using hBound'

theorem quadratic_forcing_affine_identity {n q : ℕ}
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (a : Domain n) (t : ℝ) (z : Domain n) :
    t ^ 2 • (∑ i : Fin n, A (u (a + t • z)) (Du (a + t • z) i) (Du (a + t • z) i)) =
      ∑ i : Fin n, A (u (a + t • z)) (t • Du (a + t • z) i) (t • Du (a + t • z) i) := by
  simp only [map_smul, smul_apply, smul_smul, ← Finset.smul_sum, pow_two]

theorem quadratic_poisson_affine_unit_equation {n q : ℕ}
    (a : Domain n) (R : PositiveRadius)
    (A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q)
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R.val) u Du)
    (hEq : WeakPoissonOn (ballDomain a R.val) Du
      (fun x => ∑ i : Fin n, A (u x) (Du x i) (Du x i))) (K : ℝ)
    (hBound : ∀ᵐ x ∂volume.restrict (Metric.ball a R.val),
      ‖∑ i : Fin n, A (u x) (Du x i) (Du x i)‖ ≤ K * hsNormSq (Du x)) :
    WeakPoissonOn (ballDomain (0 : Domain n) 1)
      (fun z i => R.val • Du (a + R.val • z) i)
      (fun z => ∑ i : Fin n, A (u (a + R.val • z))
        (R.val • Du (a + R.val • z) i) (R.val • Du (a + R.val • z) i)) := by
  have hEq' : WeakPoissonOn (ballDomain (0 : Domain n) 1)
      (fun z i => R.val • Du (a + R.val • z) i)
      (fun z => R.val ^ 2 • (∑ i : Fin n, A (u (a + R.val • z))
        (Du (a + R.val • z) i) (Du (a + R.val • z) i))) := by
    simpa only [sub_zero, div_self R.property.ne'] using
      hEq.affineBall_pullback hu K hBound (0 : Domain n) R.property
  exact hEq'.congr (EventuallyEq.refl _ _) (Eventually.of_forall fun z =>
    quadratic_forcing_affine_identity A u Du a R.val z)

end HolderToCK
end
