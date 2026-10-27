module

public import HolderToCK.Analysis.WeakPoissonAffine

/-! # Affine transport of actual local Sobolev and weak Poisson data

Compact image sets transport local integrability and local L2 membership.
Inverse affine tests transport the same weak columns multiplied by the dilation
and the same forcing multiplied by its square in the signed Poisson equation.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ENNReal ContDiff Topology

namespace HolderToCK

theorem affineBall_map_restrict_set {n : ℕ} (a b : Domain n) {t : ℝ}
    (ht : 0 < t) (K : Set (Domain n)) :
    Measure.map (fun x => a + t • (x - b)) (volume.restrict K) =
      ENNReal.ofReal ((t ^ n)⁻¹) •
        volume.restrict ((fun x => a + t • (x - b)) '' K) := by
  have he := affineBall_measurableEmbedding a b ht.ne'
  have hpre : (fun x => a + t • (x - b)) ⁻¹'
      ((fun x => a + t • (x - b)) '' K) = K :=
    preimage_image_eq K he.injective
  calc
    _ = (Measure.map (fun x => a + t • (x - b)) volume).restrict
        ((fun x => a + t • (x - b)) '' K) := by rw [he.restrict_map, hpre]
    _ = _ := by rw [affineBall_map_volume a b ht, Measure.restrict_smul]

theorem integrableOn_affineSet_pullback {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (a b : Domain n) {t : ℝ} (ht : 0 < t) {K : Set (Domain n)} {f : Domain n → E}
    (hf : IntegrableOn f ((fun x => a + t • (x - b)) '' K) volume) :
    IntegrableOn (fun x => f (a + t • (x - b))) K volume := by
  have hf' := hf.smul_measure (c := ENNReal.ofReal ((t ^ n)⁻¹)) ENNReal.ofReal_ne_top
  rw [← affineBall_map_restrict_set a b ht K] at hf'
  exact hf'.comp_measurable (affineBall_measurableEmbedding a b ht.ne').measurable

theorem memLp_affineSet_pullback {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (a b : Domain n) {t : ℝ} (ht : 0 < t) {K : Set (Domain n)} {f : Domain n → E}
    {p : ℝ≥0∞} (hf : MemLp f p (volume.restrict ((fun x => a + t • (x - b)) '' K))) :
    MemLp (fun x => f (a + t • (x - b))) p (volume.restrict K) := by
  have hf' := hf.smul_measure (c := ENNReal.ofReal ((t ^ n)⁻¹)) ENNReal.ofReal_ne_top
  rw [← affineBall_map_restrict_set a b ht K] at hf'
  exact hf'.comp_of_map (affineBall_measurableEmbedding a b ht.ne').measurable.aemeasurable

theorem locallyIntegrableOn_affineBall_pullback {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] (a b : Domain n) {r t : ℝ} (ht : 0 < t)
    {f : Domain n → E} (hf : LocallyIntegrableOn f (Metric.ball a r) volume) :
    LocallyIntegrableOn (fun x => f (a + t • (x - b))) (Metric.ball b (r / t)) volume := by
  apply (locallyIntegrableOn_iff Metric.isOpen_ball.isLocallyClosed).mpr
  intro K hKsub hK
  have himage : (fun x => a + t • (x - b)) '' K ⊆ Metric.ball a r := by
    rintro _ ⟨x, hx, rfl⟩
    exact (affineBall_mem_ball_iff a b ht r x).mpr (hKsub hx)
  have hcompact : IsCompact ((fun x => a + t • (x - b)) '' K) :=
    hK.image (affineBall_contDiff a b t).continuous
  exact integrableOn_affineSet_pullback a b ht (hf.integrableOn_compact_subset himage hcompact)

theorem locallyMemL2_affineBall_pullback {n q : ℕ} (a b : Domain n)
    {r t : ℝ} (ht : 0 < t) {f : Domain n → Ambient q}
    (hf : LocallyMemL2 (ballDomain a r) f) :
    LocallyMemL2 (ballDomain b (r / t)) (fun x => f (a + t • (x - b))) := by
  intro K hK hKsub
  have himage : (fun x => a + t • (x - b)) '' K ⊆ (ballDomain a r).val := by
    rintro _ ⟨x, hx, rfl⟩
    exact (affineBall_mem_ball_iff a b ht r x).mpr (hKsub hx)
  exact memLp_affineSet_pullback a b ht
    (hf _ (hK.image (affineBall_contDiff a b t).continuous) himage)

theorem affineBall_inverseTest_coordinateDerivative {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : Domain n → E} (hφ : ContDiff ℝ ∞ φ) (a b : Domain n)
    {t : ℝ} (ht : 0 < t) (i : Fin n) (x : Domain n) :
    fderiv ℝ (fun z => φ (b + t⁻¹ • (z - a))) (a + t • (x - b))
      (EuclideanSpace.single i 1) =
      t⁻¹ • fderiv ℝ φ x (EuclideanSpace.single i 1) := by
  simpa only [coordinateDerivative, affineBall_inverse a b ht.ne'] using
    affineBallTest_coordinateDerivative hφ b a t⁻¹ i (a + t • (x - b))

theorem hasWeakGradient_affineBall_pullback {n q : ℕ} {a : Domain n} {r : ℝ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : HasWeakGradient (ballDomain a r) u Du) (b : Domain n) {t : ℝ} (ht : 0 < t) :
    HasWeakGradient (ballDomain b (r / t)) (fun x => u (a + t • (x - b)))
      (fun x i => t • Du (a + t • (x - b)) i) := by
  refine ⟨locallyIntegrableOn_affineBall_pullback a b ht hu.1, ?_, ?_⟩
  · intro i
    exact (locallyIntegrableOn_affineBall_pullback a b ht (hu.2.1 i)).smul t
  intro i φ hφ hcφ hsφ
  let Ψ : Domain n → ℝ := fun z => φ (b + t⁻¹ • (z - a))
  have hΨ : ContDiff ℝ ∞ Ψ := hφ.comp (affineBall_contDiff b a t⁻¹)
  have hcΨ : HasCompactSupport Ψ := affineBallTest_hasCompactSupport hcφ b a (inv_ne_zero ht.ne')
  have hratio : r / t / t⁻¹ = r := by field_simp
  have hsΨ : tsupport Ψ ⊆ (ballDomain a r).val := by
    simpa only [hratio, Ψ, ballDomain] using
      affineBallTest_tsupport_subset b a (inv_pos.mpr ht) (r / t) hsφ
  have hder (x : Domain n) :
      coordinateDerivative Ψ hΨ i (a + t • (x - b)) =
        t⁻¹ • coordinateDerivative φ hφ i x :=
    affineBall_inverseTest_coordinateDerivative hφ a b ht i x
  let A : Domain n → Ambient q := fun z => coordinateDerivative Ψ hΨ i z • u z
  let B : Domain n → Ambient q := fun z => Ψ z • Du z i
  have hA (x : Domain n) : coordinateDerivative φ hφ i x • u (a + t • (x - b)) =
      t • A (a + t • (x - b)) := by
    simp only [A, hder, smul_eq_mul, smul_smul, ← mul_assoc,
      mul_inv_cancel₀ ht.ne', one_mul]
  have hB (x : Domain n) : φ x • (t • Du (a + t • (x - b)) i) =
      t • B (a + t • (x - b)) := by
    simp only [B, Ψ, affineBall_inverse a b ht.ne']
    exact smul_comm _ _ _
  have heq := hu.2.2 i Ψ hΨ hcΨ hsΨ
  change (∫ z in Metric.ball a r, A z) = -(∫ z in Metric.ball a r, B z) at heq
  change (∫ x in Metric.ball b (r / t), coordinateDerivative φ hφ i x • u (a + t • (x - b))) =
    -(∫ x in Metric.ball b (r / t), φ x • (t • Du (a + t • (x - b)) i))
  rw [setIntegral_congr_fun measurableSet_ball (fun x _ => hA x), integral_smul,
    integral_affineBall a b ht r A,
    setIntegral_congr_fun measurableSet_ball (fun x _ => hB x), integral_smul,
    integral_affineBall a b ht r B, heq, smul_neg, smul_neg]

theorem MemW12Loc.affineBall_pullback_local {n q : ℕ} {a : Domain n} {r : ℝ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12Loc (ballDomain a r) u Du) (b : Domain n) {t : ℝ} (ht : 0 < t) :
    MemW12Loc (ballDomain b (r / t)) (fun x => u (a + t • (x - b)))
      (fun x i => t • Du (a + t • (x - b)) i) := by
  refine ⟨hasWeakGradient_affineBall_pullback hu.1 b ht,
    locallyMemL2_affineBall_pullback a b ht hu.2.1, ?_⟩
  intro i K hK hKsub
  exact (locallyMemL2_affineBall_pullback a b ht (hu.2.2 i) K hK hKsub).const_smul t

theorem WeakPoissonOn.affineBall_pullback_local {n q : ℕ}
    {a : Domain n} {r : ℝ} {F : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hEq : WeakPoissonOn (ballDomain a r) Du F) (b : Domain n) {t : ℝ} (ht : 0 < t) :
    WeakPoissonOn (ballDomain b (r / t))
      (fun x i => t • Du (a + t • (x - b)) i)
      (fun x => t ^ 2 • F (a + t • (x - b))) := by
  refine ⟨(locallyIntegrableOn_affineBall_pullback a b ht hEq.1).smul (t ^ 2), ?_⟩
  intro ψ hψ hcψ hsψ
  let Ψ : Domain n → Ambient q := fun z => ψ (b + t⁻¹ • (z - a))
  have hΨ : ContDiff ℝ ∞ Ψ := hψ.comp (affineBall_contDiff b a t⁻¹)
  have hcΨ : HasCompactSupport Ψ := affineBallTest_hasCompactSupport hcψ b a (inv_ne_zero ht.ne')
  have hratio : r / t / t⁻¹ = r := by field_simp
  have hsΨ : tsupport Ψ ⊆ (ballDomain a r).val := by
    simpa only [hratio, Ψ, ballDomain] using
      affineBallTest_tsupport_subset b a (inv_pos.mpr ht) (r / t) hsψ
  have hder (x : Domain n) (i : Fin n) :
      fderiv ℝ Ψ (a + t • (x - b)) (EuclideanSpace.single i 1) =
        t⁻¹ • fderiv ℝ ψ x (EuclideanSpace.single i 1) :=
    affineBall_inverseTest_coordinateDerivative hψ a b ht i x
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
  refine ⟨hleft', hright', ?_⟩
  change (∫ x in Metric.ball b (r / t), ∑ i : Fin n,
      inner ℝ (t • Du (a + t • (x - b)) i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
    -(∫ x in Metric.ball b (r / t), inner ℝ (t ^ 2 • F (a + t • (x - b))) (ψ x))
  rw [setIntegral_congr_fun measurableSet_ball (fun x _ => hA x), integral_const_mul,
    integral_affineBall a b ht r A,
    setIntegral_congr_fun measurableSet_ball (fun x _ => hB x), integral_const_mul,
    integral_affineBall a b ht r B]
  change (∫ z in Metric.ball a r, A z) = -(∫ z in Metric.ball a r, B z) at heq
  rw [heq, smul_neg, mul_neg]

end HolderToCK
end
