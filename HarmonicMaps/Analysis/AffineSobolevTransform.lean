module

public import HarmonicMaps.Analysis.AffineSobolevBasic
public import HarmonicMaps.Analysis.L2AffineContinuity
public import HarmonicMaps.Analysis.SobolevMollificationGradient

/-!
# Weak Sobolev gradients under centered dilations

The weak test is pulled back by the inverse affine map. Its reciprocal
derivative factor and the affine Jacobian recover the displayed gradient
multiplied by the dilation parameter.
-/

@[expose] public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace HarmonicMaps

noncomputable section

/-- The finite L2 pullback on the expanded ball uses only data on the source ball. -/
theorem memLp_ballAffine_ball {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (a : Domain n) (R : ℝ) {t : ℝ} (ht : 0 < t) {f : Domain n → E}
    (hf : MemLp f 2 (volume.restrict (Metric.ball a R))) :
    MemLp (fun x => f (ballAffine a t x)) 2
      (volume.restrict (Metric.ball a (R / t))) := by
  have hext := memLp_zeroExtension measurableSet_ball hf
  have hcomp := memLp_comp_centeredDilation hext a ht.ne'
  refine MemLp.ae_eq ?_ (hcomp.mono_measure Measure.restrict_le_self)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact indicator_of_mem ((ballAffine_mem_ball_iff a ht R x).mpr hx) f

private theorem setIntegral_test_eq_integral {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set (Domain n)} {φ : Domain n → ℝ} (hs : tsupport φ ⊆ s)
    (f : Domain n → E) :
    (∫ x in s, φ x • f x) = ∫ x, φ x • f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hn : x ∉ tsupport φ := fun h => hx (hs h)
  simp [image_eq_zero_of_notMem_tsupport hn]

private theorem setIntegral_derivativeTest_eq_integral {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set (Domain n)} {φ : Domain n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hs : tsupport φ ⊆ s) (i : Fin n) (f : Domain n → E) :
    (∫ x in s, coordinateDerivative φ hφ i x • f x) =
      ∫ x, coordinateDerivative φ hφ i x • f x := by
  apply setIntegral_test_eq_integral _ f
  exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hs

/-- A positive affine pullback has the actual transformed weak gradient on its
expanded ball. Invertibility and every test condition are proved internally. -/
theorem MemW12.affinePullback_ball {n q : ℕ} {a : Domain n} {R : ℝ}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du) {t : ℝ} (ht : 0 < t) :
    MemW12 (ballDomain a (R / t)) (fun x => u (ballAffine a t x))
      (fun x i => t • Du (ballAffine a t x) i) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a (R / t))) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have huL := memLp_ballAffine_ball a R ht hu.2.1
  have hDuL (i : Fin n) := (memLp_ballAffine_ball a R ht (hu.2.2 i)).const_smul t
  have huInt : IntegrableOn (fun x => u (ballAffine a t x))
      (Metric.ball a (R / t)) := huL.integrable (by norm_num)
  have hDuInt (i : Fin n) : IntegrableOn (fun x => t • Du (ballAffine a t x) i)
      (Metric.ball a (R / t)) := (hDuL i).integrable (by norm_num)
  refine ⟨⟨huInt.locallyIntegrableOn, fun i => (hDuInt i).locallyIntegrableOn, ?_⟩,
    huL, hDuL⟩
  intro i φ hφ hcφ hsφ
  change tsupport φ ⊆ Metric.ball a (R / t) at hsφ
  let ψ : Domain n → ℝ := fun z => φ (ballAffine a t⁻¹ z)
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (ballAffine_contDiff a t⁻¹)
  have hcψ : HasCompactSupport ψ :=
    ballAffineTest_hasCompactSupport hcφ a (inv_ne_zero ht.ne')
  have hsψ : tsupport ψ ⊆ Metric.ball a R := ballAffineTest_tsupport_subset a ht R hsφ
  have hIBP := hu.1.2.2 i ψ hψ hcψ hsψ
  change (∫ z in Metric.ball a R, coordinateDerivative ψ hψ i z • u z) =
    -(∫ z in Metric.ball a R, ψ z • Du z i) at hIBP
  rw [setIntegral_derivativeTest_eq_integral hψ hsψ i u,
    setIntegral_test_eq_integral hsψ (fun z => Du z i)] at hIBP
  have hleft : (∫ x, coordinateDerivative φ hφ i x • u (ballAffine a t x)) =
      (t ^ n)⁻¹ • (t • ∫ z, coordinateDerivative ψ hψ i z • u z) := by
    calc
      (∫ x, coordinateDerivative φ hφ i x • u (ballAffine a t x)) =
          ∫ x, (t * coordinateDerivative ψ hψ i (ballAffine a t x)) •
            u (ballAffine a t x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        have hder := ballAffineTest_coordinateDerivative hφ a t⁻¹ i (ballAffine a t x)
        dsimp [ψ] at hder ⊢
        rw [hder, ballAffine_inverse a ht.ne']
        congr 1
        field_simp
      _ = (t ^ n)⁻¹ • ∫ z, (t * coordinateDerivative ψ hψ i z) • u z :=
        integral_ballAffine a ht
          (fun z => (t * coordinateDerivative ψ hψ i z) • u z)
      _ = (t ^ n)⁻¹ • (t • ∫ z, coordinateDerivative ψ hψ i z • u z) := by
        simp only [mul_smul, integral_smul]
  have hright : (∫ x, φ x • (t • Du (ballAffine a t x) i)) =
      (t ^ n)⁻¹ • (t • ∫ z, ψ z • Du z i) := by
    calc
      (∫ x, φ x • (t • Du (ballAffine a t x) i)) =
          ∫ x, t • (ψ (ballAffine a t x) • Du (ballAffine a t x) i) := by
        apply integral_congr_ae
        filter_upwards [] with x
        change φ x • (t • Du (ballAffine a t x) i) =
          t • (φ (ballAffine a t⁻¹ (ballAffine a t x)) • Du (ballAffine a t x) i)
        rw [ballAffine_inverse a ht.ne']
        exact smul_comm _ _ _
      _ = (t ^ n)⁻¹ • ∫ z, t • (ψ z • Du z i) :=
        integral_ballAffine a ht (fun z => t • (ψ z • Du z i))
      _ = (t ^ n)⁻¹ • (t • ∫ z, ψ z • Du z i) := by rw [integral_smul]
  change (∫ x in Metric.ball a (R / t), coordinateDerivative φ hφ i x •
    u (ballAffine a t x)) =
    -(∫ x in Metric.ball a (R / t), φ x • (t • Du (ballAffine a t x) i))
  rw [setIntegral_derivativeTest_eq_integral hφ hsφ,
    setIntegral_test_eq_integral hsφ, hleft, hright, hIBP]
  simp only [smul_neg]

end
end HarmonicMaps
