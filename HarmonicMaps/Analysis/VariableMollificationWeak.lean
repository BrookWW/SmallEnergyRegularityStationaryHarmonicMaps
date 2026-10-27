module

public import HarmonicMaps.Analysis.VariableMollificationSmooth
public import HarmonicMaps.Analysis.VariableMollificationBounds
public import HarmonicMaps.Analysis.SmoothWeakGradient

/-!
# Weak columns from the local smooth averaging formula

Differentiability is needed only on the actual open ball. Compact tests
vanish outside that ball, so ordinary integration by parts identifies the
displayed locally classical columns without a global smoothness assumption.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- Locally classical derivatives and finite ball L2 data give the literal
Sobolev predicate on that ball. -/
theorem memW12_ball_of_differentiableAt {n q : ℕ} {a : Domain n} {R : ℝ}
    {f : Domain n → Ambient q} {Df : Domain n → Gradient n q}
    (hfd : ∀ x ∈ Metric.ball a R, DifferentiableAt ℝ f x)
    (hD : ∀ x ∈ Metric.ball a R, ∀ i : Fin n,
      fderiv ℝ f x (EuclideanSpace.single i 1) = Df x i)
    (hf : MemLp f 2 (volume.restrict (Metric.ball a R)))
    (hDf : ∀ i : Fin n, MemLp (fun x => Df x i) 2 (volume.restrict (Metric.ball a R))) :
    MemW12 (ballDomain a R) f Df := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  refine ⟨⟨IntegrableOn.locallyIntegrableOn (hf.integrable (by norm_num)),
    fun i => IntegrableOn.locallyIntegrableOn ((hDf i).integrable (by norm_num)), ?_⟩, hf, hDf⟩
  intro i φ hφ hcφ hsφ
  have htest : MemLp φ ∞ (volume.restrict (Metric.ball a R)) :=
    hφ.continuous.memLp_top_of_hasCompactSupport hcφ _
  have hdφ : Continuous (coordinateDerivative φ hφ i) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdφ : HasCompactSupport (coordinateDerivative φ hφ i) :=
    hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hdtest : MemLp (coordinateDerivative φ hφ i) ∞ (volume.restrict (Metric.ball a R)) :=
    hdφ.memLp_top_of_hasCompactSupport hcdφ _
  have hleftOn : IntegrableOn (fun x => coordinateDerivative φ hφ i x • f x)
      (Metric.ball a R) volume := (hf.integrable (by norm_num)).smul_of_top_right hdtest
  have hrightOn : IntegrableOn (fun x => φ x • Df x i) (Metric.ball a R) volume :=
    ((hDf i).integrable (by norm_num)).smul_of_top_right htest
  have hvalueOn : IntegrableOn (fun x => φ x • f x) (Metric.ball a R) volume :=
    (hf.integrable (by norm_num)).smul_of_top_right htest
  have hleftZero (x : Domain n) (hx : x ∉ Metric.ball a R) :
      coordinateDerivative φ hφ i x • f x = 0 := by
    have hnot : x ∉ tsupport φ := fun hmem => hx (hsφ hmem)
    have hdnot : x ∉ tsupport (coordinateDerivative φ hφ i) :=
      fun hmem => hnot (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) hmem)
    rw [image_eq_zero_of_notMem_tsupport hdnot, zero_smul]
  have hscalarZero (x : Domain n) (hx : x ∉ Metric.ball a R) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hmem => hx (hsφ hmem))
  have hl : Integrable (fun x => coordinateDerivative φ hφ i x • f x) volume := by
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp hleftOn
    intro x hx
    by_contra hxnot
    exact hx (hleftZero x hxnot)
  have hr : Integrable (fun x => φ x • fderiv ℝ f x (EuclideanSpace.single i 1)) volume := by
    have hi : IntegrableOn (fun x => φ x • fderiv ℝ f x (EuclideanSpace.single i 1))
        (Metric.ball a R) volume := hrightOn.congr_fun
          (fun x hx => by rw [hD x hx i]) measurableSet_ball
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
    intro x hx
    by_contra hxnot
    exact hx (by simp only [hscalarZero x hxnot, zero_smul])
  have hv : Integrable (fun x => φ x • f x) volume := by
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp hvalueOn
    intro x hx
    by_contra hxnot
    exact hx (by simp only [hscalarZero x hxnot, zero_smul])
  have hIBP := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (f := φ) (g := f) (v := EuclideanSpace.single i 1) hl hr hv
    (fun _ _ => (hφ.differentiable (by simp)).differentiableAt)
    (fun x hx => hfd x (hsφ hx))
  have hleftEq : (∫ x in Metric.ball a R, coordinateDerivative φ hφ i x • f x) =
      ∫ x, coordinateDerivative φ hφ i x • f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hleftZero
  have hrightEq : (∫ x in Metric.ball a R, φ x • Df x i) =
      ∫ x, φ x • fderiv ℝ f x (EuclideanSpace.single i 1) := by
    calc
      _ = ∫ x in Metric.ball a R, φ x • fderiv ℝ f x (EuclideanSpace.single i 1) :=
        setIntegral_congr_fun measurableSet_ball fun x hx => by rw [hD x hx i]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hscalarZero x hx, zero_smul])
  change (∫ x in Metric.ball a R, coordinateDerivative φ hφ i x • f x) =
    -(∫ x in Metric.ball a R, φ x • Df x i)
  rw [hleftEq, hrightEq]
  exact neg_eq_iff_eq_neg.mp hIBP.symm

end HarmonicMaps
