module

public import HolderToCK.Analysis.WeakPoissonMollification
public import HarmonicMaps.Analysis.AffineBallMeasure

/-! # Signed weak Poisson data under translation of balls

Translation preserves the original forcing and displayed weak columns. Compact
tests and both integral pairings are transported through the same affine map,
with unit Jacobian and no change in the negative weak sign.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff

namespace HolderToCK

theorem integrable_translate_ball {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (a b : Domain n) (r : ℝ) {f : Domain n → E}
    (hf : IntegrableOn f (Metric.ball a r) volume) :
    IntegrableOn (fun x => f (a + (x - b))) (Metric.ball b r) volume := by
  have hmap : Measure.map (fun x : Domain n => a + (x - b))
      (volume.restrict (Metric.ball b r)) = volume.restrict (Metric.ball a r) := by
    simpa only [one_smul, div_one, one_pow, inv_one, ENNReal.ofReal_one, one_smul] using
      affineBall_map_restrict a b (by norm_num : (0 : ℝ) < 1) r
  have hf' : Integrable f (Measure.map (fun x : Domain n => a + (x - b))
      (volume.restrict (Metric.ball b r))) := by rwa [hmap]
  exact hf'.comp_measurable (by fun_prop)

theorem WeakPoissonOn.translate_ball_of_quadratic_bound {n q : ℕ}
    {a : Domain n} {r : ℝ} {u F : Domain n → Ambient q}
    {Du : Domain n → Gradient n q}
    (hEq : WeakPoissonOn (ballDomain a r) Du F)
    (hu : MemW12 (ballDomain a r) u Du) (K : ℝ)
    (hBound : ∀ᵐ x ∂volume.restrict (Metric.ball a r), ‖F x‖ ≤ K * hsNormSq (Du x))
    (b : Domain n) :
    WeakPoissonOn (ballDomain b r) (fun x i => Du (a + (x - b)) i)
      (fun x => F (a + (x - b))) := by
  have hF := hEq.integrable_of_quadratic_bound hu K hBound
  have hF' := integrable_translate_ball a b r hF
  refine ⟨hF'.locallyIntegrableOn, ?_⟩
  intro ψ hψ hcψ hsψ
  let Ψ : Domain n → Ambient q := fun z => ψ (b + (z - a))
  have hΨ : ContDiff ℝ ∞ Ψ := by
    simpa only [Function.comp_def, one_smul] using hψ.comp (affineBall_contDiff b a 1)
  have hcΨ : HasCompactSupport Ψ := by
    simpa only [one_smul] using
      affineBallTest_hasCompactSupport hcψ b a (by norm_num : (1 : ℝ) ≠ 0)
  have hsΨ : tsupport Ψ ⊆ (ballDomain a r).val := by
    simpa only [one_smul, div_one, Ψ, ballDomain] using
      affineBallTest_tsupport_subset b a (by norm_num : (0 : ℝ) < 1) r hsψ
  have hder (x : Domain n) (i : Fin n) :
      fderiv ℝ Ψ (a + (x - b)) (EuclideanSpace.single i 1) =
        fderiv ℝ ψ x (EuclideanSpace.single i 1) := by
    have hd := affineBallTest_coordinateDerivative hψ b a 1 i (a + (x - b))
    simpa only [coordinateDerivative, one_smul, add_sub_cancel_left, add_sub_cancel,
      Ψ] using hd
  obtain ⟨hleft, hright, heq⟩ := hEq.2 Ψ hΨ hcΨ hsΨ
  let A : Domain n → ℝ := fun z => ∑ i : Fin n,
    inner ℝ (Du z i) (fderiv ℝ Ψ z (EuclideanSpace.single i 1))
  let B : Domain n → ℝ := fun z => inner ℝ (F z) (Ψ z)
  have hA (x : Domain n) : A (a + (x - b)) =
      ∑ i : Fin n, inner ℝ (Du (a + (x - b)) i)
        (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    simp only [A, hder]
  have hB (x : Domain n) : B (a + (x - b)) =
      inner ℝ (F (a + (x - b))) (ψ x) := by
    simp only [B, Ψ, add_sub_cancel_left, add_sub_cancel]
  have hleft' : IntegrableOn (fun x => ∑ i : Fin n,
      inner ℝ (Du (a + (x - b)) i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)))
      (Metric.ball b r) volume :=
    (integrable_translate_ball a b r hleft).congr (Filter.Eventually.of_forall hA)
  have hright' : IntegrableOn (fun x => inner ℝ (F (a + (x - b))) (ψ x))
      (Metric.ball b r) volume :=
    (integrable_translate_ball a b r hright).congr (Filter.Eventually.of_forall hB)
  have hleftEq : (∫ x in Metric.ball b r, ∑ i : Fin n,
      inner ℝ (Du (a + (x - b)) i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
      ∫ z in Metric.ball a r, A z := by
    calc
      _ = ∫ x in Metric.ball b r, A (a + (x - b)) :=
        setIntegral_congr_fun measurableSet_ball (fun x _ => (hA x).symm)
      _ = _ := by
        simpa only [one_smul, div_one, one_pow, inv_one, one_smul] using
          integral_affineBall a b (by norm_num : (0 : ℝ) < 1) r A
  have hrightEq : (∫ x in Metric.ball b r, inner ℝ (F (a + (x - b))) (ψ x)) =
      ∫ z in Metric.ball a r, B z := by
    calc
      _ = ∫ x in Metric.ball b r, B (a + (x - b)) :=
        setIntegral_congr_fun measurableSet_ball (fun x _ => (hB x).symm)
      _ = _ := by
        simpa only [one_smul, div_one, one_pow, inv_one, one_smul] using
          integral_affineBall a b (by norm_num : (0 : ℝ) < 1) r B
  refine ⟨hleft', hright', ?_⟩
  dsimp only [ballDomain]
  rw [hleftEq, hrightEq]
  simpa only [A, B, ballDomain] using heq

end HolderToCK
end
