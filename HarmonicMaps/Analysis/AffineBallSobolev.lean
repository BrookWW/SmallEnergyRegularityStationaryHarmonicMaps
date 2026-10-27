module

public import HarmonicMaps.Analysis.AffineBallMeasure
public import HarmonicMaps.SobolevRestriction

/-!
# Finite Sobolev transport between arbitrary balls

Translations transfer the original weak test identities. The accepted centered
dilation theorem then supplies the derivative multiplier for arbitrary centers.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

theorem MemW12.translate_ball {n q : ℕ} {a : Domain n} {r : ℝ}
    {f : Domain n → Ambient q} {Df : Domain n → Gradient n q}
    (hf : MemW12 (ballDomain a r) f Df) (b : Domain n) :
    MemW12 (ballDomain b r) (fun x => f (a + (x - b)))
      (fun x i => Df (a + (x - b)) i) := by
  have hm := memLp_affineBall a b (by norm_num : (0 : ℝ) < 1) r hf.2.1
  have hd (i : Fin n) := memLp_affineBall a b (by norm_num : (0 : ℝ) < 1) r (hf.2.2 i)
  simp only [one_smul, div_one] at hm hd
  letI : IsFiniteMeasure (volume.restrict (Metric.ball b r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hmI : IntegrableOn (fun x => f (a + (x - b))) (Metric.ball b r) :=
    hm.integrable (by norm_num)
  have hdI (i : Fin n) : IntegrableOn (fun x => Df (a + (x - b)) i) (Metric.ball b r) :=
    (hd i).integrable (by norm_num)
  refine ⟨⟨hmI.locallyIntegrableOn, fun i => (hdI i).locallyIntegrableOn, ?_⟩, hm, hd⟩
  intro i φ hφ hcφ hsφ
  let ψ : Domain n → ℝ := fun z => φ (b + (z - a))
  have hψ : ContDiff ℝ ∞ ψ := by
    simpa [ψ, Function.comp_def] using hφ.comp (affineBall_contDiff b a 1)
  have hcψ : HasCompactSupport ψ := by
    simpa using affineBallTest_hasCompactSupport hcφ b a (by norm_num : (1 : ℝ) ≠ 0)
  have hsψ : tsupport ψ ⊆ Metric.ball a r := by
    simpa using affineBallTest_tsupport_subset b a (by norm_num : (0 : ℝ) < 1) r hsφ
  have hder (x : Domain n) :
      coordinateDerivative ψ hψ i (a + (x - b)) = coordinateDerivative φ hφ i x := by
    have h := affineBallTest_coordinateDerivative hφ b a 1 i (a + (x - b))
    simpa [ψ] using h
  have hleft := integral_affineBall a b (by norm_num : (0 : ℝ) < 1) r
    (fun z => coordinateDerivative ψ hψ i z • f z)
  simp only [one_pow, inv_one, one_smul, div_one] at hleft
  simp_rw [hder] at hleft
  have hright := integral_affineBall a b (by norm_num : (0 : ℝ) < 1) r
    (fun z => ψ z • Df z i)
  simp only [one_pow, inv_one, one_smul, div_one] at hright
  simp only [ψ, add_sub_cancel_left, add_sub_cancel] at hright
  change (∫ x in Metric.ball b r, coordinateDerivative φ hφ i x • f (a + (x - b))) =
    -(∫ x in Metric.ball b r, φ x • Df (a + (x - b)) i)
  rw [hleft, hright]
  exact hf.1.2.2 i ψ hψ hcψ hsψ

theorem MemW12.affineBall_pullback {n q : ℕ} {a : Domain n} {r : ℝ}
    {f : Domain n → Ambient q} {Df : Domain n → Gradient n q}
    (hf : MemW12 (ballDomain a r) f Df) (b : Domain n) {t : ℝ} (ht : 0 < t) :
    MemW12 (ballDomain b (r / t)) (fun x => f (a + t • (x - b)))
      (fun x i => t • Df (a + t • (x - b)) i) := by
  simpa only [ballAffine, add_sub_cancel_left] using
    (hf.affinePullback_ball ht).translate_ball b

theorem affineBall_memW12_iff {n q : ℕ} (a b : Domain n) (r : ℝ)
    {t : ℝ} (ht : 0 < t) (f : Domain n → Ambient q)
    (Df : Domain n → Gradient n q) :
    MemW12 (ballDomain a r) f Df ↔
      MemW12 (ballDomain b (r / t)) (fun x => f (a + t • (x - b)))
        (fun x i => t • Df (a + t • (x - b)) i) := by
  refine ⟨fun h => h.affineBall_pullback b ht, fun h => ?_⟩
  have hback := h.affineBall_pullback a (inv_pos.mpr ht)
  have hr : r / t / t⁻¹ = r := by field_simp
  simpa [hr, smul_smul, ht.ne'] using hback

theorem affineBall_unit_memW12_iff {n q : ℕ} (a : Domain n) (R : PositiveRadius)
    (f : Domain n → Ambient q) (Df : Domain n → Gradient n q) :
    MemW12 (ballDomain a R.val) f Df ↔
      MemW12 (ballDomain (0 : Domain n) 1) (fun z => f (a + R.val • z))
        (fun z i => R.val • Df (a + R.val • z) i) := by
  simpa only [div_self R.property.ne', sub_zero] using
    affineBall_memW12_iff a (0 : Domain n) R.val R.property f Df

end HarmonicMaps
