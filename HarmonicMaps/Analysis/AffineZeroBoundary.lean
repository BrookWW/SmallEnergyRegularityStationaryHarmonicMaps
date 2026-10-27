module

public import HarmonicMaps.Analysis.AffineBallSobolev

/-!
# Actual zero-boundary approximation under affine changes of balls

Every compact smooth approximant and each of its classical gradient columns
is transported. The original displayed weak gradient is retained throughout.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

namespace HarmonicMaps

theorem HasZeroBoundaryValues.affineBall_pullback {n q : ℕ}
    {a : Domain n} {r : ℝ} {f : Domain n → Ambient q}
    {Df : Domain n → Gradient n q}
    (hf : HasZeroBoundaryValues (ballDomain a r) f Df)
    (b : Domain n) {t : ℝ} (ht : 0 < t) :
    HasZeroBoundaryValues (ballDomain b (r / t))
      (fun x => f (a + t • (x - b)))
      (fun x i => t • Df (a + t • (x - b)) i) := by
  obtain ⟨hw, m, hm, hmc, hlim, hdlim⟩ := hf
  let M : ℕ → Domain n → Ambient q := fun k x => m k (a + t • (x - b))
  have hM (k : ℕ) : ContDiff ℝ ∞ (M k) := (hm k).comp (affineBall_contDiff a b t)
  let c : ℝ≥0∞ := ENNReal.ofReal ((t ^ n)⁻¹) ^ (1 / 2 : ℝ)
  have hc : c ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  refine ⟨hw.affineBall_pullback b ht, M, hM, ?_, ?_, ?_⟩
  · intro k
    exact ⟨affineBallTest_hasCompactSupport (hmc k).1 a b ht.ne',
      affineBallTest_tsupport_subset a b ht r (hmc k).2⟩
  · have heq (k : ℕ) :
        eLpNorm (M k - (fun x => f (a + t • (x - b)))) 2
          (volume.restrict (Metric.ball b (r / t))) =
        c * eLpNorm (m k - f) 2 (volume.restrict (Metric.ball a r)) :=
      eLpNorm_affineBall a b ht r (m k - f)
    change Tendsto (fun k => eLpNorm (M k - (fun x => f (a + t • (x - b)))) 2
      (volume.restrict (Metric.ball b (r / t)))) atTop (𝓝 0)
    simp_rw [heq]
    simpa only [mul_zero, ballDomain] using ENNReal.Tendsto.const_mul hlim (Or.inr hc)
  · intro i
    have heq (k : ℕ) : eLpNorm
        (fun x => coordinateDerivative (M k) (hM k) i x -
          t • Df (a + t • (x - b)) i) 2
          (volume.restrict (Metric.ball b (r / t))) =
        ‖t‖ₑ * c * eLpNorm
          (fun x => coordinateDerivative (m k) (hm k) i x - Df x i) 2
          (volume.restrict (Metric.ball a r)) := by
      have hpoint : (fun x => coordinateDerivative (M k) (hM k) i x -
          t • Df (a + t • (x - b)) i) =
          t • (fun x => coordinateDerivative (m k) (hm k) i
            (a + t • (x - b)) - Df (a + t • (x - b)) i) := by
        funext x
        rw [affineBallTest_coordinateDerivative (hm k) a b t i x]
        exact (smul_sub _ _ _).symm
      rw [hpoint, eLpNorm_const_smul,
        eLpNorm_affineBall a b ht r
          (fun x => coordinateDerivative (m k) (hm k) i x - Df x i), mul_assoc]
    change Tendsto (fun k => eLpNorm
      (fun x => coordinateDerivative (M k) (hM k) i x -
        t • Df (a + t • (x - b)) i) 2
      (volume.restrict (Metric.ball b (r / t)))) atTop (𝓝 0)
    simp_rw [heq]
    have hc' : ‖t‖ₑ * c ≠ (⊤ : ℝ≥0∞) := ENNReal.mul_ne_top (by simp) hc
    simpa only [mul_zero, ballDomain] using ENNReal.Tendsto.const_mul (hdlim i) (Or.inr hc')

theorem affineBall_zeroBoundary_iff {n q : ℕ} (a b : Domain n) (r : ℝ)
    {t : ℝ} (ht : 0 < t) (f : Domain n → Ambient q)
    (Df : Domain n → Gradient n q) :
    HasZeroBoundaryValues (ballDomain a r) f Df ↔
      HasZeroBoundaryValues (ballDomain b (r / t))
        (fun x => f (a + t • (x - b)))
        (fun x i => t • Df (a + t • (x - b)) i) := by
  refine ⟨fun h => h.affineBall_pullback b ht, fun h => ?_⟩
  have hback := h.affineBall_pullback a (inv_pos.mpr ht)
  have hr : r / t / t⁻¹ = r := by field_simp
  simpa [hr, smul_smul, ht.ne'] using hback

theorem affineBall_unit_spaces_iff {n q : ℕ} (a : Domain n) (R : PositiveRadius)
    (f : Domain n → Ambient q) (Df : Domain n → Gradient n q) :
    let F : Domain n → Ambient q := fun z => f (a + R.val • z)
    let DF : Domain n → Gradient n q := fun z i => R.val • Df (a + R.val • z) i
    (MemW12 (ballDomain a R.val) f Df ↔
      MemW12 (ballDomain (0 : Domain n) 1) F DF) ∧
    (HasZeroBoundaryValues (ballDomain a R.val) f Df ↔
      HasZeroBoundaryValues (ballDomain (0 : Domain n) 1) F DF) := by
  refine ⟨affineBall_unit_memW12_iff a R f Df, ?_⟩
  simpa only [div_self R.property.ne', sub_zero] using
    affineBall_zeroBoundary_iff a (0 : Domain n) R.val R.property f Df

end HarmonicMaps
