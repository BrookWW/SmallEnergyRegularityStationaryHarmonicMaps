module

public import HarmonicMaps.Analysis.AffineZeroBoundary
public import HarmonicMaps.EnergyLemmas

/-!
# Exact Hilbert--Schmidt energy under positive affine transport

The squared gradient multiplier and volume Jacobian give the integer exponent
`2 - n`. The identity uses extended energy and also covers zero energy.
-/

public section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace HarmonicMaps

theorem hsNormSq_const_smul {n q : ℕ} (t : ℝ) (A : Gradient n q) :
    hsNormSq (fun i => t • A i) = t ^ 2 * hsNormSq A := by
  simp only [hsNormSq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]

theorem dirichletEnergy_affineBall {n q : ℕ} (a b : Domain n) {t : ℝ}
    (ht : 0 < t) (r : ℝ) (Df : Domain n → Gradient n q) :
    dirichletEnergy (fun x i => t • Df (a + t • (x - b)) i)
      (Metric.ball b (r / t)) =
      ENNReal.ofReal (t ^ (2 - (n : ℤ))) * dirichletEnergy Df (Metric.ball a r) := by
  unfold dirichletEnergy
  simp_rw [hsNormSq_const_smul, ENNReal.ofReal_mul (sq_nonneg t)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_affineBall a b ht r (fun x => ENNReal.ofReal (hsNormSq (Df x))), ← mul_assoc,
    ← ENNReal.ofReal_mul (sq_nonneg t)]
  congr 2
  rw [zpow_sub₀ ht.ne', zpow_ofNat, zpow_natCast]
  rfl

theorem affineBall_unit_energy {n q : ℕ} (a : Domain n) (R : PositiveRadius)
    (Df : Domain n → Gradient n q) :
    dirichletEnergy (fun z i => R.val • Df (a + R.val • z) i)
      (Metric.ball (0 : Domain n) 1) = normalizedEnergy Df a R := by
  simpa only [div_self R.property.ne', sub_zero, normalizedEnergy] using
    dirichletEnergy_affineBall a (0 : Domain n) R.property R.val Df

theorem affineBall_subball_energy {n q : ℕ} (a : Domain n) (R : PositiveRadius)
    (f : Domain n → Ambient q) (Df : Domain n → Gradient n q)
    (_hf : MemW12 (ballDomain a R.val) f Df) :
    let DF : Domain n → Gradient n q := fun z i => R.val • Df (a + R.val • z) i
    ∀ (b : Domain n) (r : PositiveRadius),
      Metric.closedBall b r.val ⊆ Metric.ball (0 : Domain n) 1 →
      dirichletEnergy DF (Metric.ball b r.val) =
        ENNReal.ofReal (R.val ^ (2 - (n : ℤ))) *
          dirichletEnergy Df (Metric.ball (a + R.val • b) (R.val * r.val)) := by
  intro DF b r _hclosed
  have h := dirichletEnergy_affineBall (a + R.val • b) b R.property
    (R.val * r.val) Df
  have heq : (fun z i => R.val • Df (a + R.val • b + R.val • (z - b)) i) = DF := by
    funext z i
    dsimp [DF]
    congr 2
    simp only [smul_sub]
    abel
  simpa only [mul_div_cancel_left₀ _ R.property.ne', heq] using h

end HarmonicMaps
