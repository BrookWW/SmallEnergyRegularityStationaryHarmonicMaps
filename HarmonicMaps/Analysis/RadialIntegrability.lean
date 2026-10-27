module

public import HarmonicMaps.Analysis.RadialStressBasic
public import HarmonicMaps.EnergyLemmas
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Hilbert--Schmidt control of radial energy

The same displayed Sobolev gradient controls its evaluation in the radial unit
direction. Integral statements use the literal column formula; away from the
center this is the existing punctured radial derivative.
-/

public section

open MeasureTheory Set
open scoped BigOperators

namespace HarmonicMaps

/-- The column map has squared norm bounded by its HS density times the
squared Euclidean norm of the input. -/
theorem norm_sq_sum_gradient_le {n q : ℕ} (A : Gradient n q) (x : Domain n) :
    ‖∑ i : Fin n, x i • A i‖ ^ 2 ≤ ‖x‖ ^ 2 * hsNormSq A := by
  have hnorm : ‖∑ i : Fin n, x i • A i‖ ≤ ∑ i : Fin n, |x i| * ‖A i‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using
      (norm_sum_le (s := Finset.univ) (f := fun i => x i • A i))
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin n => |x i|) (fun i : Fin n => ‖A i‖)
  calc
    _ ≤ (∑ i : Fin n, |x i| * ‖A i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∑ i : Fin n, |x i| ^ 2) * (∑ i : Fin n, ‖A i‖ ^ 2) := hsq
    _ = ‖x‖ ^ 2 * hsNormSq A := by
      simp only [sq_abs, hsNormSq, EuclideanSpace.real_norm_sq_eq]

/-- The literal radial column formula is controlled everywhere by the HS
energy. At zero its value is zero by scalar multiplication, without assigning
a radial unit direction there. -/
theorem norm_sq_radial_columns_le {n q : ℕ} (A : Gradient n q) (x : Domain n) :
    ‖‖x‖⁻¹ • ∑ i : Fin n, x i • A i‖ ^ 2 ≤ hsNormSq A := by
  by_cases hx : x = 0
  · subst x
    simpa only [norm_zero, inv_zero, zero_smul, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      using hsNormSq_nonneg A
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), mul_pow]
  calc
    _ ≤ (‖x‖⁻¹) ^ 2 * (‖x‖ ^ 2 * hsNormSq A) :=
      mul_le_mul_of_nonneg_left (norm_sq_sum_gradient_le A x) (sq_nonneg _)
    _ = hsNormSq A := by rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hn, one_pow, one_mul]

/-- Squared radial derivatives use the HS norm of the same gradient columns. -/
theorem gradientRadialDerivative_norm_sq_le {n q : ℕ}
    (A : Gradient n q) (x : {x : Domain n // x ≠ 0}) :
    ‖gradientRadialDerivative A x‖ ^ 2 ≤ hsNormSq A :=
  norm_sq_radial_columns_le A x.val

/-- The arbitrary-center integral formula agrees with the established radial
derivative at every point where the radial direction exists. -/
theorem radial_columns_eq_gradientRadialDerivative {n q : ℕ}
    (Du : Domain n → Gradient n q) (a x : Domain n) (hx : x ≠ a) :
    ‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i =
      gradientRadialDerivative (Du x) ⟨x - a, sub_ne_zero.mpr hx⟩ := rfl

/-- L2 gradient columns imply L1 radial energy around every center. -/
theorem integrable_radial_columns_of_memLp {n q : ℕ}
    {Du : Domain n → Gradient n q} {μ : Measure (Domain n)}
    (hDu : ∀ i : Fin n, MemLp (fun x => Du x i) 2 μ) (a : Domain n) :
    Integrable (fun x => ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2) μ := by
  have hsum : AEStronglyMeasurable
      (fun x => ∑ i : Fin n, (x - a) i • Du x i) μ := by
    have hh := Finset.aestronglyMeasurable_sum Finset.univ fun i _ =>
      (by fun_prop : Continuous (fun x : Domain n => (x - a) i)).aestronglyMeasurable.smul
        (hDu i).aestronglyMeasurable
    convert hh using 1
    funext x
    simp only [Finset.sum_apply]
    rfl
  have hinv : AEStronglyMeasurable (fun x : Domain n => ‖x - a‖⁻¹) μ :=
    (by fun_prop : Continuous (fun x : Domain n => ‖x - a‖)).aestronglyMeasurable.inv₀
  exact (integrable_hsNormSq_of_memLp_columns hDu).mono'
    ((hinv.smul hsum).norm.pow 2)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact norm_sq_radial_columns_le (Du x) (x - a))

/-- A genuine Sobolev map has integrable radial energy on its domain. -/
theorem MemW12.integrable_radial_columns {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (h : MemW12 Ω u Du) (a : Domain n) :
    IntegrableOn (fun x => ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2)
      Ω.val volume :=
  integrable_radial_columns_of_memLp h.2.2 a

/-- Local Sobolev membership supplies radial integrability on a compactly
contained ball, with the same gradient witness. -/
theorem MemW12Loc.integrable_radial_columns_ball {n q : ℕ}
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (h : MemW12Loc Ω u Du) {a : Domain n} {r : ℝ}
    (hball : Metric.closedBall a r ⊆ Ω.val) :
    IntegrableOn (fun x => ‖‖x - a‖⁻¹ • ∑ i : Fin n, (x - a) i • Du x i‖ ^ 2)
      (Metric.ball a r) volume :=
  IntegrableOn.mono_set (integrable_radial_columns_of_memLp
    (fun i => h.2.2 i (Metric.closedBall a r) (isCompact_closedBall a r) hball) a)
      Metric.ball_subset_closedBall

end HarmonicMaps
