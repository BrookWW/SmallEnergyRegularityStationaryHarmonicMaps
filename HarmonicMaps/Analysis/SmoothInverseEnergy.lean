module

public import HarmonicMaps.Analysis.SmoothInverseSobolev
public import HarmonicMaps.EnergyLemmas

/-!
# The exact Sobolev energy change of variables

The differential of the actual smooth inverse is the genuine algebraic
inverse of the forward differential. Applying the Jacobian formula to the
proved Sobolev pullback gives an integrable transformed energy density and
the real value of the finite extended energy, with the original HS convention.
-/

public section

open MeasureTheory Set
open scoped ContDiff BigOperators

namespace HarmonicMaps

/-- The differential of a genuine smooth inverse is the ring inverse of the
actual forward differential; both composition identities are differentiated. -/
theorem fderiv_inverse_comp_eq_ringInverse {n : ℕ}
    {f g : Domain n → Domain n} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfg : Function.RightInverse g f) (hgf : Function.LeftInverse g f) (x : Domain n) :
    fderiv ℝ g (f x) = Ring.inverse (fderiv ℝ f x) := by
  have hleft : (fderiv ℝ g (f x)).comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ (Domain n) := by
    rw [← fderiv_comp x (hg.differentiable (by simp) (f x)) (hf.differentiable (by simp) x)]
    have heq : g ∘ f = id := funext hgf
    rw [heq, fderiv_id]
  have hright : (fderiv ℝ f x).comp (fderiv ℝ g (f x)) = ContinuousLinearMap.id ℝ (Domain n) := by
    have h := fderiv_comp (f x) (hf.differentiable (by simp) (g (f x)))
      (hg.differentiable (by simp) (f x))
    have heq : f ∘ g = id := funext hfg
    rw [heq, fderiv_id, hgf x] at h
    exact h.symm
  let e : (Domain n →L[ℝ] Domain n)ˣ :=
    ⟨fderiv ℝ f x, fderiv ℝ g (f x), hright, hleft⟩
  exact (Ring.inverse_unit e).symm

/-- The finite energy of the actual inverse Sobolev pullback equals its
Jacobian-substituted density, whose L1 property is also proved. -/
theorem MemW12.energy_comp_smooth_inverse_ball {n q : ℕ} {a : Domain n} {R : ℝ}
    (hR : 0 < R) {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hu : MemW12 (ballDomain a R) u Du)
    {f g : Domain n → Domain n} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfg : Function.RightInverse g f) (hgf : Function.LeftInverse g f)
    (hfball : MapsTo f (Metric.ball a R) (Metric.ball a R))
    (hgball : MapsTo g (Metric.ball a R) (Metric.ball a R)) :
    IntegrableOn (fun x => |(fderiv ℝ f x).det| *
      hsNormSq (fun i => ∑ j : Fin n,
        ((Ring.inverse (fderiv ℝ f x)) (EuclideanSpace.single i 1)) j • Du x j))
      (Metric.ball a R) ∧
    (dirichletEnergy
      (fun x i => ∑ j : Fin n, (fderiv ℝ g x (EuclideanSpace.single i 1)) j • Du (g x) j)
      (Metric.ball a R)).toReal =
      ∫ x in Metric.ball a R, |(fderiv ℝ f x).det| *
        hsNormSq (fun i => ∑ j : Fin n,
          ((Ring.inverse (fderiv ℝ f x)) (EuclideanSpace.single i 1)) j • Du x j) := by
  have hv := hu.comp_smooth_inverse_ball hR hf hg hfg hgf hfball hgball
  have himage : f '' Metric.ball a R = Metric.ball a R := by
    apply Subset.antisymm hfball.image_subset
    intro y hy
    exact ⟨g y, hgball hy, hfg y⟩
  have hder (x : Domain n) (_hx : x ∈ Metric.ball a R) :=
    (hf.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt (s := Metric.ball a R)
  let E : Domain n → ℝ := fun x => hsNormSq
    (fun i => ∑ j : Fin n, (fderiv ℝ g x (EuclideanSpace.single i 1)) j • Du (g x) j)
  have heq : (fun x => |(fderiv ℝ f x).det| • E (f x)) =
      (fun x => |(fderiv ℝ f x).det| * hsNormSq (fun i => ∑ j : Fin n,
        ((Ring.inverse (fderiv ℝ f x)) (EuclideanSpace.single i 1)) j • Du x j)) := by
    funext x
    dsimp only [E]
    rw [hgf x, fderiv_inverse_comp_eq_ringInverse hf hg hfg hgf x, smul_eq_mul]
  have hi := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    measurableSet_ball hder hgf.injective.injOn E).mp
    (by rw [himage]; exact hv.integrable_hsNormSq)
  have he := integral_image_eq_integral_abs_det_fderiv_smul volume
    measurableSet_ball hder hgf.injective.injOn E
  rw [heq] at hi he
  refine ⟨hi, ?_⟩
  rw [himage] at he
  exact (dirichletEnergy_toReal (U := Metric.ball a R) hv.integrable_hsNormSq).trans he

end HarmonicMaps
