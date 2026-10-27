module

public import HarmonicMaps.Analysis.InnerVariationAdmissibility
public import HarmonicMaps.Analysis.SmoothInverseEnergy

/-!
# Minimality after the inner-variation energy substitution

The real Jacobian-transformed energy is integrable and minimized at zero on
a two-sided parameter interval. The original local minimizer definition
supplies the comparison after genuine competitor admissibility is proved.
-/

public section

open MeasureTheory Set
open scoped ContDiff BigOperators

namespace HarmonicMaps

/-- Local minimality implies the actual transformed energy comparison for
both signs of the parameter, with every Sobolev admissibility obligation
and the energy substitution discharged inside the proof. -/
theorem IsLocallyEnergyMinimizing.innerVariation_transformed_energy_minimum {n q : ℕ}
    {Ω : OpenDomain n} {N : CompactSmoothEmbeddedTarget q}
    {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) (hu : MemW12Loc Ω u Du)
    (hN : TakesValuesIn N Ω u) {a : Domain n} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall a R ⊆ Ω.val)
    {ζ : Domain n → Domain n} (hζ : ContDiff ℝ ∞ ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Metric.ball a R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      IntegrableOn (fun x => |(1 + t • fderiv ℝ ζ x).det| *
        hsNormSq (fun i => ∑ j : Fin n,
          ((Ring.inverse (1 + t • fderiv ℝ ζ x)) (EuclideanSpace.single i 1)) j • Du x j))
        (Metric.ball a R) ∧
      (∫ x in Metric.ball a R, hsNormSq (Du x)) ≤
        ∫ x in Metric.ball a R, |(1 + t • fderiv ℝ ζ x).det| *
          hsNormSq (fun i => ∑ j : Fin n,
            ((Ring.inverse (1 + t • fderiv ℝ ζ x)) (EuclideanSpace.single i 1)) j • Du x j) := by
  have hw := hu.memW12_ball hball
  have ht : TakesValuesIn N (ballDomain a R) u :=
    ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_closedBall.trans hball) hN
  obtain ⟨ε, hε, hcomp⟩ := hw.innerVariation_admissible hR ht hζ hc hs
  refine ⟨ε, hε, ?_⟩
  intro t ht'
  obtain ⟨g, hg, hfg, hgf, hv, hNv, hzero⟩ := hcomp t ht'
  let f : Domain n → Domain n := fun x => x + t • ζ x
  have hf : ContDiff ℝ ∞ f := contDiff_id.add (hζ.const_smul t)
  have hri : Function.RightInverse g f := hfg
  have hli : Function.LeftInverse g f := hgf
  have hoff : ∀ x ∉ Metric.ball a R, f x = x := by
    intro x hx
    have hn : x ∉ tsupport ζ := fun h => hx (hs h)
    dsimp only [f]
    rw [image_eq_zero_of_notMem_tsupport hn, smul_zero, add_zero]
  have himage := innerVariation_image_eq_of_fixed_compl ⟨hli.injective, hri.surjective⟩ hoff
  have hfball : MapsTo f (Metric.ball a R) (Metric.ball a R) := by
    intro x hx
    rw [← himage]
    exact mem_image_of_mem f hx
  have hgball : MapsTo g (Metric.ball a R) (Metric.ball a R) := by
    intro z hz
    rw [← himage] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [hli x]
    exact hx
  have hcv := hw.energy_comp_smooth_inverse_ball hR hf hg hri hli hfball hgball
  have hder (x : Domain n) : fderiv ℝ f x = 1 + t • fderiv ℝ ζ x :=
    (innerVariation_hasFDerivAt hζ t x).fderiv
  simp_rw [hder] at hcv
  refine ⟨hcv.1, ?_⟩
  have hle := hmin a R hR hball (u ∘ g) _ hv hNv hzero
  have hreal := ENNReal.toReal_mono hv.dirichletEnergy_ne_top hle
  calc
    (∫ x in Metric.ball a R, hsNormSq (Du x)) =
        (dirichletEnergy Du (Metric.ball a R)).toReal :=
      (dirichletEnergy_toReal (U := Metric.ball a R) hw.integrable_hsNormSq).symm
    _ ≤ _ := hreal
    _ = _ := hcv.2

end HarmonicMaps
