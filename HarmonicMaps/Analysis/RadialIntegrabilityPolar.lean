module

public import HarmonicMaps.Analysis.RadialIntegrability
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Polar integrability of Sobolev energy

The unit-sphere measure is Mathlib's `volume.toSphere`, and the radial
Jacobian is the exact factor `r^(n-1)`.
-/

public section

open MeasureTheory Set
open scoped BigOperators

namespace HarmonicMaps

/-- An integrable Euclidean function has an integrable polar boundary density
around every center, with the Haar-normalized sphere measure. -/
theorem integrable_polar_boundary_density {n : ℕ} (_hn : 0 < n)
    {f : Domain n → ℝ} (hf : Integrable f volume) (a : Domain n) :
    IntegrableOn (fun r : ℝ => r ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1, f (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) (Ioi 0) volume := by
  have ht := hf.comp_add_left a
  have hp : Integrable (fun p : Metric.sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
      f (a + p.2.val • p.1.val))
      ((volume : Measure (Domain n)).toSphere.prod (Measure.volumeIoiPow (n - 1))) := by
    have hs : Integrable
        ((fun x : Domain n => f (a + x)) ∘ (↑) : ({(0 : Domain n)}ᶜ : Set (Domain n)) → ℝ)
        ((volume : Measure (Domain n)).comap
          (Subtype.val : ({(0 : Domain n)}ᶜ : Set (Domain n)) → Domain n)) :=
      (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : Domain n)).compl).mp
        ht.integrableOn
    have hm := (volume : Measure (Domain n)).measurePreserving_homeomorphUnitSphereProd
    have hh := (hm.integrable_comp_emb (Homeomorph.measurableEmbedding _)
      (g := fun p => f (a + ((homeomorphUnitSphereProd (Domain n)).symm p).val))).mp
      (by simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hs)
    simpa only [homeomorphUnitSphereProd_symm_apply_coe, finrank_euclideanSpace,
      Fintype.card_fin] using hh
  have hi := hp.integral_prod_right
  rw [Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul'] at hi
  · rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioi]
    convert hi using 1
    funext r
    simp only [Function.comp_def, smul_eq_mul,
      ENNReal.toReal_ofReal (pow_nonneg r.property.le _)]
  · fun_prop
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

/-- Integrability on a ball gives ordinary-radius integrability of its polar
boundary density on the whole positive radius interval. -/
theorem integrableOn_polar_boundary_density {n : ℕ} (hn : 0 < n)
    {f : Domain n → ℝ} {a : Domain n} {R : ℝ}
    (hf : IntegrableOn f (Metric.ball a R) volume) :
    IntegrableOn (fun r : ℝ => r ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1, f (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) (Ioo 0 R) volume := by
  have hg : Integrable ((Metric.ball a R).indicator f) volume :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr hf
  have hi := (integrable_polar_boundary_density hn hg a).mono_set (show Ioo 0 R ⊆ Ioi 0 from Ioo_subset_Ioi_self)
  apply hi.congr_fun
  · intro r hr
    dsimp only
    apply congrArg (fun z : ℝ => r ^ (n - 1) * z)
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro θ
    dsimp only
    rw [indicator_of_mem]
    rw [Metric.mem_ball, dist_eq_norm_sub, add_sub_cancel_left,
      norm_smul, Real.norm_of_nonneg hr.1.le]
    have hθ : ‖θ.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    simpa only [hθ, mul_one] using hr.2
  · exact measurableSet_Ioo

/-- Both actual Sobolev energy densities have integrable polar boundary
integrals. The gradient is exactly the displayed weak-gradient witness. -/
theorem MemW12Loc.integrable_polar_energy_densities {n q : ℕ} (hn : 0 < n)
    {Ω : OpenDomain n} {u : Domain n → Ambient q} {Du : Domain n → Gradient n q}
    (h : MemW12Loc Ω u Du) {a : Domain n} {R : ℝ}
    (hball : Metric.closedBall a R ⊆ Ω.val) :
    IntegrableOn (fun r : ℝ => r ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1, hsNormSq (Du (a + r • θ.val))
        ∂(volume : Measure (Domain n)).toSphere) (Ioo 0 R) volume ∧
    IntegrableOn (fun r : ℝ => r ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1,
        ‖‖(a + r • θ.val) - a‖⁻¹ •
          ∑ i : Fin n, ((a + r • θ.val) - a) i • Du (a + r • θ.val) i‖ ^ 2
        ∂(volume : Measure (Domain n)).toSphere) (Ioo 0 R) volume :=
  ⟨integrableOn_polar_boundary_density hn (h.integrable_hsNormSq_ball hball),
    integrableOn_polar_boundary_density hn (h.integrable_radial_columns_ball hball)⟩

end HarmonicMaps
