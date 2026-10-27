module

public import StationaryHarmonicMaps.Analysis.NeumannKelvinAdjoint
public import StationaryHarmonicMaps.Analysis.NeumannKelvinDerivative

/-!
# The actual derivative of the native Neumann adjoint test

The globally smooth test has the same punctured expression as the genuine
spatial reflection. Its actual derivative therefore retains the inversion
term and the tangential radial integral, with the map-value terms cancelled.
The original sphere-centered support also localizes the actual gradient.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set Metric
open StationaryHarmonicMaps.Geometry
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The first actual adjoint derivative term is the weighted derivative of the genuine unit inversion. -/
theorem neumann_adjoint_first_derivative_term {n q : ℕ}
    (ψ : Domain n → Ambient q) (y v : Domain n) (hy : y≠0) :
    let r := ‖y‖
    let θ := r⁻¹ • y
    r^(-(n : ℝ)) • fderiv ℝ ψ (r⁻¹ • θ) (v-(2*inner ℝ θ v) • θ)=
      r^(2-(n : ℝ)) • fderiv ℝ ψ (inversion (0 : Domain n) 1 y)
        (fderiv ℝ (inversion (0 : Domain n) 1) y v) := by
  intro r θ
  have hr : 0<r := norm_pos_iff.mpr hy
  have hI : inversion (0 : Domain n) 1 y=r⁻¹ • θ := by
    simp only [inversion,dist_zero_right,vsub_eq_sub,sub_zero,vadd_eq_add,add_zero,
      one_div,θ,smul_smul,pow_two]
    rfl
  have hQ : ((ℝ ∙ y)ᗮ.reflection : Domain n →L[ℝ] Domain n) v=
      v-(2*inner ℝ θ v) • θ := by
    change (ℝ ∙ y)ᗮ.reflection v=_
    rw [Submodule.reflection_orthogonal_apply,Submodule.reflection_singleton_apply]
    simp only [RCLike.ofReal_real_eq_id,id_eq,θ,real_inner_smul_left,div_eq_mul_inv,← inv_pow,smul_smul]
    change -(2 • ((inner ℝ y v * r⁻¹^2) • y)-v)=v-(2*(r⁻¹*inner ℝ y v)*r⁻¹) • y
    module
  have hInv2 : (r^2)⁻¹=r^(-2 : ℝ) := by
    rw [Real.rpow_neg hr.le,Real.rpow_two]
  have hWeight : r^(2-(n : ℝ))*(r^2)⁻¹=r^(-(n : ℝ)) := by
    rw [hInv2,← Real.rpow_add hr]
    congr 1
    ring
  rw [hI,(hasFDerivAt_unit_inversion y hy).fderiv]
  simp only [smul_apply,map_smul,smul_smul]
  change _=(r^(2-(n : ℝ))*(r^2)⁻¹) • fderiv ℝ ψ (r⁻¹ • θ)
    (((ℝ ∙ y)ᗮ.reflection : Domain n →L[ℝ] Domain n) v)
  rw [hWeight,hQ]

/-- Original smooth support data produce one native adjoint with its actual full derivative and same-cap localization of both values and gradients. -/
theorem exists_neumann_kelvin_adjoint_with_gradient {n q : ℕ}
    (upper : ℝ) (hUpper : 0<upper) (ψ : Domain n → Ambient q)
    (hψ : ContDiff ℝ ∞ ψ) (hZero : ∀z : Domain n,upper≤‖z‖ → ψ z=0) :
    ∃ φ : Domain n → Ambient q,ContDiff ℝ ∞ φ ∧
      MemW12 (ballDomain (0 : Domain n) 1) φ
        (fun x i=>fderiv ℝ φ x (EuclideanSpace.single i 1)) ∧
      (∀y : Domain n,y≠0 → φ y=neumannKelvinRay upper ψ (‖y‖⁻¹ • y) ‖y‖) ∧
      (∀y : Domain n,‖y‖≤upper⁻¹ → φ y=0) ∧
      (∀ (y v : Domain n),y≠0 →
        let r := ‖y‖
        let θ := r⁻¹ • y
        let vT := v-(inner ℝ θ v) • θ
        fderiv ℝ φ y v=r^(2-(n : ℝ)) • fderiv ℝ ψ (inversion (0 : Domain n) 1 y)
          (fderiv ℝ (inversion (0 : Domain n) 1) y v)+(((n : ℝ)-2)/r) •
          (∫t in r⁻¹..upper,t^((n : ℝ)-2) • fderiv ℝ ψ (t • θ) vT)) ∧
      (∀ (a : Domain n) (s : ℝ),‖a‖=1 → tsupport ψ⊆ball a s →
        ∀y : Domain n,‖y‖≤1 → y∉ball a s → φ y=0) ∧
      ∀ (a : Domain n) (s : ℝ),‖a‖=1 → tsupport ψ⊆ball a s →
        ∀y : Domain n,‖y‖<1 → s<dist y a → fderiv ℝ φ y=0 := by
  obtain ⟨φ,hφ,hNative,hEq,hNear,hSupport⟩ :=
    exists_neumann_kelvin_adjoint_of_support_radius upper hUpper ψ hψ hZero
  refine ⟨φ,hφ,hNative,hEq,hNear,?_,hSupport,?_⟩
  · intro y v hy r θ vT
    have hLocal : φ=ᶠ[𝓝 y] (fun z=>neumannKelvinRay upper ψ (‖z‖⁻¹ • z) ‖z‖) :=
      (eventually_ne_nhds hy).mono fun z hz=>hEq z hz
    rw [hLocal.fderiv_eq]
    rw [← neumann_adjoint_first_derivative_term ψ y v hy]
    exact neumannKelvinReflection_fderiv_apply upper hUpper ψ hψ y v hy
  · intro a s ha hS y hy hys
    have hOpen : IsOpen {z : Domain n | ‖z‖<1 ∧ s<dist z a} :=
      (isOpen_lt continuous_norm continuous_const).inter
        (isOpen_lt continuous_const (continuous_id.dist continuous_const))
    have hLocal : φ=ᶠ[𝓝 y] (fun _=>0) := by
      filter_upwards [hOpen.mem_nhds (show y∈{z : Domain n | ‖z‖<1 ∧ s<dist z a} from ⟨hy,hys⟩)] with z hz
      exact hSupport a s ha hS z hz.1.le (fun hmem=>(not_lt_of_ge hz.2.le) hmem)
    rw [hLocal.fderiv_eq]
    simp only [fderiv_const_apply]

end StationaryHarmonicMaps.Analysis

end
