module

public import StationaryHarmonicMaps.Analysis.NeumannKelvinReflection
public import StationaryHarmonicMaps.Analysis.NeumannKelvinAdjointGeometry
public import StationaryHarmonicMaps.Analysis.ScaledBallCutoff
public import StationaryHarmonicMaps.Analysis.NeumannGradientSpace

/-!
# Actual smooth native tests for the Neumann Kelvin adjoint

The original support radius makes the literal weighted radial expression
zero near the puncture. A genuine smooth origin cutoff removes its isolated
value there. The resulting globally smooth map is an actual native test
with unrestricted sphere values. All interior support balls centered on
the unit sphere are preserved.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- An original smooth test with a genuine support radius produces its globally smooth native Neumann adjoint, its exact off-origin formula and its original sphere-centered localization. -/
theorem exists_neumann_kelvin_adjoint_of_support_radius {n q : ℕ}
    (upper : ℝ) (hUpper : 0<upper) (ψ : Domain n → Ambient q)
    (hψ : ContDiff ℝ ∞ ψ) (hZero : ∀z : Domain n,upper≤‖z‖ → ψ z=0) :
    ∃ φ : Domain n → Ambient q,ContDiff ℝ ∞ φ ∧
      MemW12 (ballDomain (0 : Domain n) 1) φ
        (fun x i=>fderiv ℝ φ x (EuclideanSpace.single i 1)) ∧
      (∀y : Domain n,y≠0 → φ y=neumannKelvinRay upper ψ (‖y‖⁻¹ • y) ‖y‖) ∧
      (∀y : Domain n,‖y‖≤upper⁻¹ → φ y=0) ∧
      ∀ (a : Domain n) (s : ℝ),‖a‖=1 → tsupport ψ⊆ball a s →
        ∀y : Domain n,‖y‖≤1 → y∉ball a s → φ y=0 := by
  let δ : ℝ := 1/(4*(upper+1))
  have hδ : 0<δ := by dsimp only [δ];positivity
  have hδInv : (2*δ)⁻¹=2*(upper+1) := by
    dsimp only [δ]
    field_simp
    ring
  have hUpperInv : upper≤(2*δ)⁻¹ := by rw [hδInv];linarith only [hUpper]
  obtain ⟨_C,_hC,Hcut⟩ := exists_scaled_ball_cutoff n
  obtain ⟨χ,hχ,_hcχ,hsχ,hχOne,_hχBound,_hDχ⟩ := Hcut (0 : Domain n) δ hδ
  let raw := fun y : Domain n=>neumannKelvinRay upper ψ (‖y‖⁻¹ • y) ‖y‖
  let φ := fun y : Domain n=>(1-χ y) • raw y
  have hRawZero (y : Domain n) (hy : y≠0) (hRange : upper≤‖y‖⁻¹) : raw y=0 := by
    have hyPos : 0<‖y‖ := norm_pos_iff.mpr hy
    have hθ : ‖‖y‖⁻¹ • y‖=1 := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hyPos.le),inv_mul_cancel₀ hyPos.ne']
    exact neumann_adjoint_ray_eq_zero_of_support_radius ψ upper hUpper hZero _ hθ _ hyPos hRange
  have hEq (y : Domain n) (hy : y≠0) : φ y=raw y := by
    by_cases hχy : χ y=0
    · simp only [φ,hχy,sub_zero,one_smul]
    · have hNorm : ‖y‖<2*δ := by
        simpa only [mem_ball,dist_zero_right] using hsχ (subset_tsupport χ hχy)
      have hLarge : upper≤‖y‖⁻¹ := hUpperInv.trans (by
        simpa only [one_div] using one_div_le_one_div_of_le (norm_pos_iff.mpr hy) hNorm.le)
      rw [show φ y=(1-χ y) • raw y from rfl,hRawZero y hy hLarge,smul_zero]
  have hAtZero : φ (0 : Domain n)=0 := by
    have hχ0 : χ (0 : Domain n)=1 := hχOne 0 (mem_closedBall_self hδ.le)
    simp only [φ,hχ0,sub_self,zero_smul]
  have hφ : ContDiff ℝ ∞ φ := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y=0
    · subst y
      have hNear : φ=ᶠ[𝓝 (0 : Domain n)] (fun _=>0) := by
        filter_upwards [ball_mem_nhds (0 : Domain n) hδ] with z hz
        have hzOne := hχOne z (ball_subset_closedBall hz)
        simp only [φ,hzOne,sub_self,zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hNear
    · exact (contDiffAt_const.sub hχ.contDiffAt).smul
        (neumannKelvinReflection_contDiffAt upper hUpper ψ hψ y hy)
  refine ⟨φ,hφ,memW12_ball_of_ambient_c1 (0 : Domain n) 1 φ (hφ.of_le (by simp)),hEq,?_,?_⟩
  · intro y hy
    by_cases hy0 : y=0
    · simpa only [hy0] using hAtZero
    · rw [hEq y hy0]
      exact hRawZero y hy0 ((le_inv_comm₀ hUpper (norm_pos_iff.mpr hy0)).mpr hy)
  · intro a s ha hSupport y hyOne hyOutside
    by_cases hy0 : y=0
    · simpa only [hy0] using hAtZero
    · rw [hEq y hy0]
      exact neumann_adjoint_expression_eq_zero_off_boundary_ball ψ upper hUpper hZero
        a s hSupport ha y hy0 hyOne hyOutside

/-- Every original compact smooth test produces a genuine support radius and the same actual smooth native Neumann adjoint. -/
theorem exists_compact_smooth_neumann_kelvin_adjoint {n q : ℕ}
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    ∃ (upper : ℝ) (φ : Domain n → Ambient q),0<upper ∧
      (∀z : Domain n,upper≤‖z‖ → ψ z=0) ∧ ContDiff ℝ ∞ φ ∧
      MemW12 (ballDomain (0 : Domain n) 1) φ
        (fun x i=>fderiv ℝ φ x (EuclideanSpace.single i 1)) ∧
      (∀y : Domain n,y≠0 → φ y=neumannKelvinRay upper ψ (‖y‖⁻¹ • y) ‖y‖) ∧
      (∀y : Domain n,‖y‖≤upper⁻¹ → φ y=0) ∧
      ∀ (a : Domain n) (s : ℝ),‖a‖=1 → tsupport ψ⊆ball a s →
        ∀y : Domain n,‖y‖≤1 → y∉ball a s → φ y=0 := by
  obtain ⟨upper,hUpper,hZero⟩ := hcψ.exists_pos_le_norm
  obtain ⟨φ,hφ,hNative,hEq,hNear,hSupport⟩ :=
    exists_neumann_kelvin_adjoint_of_support_radius upper hUpper ψ hψ hZero
  exact ⟨upper,φ,hUpper,hZero,hφ,hNative,hEq,hNear,hSupport⟩

end StationaryHarmonicMaps.Analysis

end
