module

public import StationaryHarmonicMaps.Analysis.NeumannKelvinLambda

/-!
# A globally smooth exterior Neumann Kelvin extension

An actual origin cutoff regularizes only the puncture. The resulting
smooth map agrees with the original map on the unit sphere, and retains
the literal exterior value and original-gradient dilation formulas.
-/

public section

open HarmonicMaps MeasureTheory Set Filter Metric EuclideanGeometry
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Original ambient smooth data produce a globally smooth sphere-matching exterior extension with its actual value and derivative columns. -/
theorem exists_smooth_neumann_kelvin_extension {n q : ℕ}
    (u : Domain n → Ambient q) (hu : ContDiff ℝ ∞ u) :
    let I := inversion (0 : Domain n) 1
    ∃ v : Domain n → Ambient q,
      ContDiff ℝ ∞ v ∧
      (∀ x : Domain n, ‖x‖ = 1 → v x = u x) ∧
      (∀ x : Domain n, 1 < ‖x‖ →
        v x = ‖x‖ ^ (2-(n : ℝ)) • u (I x) +
          ((n : ℝ)-2) • (‖x‖ ^ ((n : ℝ)-2) •
            (∫ s in (‖x‖^2)⁻¹..‖x‖⁻¹, s ^ ((n : ℝ)-3) • u (s • x)))) ∧
      ∀ x : Domain n, 1 < ‖x‖ → ∀ i : Fin n,
        let P := fun w : Domain n => w - (inner ℝ x w / ‖x‖^2) • x
        fderiv ℝ v x (EuclideanSpace.single i 1) =
          ‖x‖ ^ (2-(n : ℝ)) • (∑ j : Fin n,
            (fderiv ℝ I x (EuclideanSpace.single i 1)) j •
              fderiv ℝ u (I x) (EuclideanSpace.single j 1)) +
          ((n : ℝ)-2) • (∑ j : Fin n, (P (EuclideanSpace.single i 1)) j •
            (‖x‖ ^ ((n : ℝ)-2) • (∫ s in (‖x‖^2)⁻¹..‖x‖⁻¹,
              s ^ ((n : ℝ)-2) • fderiv ℝ u (s • x) (EuclideanSpace.single j 1)))) := by
  intro I
  obtain ⟨_M, _hM, hCut⟩ := exists_scaled_ball_cutoff n
  obtain ⟨χ, hχ, _hcχ, hSupport, hOne, _hA, _hDχ⟩ :=
    hCut (0 : Domain n) (1/4) (by norm_num : (0 : ℝ) < 1/4)
  let Φ := fun x : Domain n => neumannKelvinRay 1 u (‖x‖⁻¹ • x) ‖x‖
  let v := fun x : Domain n => (1-χ x) • Φ x
  have hχZero (x : Domain n) (hx : 1/2 < ‖x‖) : χ x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hMem
    have H := hSupport hMem
    have H' : ‖x‖ < (1/2 : ℝ) := by norm_num only [mem_ball, dist_zero_right] at H ⊢; exact H
    exact (not_lt_of_ge hx.le) H'
  have hV (x : Domain n) (hx : 1/2 < ‖x‖) : v x = Φ x := by
    simp only [v, hχZero x hx, sub_zero, one_smul]
  have hv : ContDiff ℝ ∞ v := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      have hNear : v =ᶠ[𝓝 (0 : Domain n)] (fun _ => 0) := by
        filter_upwards [ball_mem_nhds (0 : Domain n) (by norm_num : (0 : ℝ) < 1/4)] with y hy
        have hχy : χ y = 1 := hOne y (ball_subset_closedBall hy)
        simp only [v, hχy, sub_self, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hNear
    · exact (contDiffAt_const.sub hχ.contDiffAt).smul
        (neumannKelvinReflection_contDiffAt 1 (by norm_num : (0 : ℝ) < 1) u hu x hx)
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · intro x hx
    rw [hV x (by rw [hx]; norm_num)]
    simp only [Φ, neumannKelvinRay, hx, inv_one, one_smul, Real.one_rpow,
      intervalIntegral.integral_same, smul_zero, add_zero]
  · intro x hx
    rw [hV x (by linarith only [hx])]
    exact neumannKelvinReflection_eq_dilation u x (norm_pos_iff.mp (lt_trans zero_lt_one hx))
  · intro x hx i P
    have hOpen : IsOpen {y : Domain n | (1/2 : ℝ) < ‖y‖} := isOpen_lt continuous_const continuous_norm
    have hNear : v =ᶠ[𝓝 x] Φ := by
      filter_upwards [hOpen.mem_nhds (show (1/2 : ℝ) < ‖x‖ by linarith only [hx])] with y hy
      exact hV y hy
    rw [hNear.fderiv_eq]
    exact neumannKelvinReflection_fderiv_column_dilation u hu x
      (norm_pos_iff.mp (lt_trans zero_lt_one hx)) i

end StationaryHarmonicMaps.Analysis

end
