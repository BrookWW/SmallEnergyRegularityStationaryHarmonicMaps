module

public import StationaryHarmonicMaps.Analysis.NeumannRadialDuality
public import StationaryHarmonicMaps.Analysis.NeumannTangentTests

/-!
# The actual tangential radial part of the Neumann pairing

The original columns pair with genuine compact projected tests. Ordinary
dilation duality, the actual projection symmetry and the true reciprocal
parameter give the full vector-valued radial adjoint pairing.
-/

public section

open HarmonicMaps MeasureTheory Set Filter Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The original L2 columns have the true ordinary tangential radial adjoint pairing, with both actual integrabilities. -/
theorem neumann_kelvin_radial_integral_pairing {n q : ℕ} (hn : 2 ≤ n)
    (D : Domain n → Gradient n q)
    (hD : ∀ j, MemLp (fun x => D x j) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ ball (0 : Domain n) 2) :
    let A := {x : Domain n | 1 < ‖x‖ ∧ ‖x‖ < 2}
    let V := fun x j => ‖x‖^(n-2) •
      (∫ t in (‖x‖⁻¹)^2..‖x‖⁻¹, t^(n-2) • D (t • x) j)
    let T := fun x i => ∑ j : Fin n,
      ((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j • V x j
    let R := fun y i => ‖y‖^(n-2) •
      (∫ t in ‖y‖/2..‖y‖^2, t^(-(n : ℝ)) •
        fderiv ℝ ψ (t⁻¹ • y) ((ℝ ∙ y)ᗮ.starProjection (EuclideanSpace.single i 1)))
    IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (T x i)
      (fderiv ℝ ψ x (EuclideanSpace.single i 1))) A volume ∧
      IntegrableOn (fun y => ∑ i : Fin n, inner ℝ (D y i) (R y i)) (ball (0 : Domain n) 1) volume ∧
      (∫ x in A, ∑ i : Fin n, inner ℝ (T x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) =
        ∫ y in ball (0 : Domain n) 1, ∑ i : Fin n, inner ℝ (D y i) (R y i) := by
  intro A V T R
  let μ := volume.restrict A
  let ν := volume.restrict (ball (0 : Domain n) 1)
  obtain ⟨v, hv, hcv, hsv, hV⟩ := exists_compact_neumann_tangent_tests ψ hψ hcψ hsψ
  let B := fun j (y : Domain n) => ‖y‖^(n-2) *
    (∫ t in ‖y‖/2..‖y‖^2, (t^n)⁻¹ * inner ℝ (D y j) (v j (t⁻¹ • y)))
  have hDual (j : Fin n) := neumann_radial_interval_duality (by omega : 1 ≤ n) (n-2)
    (fun x => D x j) (v j) (hD j) (hv j).continuous (hcv j) (hsv j)
  have hLeft (x : Domain n) (hx : x ∈ A) :
      (∑ j : Fin n, inner ℝ (V x j) (v j x)) =
        ∑ i : Fin n, inner ℝ (T x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1)) := by
    simp only [hV _ x hx.1.le]
    exact (neumann_tangent_columns_pairing x (V x) (fderiv ℝ ψ x)).symm
  have hRight (y : Domain n) (hy : y ≠ 0) (hyBall : y ∈ ball (0 : Domain n) 1) (j : Fin n) :
      B j y = inner ℝ (D y j) (R y j) := by
    have hyPos : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hyOne : ‖y‖ < 1 := mem_ball_zero_iff.mp hyBall
    let W := fun t : ℝ => t^(-(n : ℝ)) •
      fderiv ℝ ψ (t⁻¹ • y) ((ℝ ∙ y)ᗮ.starProjection (EuclideanSpace.single j 1))
    have hPositive (t : ℝ) (ht : t ∈ uIcc (‖y‖/2) (‖y‖^2)) : 0 < t :=
      (lt_min (half_pos hyPos) (sq_pos_of_pos hyPos)).trans_le ht.1
    have hWI : IntervalIntegrable W volume (‖y‖/2) (‖y‖^2) := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      have htPos := hPositive t ht
      exact ((Real.continuousAt_rpow_const t (-(n : ℝ)) (Or.inl htPos.ne')).smul
        (((hψ.continuous_fderiv (by simp)).continuousAt.comp
          ((continuousAt_id.inv₀ htPos.ne').smul continuousAt_const)).clm_apply
            continuousAt_const)).continuousWithinAt
    have hPoint (t : ℝ) (ht : t ∈ uIcc (‖y‖/2) (‖y‖^2)) :
        (t^n)⁻¹ * inner ℝ (D y j) (v j (t⁻¹ • y)) = inner ℝ (D y j) (W t) := by
      have htPos := hPositive t ht
      have htLe : t ≤ ‖y‖ := ht.2.trans (max_le (by linarith only [hyPos])
        (by nlinarith only [hyPos, hyOne]))
      have hSample : 1 ≤ ‖t⁻¹ • y‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr htPos.le)]
        have H : 1 ≤ ‖y‖/t := (one_le_div htPos).mpr htLe
        simpa only [div_eq_inv_mul] using H
      rw [hV j _ hSample, neumann_tangent_projection_smul t⁻¹ (inv_ne_zero htPos.ne')]
      dsimp only [W]
      rw [inner_smul_right, Real.rpow_neg htPos.le, Real.rpow_natCast]
    have hInner := (innerSL ℝ (D y j)).intervalIntegral_comp_comm hWI
    simp only [innerSL_apply_apply] at hInner
    change ‖y‖^(n-2) * (∫ t in ‖y‖/2..‖y‖^2,
      (t^n)⁻¹ * inner ℝ (D y j) (v j (t⁻¹ • y))) = _
    rw [intervalIntegral.integral_congr hPoint, hInner]
    exact (real_inner_smul_right _ _ _).symm
  have hALeft : (fun x => ∑ j : Fin n, inner ℝ (V x j) (v j x)) =ᵐ[μ]
      (fun x => ∑ i : Fin n, inner ℝ (T x i) (fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
    filter_upwards [ae_restrict_mem ((measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const))] with x hx
    exact hLeft x hx
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hAE0 : ∀ᵐ y : Domain n ∂volume, y ≠ 0 := by simp [ae_iff]
  have hARight : (fun y => ∑ j : Fin n, B j y) =ᵐ[ν]
      (fun y => ∑ j : Fin n, inner ℝ (D y j) (R y j)) := by
    filter_upwards [hAE0.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_ball] with y hy hyBall
    exact Finset.sum_congr rfl (fun j _ => hRight y hy hyBall j)
  have hLI : Integrable (fun x => ∑ j : Fin n, inner ℝ (V x j) (v j x)) μ :=
    integrable_finsetSum _ (fun j _ => (hDual j).1)
  have hRI : Integrable (fun y => ∑ j : Fin n, B j y) ν :=
    integrable_finsetSum _ (fun j _ => (hDual j).2.1)
  refine ⟨hLI.congr hALeft, hRI.congr hARight, ?_⟩
  calc
    _ = ∫ x, ∑ j : Fin n, inner ℝ (V x j) (v j x) ∂μ := (integral_congr_ae hALeft).symm
    _ = ∑ j : Fin n, ∫ x, inner ℝ (V x j) (v j x) ∂μ :=
      integral_finsetSum _ (fun j _ => (hDual j).1)
    _ = ∑ j : Fin n, ∫ y, B j y ∂ν := Finset.sum_congr rfl (fun j _ => (hDual j).2.2)
    _ = ∫ y, ∑ j : Fin n, B j y ∂ν := (integral_finsetSum _ (fun j _ => (hDual j).2.1)).symm
    _ = _ := integral_congr_ae hARight

end StationaryHarmonicMaps.Analysis

end
