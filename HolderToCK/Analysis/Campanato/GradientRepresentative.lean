module

public import HolderToCK.Analysis.Campanato.Representative
public import HolderToCK.Analysis.GradientLinearAlgebra
public import HarmonicMaps.EnergyLemmas

/-! # Campanato reconstruction of the displayed gradient columns

The same Hilbert--Schmidt energy and mean excess control every actual column.
Reconstructing these finitely many columns gives one field, with a common
almost-everywhere identity and all-radius limits. The field has no assumed
Sobolev derivative.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace HolderToCK

theorem sqrt_hsNormSq_le_of_columns_bound {n q : ℕ} (P : Gradient n q)
    {B : ℝ} (hB : 0 ≤ B) (hcolumns : ∀ i : Fin n, ‖P i‖ ≤ B) :
    Real.sqrt (hsNormSq P) ≤ Real.sqrt (n : ℝ) * B := by
  have hHS : hsNormSq P ≤ (n : ℝ) * B ^ 2 := by
    unfold hsNormSq
    calc
      _ ≤ ∑ _i : Fin n, B ^ 2 := Finset.sum_le_sum (fun i _ =>
        (sq_le_sq₀ (norm_nonneg _) hB).mpr (hcolumns i))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ ≤ Real.sqrt ((n : ℝ) * B ^ 2) := Real.sqrt_le_sqrt hHS
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hB]

theorem campanato_gradient_columns_representative (n : ℕ) (γ r₀ M : ℝ)
    (hγ : 0 < γ) (hγone : γ < 1) (hr₀ : 0 < r₀) (hr₀small : r₀ ≤ 1 / 8)
    (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (Du : Domain n → Gradient n q) (E : ℝ),
      (∀ i : Fin n, MemLp (fun x => Du x i) 2
        (volume.restrict (Metric.ball (0 : Domain n) (3 / 4)))) →
      0 ≤ E → (∫ x in Metric.ball (0 : Domain n) (3 / 4), hsNormSq (Du x)) ≤ E →
      (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ∀ r : ℝ, 0 < r → r ≤ r₀ →
        (∫ y in Metric.ball x r, hsNormSq (fun i =>
          Du y i - ⨍ z in Metric.ball x r, Du z i)) ≤
          M * E * Real.rpow r ((n : ℝ) + 2 * γ)) →
      ∃ G : Domain n → Gradient n q,
        (∀ i : Fin n, ContinuousOn (fun x => G x i) (Metric.ball (0 : Domain n) (5 / 8))) ∧
        G =ᵐ[volume.restrict (Metric.ball (0 : Domain n) (5 / 8))] Du ∧
        (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ∀ i : Fin n, ‖G x i‖ ≤ C * Real.sqrt E) ∧
        (∀ i : Fin n, HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
          (fun x => G x i) γ (C * Real.sqrt E)) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), Real.sqrt (hsNormSq (G x)) ≤
          Real.sqrt (n : ℝ) * C * Real.sqrt E) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ∀ y ∈ Metric.ball (0 : Domain n) (5 / 8),
          Real.sqrt (hsNormSq (fun i => G x i - G y i)) ≤
            (Real.sqrt (n : ℝ) * C * Real.sqrt E) * Real.rpow (dist x y) γ) ∧
        ∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ∀ i : Fin n,
          Tendsto (fun r : ℝ => ⨍ y in Metric.ball x r, Du y i)
            (𝓝[>] (0 : ℝ)) (𝓝 (G x i)) := by
  classical
  obtain ⟨hC, hrec⟩ := campanato_reconstruction n γ r₀ M hγ hγone hr₀ hr₀small hM
  let C := campanatoReconstructionConstant n γ r₀ M
  refine ⟨C, hC, ?_⟩
  intro q Du E hDu hE hEnergy hExcess
  have hI : IntegrableOn (fun x => hsNormSq (Du x)) (Metric.ball (0 : Domain n) (3 / 4)) :=
    integrable_hsNormSq_of_memLp_columns hDu
  have hcolEnergy (i : Fin n) :
      (∫ x in Metric.ball (0 : Domain n) (3 / 4), ‖Du x i‖ ^ 2) ≤ E := by
    have hi : IntegrableOn (fun x => ‖Du x i‖ ^ 2) (Metric.ball (0 : Domain n) (3 / 4)) :=
      (hDu i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
    apply (integral_mono hi hI _).trans hEnergy
    intro x
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖Du x j‖) (Finset.mem_univ i)
  have hcolExcess (i : Fin n) : ∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ∀ r : ℝ,
      0 < r → r ≤ r₀ →
      (∫ y in Metric.ball x r, ‖Du y i - ⨍ z in Metric.ball x r, Du z i‖ ^ 2) ≤
        M * E * Real.rpow r ((n : ℝ) + 2 * γ) := by
    intro x hx r hr hrr₀
    let μ := volume.restrict (Metric.ball x r)
    letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
    have hsmall (j : Fin n) : MemLp (fun y => Du y j) 2 μ :=
      (hDu j).mono_measure (Measure.restrict_mono_set volume
        (campanato_ball_subset_outer hx (hrr₀.trans hr₀small)))
    have hcenter (j : Fin n) : MemLp
        (fun y => Du y j - ⨍ z in Metric.ball x r, Du z j) 2 μ :=
      (hsmall j).sub (memLp_const _)
    have hi : Integrable (fun y => ‖Du y i - ⨍ z in Metric.ball x r, Du z i‖ ^ 2) μ :=
      (hcenter i).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
    have hHS : Integrable
        (fun y => hsNormSq (fun j => Du y j - ⨍ z in Metric.ball x r, Du z j)) μ :=
      integrable_hsNormSq_of_memLp_columns hcenter
    apply (integral_mono hi hHS _).trans (hExcess x hx r hr hrr₀)
    intro y
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖Du y j - ⨍ z in Metric.ball x r, Du z j‖)
      (Finset.mem_univ i)
  have hex (i : Fin n) := hrec q (fun x => Du x i) E (hDu i) hE (hcolEnergy i) (hcolExcess i)
  choose Gi hcont hAE hsup hHolder hlimit using hex
  let G : Domain n → Gradient n q := fun x i => Gi i x
  have hAEall : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) (5 / 8)),
      ∀ i : Fin n, Gi i x = Du x i := ae_all_iff.mpr hAE
  refine ⟨G, hcont, ?_, (fun x hx i => hsup i x hx), hHolder, ?_, ?_, ?_⟩
  · exact hAEall.mono (fun _ hx => funext hx)
  · intro x hx
    simpa only [mul_assoc] using sqrt_hsNormSq_le_of_columns_bound (G x)
      (mul_nonneg hC.le (Real.sqrt_nonneg E)) (fun i => hsup i x hx)
  · intro x hx y hy
    simpa only [C, mul_assoc, Real.rpow_eq_pow] using
      sqrt_hsNormSq_le_of_columns_bound (fun i => G x i - G y i)
      (mul_nonneg (mul_nonneg hC.le (Real.sqrt_nonneg E)) (Real.rpow_nonneg dist_nonneg _))
      (fun i => hHolder i x hx y hy)
  · exact fun x hx i => hlimit i x hx

end HolderToCK
end
