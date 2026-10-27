module

public import StationaryHarmonicMaps.Analysis.NeumannGradientSpace

/-!
# Actual closed projection onto unrestricted smooth gradients

The genuine full smooth-gradient range gives a closed Hilbert subspace.
Its actual orthogonal projection contracts the full HS energy, has genuine
smooth-gradient approximants and answers all ambient smooth tests with
arbitrary boundary values. A native mean-zero potential is recovered
separately from the actual coefficient sequence.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Every actual L2 one-form has a genuine closed unrestricted-gradient projection with energy coefficient one and all smooth natural tests. -/
theorem exists_closed_smooth_gradient_projection_ball {n q : ℕ} (a : Domain n) (r : ℝ)
    (F : Domain n → Gradient n q)
    (hF : ∀ i : Fin n, MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a r))) :
    let μ := volume.restrict (Metric.ball a r)
    let E : Gradient n q → Ambient (n * q) := fun A => WithLp.toLp 2
      (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    let T : Set (Lp (Ambient (n * q)) 2 μ) := {Z | ∃ ψ : Domain n → Ambient q,
      ContDiff ℝ ∞ ψ ∧
      (Z : Domain n → Ambient (n * q)) =ᵐ[μ]
        (fun x => E (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1)))}
    ∃ A P : Lp (Ambient (n * q)) 2 μ,
      (A : Domain n → Ambient (n * q)) =ᵐ[μ] (fun x => E (F x)) ∧
      P ∈ (Submodule.span ℝ T).topologicalClosure ∧
      (∀ Z ∈ (Submodule.span ℝ T).topologicalClosure, inner ℝ (P - A) Z = 0) ∧
      (∃ Z : ℕ → Lp (Ambient (n * q)) 2 μ,
        (∀ j, Z j ∈ T) ∧ Tendsto Z atTop (𝓝 P)) ∧
      (∫ x, ‖P x‖ ^ 2 ∂μ) ≤ ∫ x, hsNormSq (F x) ∂μ ∧
      ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ →
        Integrable (fun x => inner ℝ (P x)
          (E (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1)))) μ ∧
        Integrable (fun x => ∑ i : Fin n, inner ℝ (F x i)
          (fderiv ℝ ψ x (EuclideanSpace.single i 1))) μ ∧
        (∫ x, inner ℝ (P x)
          (E (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1))) ∂μ) =
          ∫ x, ∑ i : Fin n, inner ℝ (F x i)
            (fderiv ℝ ψ x (EuclideanSpace.single i 1)) ∂μ := by
  let μ := volume.restrict (Metric.ball a r)
  let E : Gradient n q → Ambient (n * q) := fun A => WithLp.toLp 2
    (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  let T : Set (Lp (Ambient (n * q)) 2 μ) := {Z | ∃ ψ : Domain n → Ambient q,
    ContDiff ℝ ∞ ψ ∧
    (Z : Domain n → Ambient (n * q)) =ᵐ[μ]
      (fun x => E (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1)))}
  obtain ⟨S, hS⟩ := exists_smooth_gradient_submodule_ball (q := q) a r
  have hST : (S : Set (Lp (Ambient (n * q)) 2 μ)) = T := Set.ext hS
  have hspan : Submodule.span ℝ T = S := by
    rw [← hST]
    exact Submodule.span_eq S
  let A : Lp (Ambient (n * q)) 2 μ := (memLp_hs_flatten F hF).toLp (fun x => E (F x))
  let P : Lp (Ambient (n * q)) 2 μ := S.topologicalClosure.starProjection A
  have hA : (A : Domain n → Ambient (n * q)) =ᵐ[μ] (fun x => E (F x)) :=
    (memLp_hs_flatten F hF).coeFn_toLp
  have hPmem : P ∈ (Submodule.span ℝ T).topologicalClosure := by
    rw [hspan]
    exact S.topologicalClosure.starProjection_apply_mem A
  have horth : ∀ Z ∈ (Submodule.span ℝ T).topologicalClosure,
      inner ℝ (P - A) Z = 0 := by
    intro Z hZ
    rw [hspan] at hZ
    have H := S.topologicalClosure.starProjection_inner_eq_zero A Z hZ
    change inner ℝ (P - A) Z = 0
    calc
      _ = -(inner ℝ (A - P) Z) := by simp only [inner_sub_left]; ring
      _ = 0 := by rw [H, neg_zero]
  have hseq : ∃ Z : ℕ → Lp (Ambient (n * q)) 2 μ,
      (∀ j, Z j ∈ T) ∧ Tendsto Z atTop (𝓝 P) := by
    have hpS : P ∈ closure (S : Set (Lp (Ambient (n * q)) 2 μ)) := by
      rw [← Submodule.topologicalClosure_coe]
      rw [hspan] at hPmem
      exact hPmem
    rw [hST] at hpS
    exact mem_closure_iff_seq_limit.mp hpS
  have hnorm (Z : Lp (Ambient (n * q)) 2 μ) : ‖Z‖ ^ 2 = ∫ x, ‖Z x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    exact integral_congr_ae (Eventually.of_forall fun x => real_inner_self_eq_norm_sq (Z x))
  have hAnorm : ‖A‖ ^ 2 = ∫ x, hsNormSq (F x) ∂μ := by
    rw [hnorm]
    apply integral_congr_ae
    filter_upwards [hA] with x hx
    rw [hx]
    exact hs_flatten_norm_sq (F x)
  have henergy : (∫ x, ‖P x‖ ^ 2 ∂μ) ≤ ∫ x, hsNormSq (F x) ∂μ := by
    rw [← hnorm, ← hAnorm]
    exact pow_le_pow_left₀ (norm_nonneg _) (S.topologicalClosure.norm_starProjection_apply_le A) 2
  refine ⟨A, P, hA, hPmem, horth, hseq, henergy, ?_⟩
  intro ψ hψ
  let Dψ (x : Domain n) (i : Fin n) := fderiv ℝ ψ x (EuclideanSpace.single i 1)
  have hWDψ := memW12_ball_of_ambient_c1 a r ψ (hψ.of_le (by simp))
  have hDψ (i : Fin n) : MemLp (fun x => Dψ x i) 2 μ := hWDψ.2.2 i
  have hEDψ : MemLp (fun x => E (Dψ x)) 2 μ := memLp_hs_flatten Dψ hDψ
  let Z : Lp (Ambient (n * q)) 2 μ := hEDψ.toLp (fun x => E (Dψ x))
  have hZ : (Z : Domain n → Ambient (n * q)) =ᵐ[μ] (fun x => E (Dψ x)) := hEDψ.coeFn_toLp
  have hZT : Z ∈ T := ⟨ψ, hψ, hZ⟩
  have hZclosure : Z ∈ (Submodule.span ℝ T).topologicalClosure :=
    (Submodule.span ℝ T).le_topologicalClosure (Submodule.subset_span hZT)
  have hinner : inner ℝ P Z = inner ℝ A Z := by
    have H := horth Z hZclosure
    rw [inner_sub_left] at H
    exact sub_eq_zero.mp H
  have hPI : Integrable (fun x => inner ℝ (P x) (E (Dψ x))) μ :=
    HolderToCK.integrable_inner_of_memLp_two (Lp.memLp P) hEDψ
  have hFI : Integrable (fun x => ∑ i : Fin n, inner ℝ (F x i) (Dψ x i)) μ :=
    (HolderToCK.integrable_inner_of_memLp_two (memLp_hs_flatten F hF) hEDψ).congr
      (Eventually.of_forall fun x => hs_flatten_inner (F x) (Dψ x))
  have hPZ : inner ℝ P Z = ∫ x, inner ℝ (P x) (E (Dψ x)) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hZ] with x hx
    rw [hx]
  have hAZ : inner ℝ A Z = ∫ x, ∑ i : Fin n, inner ℝ (F x i) (Dψ x i) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hA, hZ] with x hx hy
    rw [hx, hy]
    exact hs_flatten_inner (F x) (Dψ x)
  exact ⟨hPI, hFI, hPZ.symm.trans (hinner.trans hAZ)⟩

end StationaryHarmonicMaps.Analysis

end
