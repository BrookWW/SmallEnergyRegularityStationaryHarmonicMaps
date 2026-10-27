module

public import StationaryHarmonicMaps.Analysis.DistributionHarmonicMollification
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtEncoding

/-!
# Actual vector and scalar distributional Laplacian tests

Testing a vector distribution against a smooth scalar test times each
constant coordinate vector recovers its actual Bochner-valued scalar-test
identity. Finite coordinate projections then assemble the complete HS
encoding from the original column identities.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

private theorem laplacian_test_continuous_compact {n : ℕ} (η : Domain n → ℝ)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) :
    Continuous (Laplacian.laplacian η) ∧ HasCompactSupport (Laplacian.laplacian η) := by
  have hfun : Laplacian.laplacian η = fun x => ∑ i : Fin n,
      fderiv ℝ (fun z => fderiv ℝ η z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := funext (laplacian_eq_sum_second_coordinate η hη)
  refine ⟨?_, HasCompactSupport.intro hcη ?_⟩
  · rw [hfun]
    apply continuous_finsetSum
    intro i _
    have hd : ContDiff ℝ ∞ (fun z => fderiv ℝ η z (EuclideanSpace.single i 1)) :=
      (hη.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact (hd.continuous_fderiv (by simp)).clm_apply continuous_const
  · intro x hx
    have hlocal : η =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have H := InnerProductSpace.laplacian_congr_nhds hlocal
    simpa only [InnerProductSpace.laplacian_const, Pi.zero_apply] using H.eq_of_nhds

private theorem integrable_laplacian_smul_test {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val volume)
    (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) :
    IntegrableOn (fun x => Laplacian.laplacian η x • u x) Ω.val volume := by
  obtain ⟨hcont, hcompact⟩ := laplacian_test_continuous_compact η hη hcη
  exact hu.smul_of_top_right (hcont.memLp_top_of_hasCompactSupport hcompact _)

/-- Actual vector Laplacian pairings give the integrable scalar-test Bochner identity. -/
theorem scalar_vector_laplacian_of_vector_tests {n q : ℕ} (Ω : OpenDomain n)
    (u : Domain n → Ambient q) (hu : IntegrableOn u Ω.val volume)
    (hvector : ∀ (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ω.val → (∫ x in Ω.val, inner ℝ (u x) (Laplacian.laplacian ψ x)) = 0)
    (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ Ω.val) :
    IntegrableOn (fun x => Laplacian.laplacian η x • u x) Ω.val volume ∧
      (∫ x in Ω.val, Laplacian.laplacian η x • u x) = 0 := by
  have hI := integrable_laplacian_smul_test Ω u hu η hη hcη
  refine ⟨hI, ?_⟩
  ext j
  let e : Ambient q := EuclideanSpace.single j 1
  let L : ℝ →L[ℝ] Ambient q := (ContinuousLinearMap.id ℝ ℝ).smulRight e
  let ψ : Domain n → Ambient q := L ∘ η
  have hψ : ContDiff ℝ ∞ ψ := L.contDiff.comp hη
  have hcψ : HasCompactSupport ψ := hcη.comp_left (g := L) (map_zero L)
  have hsψη : tsupport ψ ⊆ tsupport η := by
    apply closure_mono
    intro x hx hzero
    apply hx
    change L (η x) = 0
    rw [hzero, map_zero]
  have hΔψ (x : Domain n) : Laplacian.laplacian ψ x = Laplacian.laplacian η x • e := by
    exact (hη.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.laplacian_CLM_comp_left
  have H := hvector ψ hψ hcψ (hsψη.trans hsη)
  have Hscalar : (∫ x in Ω.val, Laplacian.laplacian η x * u x j) = 0 := by
    simpa only [hΔψ, inner_smul_right, e, EuclideanSpace.inner_single_right,
      conj_trivial, one_mul] using H
  have Hcoord := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).integral_comp_comm hI
  exact Hcoord.symm.trans Hscalar

/-- Original L² columns and their vector distribution tests produce the literal full HS scalar-test identity. -/
theorem hs_flatten_laplacian_of_column_vector_tests {n q : ℕ}
    (a : Domain n) (R : ℝ) (F : Domain n → Gradient n q)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict (Metric.ball a R)))
    (hvector : ∀ (i : Fin n) (ψ : Domain n → Ambient q), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball a R →
        (∫ x in Metric.ball a R, inner ℝ (F x i) (Laplacian.laplacian ψ x)) = 0)
    (η : Domain n → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ Metric.ball a R) :
    let E := fun x => WithLp.toLp 2 (fun j : Fin (n * q) =>
      F x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
    IntegrableOn (fun x => Laplacian.laplacian η x • E x) (Metric.ball a R) volume ∧
      (∫ x in Metric.ball a R, Laplacian.laplacian η x • E x) = 0 := by
  intro E
  let Ω := ballDomain a R
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hEI : IntegrableOn E (Metric.ball a R) volume :=
    (memLp_hs_flatten F hF).integrable (by norm_num)
  have H (i : Fin n) := scalar_vector_laplacian_of_vector_tests Ω (fun x => F x i)
    ((hF i).integrable (by norm_num)) (hvector i) η hη hcη hsη
  have hI := integrable_laplacian_smul_test Ω E hEI η hη hcη
  refine ⟨hI, ?_⟩
  ext j
  let i := (finProdFinEquiv.symm j).1
  let k := (finProdFinEquiv.symm j).2
  have Hcol := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) k).integral_comp_comm (H i).1
  have Hscalar : (∫ x in Ω.val, Laplacian.laplacian η x * F x i k) = 0 := by
    change (∫ x in Ω.val, Laplacian.laplacian η x * F x i k) =
      (∫ x in Ω.val, Laplacian.laplacian η x • F x i) k at Hcol
    rw [(H i).2] at Hcol
    exact Hcol
  have Hcoord := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin (n * q) => ℝ) j).integral_comp_comm hI
  exact Hcoord.symm.trans Hscalar

end StationaryHarmonicMaps.Analysis

end
