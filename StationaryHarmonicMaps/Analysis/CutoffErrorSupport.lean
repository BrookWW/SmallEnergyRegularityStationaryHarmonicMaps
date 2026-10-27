module

public import StationaryHarmonicMaps.Analysis.OrthogonalFrameCutoff

/-! # Actual compact support and integrability of the expanded cutoff error -/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- The native Laplacian vanishes away from the actual topological support. -/
theorem laplacian_eq_zero_off_tsupport {n : ℕ} (χ : Domain n → ℝ)
    {x : Domain n} (hx : x ∉ tsupport χ) : Laplacian.laplacian χ x = 0 := by
  have hlocal : χ =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have H := InnerProductSpace.laplacian_congr_nhds hlocal
  simpa only [InnerProductSpace.laplacian_const, Pi.zero_apply] using H.eq_of_nhds

/-- Every term of the literal four-term error is supported inside the actual cutoff support. -/
theorem tsupport_expanded_cutoff_error_subset {n q : ℕ}
    (P : Domain n → Ambient q →L[ℝ] Ambient q)
    (D Z : Domain n → Fin n → Ambient q →L[ℝ] Ambient q)
    (w : Domain n → Ambient q) (v : Domain n → Gradient n q) (χ : Domain n → ℝ) :
    tsupport (fun x =>
      (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • star (D x i) (w x)) +
      (2 : ℝ) • (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • star (P x) (v x i)) +
      Laplacian.laplacian χ x • star (P x) (w x) +
      ∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • Z x i (star (P x) (w x))) ⊆
      tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hnot
  apply hx
  have hDχ (i : Fin n) : fderiv ℝ χ x (EuclideanSpace.single i 1) = 0 := by
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot, zero_apply]
  simp only [hDχ, laplacian_eq_zero_off_tsupport χ hnot, zero_smul,
    Finset.sum_const_zero, smul_zero, add_zero]

/-- Local L¹ on the original domain and an actual compact support give global L¹. -/
theorem integrable_of_local_of_tsupport_subset {n k : ℕ} {Ω : OpenDomain n}
    {f : Domain n → Ambient k} (hf : LocallyIntegrableOn f Ω.val volume)
    {χ : Domain n → ℝ} (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω.val)
    (hfs : tsupport f ⊆ tsupport χ) : Integrable f volume := by
  have hK := hf.integrableOn_compact_subset hsχ hcχ
  exact (integrableOn_iff_integrable_of_support_subset
    ((subset_tsupport f).trans hfs)).mp hK

end StationaryHarmonicMaps.Analysis

end
