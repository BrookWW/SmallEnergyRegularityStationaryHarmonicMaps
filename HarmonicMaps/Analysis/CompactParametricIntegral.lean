module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Smooth integration over compact parameter spaces

Joint smoothness on an open set supplies bounds on each derivative over a
compact local source ball and the compact parameter image. Finite parameter
measure turns these bounds into integrable majorants.
-/

public section

universe u v w t

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace HarmonicMaps

private theorem compactParameter_continuous
    {E : Type u} [NormedAddCommGroup E] {B : Type v} [NormedAddCommGroup B]
    {G : Type w} [NormedAddCommGroup G]
    {A : Type t} [TopologicalSpace A]
    (β : A → B) (hβ : Continuous β) (D : Set (E × B)) (hD : IsOpen D)
    (J : E × B → G) (hJ : ContinuousOn J D)
    (x : E) (hx : ∀ θ : A, (x, β θ) ∈ D) :
    Continuous (fun θ : A => J (x, β θ)) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  exact (hJ.continuousAt (hD.mem_nhds (hx θ))).comp
    (f := fun θ : A => (x, β θ)) (continuous_const.prodMk hβ).continuousAt

private theorem compactParameter_integrable
    {E : Type u} [NormedAddCommGroup E] {B : Type v} [NormedAddCommGroup B]
    {G : Type w} [NormedAddCommGroup G]
    {A : Type t} [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A]
    [BorelSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    (β : A → B) (hβ : Continuous β) (D : Set (E × B)) (hD : IsOpen D)
    (J : E × B → G) (hJ : ContinuousOn J D)
    (x : E) (hx : ∀ θ : A, (x, β θ) ∈ D) :
    Integrable (fun θ : A => J (x, β θ)) μ := by
  exact (compactParameter_continuous β hβ D hD J hJ x hx).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem compactParameter_partial_smooth
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (D : Set (E × B)) (hD : IsOpen D)
    (J : E × B → G) (hJ : ContDiffOn ℝ ∞ J D) :
    ContDiffOn ℝ ∞ (fun p : E × B =>
      (fderiv ℝ J p).comp (ContinuousLinearMap.inl ℝ E B)) D := by
  exact (hJ.fderiv_of_isOpen hD (by simp)).clm_comp contDiffOn_const

private theorem compactParameter_slice_hasFDerivAt
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (D : Set (E × B)) (hD : IsOpen D)
    (J : E × B → G) (hJ : ContDiffOn ℝ ∞ J D)
    (x : E) (b : B) (hx : (x, b) ∈ D) :
    HasFDerivAt (fun z : E => J (z, b))
      ((fderiv ℝ J (x, b)).comp (ContinuousLinearMap.inl ℝ E B)) x := by
  have h := (hJ.contDiffAt (hD.mem_nhds hx)).differentiableAt (by simp)
  exact h.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x b)

/-- Differentiation under a finite measure over compact parameters, with all
local domination and measurability obtained from joint smoothness. -/
theorem compactParametricIntegral_hasFDerivAt {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {A : Type t} [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A]
    [BorelSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    (β : A → B) (hβ : Continuous β) (S : Set E) (hS : IsOpen S)
    (D : Set (E × B)) (hD : IsOpen D)
    (hPairs : ∀ x ∈ S, ∀ θ : A, (x, β θ) ∈ D)
    (J : E × B → G) (hJ : ContDiffOn ℝ ∞ J D)
    (x : E) (hx : x ∈ S) :
    HasFDerivAt (fun z : E => ∫ θ : A, J (z, β θ) ∂μ)
      (∫ θ : A, (fderiv ℝ J (x, β θ)).comp
        (ContinuousLinearMap.inl ℝ E B) ∂μ) x := by
  let J₁ : E × B → E →L[ℝ] G := fun p =>
    (fderiv ℝ J p).comp (ContinuousLinearMap.inl ℝ E B)
  have hJ₁ : ContDiffOn ℝ ∞ J₁ D := compactParameter_partial_smooth D hD J hJ
  obtain ⟨r, hr, hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hS.mem_nhds hx)
  have hK : IsCompact (Metric.closedBall x r ×ˢ range β) :=
    (isCompact_closedBall x r).prod (isCompact_range hβ)
  have hKD : Metric.closedBall x r ×ˢ range β ⊆ D := by
    rintro ⟨z, b⟩ ⟨hz, θ, rfl⟩
    exact hPairs z (hrs hz) θ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hJ₁.continuousOn.mono hKD)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun z θ => J₁ (z, β θ)) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds x hr)
  · filter_upwards [hS.eventually_mem hx] with z hz
    exact (compactParameter_continuous β hβ D hD J hJ.continuousOn z
      (hPairs z hz)).aestronglyMeasurable_of_compactSpace
  · exact compactParameter_integrable μ β hβ D hD J hJ.continuousOn x (hPairs x hx)
  · exact (compactParameter_continuous β hβ D hD J₁ hJ₁.continuousOn x
      (hPairs x hx)).aestronglyMeasurable_of_compactSpace
  · filter_upwards with θ z hz
    exact hC (z, β θ) ⟨hz, mem_range_self θ⟩
  · exact integrable_const C
  · filter_upwards with θ z hz
    exact compactParameter_slice_hasFDerivAt D hD J hJ z (β θ) (hPairs z (hrs hz) θ)


private theorem compactParametricIntegral_contDiffOn_nat
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {G : Type (max u w)} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {A : Type t} [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A]
    [BorelSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    (β : A → B) (hβ : Continuous β) (S : Set E) (hS : IsOpen S)
    (D : Set (E × B)) (hD : IsOpen D)
    (hPairs : ∀ x ∈ S, ∀ θ : A, (x, β θ) ∈ D)
    (J : E × B → G) (hJ : ContDiffOn ℝ ∞ J D) (k : ℕ) :
    ContDiffOn ℝ k (fun x : E => ∫ θ : A, J (x, β θ) ∂μ) S := by
  induction k generalizing G with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    apply DifferentiableOn.continuousOn (𝕜 := ℝ)
    intro x hx
    exact (compactParametricIntegral_hasFDerivAt μ β hβ S hS D hD hPairs J hJ x hx).differentiableAt.differentiableWithinAt
  | succ k ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hS]
    refine ⟨?_, by simp, ?_⟩
    · intro x hx
      exact (compactParametricIntegral_hasFDerivAt μ β hβ S hS D hD hPairs J hJ x hx).differentiableAt.differentiableWithinAt
    · have H := ih (fun p : E × B =>
          (fderiv ℝ J p).comp (ContinuousLinearMap.inl ℝ E B))
          (compactParameter_partial_smooth D hD J hJ)
      apply H.congr
      intro x hx
      exact (compactParametricIntegral_hasFDerivAt μ β hβ S hS D hD hPairs J hJ x hx).fderiv

/-- A jointly smooth integrand remains smooth after integration over compact
parameters with finite measure. -/
theorem compactParametricIntegral_contDiffOn {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {A : Type t} [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A]
    [BorelSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    (β : A → B) (hβ : Continuous β) (S : Set E) (hS : IsOpen S)
    (D : Set (E × B)) (hD : IsOpen D)
    (hPairs : ∀ x ∈ S, ∀ θ : A, (x, β θ) ∈ D)
    (J : E × B → G) (hJ : ContDiffOn ℝ ∞ J D)
    : ContDiffOn ℝ ∞ (fun x : E => ∫ θ : A, J (x, β θ) ∂μ) S := by
  let e : ULift.{u} G ≃L[ℝ] G := ContinuousLinearEquiv.ulift
  have hLift : ContDiffOn ℝ ∞ (fun p : E × B => e.symm (J p)) D :=
    e.symm.contDiff.comp_contDiffOn hJ
  have H : ContDiffOn ℝ ∞ (fun x : E => ∫ θ : A, e.symm (J (x, β θ)) ∂μ) S := by
    apply contDiffOn_infty.mpr
    intro k
    exact compactParametricIntegral_contDiffOn_nat μ β hβ S hS D hD hPairs _ hLift k
  apply (e.contDiff.comp_contDiffOn H).congr
  intro x hx
  have hInt := compactParameter_integrable μ β hβ D hD _ hLift.continuousOn x (hPairs x hx)
  change (∫ θ : A, J (x, β θ) ∂μ) =
    e.toContinuousLinearMap (∫ θ : A, e.symm (J (x, β θ)) ∂μ)
  rw [← e.toContinuousLinearMap.integral_comp_comm hInt]
  apply integral_congr_ae
  filter_upwards with θ
  exact (e.apply_symm_apply (J (x, β θ))).symm


/-- The native Euclidean Laplacian commutes with compact finite-measure
integration of a jointly smooth integrand. -/
theorem compactParametricIntegral_laplacian {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {B : Type v} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {A : Type t} [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A]
    [BorelSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    (β : A → B) (hβ : Continuous β) (S : Set E) (hS : IsOpen S)
    (D : Set (E × B)) (hD : IsOpen D)
    (hPairs : ∀ x ∈ S, ∀ θ : A, (x, β θ) ∈ D)
    (J : E × B → G) (hJ : ContDiffOn ℝ ∞ J D)
    (x : E) (hx : x ∈ S) :
    Laplacian.laplacian (fun z : E => ∫ θ : A, J (z, β θ) ∂μ) x =
      ∫ θ : A, Laplacian.laplacian (fun z : E => J (z, β θ)) x ∂μ := by
  let I : E → G := fun z => ∫ θ : A, J (z, β θ) ∂μ
  let J₁ : E × B → E →L[ℝ] G := fun p =>
    (fderiv ℝ J p).comp (ContinuousLinearMap.inl ℝ E B)
  let J₂ : E × B → E →L[ℝ] E →L[ℝ] G := fun p =>
    (fderiv ℝ J₁ p).comp (ContinuousLinearMap.inl ℝ E B)
  have hJ₁ : ContDiffOn ℝ ∞ J₁ D := compactParameter_partial_smooth D hD J hJ
  have hJ₂ : ContDiffOn ℝ ∞ J₂ D := compactParameter_partial_smooth D hD J₁ hJ₁
  have hI₁ : fderiv ℝ I =ᶠ[𝓝 x] (fun z => ∫ θ : A, J₁ (z, β θ) ∂μ) := by
    filter_upwards [hS.eventually_mem hx] with z hz
    exact (compactParametricIntegral_hasFDerivAt μ β hβ S hS D hD hPairs J hJ z hz).fderiv
  have hI₂ : fderiv ℝ (fderiv ℝ I) x = ∫ θ : A, J₂ (x, β θ) ∂μ := by
    rw [hI₁.fderiv_eq]
    exact (compactParametricIntegral_hasFDerivAt μ β hβ S hS D hD hPairs J₁ hJ₁ x hx).fderiv
  have hθ₂ (θ : A) :
      fderiv ℝ (fderiv ℝ (fun z : E => J (z, β θ))) x = J₂ (x, β θ) := by
    have H : fderiv ℝ (fun z : E => J (z, β θ)) =ᶠ[𝓝 x] (fun z => J₁ (z, β θ)) := by
      filter_upwards [hS.eventually_mem hx] with z hz
      exact (compactParameter_slice_hasFDerivAt D hD J hJ z (β θ) (hPairs z hz θ)).fderiv
    rw [H.fderiv_eq]
    exact (compactParameter_slice_hasFDerivAt D hD J₁ hJ₁ x (β θ) (hPairs x hx θ)).fderiv
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] G) := inferInstance
  have hInt : Integrable (fun θ : A => J₂ (x, β θ)) μ :=
    compactParameter_integrable μ β hβ D hD J₂ hJ₂.continuousOn x (hPairs x hx)
  let e := stdOrthonormalBasis ℝ E
  change Laplacian.laplacian I x = _
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hI₂, hθ₂]
  simp_rw [ContinuousLinearMap.integral_apply hInt]
  have hEval (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun θ : A => J₂ (x, β θ) (e i) (e i)) μ :=
    (hInt.apply_continuousLinearMap (e i)).apply_continuousLinearMap (e i)
  simp_rw [ContinuousLinearMap.integral_apply (hInt.apply_continuousLinearMap _)]
  exact (integral_finsetSum Finset.univ (fun i _ => hEval i)).symm

end HarmonicMaps

end
