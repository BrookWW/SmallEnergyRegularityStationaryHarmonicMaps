module

public import StationaryHarmonicMaps.Analysis.HilbertSchmidtEncoding
public import HolderToCK.Analysis.L2PairingContinuity
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Topology.Sequences

/-!
# The L² projection onto the closure of actual compact test gradients

All coefficients use a literal Euclidean Hilbert--Schmidt encoding. The
smooth compact gradient range is a genuine linear subspace of L². Its closed
subspace projection has the contraction and test orthogonality properties.
A potential with zero boundary values requires an additional recovery argument.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The L² classes of actual compact smooth test gradients form a linear subspace. -/
theorem exists_smooth_compact_gradient_submodule {n q : ℕ} (Ω : OpenDomain n) :
    let μ := volume.restrict Ω.val
    let E : Gradient n q → Ambient (n * q) := fun A => WithLp.toLp 2
      (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    ∃ S : Submodule ℝ (Lp (Ambient (n * q)) 2 μ), ∀ Z, Z ∈ S ↔
      ∃ ψ : Domain n → Ambient q, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        tsupport ψ ⊆ Ω.val ∧
        (Z : Domain n → Ambient (n * q)) =ᵐ[μ]
          (fun x => E (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1))) := by
  let μ := volume.restrict Ω.val
  let E : Gradient n q → Ambient (n * q) := fun A => WithLp.toLp 2
    (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  let S : Submodule ℝ (Lp (Ambient (n * q)) 2 μ) :=
    { carrier := {Z | ∃ ψ : Domain n → Ambient q,
        ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω.val ∧
        (Z : Domain n → Ambient (n * q)) =ᵐ[μ]
          (fun x => E (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1)))}
      zero_mem' := by
        refine ⟨0, contDiff_const, HasCompactSupport.zero, by simp, ?_⟩
        filter_upwards [Lp.coeFn_zero (Ambient (n * q)) 2 μ] with x hx
        rw [hx]
        ext k
        change 0 = (fderiv ℝ (0 : Domain n → Ambient q) x
          (EuclideanSpace.single (finProdFinEquiv.symm k).1 1)) (finProdFinEquiv.symm k).2
        rw [fderiv_zero]
        rfl
      add_mem' := by
        rintro Z W ⟨ψ, hψ, hcψ, hsψ, hZ⟩ ⟨φ, hφ, hcφ, hsφ, hW⟩
        refine ⟨ψ + φ, hψ.add hφ, hcψ.add hcφ,
          (tsupport_add ψ φ).trans (union_subset hsψ hsφ), ?_⟩
        filter_upwards [Lp.coeFn_add Z W, hZ, hW] with x hx hz hw
        rw [hx]
        change Z x + W x = _
        rw [hz, hw]
        ext k
        change (fderiv ℝ ψ x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
            (finProdFinEquiv.symm k).2 +
          (fderiv ℝ φ x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
            (finProdFinEquiv.symm k).2 =
          (fderiv ℝ (ψ + φ) x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
            (finProdFinEquiv.symm k).2
        rw [fderiv_add (hψ.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
        rfl
      smul_mem' := by
        rintro c Z ⟨ψ, hψ, hcψ, hsψ, hZ⟩
        refine ⟨c • ψ, contDiff_const.smul hψ,
          HasCompactSupport.smul_left (f := fun _ : Domain n => c) hcψ,
          (tsupport_smul_subset_right (fun _ : Domain n => c) ψ).trans hsψ, ?_⟩
        filter_upwards [Lp.coeFn_smul c Z, hZ] with x hx hz
        rw [hx]
        change c • Z x = _
        rw [hz]
        ext k
        change c * (fderiv ℝ ψ x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
          (finProdFinEquiv.symm k).2 =
          (fderiv ℝ (c • ψ) x (EuclideanSpace.single (finProdFinEquiv.symm k).1 1))
            (finProdFinEquiv.symm k).2
        rw [fderiv_const_smul (hψ.differentiable (by simp) x) c]
        rfl }
  exact ⟨S, fun _ => Iff.rfl⟩

/-- Arbitrary L² one-forms have a genuine closed-gradient projection, before potential recovery. -/
theorem exists_closed_compact_gradient_projection {n q : ℕ} (Ω : OpenDomain n)
    (F : Domain n → Gradient n q)
    (hF : ∀ i : Fin n, MemLp (fun x => F x i) 2 (volume.restrict Ω.val)) :
    let μ := volume.restrict Ω.val
    let E : Gradient n q → Ambient (n * q) := fun A => WithLp.toLp 2
      (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    let T : Set (Lp (Ambient (n * q)) 2 μ) := {Z | ∃ ψ : Domain n → Ambient q,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω.val ∧
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
        HasCompactSupport ψ → tsupport ψ ⊆ Ω.val →
        Integrable (fun x => inner ℝ (P x)
          (E (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1)))) μ ∧
        Integrable (fun x => ∑ i : Fin n, inner ℝ (F x i)
          (fderiv ℝ ψ x (EuclideanSpace.single i 1))) μ ∧
        (∫ x, inner ℝ (P x)
          (E (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1))) ∂μ) =
          ∫ x, ∑ i : Fin n, inner ℝ (F x i)
            (fderiv ℝ ψ x (EuclideanSpace.single i 1)) ∂μ := by
  let μ := volume.restrict Ω.val
  let E : Gradient n q → Ambient (n * q) := fun A => WithLp.toLp 2
    (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  let T : Set (Lp (Ambient (n * q)) 2 μ) := {Z | ∃ ψ : Domain n → Ambient q,
    ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω.val ∧
    (Z : Domain n → Ambient (n * q)) =ᵐ[μ]
      (fun x => E (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1)))}
  obtain ⟨S, hS⟩ := exists_smooth_compact_gradient_submodule (q := q) Ω
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
  intro ψ hψ hcψ hsψ
  let Dψ (x : Domain n) (i : Fin n) := fderiv ℝ ψ x (EuclideanSpace.single i 1)
  have hDψ (i : Fin n) : MemLp (fun x => Dψ x i) 2 μ :=
    ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hcψ.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hEDψ : MemLp (fun x => E (Dψ x)) 2 μ := memLp_hs_flatten Dψ hDψ
  let Z : Lp (Ambient (n * q)) 2 μ := hEDψ.toLp (fun x => E (Dψ x))
  have hZ : (Z : Domain n → Ambient (n * q)) =ᵐ[μ] (fun x => E (Dψ x)) := hEDψ.coeFn_toLp
  have hZT : Z ∈ T := ⟨ψ, hψ, hcψ, hsψ, hZ⟩
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

/-- Every point of the closed compact-gradient space has actual smooth gradient approximants. -/
theorem exists_smooth_gradient_approximation_of_mem_closedSpan {n q : ℕ} (Ω : OpenDomain n) :
    let μ := volume.restrict Ω.val
    let E : Gradient n q → Ambient (n * q) := fun A => WithLp.toLp 2
      (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    let T : Set (Lp (Ambient (n * q)) 2 μ) := {Z | ∃ ψ : Domain n → Ambient q,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω.val ∧
      (Z : Domain n → Ambient (n * q)) =ᵐ[μ]
        (fun x => E (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1)))}
    ∀ P ∈ (Submodule.span ℝ T).topologicalClosure,
      ∃ ψ : ℕ → Domain n → Ambient q,
        (∀ j, ContDiff ℝ ∞ (ψ j) ∧ HasCompactSupport (ψ j) ∧ tsupport (ψ j) ⊆ Ω.val) ∧
        Tendsto (fun j => eLpNorm (fun x =>
          E (fun i => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) - P x) 2 μ)
          atTop (𝓝 0) := by
  dsimp only
  let μ := volume.restrict Ω.val
  let E : Gradient n q → Ambient (n * q) := fun A => WithLp.toLp 2
    (fun k => A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
  let T : Set (Lp (Ambient (n * q)) 2 μ) := {Z | ∃ ψ : Domain n → Ambient q,
    ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω.val ∧
    (Z : Domain n → Ambient (n * q)) =ᵐ[μ]
      (fun x => E (fun i => fderiv ℝ ψ x (EuclideanSpace.single i 1)))}
  obtain ⟨S, hS⟩ := exists_smooth_compact_gradient_submodule (q := q) Ω
  have hST : (S : Set (Lp (Ambient (n * q)) 2 μ)) = T := Set.ext hS
  have hspan : Submodule.span ℝ T = S := by
    rw [← hST]
    exact Submodule.span_eq S
  intro P hP
  have hpS : P ∈ closure (S : Set (Lp (Ambient (n * q)) 2 μ)) := by
    rw [← Submodule.topologicalClosure_coe]
    rw [hspan] at hP
    exact hP
  rw [hST] at hpS
  obtain ⟨Z, hZ, hlim⟩ := mem_closure_iff_seq_limit.mp hpS
  choose ψ hψ hcψ hsψ hae using hZ
  refine ⟨ψ, (fun j => ⟨hψ j, hcψ j, hsψ j⟩), ?_⟩
  have H := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' Z P).mp hlim
  apply H.congr
  intro j
  apply eLpNorm_congr_ae
  filter_upwards [hae j] with x hx
  change Z j x - P x = E (fun i => fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) - P x
  rw [hx]

end StationaryHarmonicMaps.Analysis

end
