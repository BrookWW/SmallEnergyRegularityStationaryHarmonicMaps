module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Gluing local C¹ extensions

Local C¹ extensions from a closed Euclidean subset glue by the existing smooth
partition-of-unity theorem. A compact subset additionally admits a compactly
supported extension whose ambient derivative has a uniform operator bound.
The resulting extensions are existence witnesses, with no canonical choice.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace StationaryHarmonicMaps.Geometry

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Local C¹ extension near a closed subset gives a genuine global C¹ extension. -/
theorem exists_contDiff_extension_of_local (K : Set X) (hK : IsClosed K) (f : K → E)
    (hloc : ∀ p : K, ∃ (U : Set X) (g : X → E),
      IsOpen U ∧ p.val ∈ U ∧ ContDiffOn ℝ 1 g U ∧
      ∀ y : K, y.val ∈ U → g y.val = f y) :
    ∃ G : X → E, ContDiff ℝ 1 G ∧ ∀ p : K, G p.val = f p := by
  let t : X → Set E := fun x => {v | ∀ hx : x ∈ K, v = f ⟨x, hx⟩}
  have ht (x : X) : Convex ℝ (t x) := by
    intro a ha b hb c d hc hd hsum hx
    rw [ha hx, hb hx, ← add_smul, hsum, one_smul]
  have hlocal : ∀ x : X, ∃ U ∈ 𝓝 x, ∃ g : X → E,
      ContMDiffOn 𝓘(ℝ, X) 𝓘(ℝ, E) 1 g U ∧ ∀ y ∈ U, g y ∈ t y := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨U, g, hUo, hxU, hg, hmatch⟩ := hloc ⟨x, hx⟩
      refine ⟨U, hUo.mem_nhds hxU, g, hg.contMDiffOn, ?_⟩
      intro y hy hyK
      exact hmatch ⟨y, hyK⟩ hy
    · refine ⟨Kᶜ, hK.isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, ?_⟩
      intro y hy hyK
      exact (hy hyK).elim
  obtain ⟨G, hG⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    𝓘(ℝ, X) (n := (1 : ℕ∞)) ht hlocal
  exact ⟨G, G.contMDiff.contDiff, fun p => hG p.val p.property⟩

/-- On a compact subset, a global C¹ extension can have compact support. -/
theorem exists_compactlySupported_contDiff_extension_of_local
    (K : Set X) (hK : IsCompact K) (f : K → E)
    (hloc : ∀ p : K, ∃ (U : Set X) (g : X → E),
      IsOpen U ∧ p.val ∈ U ∧ ContDiffOn ℝ 1 g U ∧
      ∀ y : K, y.val ∈ U → g y.val = f y) :
    ∃ G : X → E, ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      ∀ p : K, G p.val = f p := by
  obtain ⟨g, hg, hmatch⟩ := exists_contDiff_extension_of_local K hK.isClosed f hloc
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let χ : ContDiffBump (0 : X) :=
    { rIn := R, rOut := R + 1, rIn_pos := hR, rIn_lt_rOut := lt_add_one R }
  have hχ : ContDiff ℝ 1 (χ : X → ℝ) := χ.contDiff
  refine ⟨fun x => χ x • g x, hχ.smul hg, χ.hasCompactSupport.smul_right, ?_⟩
  intro p
  have hp : p.val ∈ Metric.closedBall (0 : X) χ.rIn := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound p.val p.property
  change χ p.val • g p.val = f p
  rw [χ.one_of_mem_closedBall hp, one_smul, hmatch p]

/-- The compact C¹ extension has a uniform bound for its actual ambient derivative. -/
theorem exists_compactlySupported_contDiff_extension_bounded_derivative
    (K : Set X) (hK : IsCompact K) (f : K → E)
    (hloc : ∀ p : K, ∃ (U : Set X) (g : X → E),
      IsOpen U ∧ p.val ∈ U ∧ ContDiffOn ℝ 1 g U ∧
      ∀ y : K, y.val ∈ U → g y.val = f y) :
    ∃ (G : X → E) (C : ℝ), ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      (∀ p : K, G p.val = f p) ∧ 0 ≤ C ∧ ∀ x : X, ‖fderiv ℝ G x‖ ≤ C := by
  obtain ⟨G, hG, hcG, hmatch⟩ :=
    exists_compactlySupported_contDiff_extension_of_local K hK f hloc
  obtain ⟨C, hC⟩ := (hcG.fderiv ℝ).exists_bound_of_continuous
    (hG.continuous_fderiv (by norm_num))
  exact ⟨G, C, hG, hcG, hmatch, (norm_nonneg _).trans (hC 0), hC⟩

end StationaryHarmonicMaps.Geometry

end
