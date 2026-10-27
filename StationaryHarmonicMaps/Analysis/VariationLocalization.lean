module

public import HarmonicMaps.Sobolev
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Finite localization of compact C¹ variations

A finite smooth partition on the compact projection of the field support
splits the original field into fields supported over interior balls. Their
sum is the original field as a function on the full product space.
-/

public section

open HarmonicMaps Set
open scoped ContDiff Manifold

namespace StationaryHarmonicMaps.Analysis

/-- Compact product variations split into finitely many actual interior-ball variations. -/
theorem exists_finite_ball_variation_localization {n q : ℕ} (Ω : OpenDomain n)
    (V : Domain n × Ambient q → Ambient q) (hV : ContDiff ℝ 1 V)
    (hcV : HasCompactSupport V)
    (hsV : tsupport V ⊆ Ω.val ×ˢ (Set.univ : Set (Ambient q))) :
    let K : Set (Domain n) := Prod.fst '' tsupport V
    ∃ (r : K → ℝ) (t : Finset K) (W : t → Domain n × Ambient q → Ambient q),
      (∀ p : K, 0 < r p ∧ Metric.closedBall p.val (r p) ⊆ Ω.val) ∧
      (∀ j : t, ContDiff ℝ 1 (W j) ∧ HasCompactSupport (W j) ∧
        Prod.fst '' tsupport (W j) ⊆ Metric.ball j.val.val (r j.val) ∧
        ∀ z, ∃ c : ℝ, W j z = c • V z) ∧
      (∑ j : t, W j) = V := by
  let K : Set (Domain n) := Prod.fst '' tsupport V
  have hK : IsCompact K := hcV.image continuous_fst
  have hKΩ : K ⊆ Ω.val := by
    rintro x ⟨z, hz, rfl⟩
    exact (hsV hz).1
  have hballs (p : K) : ∃ r : ℝ, 0 < r ∧ Metric.closedBall p.val r ⊆ Ω.val := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Ω.property p.val (hKΩ p.property)
    exact ⟨ε / 2, by positivity,
      (Metric.closedBall_subset_ball (by linarith only [hε])).trans hball⟩
  choose r hr hclosed using hballs
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun p : K => Metric.ball p.val (r p)) (fun _ => Metric.isOpen_ball)
    (fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ (Metric.mem_ball_self (hr ⟨x, hx⟩)))
  let U : t → Set (Domain n) := fun j => Metric.ball j.val.val (r j.val)
  have hcover : K ⊆ ⋃ j : t, U j := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion_of_mem ⟨j, hj⟩ hxj
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, Domain n) hK.isClosed U (fun _ => Metric.isOpen_ball) hcover
  let W (j : t) (z : Domain n × Ambient q) := ρ j z.1 • V z
  refine ⟨r, t, W, (fun p => ⟨hr p, hclosed p⟩), ?_, ?_⟩
  · intro j
    have hρC1 : ContDiff ℝ 1 (ρ j) := (ρ j).contMDiff.contDiff.of_le (by simp)
    have hW : ContDiff ℝ 1 (W j) := (hρC1.comp contDiff_fst).smul hV
    have hcW : HasCompactSupport (W j) :=
      HasCompactSupport.smul_left (f := fun z : Domain n × Ambient q => (ρ j z.1 : ℝ)) hcV
    have hts : tsupport (W j) ⊆ tsupport (ρ j) ×ˢ (Set.univ : Set (Ambient q)) := by
      apply closure_minimal _ ((isClosed_tsupport (ρ j)).prod isClosed_univ)
      intro z hz
      exact ⟨subset_tsupport _ (left_ne_zero_of_smul hz), mem_univ _⟩
    refine ⟨hW, hcW, ?_, fun z => ⟨ρ j z.1, rfl⟩⟩
    rintro x ⟨z, hz, rfl⟩
    exact hρ j (hts hz).1
  · funext z
    simp only [Finset.sum_apply, W]
    rw [← Finset.sum_smul]
    by_cases hz : z ∈ tsupport V
    · have H := ρ.sum_eq_one (show z.1 ∈ K from ⟨z, hz, rfl⟩)
      rw [finsum_eq_sum_of_fintype] at H
      rw [H, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hz, smul_zero]

end StationaryHarmonicMaps.Analysis

end
