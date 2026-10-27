module

public import HarmonicMaps.Sobolev
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Finite interior-ball localization of actual smooth compact vector tests -/

public section

open HarmonicMaps Set
open scoped ContDiff Manifold

namespace StationaryHarmonicMaps.Analysis

/-- A compact smooth vector test splits into finitely many compact smooth interior-ball tests. -/
theorem exists_finite_ball_smooth_test_localization {n q : ℕ} (Ω : OpenDomain n)
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ Ω.val) :
    ∃ (r : tsupport ψ → ℝ) (t : Finset (tsupport ψ)) (φ : t → Domain n → Ambient q),
      (∀ p : tsupport ψ, 0 < r p ∧ Metric.closedBall p.val (r p) ⊆ Ω.val) ∧
      (∀ j : t, ContDiff ℝ ∞ (φ j) ∧ HasCompactSupport (φ j) ∧
        tsupport (φ j) ⊆ Metric.ball j.val.val (r j.val)) ∧
      (∑ j : t, φ j) = ψ := by
  have hballs (p : tsupport ψ) : ∃ r : ℝ, 0 < r ∧ Metric.closedBall p.val r ⊆ Ω.val := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Ω.property p.val (hsψ p.property)
    exact ⟨ε / 2, by positivity,
      (Metric.closedBall_subset_ball (by linarith only [hε])).trans hball⟩
  choose r hr hclosed using hballs
  obtain ⟨t, ht⟩ := hcψ.elim_finite_subcover
    (fun p : tsupport ψ => Metric.ball p.val (r p)) (fun _ => Metric.isOpen_ball)
    (fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ (Metric.mem_ball_self (hr ⟨x, hx⟩)))
  let U : t → Set (Domain n) := fun j => Metric.ball j.val.val (r j.val)
  have hcover : tsupport ψ ⊆ ⋃ j : t, U j := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion_of_mem ⟨j, hj⟩ hxj
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, Domain n) (isClosed_tsupport ψ) U (fun _ => Metric.isOpen_ball) hcover
  let φ (j : t) (x : Domain n) := ρ j x • ψ x
  refine ⟨r, t, φ, (fun p => ⟨hr p, hclosed p⟩), ?_, ?_⟩
  · intro j
    have hφ : ContDiff ℝ ∞ (φ j) := (ρ j).contMDiff.contDiff.smul hψ
    have hcφ : HasCompactSupport (φ j) :=
      HasCompactSupport.smul_left (f := fun x : Domain n => (ρ j x : ℝ)) hcψ
    exact ⟨hφ, hcφ, (tsupport_smul_subset_left (ρ j) ψ).trans (hρ j)⟩
  · funext x
    simp only [Finset.sum_apply, φ]
    rw [← Finset.sum_smul]
    by_cases hx : x ∈ tsupport ψ
    · have H := ρ.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at H
      rw [H, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]

end StationaryHarmonicMaps.Analysis

end
