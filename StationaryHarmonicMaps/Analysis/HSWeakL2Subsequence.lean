module

public import StationaryHarmonicMaps.Analysis.WeakL2Subsequence
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtDecoding

/-!
# Actual weak L2 subsequences of complete HS fields

The literal n*q-entry Euclidean encoding carries the complete HS energy.
A single weak vector subsequence decodes to the same actual column limits.
Encoded single-column tests recover weak convergence against every genuine
L2 column test, with no independently chosen column subsequences.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- A uniformly HS-energy-bounded field sequence has one weak subsequence for all original columns. -/
theorem exists_weak_HS_L2_subsequence {n q : ℕ} (μ : Measure (Domain n)) [IsSeparable μ]
    (F : ℕ → Domain n → Gradient n q)
    (hF : ∀ k i, MemLp (fun x => F k x i) 2 μ)
    {M : ℝ} (hM : 0 ≤ M) (henergy : ∀ k, (∫ x, hsNormSq (F k x) ∂μ) ≤ M) :
    ∃ G : Domain n → Gradient n q,
      (∀ i, MemLp (fun x => G x i) 2 μ) ∧
      (∫ x, hsNormSq (G x) ∂μ) ≤ M ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∀ (i : Fin n) (g : Domain n → Ambient q), MemLp g 2 μ →
          Tendsto (fun k => ∫ x, inner ℝ (F (σ k) x i) (g x) ∂μ) atTop
            (𝓝 (∫ x, inner ℝ (G x i) (g x) ∂μ)) := by
  let E := fun k x => WithLp.toLp 2 (fun j : Fin (n * q) =>
    F k x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
  have hE (k : ℕ) : MemLp (E k) 2 μ := memLp_hs_flatten (F k) (hF k)
  have hEenergy (k : ℕ) : (∫ x, ‖E k x‖ ^ 2 ∂μ) ≤ M := by
    simpa only [E, hs_flatten_norm_sq] using henergy k
  obtain ⟨v, hv, hEv, σ, hσ, hweak⟩ := exists_weak_L2_subsequence μ E hE hM hEenergy
  let G := fun x i => WithLp.toLp 2 (fun j : Fin q => v x (finProdFinEquiv (i, j)))
  have hG (i : Fin n) : MemLp (fun x => G x i) 2 μ := memLp_hs_unflatten v hv i
  have hGenergy : (∫ x, hsNormSq (G x) ∂μ) ≤ M := by
    simpa only [G, hs_unflatten_hsNormSq] using hEv
  refine ⟨G, hG, hGenergy, σ, hσ, ?_⟩
  intro i g hg
  let B := fun x j => if j = i then g x else 0
  let T := fun x => WithLp.toLp 2 (fun j : Fin (n * q) =>
    B x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
  have hB (j : Fin n) : MemLp (fun x => B x j) 2 μ := by
    by_cases hji : j = i
    · simpa only [B, if_pos hji] using hg
    · simp only [B, if_neg hji]
      exact MemLp.zero
  have hT : MemLp T 2 μ := memLp_hs_flatten B hB
  have hpairF (k : ℕ) (x : Domain n) : inner ℝ (E k x) (T x) = inner ℝ (F k x i) (g x) := by
    rw [show E k x = WithLp.toLp 2 (fun j : Fin (n*q) =>
      F k x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2) from rfl,
      show T x = WithLp.toLp 2 (fun j : Fin (n*q) =>
        B x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2) from rfl,
      hs_flatten_inner]
    simp only [B, apply_ite, inner_zero_right, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hpairG (x : Domain n) : inner ℝ (v x) (T x) = inner ℝ (G x i) (g x) := by
    have H := hs_flatten_inner (G x) (B x)
    have hvx : WithLp.toLp 2 (fun j : Fin (n*q) =>
        G x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2) = v x :=
      hs_flatten_unflatten (v x)
    rw [hvx] at H
    simpa only [B, apply_ite, inner_zero_right, Finset.sum_ite_eq', Finset.mem_univ, if_true] using H
  have H := hweak T hT
  simpa only [hpairF, hpairG] using H

end StationaryHarmonicMaps.Analysis

end
