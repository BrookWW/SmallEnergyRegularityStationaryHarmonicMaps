module

public import StationaryHarmonicMaps.Analysis.WeakMatrixConnectionLimit
public import StationaryHarmonicMaps.Analysis.NaturalCoulombTests

/-!
# Weak closure of actual natural Coulomb tests

Actual weak L2 column convergence preserves pairings with every native
W1,2 gradient on the original open domain. Applying the genuine nonlinear
matrix-connection limit retains these natural tests for the same decoded
limit connection. No boundary trace or zero-boundary test restriction is
introduced.
-/

public section

open HarmonicMaps MeasureTheory Filter
open scoped Topology

namespace StationaryHarmonicMaps.Analysis

/-- All native gradient tests survive actual weak L2 column convergence on an arbitrary open domain. -/
theorem native_gradient_tests_of_weak_L2_limit {n q : ℕ} (Ω : OpenDomain n)
    (F : ℕ → Domain n → Gradient n q) (f : Domain n → Gradient n q)
    (hF : ∀ k i, MemLp (fun x => F k x i) 2 (volume.restrict Ω.val))
    (hf : ∀ i, MemLp (fun x => f x i) 2 (volume.restrict Ω.val))
    (hweak : ∀ (i : Fin n) (b : Domain n → Ambient q),
      MemLp b 2 (volume.restrict Ω.val) →
      Tendsto (fun k => ∫ x in Ω.val, inner ℝ (F k x i) (b x)) atTop
        (𝓝 (∫ x in Ω.val, inner ℝ (f x i) (b x))))
    (hzero : ∀ k (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q),
      MemW12 Ω ψ Dψ →
      (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (F k x i) (Dψ x i)) = 0)
    (ψ : Domain n → Ambient q) (Dψ : Domain n → Gradient n q)
    (hψ : MemW12 Ω ψ Dψ) :
    IntegrableOn (fun x => ∑ i : Fin n, inner ℝ (f x i) (Dψ x i)) Ω.val volume ∧
    (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (f x i) (Dψ x i)) = 0 := by
  have hI (i : Fin n) := HolderToCK.integrable_inner_of_memLp_two (hf i) (hψ.2.2 i)
  have hIk (k : ℕ) (i : Fin n) := HolderToCK.integrable_inner_of_memLp_two (hF k i) (hψ.2.2 i)
  have hLim := tendsto_finsetSum Finset.univ (fun i _ => hweak i (fun x => Dψ x i) (hψ.2.2 i))
  have hSum (k : ℕ) : (∑ i : Fin n, ∫ x in Ω.val, inner ℝ (F k x i) (Dψ x i)) = 0 := by
    rw [← integral_finsetSum _ (fun i _ => hIk k i)]
    exact hzero k ψ Dψ hψ
  have hSumf : (∫ x in Ω.val, ∑ i : Fin n, inner ℝ (f x i) (Dψ x i)) =
      ∑ i : Fin n, ∫ x in Ω.val, inner ℝ (f x i) (Dψ x i) :=
    integral_finsetSum _ (fun i _ => hI i)
  have hZeroLim : Tendsto (fun k => ∑ i : Fin n, ∫ x in Ω.val, inner ℝ (F k x i) (Dψ x i))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [hSum] using (tendsto_const_nhds (x := (0 : ℝ)))
  refine ⟨integrable_finsetSum _ (fun i _ => hI i),?_⟩
  exact hSumf.trans (tendsto_nhds_unique hLim hZeroLim)

/-- The same true nonlinear matrix-connection limit preserves every native natural test. -/
theorem native_tests_encoded_connection_of_weak_L2_limits {n m q : ℕ} (Ω : OpenDomain n)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient m)
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀ T, R (E T) = T)
    (P : ℕ → Domain n → Ambient m) (Q : Domain n → Ambient m)
    (hP : ∀ k, MemLp (P k) 2 (volume.restrict Ω.val))
    (hQ : MemLp Q 2 (volume.restrict Ω.val))
    (hconv : Tendsto (fun k => eLpNorm (P k - Q) 2 (volume.restrict Ω.val)) atTop (𝓝 0))
    {B : ℝ} (hbound : ∀ k, ∀ᵐ x ∂volume.restrict Ω.val, ‖P k x‖ ≤ B)
    (D A : ℕ → Domain n → Gradient n m) (d a : Domain n → Gradient n m)
    (hD : ∀ k i, MemLp (fun x => D k x i) 2 (volume.restrict Ω.val))
    (hd : ∀ i, MemLp (fun x => d x i) 2 (volume.restrict Ω.val))
    (hA : ∀ k i, MemLp (fun x => A k x i) 2 (volume.restrict Ω.val))
    (ha : ∀ i, MemLp (fun x => a x i) 2 (volume.restrict Ω.val))
    (hweakD : ∀ (i : Fin n) (b : Domain n → Ambient m),
      MemLp b 2 (volume.restrict Ω.val) →
      Tendsto (fun k => ∫ x in Ω.val, inner ℝ (D k x i) (b x)) atTop
        (𝓝 (∫ x in Ω.val, inner ℝ (d x i) (b x))))
    (hweakA : ∀ (i : Fin n) (b : Domain n → Ambient m),
      MemLp b 2 (volume.restrict Ω.val) →
      Tendsto (fun k => ∫ x in Ω.val, inner ℝ (A k x i) (b x)) atTop
        (𝓝 (∫ x in Ω.val, inner ℝ (a x i) (b x))))
    {MD MA : ℝ} (henergyD : ∀ k i, (∫ x in Ω.val, ‖D k x i‖ ^ 2) ≤ MD)
    (henergyA : ∀ k i, (∫ x in Ω.val, ‖A k x i‖ ^ 2) ≤ MA)
    (hzero : ∀ k (ψ : Domain n → Ambient m) (Dψ : Domain n → Gradient n m),
      MemW12 Ω ψ Dψ →
      (∫ x in Ω.val, ∑ i : Fin n, inner ℝ
        (E (star (R (P k x)) * R (D k x i) +
          star (R (P k x)) * R (A k x i) * R (P k x))) (Dψ x i)) = 0) :
    (∀ i, MemLp (fun x => E (star (R (Q x)) * R (d x i) +
      star (R (Q x)) * R (a x i) * R (Q x))) 2 (volume.restrict Ω.val)) ∧
    ∀ (ψ : Domain n → Ambient m) (Dψ : Domain n → Gradient n m),
      MemW12 Ω ψ Dψ →
      IntegrableOn (fun x => ∑ i : Fin n, inner ℝ
        (E (star (R (Q x)) * R (d x i) +
          star (R (Q x)) * R (a x i) * R (Q x))) (Dψ x i)) Ω.val volume ∧
      (∫ x in Ω.val, ∑ i : Fin n, inner ℝ
        (E (star (R (Q x)) * R (d x i) +
          star (R (Q x)) * R (a x i) * R (Q x))) (Dψ x i)) = 0 := by
  have H (i : Fin n) := weak_L2_limit_matrix_connection_encoding (volume.restrict Ω.val)
    E R hRE P Q hP hQ hconv hbound (fun k x => D k x i) (fun k x => A k x i)
    (fun x => d x i) (fun x => a x i) (fun k => hD k i) (hd i) (fun k => hA k i) (ha i)
    (hweakD i) (hweakA i) (fun k => henergyD k i) (fun k => henergyA k i)
  refine ⟨fun i => (H i).1,?_⟩
  exact native_gradient_tests_of_weak_L2_limit Ω
    (fun k x i => E (star (R (P k x)) * R (D k x i) +
      star (R (P k x)) * R (A k x i) * R (P k x)))
    (fun x i => E (star (R (Q x)) * R (d x i) +
      star (R (Q x)) * R (a x i) * R (Q x)))
    (fun k i => (H i).2.1 k) (fun i => (H i).1) (fun i => (H i).2.2) hzero

end StationaryHarmonicMaps.Analysis

end
