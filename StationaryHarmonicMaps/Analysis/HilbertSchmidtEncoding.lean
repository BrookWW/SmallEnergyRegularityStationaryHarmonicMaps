module

public import HarmonicMaps.Energy
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Literal Hilbert--Schmidt encoding of one-form coefficients

Flattening every domain and target index gives an actual Euclidean vector
of dimension n*q. Its norm and inner product are the column square sum and
the column inner-product sum. L² membership follows from the actual finite
family of L² columns.
-/

public section

open HarmonicMaps MeasureTheory

namespace StationaryHarmonicMaps.Analysis

/-- All n*q real coefficients contribute to the Euclidean squared norm. -/
theorem hs_flatten_norm_sq {n q : ℕ} (A : Gradient n q) :
    ‖WithLp.toLp 2 (fun k : Fin (n * q) =>
      A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)‖ ^ 2 = hsNormSq A := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ k : Fin (n * q),
    (A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) ^ 2) = _
  rw [← Equiv.sum_comp finProdFinEquiv (fun k : Fin (n * q) =>
    (A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) ^ 2)]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun i _ => (EuclideanSpace.real_norm_sq_eq (A i)).symm)

/-- The encoded inner product is the actual sum of column inner products. -/
theorem hs_flatten_inner {n q : ℕ} (A B : Gradient n q) :
    inner ℝ (WithLp.toLp 2 (fun k : Fin (n * q) =>
      A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))
      (WithLp.toLp 2 (fun k : Fin (n * q) =>
        B (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) =
      ∑ i : Fin n, inner ℝ (A i) (B i) := by
  simp only [PiLp.inner_apply]
  change (∑ k : Fin (n * q), inner ℝ
    (A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    (B (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) = _
  rw [← Equiv.sum_comp finProdFinEquiv (fun k : Fin (n * q) => inner ℝ
    (A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    (B (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]

/-- L² columns give L² membership of the literal Hilbert--Schmidt encoding. -/
theorem memLp_hs_flatten {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {n q : ℕ} (F : X → Gradient n q)
    (hF : ∀ i : Fin n, MemLp (fun x => F x i) 2 μ) :
    MemLp (fun x => WithLp.toLp 2 (fun k : Fin (n * q) =>
      F x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) 2 μ := by
  let L : Gradient n q →ₗ[ℝ] Ambient (n * q) :=
    { toFun := fun A => WithLp.toLp 2 (fun k : Fin (n * q) =>
        A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      map_add' := fun A B => by ext k; rfl
      map_smul' := fun c A => by ext k; rfl }
  exact L.toContinuousLinearMap.lipschitz.comp_memLp (map_zero L) (MemLp.of_eval hF)

end StationaryHarmonicMaps.Analysis

end
