module

public import StationaryHarmonicMaps.Analysis.HilbertSchmidtDecoding

/-!
# Actual full-entry Hilbert--Schmidt decoding at every Lp exponent

The same original coefficient vector is decoded by its literal finite
coordinate rearrangement. Each column is a continuous linear image of
that vector, so actual Lp membership transports at every extended
exponent. The existing exact HS square identity retains all entries.
-/

public section

open HarmonicMaps MeasureTheory
open scoped ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original full-entry Euclidean Lp field supplies genuine Lp membership for each literal decoded column, including zero and infinite exponents. -/
theorem memLp_hs_unflatten_exponent {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {n q : ℕ} (P : X → Ambient (n*q)) (p : ℝ≥0∞) (hP : MemLp P p μ) (i : Fin n) :
    MemLp (fun x=>WithLp.toLp 2 (fun j : Fin q=>P x (finProdFinEquiv (i,j)))) p μ := by
  let L : Ambient (n*q) →ₗ[ℝ] Ambient q :=
    { toFun := fun v=>WithLp.toLp 2 (fun j : Fin q=>v (finProdFinEquiv (i,j)))
      map_add' := fun v w=>by ext j;rfl
      map_smul' := fun c v=>by ext j;rfl }
  exact L.toContinuousLinearMap.lipschitz.comp_memLp (map_zero L) hP

end StationaryHarmonicMaps.Analysis

end
