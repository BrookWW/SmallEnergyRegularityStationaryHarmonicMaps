module

public import StationaryHarmonicMaps.Analysis.HilbertSchmidtEncoding

/-!
# Literal decoding of Euclidean one-form coefficients

The inverse coefficient rearrangement recovers actual columns from the
Euclidean Hilbert--Schmidt vector. It preserves the square density and
transports L² membership to every column. It asserts no weak-gradient property.
-/

public section

open HarmonicMaps MeasureTheory Filter
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Decoding the actual encoding recovers every original column. -/
theorem hs_unflatten_flatten {n q : ℕ} (A : Gradient n q) :
    (fun i : Fin n => WithLp.toLp 2 (fun j : Fin q =>
      (WithLp.toLp 2 (fun k : Fin (n * q) =>
        A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))
          (finProdFinEquiv (i, j)))) = A := by
  funext i
  ext j
  change A (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = A i j
  rw [Equiv.symm_apply_apply]

/-- Encoding the actual decoded columns recovers the Euclidean coefficient vector. -/
theorem hs_flatten_unflatten {n q : ℕ} (v : Ambient (n * q)) :
    WithLp.toLp 2 (fun k : Fin (n * q) =>
      (WithLp.toLp 2 (fun j : Fin q =>
        v (finProdFinEquiv ((finProdFinEquiv.symm k).1, j))))
          (finProdFinEquiv.symm k).2) = v := by
  ext k
  change v (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) = v k
  rw [Prod.mk.eta, Equiv.apply_symm_apply]

/-- The decoded column square density equals the actual Euclidean norm squared. -/
theorem hs_unflatten_hsNormSq {n q : ℕ} (v : Ambient (n * q)) :
    hsNormSq (fun i : Fin n => WithLp.toLp 2 (fun j : Fin q =>
      v (finProdFinEquiv (i, j)))) = ‖v‖ ^ 2 := by
  have H := hs_flatten_norm_sq (fun i : Fin n => WithLp.toLp 2
    (fun j : Fin q => v (finProdFinEquiv (i, j))))
  rw [hs_flatten_unflatten] at H
  exact H.symm

/-- Actual Euclidean L² coefficients decode to genuine L² columns. -/
theorem memLp_hs_unflatten {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {n q : ℕ} (P : X → Ambient (n * q)) (hP : MemLp P 2 μ) (i : Fin n) :
    MemLp (fun x => WithLp.toLp 2 (fun j : Fin q => P x (finProdFinEquiv (i, j)))) 2 μ := by
  let L : Ambient (n * q) →ₗ[ℝ] Ambient q :=
    { toFun := fun v => WithLp.toLp 2 (fun j : Fin q => v (finProdFinEquiv (i, j)))
      map_add' := fun v w => by ext j; rfl
      map_smul' := fun c v => by ext j; rfl }
  exact L.toContinuousLinearMap.lipschitz.comp_memLp (map_zero L) hP

/-- Strong encoded L² convergence gives strong L² convergence of every actual decoded column. -/
theorem hs_unflatten_column_l2_limit {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {n q : ℕ} {f : ℕ → X → Ambient (n * q)} {P : X → Ambient (n * q)}
    (hconv : Tendsto (fun j => eLpNorm (f j - P) 2 μ) atTop (𝓝 0)) (i : Fin n) :
    Tendsto (fun j => eLpNorm (fun x =>
      WithLp.toLp 2 (fun k : Fin q => f j x (finProdFinEquiv (i, k))) -
        WithLp.toLp 2 (fun k : Fin q => P x (finProdFinEquiv (i, k)))) 2 μ)
      atTop (𝓝 0) := by
  let L : Ambient (n * q) →ₗ[ℝ] Ambient q :=
    { toFun := fun v => WithLp.toLp 2 (fun j : Fin q => v (finProdFinEquiv (i, j)))
      map_add' := fun v w => by ext j; rfl
      map_smul' := fun c v => by ext j; rfl }
  let C := L.toContinuousLinearMap
  have H := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ‖C‖) hconv
    (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using H) (fun _ => zero_le)
  intro j
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (p := 2)
  filter_upwards [] with x
  change ‖C (f j x) - C (P x)‖ ≤ ‖C‖ * ‖f j x - P x‖
  rw [← map_sub]
  exact C.le_opNorm _

end StationaryHarmonicMaps.Analysis

end
