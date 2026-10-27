module

public import StationaryHarmonicMaps.Analysis.CriticalMorreyScalar
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The actual scalar connection path in the complete critical class

The literal path tA preserves the original skew condition and L2 data.
Its complete encoded critical quantity has the true scalar-square bound,
is controlled by the same original bound on [0,1], and is genuinely
continuous in both the original L2 and complete critical quantities.
No gauge existence or gauge estimate is asserted by these coefficient data.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original L2 skew critical connection supplies its actual entire scalar path, with original data, unit-interval control and true L2/critical continuity. -/
theorem skew_connection_scalar_critical_homotopy {n q m : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient m)
    (D : Set (Domain n)) (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q))
    (hA : ∀ i,MemLp (fun x=>A x i) 2 (volume.restrict D))
    (hSkew : ∀ i,∀ᵐ x ∂volume.restrict D,star (A x i)= -A x i)
    (K : ℝ) (hK : 0≤K)
    (hCritical : criticalGradientMorreySquare (fun x i=>E (A x i)) D≤ENNReal.ofReal K) :
    (∀ t : ℝ,(∀ i,MemLp (fun x=>t • A x i) 2 (volume.restrict D)) ∧
      (∀ i,∀ᵐ x ∂volume.restrict D,star (t • A x i)= -(t • A x i)) ∧
      criticalGradientMorreySquare (fun x i=>E (t • A x i)) D≤ENNReal.ofReal (t^2*K)) ∧
    (∀ t∈Icc (0 : ℝ) 1,
      criticalGradientMorreySquare (fun x i=>E (t • A x i)) D≤ENNReal.ofReal K) ∧
    (∀ {I : Type*} (l : Filter I) (c : I → ℝ) (t : ℝ),Tendsto c l (𝓝 t) →
      ∀ i,Tendsto (fun k=>eLpNorm (fun x=>E (c k • A x i)-E (t • A x i)) 2
        (volume.restrict D)) l (𝓝 0)) ∧
    (∀ {I : Type*} (l : Filter I) (c : I → ℝ) (t : ℝ),Tendsto c l (𝓝 t) →
      Tendsto (fun k=>criticalGradientMorreySquare
        (fun x i=>E (c k • A x i)-E (t • A x i)) D) l (𝓝 0)) := by
  let F := fun x i=>E (A x i)
  have hFLp (i : Fin n) : MemLp (fun x=>F x i) 2 (volume.restrict D) :=
    E.lipschitz.comp_memLp (map_zero E) (hA i)
  have hBounds (t : ℝ) : criticalGradientMorreySquare (fun x i=>E (t • A x i)) D≤
      ENNReal.ofReal (t^2*K) := by
    simp_rw [map_smul]
    rw [criticalGradientMorreySquare_const_smul]
    exact (mul_le_mul_of_nonneg_left hCritical zero_le).trans_eq
      (ENNReal.ofReal_mul (sq_nonneg t)).symm
  refine ⟨fun t=>⟨fun i=>(hA i).const_smul t,?_,hBounds t⟩,?_,?_,?_⟩
  · intro i
    filter_upwards [hSkew i] with x hx
    change ContinuousLinearMap.adjoint (t • A x i)= -(t • A x i)
    rw [map_smul]
    change t • star (A x i)= -(t • A x i)
    rw [hx,smul_neg]
  · intro t ht
    apply (hBounds t).trans
    apply ENNReal.ofReal_le_ofReal
    have hSquare : t^2≤1 := by nlinarith only [ht.1,ht.2]
    exact (mul_le_mul_of_nonneg_right hSquare hK).trans_eq (one_mul K)
  · intro I l c t hc i
    simpa only [map_smul] using tendsto_L2_scalar_path (volume.restrict D)
      (fun x=>F x i) (hFLp i) l c t hc
  · intro I l c t hc
    have hFinite : criticalGradientMorreySquare F D≠∞ :=
      (hCritical.trans_lt ENNReal.ofReal_lt_top).ne
    simpa only [map_smul] using tendsto_criticalMorreySquare_scalar_path F D hFinite l c t hc

end StationaryHarmonicMaps.Analysis

end
