module

public import StationaryHarmonicMaps.Analysis.C1SobolevPostcomposition
public import StationaryHarmonicMaps.Analysis.SobolevLinearOperations
import HarmonicMaps.SobolevRestriction
import HarmonicMaps.Analysis.SobolevAECongruence
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Literal products of two bounded native Sobolev maps

An actual Euclidean encoding combines the two original weak graphs. A
compact C1 cutoff of the bilinear map agrees near their essential range.
The actual C1 chain rule therefore gives the original bilinear value and
its literal two-term Leibniz columns on the whole source ball.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- Two bounded native ball graphs have their genuine continuous bilinear
product graph, without a zero-boundary or smooth-test premise. -/
theorem memW12_bounded_bilinear_product_ball {n m k q : ℕ}
    (a : Domain n) (r : ℝ) (hr : 0 < r)
    (u : Domain n → Ambient m) (Du : Domain n → Gradient n m)
    (hu : MemW12 (ballDomain a r) u Du) (Mu : ℝ)
    (huBound : ∀ᵐ x ∂volume.restrict (ball a r), ‖u x‖ ≤ Mu)
    (v : Domain n → Ambient k) (Dv : Domain n → Gradient n k)
    (hv : MemW12 (ballDomain a r) v Dv) (Mv : ℝ)
    (hvBound : ∀ᵐ x ∂volume.restrict (ball a r), ‖v x‖ ≤ Mv)
    (B : Ambient m →L[ℝ] (Ambient k →L[ℝ] Ambient q)) :
    MemW12 (ballDomain a r) (fun x => B (u x) (v x))
      (fun x i => B (Du x i) (v x) + B (u x) (Dv x i)) := by
  let E : (Ambient m × Ambient k) ≃L[ℝ] Ambient (m+k) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let I : Ambient m →L[ℝ] Ambient (m+k) :=
    E.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Ambient m) (Ambient k))
  let J : Ambient k →L[ℝ] Ambient (m+k) :=
    E.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Ambient m) (Ambient k))
  let L : Ambient (m+k) →L[ℝ] Ambient m :=
    (ContinuousLinearMap.fst ℝ (Ambient m) (Ambient k)).comp E.symm.toContinuousLinearMap
  let R : Ambient (m+k) →L[ℝ] Ambient k :=
    (ContinuousLinearMap.snd ℝ (Ambient m) (Ambient k)).comp E.symm.toContinuousLinearMap
  have hPair (z : Ambient m) (w : Ambient k) : I z + J w = E (z,w) := by
    change E (z,0) + E (0,w) = E (z,w)
    rw [← map_add]
    simp only [Prod.mk_add_mk,add_zero,zero_add]
  have hLeft : MemW12 (ballDomain a r) (fun x => I (u x)) (fun x i => I (Du x i)) :=
    ⟨(memW12Loc_continuousLinearMap hu.to_memW12Loc I).1,
      I.lipschitz.comp_memLp (map_zero I) hu.2.1,
      fun i => I.lipschitz.comp_memLp (map_zero I) (hu.2.2 i)⟩
  have hRight : MemW12 (ballDomain a r) (fun x => J (v x)) (fun x i => J (Dv x i)) :=
    ⟨(memW12Loc_continuousLinearMap hv.to_memW12Loc J).1,
      J.lipschitz.comp_memLp (map_zero J) hv.2.1,
      fun i => J.lipschitz.comp_memLp (map_zero J) (hv.2.2 i)⟩
  let P := fun x => I (u x) + J (v x)
  let DP := fun x i => I (Du x i) + J (Dv x i)
  have hP : MemW12 (ballDomain a r) P DP :=
    ⟨hasWeakGradient_add hLeft.1 hRight.1, hLeft.2.1.add hRight.2.1,
      fun i => (hLeft.2.2 i).add (hRight.2.2 i)⟩
  let M := ‖E.toContinuousLinearMap‖ * (|Mu|+|Mv|)
  have hPBound : ∀ᵐ x ∂volume.restrict (ball a r), ‖P x‖ ≤ M := by
    filter_upwards [huBound,hvBound] with x hx hy
    have hNorm : ‖(u x,v x)‖ ≤ |Mu|+|Mv| := by
      rw [Prod.norm_def]
      exact max_le ((hx.trans (le_abs_self Mu)).trans (le_add_of_nonneg_right (abs_nonneg Mv)))
        ((hy.trans (le_abs_self Mv)).trans (le_add_of_nonneg_left (abs_nonneg Mu)))
    change ‖I (u x)+J (v x)‖ ≤ M
    rw [hPair]
    exact (E.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hNorm (norm_nonneg _))
  let χ : ContDiffBump (0 : Ambient (m+k)) :=
    ⟨M+1,M+2,by dsimp only [M];positivity,by linarith⟩
  let C := fun z : Ambient (m+k) => B (L z) (R z)
  let F := fun z : Ambient (m+k) => χ z • C z
  have hC : ContDiff ℝ 1 C := (B.contDiff.comp L.contDiff).clm_apply R.contDiff
  have hF : ContDiff ℝ 1 F := χ.contDiff.smul hC
  have hcF : HasCompactSupport F := χ.hasCompactSupport.smul_right
  obtain ⟨K,hK⟩ := (hcF.fderiv ℝ).exists_bound_of_continuous (hF.continuous_fderiv (by simp))
  have hComp := memW12_postcompose_c1 hr hP F hF K hK
  have hDerivative (z d : Ambient (m+k)) :
      fderiv ℝ C z d = B (L d) (R z) + B (L z) (R d) := by
    have H := ((B.comp L).hasFDerivAt (x := z)).clm_apply (R.hasFDerivAt (x := z))
    rw [show fderiv ℝ C z = _ from H.fderiv]
    change B (L z) (R d) + B (L d) (R z) = _
    exact add_comm _ _
  have hProjection (z : Ambient m) (w : Ambient k) :
      L (I z+J w)=z ∧ R (I z+J w)=w := by
    rw [hPair]
    change (E.symm (E (z,w))).1=z ∧ (E.symm (E (z,w))).2=w
    rw [E.symm_apply_apply]
    exact ⟨rfl,rfl⟩
  apply hComp.congr_ae ?_ ?_
  · filter_upwards [hPBound] with x hx
    have hBall : P x ∈ closedBall (0 : Ambient (m+k)) χ.rIn := by
      change dist (P x) 0 ≤ M+1
      rw [dist_zero_right]
      exact hx.trans (le_add_of_nonneg_right zero_le_one)
    change χ (P x) • C (P x) = _
    rw [χ.one_of_mem_closedBall hBall,one_smul]
    exact congrArg₂ (fun z w => B z w) (hProjection (u x) (v x)).1 (hProjection (u x) (v x)).2
  · filter_upwards [hPBound] with x hx
    have hBall : P x ∈ ball (0 : Ambient (m+k)) χ.rIn := by
      change dist (P x) 0 < M+1
      rw [dist_zero_right]
      exact hx.trans_lt (lt_add_one M)
    have hEq : F =ᶠ[𝓝 (P x)] C :=
      (χ.eventuallyEq_one_of_mem_ball hBall).mono (fun z hz => by
        change χ z = (1 : ℝ) at hz
        change χ z • C z = C z
        rw [hz,one_smul])
    funext i
    rw [hEq.fderiv_eq,hDerivative]
    change B (L (I (Du x i)+J (Dv x i))) (R (I (u x)+J (v x))) +
      B (L (I (u x)+J (v x))) (R (I (Du x i)+J (Dv x i))) = _
    rw [(hProjection (Du x i) (Dv x i)).1,(hProjection (u x) (v x)).2,
      (hProjection (u x) (v x)).1,(hProjection (Du x i) (Dv x i)).2]

end StationaryHarmonicMaps.Analysis

end
