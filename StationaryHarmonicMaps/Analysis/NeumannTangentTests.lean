module

public import StationaryHarmonicMaps.Analysis.NeumannTangentTransport
public import StationaryHarmonicMaps.Analysis.ScaledBallCutoff
public import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# Actual compact tangential tests for the Neumann reflection

The actual radial orthogonal projection is invariant under nonzero scaling
and has symmetric finite coordinates. An origin cutoff turns every original
compact smooth test's tangential derivatives into genuine compact smooth
fields, while preserving them throughout the exterior annulus.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ContDiff Topology

namespace StationaryHarmonicMaps.Analysis

/-- The actual tangential projection is invariant under every nonzero radial scalar. -/
theorem neumann_tangent_projection_smul {n : ℕ}
    (t : ℝ) (ht : t≠0) (x v : Domain n) :
    (ℝ ∙ t • x)ᗮ.starProjection v=(ℝ ∙ x)ᗮ.starProjection v := by
  have hSpan : ℝ ∙ t • x=ℝ ∙ x :=
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ht) x
  exact congrArg (fun K : Submodule ℝ (Domain n)=>Kᗮ.starProjection v) hSpan

/-- The full finite tangential pairing is the original pairing against the actual projected test columns. -/
theorem neumann_tangent_columns_pairing {n q : ℕ}
    (x : Domain n) (V : Gradient n q) (B : Domain n →L[ℝ] Ambient q) :
    (∑i : Fin n,inner ℝ
      (∑j : Fin n,((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j • V j)
      (B (EuclideanSpace.single i 1)))=
      ∑j : Fin n,inner ℝ (V j) (B ((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single j 1))) := by
  have hSymm (i j : Fin n) :
      ((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single i 1)) j=
        ((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single j 1)) i := by
    simpa only [EuclideanSpace.inner_single_right,EuclideanSpace.inner_single_left,
      conj_trivial,one_mul] using
      Submodule.inner_starProjection_left_eq_right ((ℝ ∙ x)ᗮ)
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))
  have hB (v : Domain n) : B v=∑i : Fin n,v i • B (EuclideanSpace.single i 1) := by
    nth_rw 1 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
    simp only [map_sum,map_smul,EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply]
  simp only [sum_inner,real_inner_smul_left]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [hB ((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single j 1))]
  simp only [inner_sum,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [hSymm]

/-- Original compact smooth tests produce genuine compact smooth tangential fields with the same support bound and the literal original values throughout the exterior annulus. -/
theorem exists_compact_neumann_tangent_tests {n q : ℕ}
    (ψ : Domain n → Ambient q) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ⊆ball (0 : Domain n) 2) :
    ∃ v : Fin n → Domain n → Ambient q,
      (∀j,ContDiff ℝ ∞ (v j)) ∧ (∀j,HasCompactSupport (v j)) ∧
      (∀j,tsupport (v j)⊆ball (0 : Domain n) 2) ∧
      ∀ (j : Fin n) (x : Domain n),1≤‖x‖ →
        v j x=fderiv ℝ ψ x ((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single j 1)) := by
  obtain ⟨_C,_hC,Hcut⟩ := exists_scaled_ball_cutoff n
  obtain ⟨χ,hχ,_hcχ,hsχ,hOne,_hBounds,_hD⟩ := Hcut (0 : Domain n) (1/4) (by norm_num)
  let v := fun (j : Fin n) (x : Domain n)=>(1-χ x) •
    fderiv ℝ ψ x ((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single j 1))
  have hProj (j : Fin n) (x : Domain n) (hx : x≠0) :
      ContDiffAt ℝ ∞ (fun y : Domain n=>(ℝ ∙ y)ᗮ.starProjection (EuclideanSpace.single j 1)) x := by
    have H : ContDiffAt ℝ ∞ (fun y : Domain n=>EuclideanSpace.single j (1 : ℝ)-
        (inner ℝ y (EuclideanSpace.single j 1)/‖y‖^2) • y) x :=
      contDiffAt_const.sub (((contDiffAt_id.inner ℝ contDiffAt_const).div
        (contDiff_norm_sq ℝ).contDiffAt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).smul contDiffAt_id)
    exact H.congr_of_eventuallyEq (Eventually.of_forall fun y=>neumann_tangent_projection_apply y _)
  have hv (j : Fin n) : ContDiff ℝ ∞ (v j) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x=0
    · subst x
      have hLocal : v j=ᶠ[𝓝 (0 : Domain n)] (fun _=>0) := by
        filter_upwards [ball_mem_nhds (0 : Domain n) (by norm_num : (0 : ℝ)<1/4)] with y hy
        have hχy := hOne y (ball_subset_closedBall hy)
        simp only [v,hχy,sub_self,zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hLocal
    · exact (contDiffAt_const.sub hχ.contDiffAt).smul
        ((hψ.fderiv_right (m := ∞) (by simp)).contDiffAt.clm_apply (hProj j x hx))
  have hSupp (j : Fin n) : tsupport (v j)⊆tsupport ψ := by
    apply closure_minimal _ (isClosed_tsupport ψ)
    intro x hx
    by_contra hnot
    apply hx
    change (1-χ x) • fderiv ℝ ψ x ((ℝ ∙ x)ᗮ.starProjection (EuclideanSpace.single j 1))=0
    rw [fderiv_of_notMem_tsupport ℝ hnot,zero_apply,smul_zero]
  refine ⟨v,hv,fun j=>hcψ.isCompact.of_isClosed_subset (isClosed_tsupport _) (hSupp j),
    fun j=>(hSupp j).trans hsψ,?_⟩
  intro j x hx
  have hχx : χ x=0 := by
    by_contra hne
    have H := hsχ (subset_tsupport χ hne)
    change dist x 0<2*(1/4 : ℝ) at H
    rw [dist_zero_right] at H
    linarith only [hx,H]
  simp only [v,hχx,sub_zero,one_smul]

end StationaryHarmonicMaps.Analysis

end
