module

public import StationaryHarmonicMaps.Analysis.NaturalCoefficientNeumannBanach
public import StationaryHarmonicMaps.Analysis.SobolevLinearOperations

/-!
# Fixed linear constraints of the actual Neumann response

Every original native Neumann test is available. Its actual adjoint
transform proves that a fixed linear zero constraint of the forcing
is preserved by the same mean-zero native response, for both the
original map and its displayed weak derivative.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

noncomputable section

namespace StationaryHarmonicMaps.Analysis

/-- A genuine fixed linear forcing constraint is inherited by the same
mean-zero native Neumann response. All adjoint tests are produced from
the original native graphs; no derivative constraint is an input. -/
theorem native_neumann_response_fixed_kernel_ae {n q d : ℕ}
    (J : Ambient q→L[ℝ]Ambient d)
    (F Q : Domain n→Gradient n q) (g : Domain n→Ambient q)
    (hg : MemW12 (ballDomain (0:Domain n) 1) g Q)
    (hMean : (∫x in ball (0:Domain n) 1,g x)=0)
    (hResponse : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0:Domain n) 1) ψ Dψ →
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (F x i) (Dψ x i))
    (hConstraint : ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),∀i,J (F x i)=0) :
    ∀ᵐx∂volume.restrict (ball (0:Domain n) 1),J (g x)=0 ∧ ∀i,J (Q x i)=0 := by
  let μ := volume.restrict (ball (0:Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let u := fun x=>J (g x)
  let Du := fun x i=>J (Q x i)
  have hu : MemW12 (ballDomain (0:Domain n) 1) u Du :=
    ⟨(memW12Loc_continuousLinearMap hg.to_memW12Loc J).1,
      J.lipschitz.comp_memLp (map_zero J) hg.2.1,
      fun i=>J.lipschitz.comp_memLp (map_zero J) (hg.2.2 i)⟩
  have huMean : (∫x in ball (0:Domain n) 1,u x)=0 := by
    have hGLp : MemLp g 2 μ := hg.2.1
    have hGI : Integrable g μ := hGLp.integrable (by norm_num)
    change (∫x,J (g x) ∂μ)=0
    calc
      _=J (∫x,g x ∂μ) := J.integral_comp_comm hGI
      _=0 := by change J (∫x in ball (0:Domain n) 1,g x)=0;rw [hMean,map_zero]
  have hZeroNative : MemW12 (ballDomain (0:Domain n) 1)
      (fun _=>(0:Ambient d)) (fun _ _=>(0:Ambient d)) := MemW12.zero _
  have hZeroMean : (∫_x in ball (0:Domain n) 1,(0:Ambient d))=0 := integral_zero _ _
  have hTests (ψ : Domain n→Ambient d) (Dψ : Domain n→Gradient n d)
      (hψ : MemW12 (ballDomain (0:Domain n) 1) ψ Dψ) :
      (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (Du x i) (Dψ x i))=
        ∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (0:Ambient d) (Dψ x i) := by
    have hAdj : MemW12 (ballDomain (0:Domain n) 1)
        (fun x=>J.adjoint (ψ x)) (fun x i=>J.adjoint (Dψ x i)) :=
      ⟨(memW12Loc_continuousLinearMap hψ.to_memW12Loc J.adjoint).1,
        J.adjoint.lipschitz.comp_memLp (map_zero J.adjoint) hψ.2.1,
        fun i=>J.adjoint.lipschitz.comp_memLp (map_zero J.adjoint) (hψ.2.2 i)⟩
    have H := hResponse (fun x=>J.adjoint (ψ x)) (fun x i=>J.adjoint (Dψ x i)) hAdj
    simp only [ContinuousLinearMap.adjoint_inner_right] at H
    have hFZero : (fun x=>∑i : Fin n,inner ℝ (J (F x i)) (Dψ x i))=ᵐ[μ](fun _=>0) := by
      filter_upwards [hConstraint] with x hx
      simp only [hx,inner_zero_left,Finset.sum_const_zero]
    have hIntegral : (∫x in ball (0:Domain n) 1,∑i : Fin n,inner ℝ (J (F x i)) (Dψ x i))=0 :=
      (integral_congr_ae hFZero).trans (integral_zero _ _)
    exact (H.trans hIntegral).trans (by simp only [inner_zero_left,Finset.sum_const_zero,integral_zero])
  have hUnique := native_meanZero_gradient_response_unique_ae (0:Domain n) (by norm_num : (0:ℝ)<1)
    u (fun _=>(0:Ambient d)) Du (fun _ _=>(0:Ambient d)) hu hZeroNative huMean hZeroMean hTests
  filter_upwards [hUnique.1,hUnique.2] with x hx hDx
  exact ⟨hx,fun i=>congrFun hDx i⟩

end StationaryHarmonicMaps.Analysis

end
