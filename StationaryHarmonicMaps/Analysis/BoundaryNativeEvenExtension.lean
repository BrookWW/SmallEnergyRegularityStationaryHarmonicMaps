module

public import StationaryHarmonicMaps.Analysis.BoundaryNativeEvenTransport
public import StationaryHarmonicMaps.Analysis.BoundaryNativeEvenSmooth
public import StationaryHarmonicMaps.Analysis.SmoothSphereSobolevGluing
public import HarmonicMaps.Analysis.BallAverageDifferentiation
public import HarmonicMaps.Analysis.SobolevL2Closure
public import HarmonicMaps.Analysis.SobolevAECongruence

/-!
# Native even inversion extension on the double ball

Whole-ball smooth graph approximation and sphere-value gluing produce the
literal even inversion of the original native map. Its exterior derivative
is the original derivative composed with the actual inversion differential.
-/

public section

open HarmonicMaps EuclideanGeometry MeasureTheory Filter Set Metric
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem tendsto_piecewise_L2 {X : Type*} [MeasurableSpace X] {q : ℕ}
    (μ : Measure X) (S : Set X) [DecidablePred (·∈S)] (hS : MeasurableSet S)
    (f g : ℕ → X → Ambient q) (v w : X → Ambient q)
    (hf : ∀k,MemLp (f k) 2 (μ.restrict S)) (hg : ∀k,MemLp (g k) 2 (μ.restrict Sᶜ))
    (hv : MemLp v 2 (μ.restrict S)) (hw : MemLp w 2 (μ.restrict Sᶜ))
    (hF : Tendsto (fun k=>eLpNorm (f k-v) 2 (μ.restrict S)) atTop (𝓝 0))
    (hG : Tendsto (fun k=>eLpNorm (g k-w) 2 (μ.restrict Sᶜ)) atTop (𝓝 0)) :
    Tendsto (fun k=>eLpNorm ((S.piecewise (f k) (g k))-(S.piecewise v w)) 2 μ) atTop (𝓝 0) := by
  classical
  have hUpper : Tendsto (fun k=>eLpNorm (f k-v) 2 (μ.restrict S)+
      eLpNorm (g k-w) 2 (μ.restrict Sᶜ)) atTop (𝓝 0) := by
    simpa only [add_zero] using hF.add hG
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper (fun _=>zero_le)
  intro k
  have heq : (S.piecewise (f k) (g k))-(S.piecewise v w)=
      S.indicator (f k-v)+Sᶜ.indicator (g k-w) := by
    funext x
    by_cases hx : x∈S <;> simp only [Pi.sub_apply,Pi.add_apply,piecewise,indicator,hx,mem_compl_iff,
      not_true_eq_false,not_false_eq_true,if_true,if_false,add_zero,zero_add]
  change eLpNorm ((S.piecewise (f k) (g k))-(S.piecewise v w)) 2 μ≤
    eLpNorm (f k-v) 2 (μ.restrict S)+eLpNorm (g k-w) 2 (μ.restrict Sᶜ)
  rw [heq]
  have hFI := (memLp_indicator_iff_restrict hS).mpr ((hf k).sub hv)
  have hGI := (memLp_indicator_iff_restrict hS.compl).mpr ((hg k).sub hw)
  simpa only [eLpNorm_indicator_eq_eLpNorm_restrict hS,eLpNorm_indicator_eq_eLpNorm_restrict hS.compl] using
    eLpNorm_add_le hFI.aestronglyMeasurable hGI.aestronglyMeasurable (by norm_num : (1:ℝ≥0∞)≤2)

/-- The original native ball graph has a genuine even inversion extension to the double ball, with literal chain columns. -/
theorem memW12_even_inversion_extension_ball_two {n q : ℕ} (hn : 2≤n)
    (u : Domain n → Ambient q) (D : Domain n → Gradient n q)
    (hu : MemW12 (ballDomain (0 : Domain n) 1) u D) :
    let I := inversion (0 : Domain n) 1
    let O := fun (f : Domain n → Ambient q) x => f (I x)
    let DO := fun (G : Domain n → Gradient n q) x i =>
      ∑ j : Fin n, (fderiv ℝ I x (EuclideanSpace.single i 1)) j • G (I x) j
    let U := fun x=>if ‖x‖≤1 then u x else O u x
    let DU := fun x i=>if ‖x‖≤1 then D x i else DO D x i
    MemW12 (ballDomain (0 : Domain n) 2) U DU := by
  classical
  intro I O DO U DU
  let Ω := ballDomain (0 : Domain n) 2
  let μ := volume.restrict (ball (0 : Domain n) 2)
  let S := closedBall (0 : Domain n) 1
  let A := {x : Domain n | 1<‖x‖ ∧ ‖x‖<2}
  let ν := volume.restrict (ball (0 : Domain n) 1)
  let σ := volume.restrict A
  have hInner : μ.restrict S=ν := by
    have hSub : S⊆ball (0 : Domain n) 2 := closedBall_subset_ball (by norm_num)
    rw [show μ.restrict S=volume.restrict (S∩ball (0 : Domain n) 2) from Measure.restrict_restrict measurableSet_closedBall,
      inter_eq_left.mpr hSub]
    exact (Measure.restrict_congr_set (HarmonicMaps.ball_ae_eq_closedBall (0 : Domain n) (by norm_num : (0 : ℝ)<1))).symm
  have hOuter : μ.restrict Sᶜ=σ := by
    rw [show μ.restrict Sᶜ=volume.restrict (Sᶜ∩ball (0 : Domain n) 2) from Measure.restrict_restrict measurableSet_closedBall.compl]
    congr 1
    ext x
    simp only [S,A,mem_inter_iff,mem_compl_iff,mem_closedBall,mem_ball,dist_zero_right,mem_setOf_eq,not_le]
  obtain ⟨ψ,hψ,hψL,hDψL,hMap,hColumns⟩ := hu.smoothDensity_ball (by norm_num : (0 : ℝ)<1)
  let Dψ := fun k x i=>fderiv ℝ (ψ k) x (EuclideanSpace.single i 1)
  have hDψ (k : ℕ) (i : Fin n) : MemLp (fun x=>Dψ k x i) 2 ν := hDψL k i
  have hDLimit (i : Fin n) : Tendsto (fun k=>eLpNorm (fun x=>Dψ k x i-D x i) 2 ν) atTop (𝓝 0) := hColumns i
  have hOutData (k : ℕ) := even_inversion_outer_memLp (ψ k) (Dψ k) (hψL k) (hDψ k)
  have hOutOriginal := even_inversion_outer_memLp u D hu.2.1 hu.2.2
  have hOutLimits := even_inversion_outer_strong_L2 ψ Dψ u D hψL hDψ hu.2.1 hu.2.2 hMap hDLimit
  have hPieceU : U=S.piecewise u (O u) := by funext x;simp only [U,piecewise,S,mem_closedBall,dist_zero_right]
  have hPieceDU (i : Fin n) : (fun x=>DU x i)=S.piecewise (fun x=>D x i) (fun x=>DO D x i) := by
    funext x;simp only [DU,piecewise,S,mem_closedBall,dist_zero_right]
  have hUL : MemLp U 2 μ := by
    rw [hPieceU]
    apply MemLp.piecewise measurableSet_closedBall
    · rw [hInner];exact hu.2.1
    · rw [hOuter];exact hOutOriginal.1
  have hDUL (i : Fin n) : MemLp (fun x=>DU x i) 2 μ := by
    rw [hPieceDU i]
    apply MemLp.piecewise measurableSet_closedBall
    · rw [hInner];exact hu.2.2 i
    · rw [hOuter];exact hOutOriginal.2 i
  choose v hv hSphere hVOutside hDVOutside using fun k=>exists_smooth_even_inversion_extension (ψ k) (hψ k)
  have hVO (k : ℕ) (x : Domain n) (hx : 1<‖x‖) : v k x=O (ψ k) x :=
    hVOutside k x hx
  have hDVO (k : ℕ) (x : Domain n) (hx : 1<‖x‖) (i : Fin n) :
      fderiv ℝ (v k) x (EuclideanSpace.single i 1)=DO (Dψ k) x i := by
    rw [hDVOutside k x (EuclideanSpace.single i 1) hx]
    have H := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr
      (fderiv ℝ I x (EuclideanSpace.single i 1))
    have hBasis : (∑ j : Fin n, (fderiv ℝ I x (EuclideanSpace.single i 1)) j •
        EuclideanSpace.single j 1) = fderiv ℝ I x (EuclideanSpace.single i 1) := by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using H
    change (fderiv ℝ (ψ k) (I x)) _ = ∑ j : Fin n,
      (fderiv ℝ I x (EuclideanSpace.single i 1)) j •
        (fderiv ℝ (ψ k) (I x)) (EuclideanSpace.single j 1)
    calc
      _ = (fderiv ℝ (ψ k) (I x)) (∑ j : Fin n,
          (fderiv ℝ I x (EuclideanSpace.single i 1)) j • EuclideanSpace.single j 1) :=
        congrArg (fderiv ℝ (ψ k) (I x)) hBasis.symm
      _ = _ := by simp only [map_sum, map_smul]
  let Uk := fun k=>S.piecewise (ψ k) (O (ψ k))
  let DUk := fun k x i=>S.piecewise (fun y=>Dψ k y i) (fun y=>DO (Dψ k) y i) x
  have hUk (k : ℕ) : MemW12 Ω (Uk k) (DUk k) := by
    have hSphere' (x : Domain n) (hx : x∈sphere (0 : Domain n) (1 : ℝ)) : ψ k x=v k x :=
      (hSphere k x (by simpa only [mem_sphere,dist_zero_right] using hx)).symm
    obtain ⟨hGlue,hGlueIn,hGlueOut⟩ := memW12_smooth_sphere_gluing_ball hn ⟨1,by norm_num⟩
      (ψ k) (v k) (hψ k) (hv k) hSphere' 2
    have hBallClosed : ball (0 : Domain n) 1=ᵐ[μ] S :=
      (HarmonicMaps.ball_ae_eq_closedBall (0 : Domain n) (by norm_num : (0 : ℝ)<1)).filter_mono (ae_mono Measure.restrict_le_self)
    have hAE : ∀ᵐx∂μ,
        (v k x+(ball (0 : Domain n) 1).indicator (ψ k-v k) x)=Uk k x ∧
        (fun i=>fderiv ℝ (v k) x (EuclideanSpace.single i 1)+(ball (0 : Domain n) 1).indicator
          (fun y=>fderiv ℝ (ψ k) y (EuclideanSpace.single i 1)-fderiv ℝ (v k) y (EuclideanSpace.single i 1)) x)=DUk k x := by
      filter_upwards [hBallClosed] with x hx
      by_cases hxS : x∈S
      · have hxB : x∈ball (0 : Domain n) 1 := Eq.mpr hx hxS
        obtain ⟨hMapIn,hGradIn⟩ := hGlueIn x hxB
        constructor
        · rw [show Uk k x=ψ k x from piecewise_eq_of_mem S _ _ hxS]
          exact hMapIn
        · funext i
          rw [show DUk k x i=Dψ k x i from piecewise_eq_of_mem S _ _ hxS]
          exact congrFun hGradIn i
      · have hxNorm : 1<‖x‖ := not_le.mp (by simpa only [S,mem_closedBall,dist_zero_right] using hxS)
        have hxB : x∉ball (0 : Domain n) 1 := fun h=>hxS (ball_subset_closedBall h)
        obtain ⟨hMapOut,hGradOut⟩ := hGlueOut x hxB
        constructor
        · rw [show Uk k x=O (ψ k) x from piecewise_eq_of_notMem S _ _ hxS]
          exact hMapOut.trans (hVO k x hxNorm)
        · funext i
          rw [show DUk k x i=DO (Dψ k) x i from piecewise_eq_of_notMem S _ _ hxS]
          exact (congrFun hGradOut i).trans (hDVO k x hxNorm i)
    exact hGlue.congr_ae (hAE.mono fun _ h=>h.1) (hAE.mono fun _ h=>h.2)
  have hULimit : Tendsto (fun k=>eLpNorm (Uk k-U) 2 μ) atTop (𝓝 0) := by
    rw [hPieceU]
    apply tendsto_piecewise_L2 μ S measurableSet_closedBall ψ (fun k=>O (ψ k)) u (O u)
    · intro k;rw [hInner];exact hψL k
    · intro k;rw [hOuter];exact (hOutData k).1
    · rw [hInner];exact hu.2.1
    · rw [hOuter];exact hOutOriginal.1
    · rw [hInner];exact hMap
    · rw [hOuter];exact hOutLimits.1
  have hDULimit (i : Fin n) : Tendsto (fun k=>eLpNorm (fun x=>DUk k x i-DU x i) 2 μ) atTop (𝓝 0) := by
    have H : Tendsto (fun k=>eLpNorm
        (S.piecewise (fun x=>Dψ k x i) (fun x=>DO (Dψ k) x i)-
          S.piecewise (fun x=>D x i) (fun x=>DO D x i)) 2 μ) atTop (𝓝 0) := by
      apply tendsto_piecewise_L2 μ S measurableSet_closedBall
      · intro k;rw [hInner];exact hDψ k i
      · intro k;rw [hOuter];exact (hOutData k).2 i
      · rw [hInner];exact hu.2.2 i
      · rw [hOuter];exact hOutOriginal.2 i
      · rw [hInner];exact hDLimit i
      · rw [hOuter];exact hOutLimits.2 i
    apply H.congr
    intro k
    apply eLpNorm_congr_ae
    exact Eventually.of_forall fun x=>by
      change (S.piecewise (fun y=>Dψ k y i) (fun y=>DO (Dψ k) y i)) x-
        (S.piecewise (fun y=>D y i) (fun y=>DO D y i)) x=DUk k x i-DU x i
      exact congrArg (fun z : Ambient q=>(S.piecewise (fun y=>Dψ k y i) (fun y=>DO (Dψ k) y i)) x-z)
        (congrFun (hPieceDU i) x).symm
  exact MemW12.of_L2_limit_ball (0 : Domain n) 2 hUk hUL hDUL hULimit hDULimit

end StationaryHarmonicMaps.Analysis

end
