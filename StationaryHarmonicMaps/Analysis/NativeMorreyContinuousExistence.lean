module

public import StationaryHarmonicMaps.Analysis.NativeMorreyMeanZero
public import StationaryHarmonicMaps.Analysis.StrongerMorreyMeanBound
public import StationaryHarmonicMaps.Analysis.ContinuousOrthogonalBoundaryFrame

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace StationaryHarmonicMaps.Analysis

private theorem continuous_closedBall_eq_of_ae {n q : ℕ}
    (W Z : C(closedBall (0 : Domain n) 1,Ambient q))
    (h : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀hx : x∈ball (0 : Domain n) 1,
      W ⟨x,ball_subset_closedBall hx⟩=Z ⟨x,ball_subset_closedBall hx⟩) : W=Z := by
  have hAE : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀hx : x∈ball (0 : Domain n) 1,
      (W-Z) ⟨x,ball_subset_closedBall hx⟩=(0 : Ambient q) := by
    filter_upwards [h] with x hx
    intro hxBall
    exact sub_eq_zero.mpr (hx hxBall)
  have hAll := closedBall_representative_mem_closed_of_ae (fun _ : Domain n=>(0 : Ambient q))
    (W-Z) (W-Z).continuous hAE {0} isClosed_singleton (Filter.Eventually.of_forall fun _=>rfl)
  apply ContinuousMap.ext
  intro x
  have hx : (W-Z) x=0 := hAll x
  exact sub_eq_zero.mp hx

/-- Every native stronger-Morrey class has a unique continuous closed-ball
representative. Its uniform norm is controlled by the intrinsic native norm,
with a coefficient independent of the target dimension. -/
theorem existsUnique_nativeMorrey_continuous_representative_bound
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    let ν := (n : ℝ)-2+γ
    ∃C : ℝ,0<C ∧ ∀(q : ℕ) (X : NativeMorreySobolevSpace n q ν),
      (∃! W : C(closedBall (0 : Domain n) 1,Ambient q),
        ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀hx : x∈ball (0 : Domain n) 1,
          W ⟨x,ball_subset_closedBall hx⟩=(nativeMorreyMapClass (n:=n) (q:=q) ν X).val x) ∧
      ∀W : C(closedBall (0 : Domain n) 1,Ambient q),
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀hx : x∈ball (0 : Domain n) 1,
          W ⟨x,ball_subset_closedBall hx⟩=(nativeMorreyMapClass (n:=n) (q:=q) ν X).val x) →
        ‖W‖≤C*‖X‖ := by
  intro ν
  obtain ⟨H,hH,hRep⟩ := exists_stronger_morrey_ae_bound_by_mean n hn γ hγ hγTwo
  let T := (Real.sqrt (volume.real (ball (0 : Domain n) 1)))⁻¹
  have hT : 0≤T := inv_nonneg.mpr (Real.sqrt_nonneg _)
  let C := 1+T+H
  have hC : 0<C := by dsimp only [C];linarith only [hT,hH]
  refine ⟨C,hC,?_⟩
  intro q X
  have hData : ∃(u : Domain n→Ambient q) (Du : Domain n→Gradient n q)
      (hu : MemW12 (ballDomain (0 : Domain n) 1) u Du),
      nativeMorreyMapClass (n:=n) (q:=q) ν X=hu.2.1.toLp u ∧
      nativeMorreyHSClass (n:=n) (q:=q) ν X=hsUnitBallL2Class Du hu.2.2 ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Du x))≤
          ‖nativeMorreyGradientClass (n:=n) (q:=q) ν X‖^2*r^ν :=
    exists_raw_native_of_nativeMorreySobolev (n:=n) (q:=q) ν X
  obtain ⟨u,Du,hu,hMap,_hGrad,hGrowth⟩ := hData
  let K := ‖nativeMorreyGradientClass (n:=n) (q:=q) ν X‖^2
  have hRepData : ∃ W : closedBall (0 : Domain n) 1→Ambient q,
      Continuous W ∧
      (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀hx : x∈ball (0 : Domain n) 1,
        W ⟨x,ball_subset_closedBall hx⟩=u x) ∧
      (∀x,‖W x‖≤‖(⨍y in ball (0 : Domain n) 1,u y)‖+H*Real.sqrt K) ∧
      ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
        ‖u x‖≤‖(⨍y in ball (0 : Domain n) 1,u y)‖+H*Real.sqrt K :=
    hRep q u Du K hu (sq_nonneg _) hGrowth
  obtain ⟨w,hw,hwAE,hwBound,_huBound⟩ := hRepData
  let W : C(closedBall (0 : Domain n) 1,Ambient q) := ⟨w,hw⟩
  have hAEX : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν X).val x=u x := by
    filter_upwards [hu.2.1.coeFn_toLp] with x hx
    exact (congrArg (fun U : MapUnitBallL2 n q=>U.val x) hMap).trans hx
  have hWAE : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀hx : x∈ball (0 : Domain n) 1,
      W ⟨x,ball_subset_closedBall hx⟩=(nativeMorreyMapClass (n:=n) (q:=q) ν X).val x := by
    filter_upwards [hwAE,hAEX] with x hx hux
    intro hxBall
    exact (hx hxBall).trans hux.symm
  have hUnique (Z : C(closedBall (0 : Domain n) 1,Ambient q))
      (hZAE : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀hx : x∈ball (0 : Domain n) 1,
        Z ⟨x,ball_subset_closedBall hx⟩=(nativeMorreyMapClass (n:=n) (q:=q) ν X).val x) : Z=W := by
    apply continuous_closedBall_eq_of_ae
    filter_upwards [hZAE,hWAE] with x hz hx
    intro hxBall
    exact (hz hxBall).trans (hx hxBall).symm
  have hMapNorm : ‖nativeMorreyMapClass (n:=n) (q:=q) ν X‖≤‖X‖ := by
    change ‖X.val.1‖≤max ‖X.val.1‖ ‖X.val.2‖
    exact le_max_left _ _
  have hGradNorm : ‖nativeMorreyGradientClass (n:=n) (q:=q) ν X‖≤‖X‖ := by
    change ‖X.val.2‖≤max ‖X.val.1‖ ‖X.val.2‖
    exact le_max_right _ _
  have hMean : ‖(⨍y in ball (0 : Domain n) 1,u y)‖≤T*‖X‖ := by
    have hMeanEq : (⨍y in ball (0 : Domain n) 1,u y)=
        unitBallAverageL2 n q (nativeMorreyMapClass (n:=n) (q:=q) ν X) :=
      (unitBallAverageL2_apply_raw u hu.2.1).symm.trans
        (congrArg (unitBallAverageL2 n q) hMap.symm)
    rw [hMeanEq]
    exact ((unitBallAverageL2 n q).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (unitBallAverageL2_norm_le n q) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hMapNorm hT))
  have hWNorm : ‖W‖≤C*‖X‖ := by
    apply (ContinuousMap.norm_le W (mul_nonneg hC.le (norm_nonneg _))).mpr
    intro x
    calc
      _≤‖(⨍y in ball (0 : Domain n) 1,u y)‖+H*Real.sqrt K := hwBound x
      _≤T*‖X‖+H*‖X‖ := by
        dsimp only [K]
        rw [Real.sqrt_sq (norm_nonneg _)]
        exact add_le_add hMean (mul_le_mul_of_nonneg_left hGradNorm hH.le)
      _≤C*‖X‖ := by dsimp only [C];nlinarith only [norm_nonneg X]
  exact ⟨⟨W,hWAE,hUnique⟩,fun Z hZ=>by rw [hUnique Z hZ];exact hWNorm⟩

end StationaryHarmonicMaps.Analysis

end
