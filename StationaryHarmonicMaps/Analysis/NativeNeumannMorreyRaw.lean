module

public import StationaryHarmonicMaps.Analysis.NativeNeumannMorreyResponse
public import StationaryHarmonicMaps.Analysis.NativeMorreyCoefficientActionExistence
public import StationaryHarmonicMaps.Analysis.NaturalCoefficientNeumannBanachConstraint

/-!
# Original raw tests and fixed kernels of the actual native Neumann operator

Every original native representative of the same selected response has the
full original raw Neumann characteristic. The response keeps fixed linear
kernels of the original forcing.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped ENNReal Topology

noncomputable section

namespace StationaryHarmonicMaps.Analysis

private theorem neumann_hs_inner_raw {n q : ℕ}
    (F G : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hG : ∀i,MemLp (fun x=>G x i) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    inner ℝ (hsUnitBallL2Class F hF) (hsUnitBallL2Class G hG)=
      ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (F x i) (G x i) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hsUnitBallL2Class_ae F hF,hsUnitBallL2Class_ae G hG] with x hxF hxG
  rw [hxF,hxG]
  exact hs_flatten_inner (F x) (G x)

private theorem neumann_class_tests_raw {n q : ℕ} (ν : ℝ)
    (X : NativeMorreySobolevSpace n q ν) (Z : Domain n→Gradient n q)
    (hZ : ∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hTests : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ),
      inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν X) (hsUnitBallL2Class Dψ hψ.2.2)=
        inner ℝ (hsUnitBallL2Class Z hZ) (hsUnitBallL2Class Dψ hψ.2.2))
    (g : Domain n→Ambient q) (Q : Domain n→Gradient n q)
    (hg : MemW12 (ballDomain (0 : Domain n) 1) g Q)
    (hGrad : nativeMorreyHSClass (n:=n) (q:=q) ν X=hsUnitBallL2Class Q hg.2.2) :
    ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Z x i) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
      (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
        ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i) := by
  intro ψ Dψ hψ
  refine ⟨integrable_column_pairing (volume.restrict (ball (0 : Domain n) 1)) Q Dψ hg.2.2 hψ.2.2,
    integrable_column_pairing (volume.restrict (ball (0 : Domain n) 1)) Z Dψ hZ hψ.2.2,?_⟩
  have H := hTests ψ Dψ hψ
  rw [hGrad,neumann_hs_inner_raw,neumann_hs_inner_raw] at H
  exact H

/-- Every original native representative of the same selected response has
both genuine integrable pairings and every original whole-ball test identity. -/
theorem nativeNeumannMorreyResponse_raw_tests
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) (q : ℕ)
    (F : MorreyCoefficientSpace n q ν) (Z : Domain n→Gradient n q)
    (hZ : ∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hClass : morreyCoefficientRecover (n:=n) (q:=q) ν F=hsUnitBallL2Class Z hZ)
    (g : Domain n→Ambient q) (Q : Domain n→Gradient n q)
    (hg : MemW12 (ballDomain (0 : Domain n) 1) g Q)
    (hMap : nativeMorreyMapClass (n:=n) (q:=q) ν
      (nativeNeumannMorreyResponse n hn ν hν hνn q F)=hg.2.1.toLp g) :
    ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Q x i) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (Z x i) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
      (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Q x i) (Dψ x i))=
        ∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i) := by
  have hGrad := nativeMorreyHSClass_eq_of_native_map ν g Q hg
    (nativeNeumannMorreyResponse n hn ν hν hνn q F) hMap
  apply neumann_class_tests_raw ν _ Z hZ _ g Q hg hGrad
  intro ψ Dψ hψ
  rw [←hClass]
  exact (nativeNeumannMorreyResponse_characterization n hn ν hν hνn q F).2 ψ Dψ hψ

private theorem neumann_class_fixed_kernel {n q d : ℕ} (ν : ℝ)
    (J : Ambient q→L[ℝ]Ambient d) (W : MeanZeroNativeMorreySpace n q ν)
    (Z : Domain n→Gradient n q)
    (hZ : ∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hTests : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ),
      inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν W.val) (hsUnitBallL2Class Dψ hψ.2.2)=
        inner ℝ (hsUnitBallL2Class Z hZ) (hsUnitBallL2Class Dψ hψ.2.2))
    (hJ : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i,J (Z x i)=0) :
    W∈constrainedMeanZeroNativeMorreySubmodule n q d ν J := by
  obtain ⟨g,Q,hg,hMean,hMap,hGrad,_hGrowth⟩ := exists_raw_native_of_meanZeroNativeMorrey (n:=n) (q:=q) ν W
  have hIntegral : (∫x in ball (0 : Domain n) 1,g x)=0 := by
    rw [average_eq] at hMean
    have hV : 0<(volume.restrict (ball (0 : Domain n) 1)).real univ := by
      rw [measureReal_restrict_apply_univ]
      exact HolderToCK.ball_volume_real_pos 0 (by norm_num)
    exact (smul_eq_zero.mp hMean).resolve_left (inv_ne_zero hV.ne')
  have hRawTests := neumann_class_tests_raw ν W.val Z hZ hTests g Q hg hGrad
  have hRaw := native_neumann_response_fixed_kernel_ae J Z Q g hg hIntegral
    (fun ψ Dψ hψ=>(hRawTests ψ Dψ hψ).2.2) hJ
  apply (mem_constrainedMeanZeroNativeMorreySubmodule_iff ν J g hg.2.1 W hMap).mpr
  exact hRaw.mono fun _ hx=>hx.1

/-- The same selected response belongs to the original fixed closed native
kernel whenever every original forcing column lies in that kernel. -/
theorem nativeNeumannMorreyResponse_preserves_fixed_kernel
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) (q d : ℕ)
    (J : Ambient q→L[ℝ]Ambient d)
    (F : MorreyCoefficientSpace n q ν) (Z : Domain n→Gradient n q)
    (hZ : ∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hClass : morreyCoefficientRecover (n:=n) (q:=q) ν F=hsUnitBallL2Class Z hZ)
    (hJ : ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀i,J (Z x i)=0) :
    let X := nativeNeumannMorreyResponse n hn ν hν hνn q F
    let W : MeanZeroNativeMorreySpace n q ν := ⟨X,nativeNeumannMorreyResponse_mem_meanZero n hn ν hν hνn q F⟩
    W∈constrainedMeanZeroNativeMorreySubmodule n q d ν J := by
  intro X W
  apply neumann_class_fixed_kernel ν J W Z hZ _ hJ
  intro ψ Dψ hψ
  rw [←hClass]
  exact (nativeNeumannMorreyResponse_characterization n hn ν hν hνn q F).2 ψ Dψ hψ

end StationaryHarmonicMaps.Analysis

end
