module

public import StationaryHarmonicMaps.Analysis.NeumannMorreyBanachOperator
public import StationaryHarmonicMaps.Analysis.MeanZeroNativeMorreyConstraint
public import StationaryHarmonicMaps.Analysis.NativeMorreyBilinearProduct

/-!
# The actual bounded native Neumann response

The operator is selected from the proved unique original mean-zero response.
Its full native characteristic determines it on every coefficient class.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

noncomputable section

namespace StationaryHarmonicMaps.Analysis

/-- The unique bounded Neumann operator for the original coefficient classes. -/
@[expose] def nativeNeumannMorreyResponse
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) (q : ℕ) :
    MorreyCoefficientSpace n q ν→L[ℝ]NativeMorreySobolevSpace n q ν :=
  Classical.choose (((Classical.choose_spec
    (exists_uniform_unique_native_neumann_morrey_operator n hn ν hν hνn)).2 q).exists)

/-- The complete original mean and every whole-ball native Neumann pairing. -/
theorem nativeNeumannMorreyResponse_characterization
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) (q : ℕ)
    (F : MorreyCoefficientSpace n q ν) :
    (∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν
      (nativeNeumannMorreyResponse n hn ν hν hνn q F)).val x)=0 ∧
      ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
        (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ),
        inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν
          (nativeNeumannMorreyResponse n hn ν hν hνn q F))
          (hsUnitBallL2Class Dψ hψ.2.2)=
          inner ℝ (morreyCoefficientRecover (n:=n) (q:=q) ν F)
            (hsUnitBallL2Class Dψ hψ.2.2) :=
  (Classical.choose_spec (((Classical.choose_spec
    (exists_uniform_unique_native_neumann_morrey_operator n hn ν hν hνn)).2 q).exists)).2 F

/-- Every bounded operator with the full original characteristic is the same
operator, independently of any particular norm bound. -/
theorem nativeNeumannMorreyResponse_eq_iff
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) (q : ℕ)
    (T : MorreyCoefficientSpace n q ν→L[ℝ]NativeMorreySobolevSpace n q ν) :
    T=nativeNeumannMorreyResponse n hn ν hν hνn q ↔
      ∀F : MorreyCoefficientSpace n q ν,
        (∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν (T F)).val x)=0 ∧
        ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
          (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ),
          inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν (T F)) (hsUnitBallL2Class Dψ hψ.2.2)=
            inner ℝ (morreyCoefficientRecover (n:=n) (q:=q) ν F) (hsUnitBallL2Class Dψ hψ.2.2) := by
  constructor
  · intro h
    subst T
    exact nativeNeumannMorreyResponse_characterization n hn ν hν hνn q
  · intro h
    apply ContinuousLinearMap.ext
    intro F
    exact (existsUnique_native_neumann_morrey_class n hn ν hν hνn q F).unique
      (h F) (nativeNeumannMorreyResponse_characterization n hn ν hν hνn q F)

theorem exists_nativeNeumannMorreyResponse_norm_bound
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) :
    ∃C : ℝ,0<C ∧ ∀q : ℕ,‖nativeNeumannMorreyResponse n hn ν hν hνn q‖≤C := by
  let H := exists_uniform_unique_native_neumann_morrey_operator n hn ν hν hνn
  refine ⟨H.choose,H.choose_spec.1,?_⟩
  intro q
  exact (Classical.choose_spec ((H.choose_spec.2 q).exists)).1

/-- The same produced response lies in the actual mean-zero native kernel. -/
theorem nativeNeumannMorreyResponse_mem_meanZero
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) (q : ℕ)
    (F : MorreyCoefficientSpace n q ν) :
    nativeNeumannMorreyResponse n hn ν hν hνn q F∈meanZeroNativeMorreySubmodule n q ν := by
  have H := (nativeNeumannMorreyResponse_characterization n hn ν hν hνn q F).1
  change nativeMorreyAverage n q ν _=0
  change (⨍x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν
    (nativeNeumannMorreyResponse n hn ν hν hνn q F)).val x)=0
  rw [average_eq,H,smul_zero]

private theorem meanZero_native_map_integral {n q : ℕ} (ν : ℝ)
    (X : MeanZeroNativeMorreySpace n q ν) :
    (∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν X.val).val x)=0 := by
  have H : (⨍x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν X.val).val x)=0 := X.property
  rw [average_eq] at H
  have hV : 0<(volume.restrict (ball (0 : Domain n) 1)).real univ := by
    rw [measureReal_restrict_apply_univ]
    exact HolderToCK.ball_volume_real_pos 0 (by norm_num)
  exact (smul_eq_zero.mp H).resolve_left (inv_ne_zero hV.ne')

/-- Applying the original Neumann operator to the same original gradient
recovers every actual mean-zero native graph. -/
theorem nativeNeumannMorreyResponse_gradient
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) (q : ℕ)
    (X : MeanZeroNativeMorreySpace n q ν) :
    nativeNeumannMorreyResponse n hn ν hν hνn q
      (nativeMorreyGradientClass (n:=n) (q:=q) ν X.val)=X.val := by
  apply (existsUnique_native_neumann_morrey_class n hn ν hν hνn q
    (nativeMorreyGradientClass (n:=n) (q:=q) ν X.val)).unique
    (nativeNeumannMorreyResponse_characterization n hn ν hν hνn q _)
  exact ⟨meanZero_native_map_integral ν X,fun _ _ _=>rfl⟩

private theorem response_hs_inner_raw {n q : ℕ}
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

/-- An original natural coefficient has zero Neumann response. -/
theorem nativeNeumannMorreyResponse_eq_zero_of_natural
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) (q : ℕ)
    (F : MorreyCoefficientSpace n q ν) (Z : Domain n→Gradient n q)
    (hZ : ∀i,MemLp (fun x=>Z x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hF : morreyCoefficientRecover (n:=n) (q:=q) ν F=hsUnitBallL2Class Z hZ)
    (hNatural : ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q),
      MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
      (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0) :
    nativeNeumannMorreyResponse n hn ν hν hνn q F=0 := by
  apply (existsUnique_native_neumann_morrey_class n hn ν hν hνn q F).unique
    (nativeNeumannMorreyResponse_characterization n hn ν hν hνn q F)
  constructor
  · rw [map_zero]
    exact (integral_congr_ae (Lp.coeFn_zero (Ambient q) 2 (volume.restrict (ball (0 : Domain n) 1)))).trans (integral_zero _ _)
  · intro ψ Dψ hψ
    rw [map_zero,inner_zero_left,hF,response_hs_inner_raw]
    exact (hNatural ψ Dψ hψ).symm

end StationaryHarmonicMaps.Analysis

end
