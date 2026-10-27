module

public import StationaryHarmonicMaps.Analysis.NeumannMorreyBanach

/-!
# The actual bounded Neumann response operator on Morrey classes

The unique mean-zero native response to each original coefficient class
is linear by the full native response identity and actual uniqueness.
The original uniform response bound makes this same map continuous and
controls its operator norm before the target dimension is chosen.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

noncomputable section

namespace StationaryHarmonicMaps.Analysis

private theorem native_map_integral_add {n q : ℕ} (ν : ℝ)
    (X Y : NativeMorreySobolevSpace n q ν) :
    (∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν (X+Y)).val x)=
      (∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν X).val x)+
      ∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν Y).val x := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let U := nativeMorreyMapClass (n:=n) (q:=q) ν X
  let V := nativeMorreyMapClass (n:=n) (q:=q) ν Y
  have hU : Integrable U μ := (Lp.memLp U).integrable (by norm_num)
  have hV : Integrable V μ := (Lp.memLp V).integrable (by norm_num)
  rw [map_add]
  exact (integral_congr_ae (Lp.coeFn_add U V)).trans (integral_add hU hV)

private theorem native_map_integral_smul {n q : ℕ} (ν c : ℝ)
    (X : NativeMorreySobolevSpace n q ν) :
    (∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν (c • X)).val x)=
      c • ∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν X).val x := by
  rw [map_smul]
  exact (integral_congr_ae (Lp.coeFn_smul c (nativeMorreyMapClass (n:=n) (q:=q) ν X))).trans
    (integral_smul c _)

private def neumann_class_choice
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) (q : ℕ)
    (F : MorreyCoefficientSpace n q ν) : NativeMorreySobolevSpace n q ν :=
  (existsUnique_native_neumann_morrey_class n hn ν hν hνn q F).choose

private theorem neumann_class_choice_spec
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) (q : ℕ)
    (F : MorreyCoefficientSpace n q ν) :
    (∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν
      (neumann_class_choice n hn ν hν hνn q F)).val x)=0 ∧
      ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
        (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ),
        inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν (neumann_class_choice n hn ν hν hνn q F))
          (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2)=
          inner ℝ (morreyCoefficientRecover (n:=n) (q:=q) ν F)
            (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2) :=
  (existsUnique_native_neumann_morrey_class n hn ν hν hνn q F).choose_spec.1

private theorem neumann_class_choice_add
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) (q : ℕ)
    (F G : MorreyCoefficientSpace n q ν) :
    neumann_class_choice n hn ν hν hνn q (F+G)=
      neumann_class_choice n hn ν hν hνn q F+neumann_class_choice n hn ν hν hνn q G := by
  apply (existsUnique_native_neumann_morrey_class n hn ν hν hνn q (F+G)).unique
    (neumann_class_choice_spec n hn ν hν hνn q (F+G))
  constructor
  · rw [native_map_integral_add (n:=n) (q:=q),(neumann_class_choice_spec n hn ν hν hνn q F).1,
      (neumann_class_choice_spec n hn ν hν hνn q G).1,add_zero]
  · intro ψ Dψ hψ
    let J : HSUnitBallL2 n q := hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2
    let X := neumann_class_choice n hn ν hν hνn q F
    let Y := neumann_class_choice n hn ν hν hνn q G
    calc
      _=inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν X+
          nativeMorreyHSClass (n:=n) (q:=q) ν Y) J :=
        congrArg (fun Z : HSUnitBallL2 n q=>inner ℝ Z J)
          ((nativeMorreyHSClass (n:=n) (q:=q) ν).map_add X Y)
      _=inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν X) J+
          inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν Y) J := inner_add_left _ _ _
      _=inner ℝ (morreyCoefficientRecover (n:=n) (q:=q) ν F) J+
          inner ℝ (morreyCoefficientRecover (n:=n) (q:=q) ν G) J :=
        congrArg₂ (fun a b : ℝ=>a+b)
          ((neumann_class_choice_spec n hn ν hν hνn q F).2 ψ Dψ hψ)
          ((neumann_class_choice_spec n hn ν hν hνn q G).2 ψ Dψ hψ)
      _=inner ℝ (morreyCoefficientRecover (n:=n) (q:=q) ν F+
          morreyCoefficientRecover (n:=n) (q:=q) ν G) J := (inner_add_left _ _ _).symm
      _=_ := congrArg (fun Z : HSUnitBallL2 n q=>inner ℝ Z J)
        ((morreyCoefficientRecover (n:=n) (q:=q) ν).map_add F G).symm

private theorem neumann_class_choice_smul
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) (q : ℕ)
    (c : ℝ) (F : MorreyCoefficientSpace n q ν) :
    neumann_class_choice n hn ν hν hνn q (c • F)=c • neumann_class_choice n hn ν hν hνn q F := by
  apply (existsUnique_native_neumann_morrey_class n hn ν hν hνn q (c • F)).unique
    (neumann_class_choice_spec n hn ν hν hνn q (c • F))
  constructor
  · rw [native_map_integral_smul (n:=n) (q:=q),(neumann_class_choice_spec n hn ν hν hνn q F).1,smul_zero]
  · intro ψ Dψ hψ
    let J : HSUnitBallL2 n q := hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2
    let X := neumann_class_choice n hn ν hν hνn q F
    calc
      _=inner ℝ (c • nativeMorreyHSClass (n:=n) (q:=q) ν X) J :=
        congrArg (fun Z : HSUnitBallL2 n q=>inner ℝ Z J)
          ((nativeMorreyHSClass (n:=n) (q:=q) ν).map_smul c X)
      _=c*inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν X) J := real_inner_smul_left _ _ _
      _=c*inner ℝ (morreyCoefficientRecover (n:=n) (q:=q) ν F) J :=
        congrArg (fun a : ℝ=>c*a) ((neumann_class_choice_spec n hn ν hν hνn q F).2 ψ Dψ hψ)
      _=inner ℝ (c • morreyCoefficientRecover (n:=n) (q:=q) ν F) J :=
        (real_inner_smul_left _ _ _).symm
      _=_ := congrArg (fun Z : HSUnitBallL2 n q=>inner ℝ Z J)
        ((morreyCoefficientRecover (n:=n) (q:=q) ν).map_smul c F).symm

private def native_neumann_linear_map
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) (q : ℕ) :
    MorreyCoefficientSpace n q ν →ₗ[ℝ] NativeMorreySobolevSpace n q ν :=
  { toFun := neumann_class_choice n hn ν hν hνn q
    map_add' := neumann_class_choice_add n hn ν hν hνn q
    map_smul' := by
      intro c F
      simpa only [RingHom.id_apply] using neumann_class_choice_smul n hn ν hν hνn q c F }

/-- The original full native pairing and actual mean-zero normalization
uniquely characterize a bounded linear Neumann response on the actual
Morrey coefficient and native graph spaces. Its operator bound depends
only on n and ν and is selected before every target dimension. -/
theorem exists_uniform_unique_native_neumann_morrey_operator
    (n : ℕ) (hn : 2≤n) (ν : ℝ) (hν : 0≤ν) (hνn : ν<(n : ℝ)) :
    ∃C : ℝ,0<C ∧ ∀q : ℕ,
      ∃! T : MorreyCoefficientSpace n q ν →L[ℝ] NativeMorreySobolevSpace n q ν,
        ‖T‖≤C ∧ ∀F : MorreyCoefficientSpace n q ν,
          (∫x in ball (0 : Domain n) 1,(nativeMorreyMapClass (n:=n) (q:=q) ν (T F)).val x)=0 ∧
          ∀(ψ : Domain n→Ambient q) (Dψ : Domain n→Gradient n q)
            (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ),
            inner ℝ (nativeMorreyHSClass (n:=n) (q:=q) ν (T F)) (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2)=
              inner ℝ (morreyCoefficientRecover (n:=n) (q:=q) ν F) (hsUnitBallL2Class (n:=n) (q:=q) Dψ hψ.2.2) := by
  let Hbound := exists_uniform_native_neumann_morrey_class_bound n hn ν hν hνn
  let C : ℝ := Hbound.choose
  have hC : 0<C := Hbound.choose_spec.1
  refine ⟨C,hC,?_⟩
  intro q
  let L : MorreyCoefficientSpace n q ν →ₗ[ℝ] NativeMorreySobolevSpace n q ν := native_neumann_linear_map n hn ν hν hνn q
  have hBound (F : MorreyCoefficientSpace n q ν) : ‖L F‖≤C*‖F‖ :=
    Hbound.choose_spec.2 q F (neumann_class_choice n hn ν hν hνn q F)
      (neumann_class_choice_spec n hn ν hν hνn q F).1
      (neumann_class_choice_spec n hn ν hν hνn q F).2
  letI : NormedSpace ℝ (NativeMorreySobolevSpace n q ν) := inferInstance
  let T : MorreyCoefficientSpace n q ν →L[ℝ] NativeMorreySobolevSpace n q ν := L.mkContinuous C hBound
  have hNorm : ‖T‖≤C := by
    change sInf {c : ℝ | 0≤c ∧ ∀F : MorreyCoefficientSpace n q ν,‖T F‖≤c*‖F‖}≤C
    exact csInf_le ⟨0,fun _ h=>h.1⟩ ⟨hC.le,hBound⟩
  refine ⟨T,⟨hNorm,?_⟩,?_⟩
  · intro F
    exact neumann_class_choice_spec n hn ν hν hνn q F
  · rintro S ⟨_hSNorm,hS⟩
    apply ContinuousLinearMap.ext
    intro F
    exact (existsUnique_native_neumann_morrey_class n hn ν hν hνn q F).unique
      (hS F) (neumann_class_choice_spec n hn ν hν hνn q F)

end StationaryHarmonicMaps.Analysis

end
