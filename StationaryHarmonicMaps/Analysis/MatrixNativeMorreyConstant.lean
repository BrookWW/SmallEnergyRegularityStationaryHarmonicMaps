module

public import StationaryHarmonicMaps.Analysis.NativeMorreyContinuousRepresentative
public import StationaryHarmonicMaps.Analysis.NeumannGradientSpace

/-!
# Constant native graphs

A constant original map and its literal zero gradient define an intrinsic
native class at every exponent. The class keeps its exact map L2 norm.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace StationaryHarmonicMaps.Analysis

theorem nativeMorreyConstant_memW12 (n q : ℕ) (c : Ambient q) :
    MemW12 (ballDomain (0 : Domain n) 1) (fun _=>c) (fun _ _=>0) := by
  simpa only [fderiv_fun_const,zero_apply,Pi.zero_apply] using
    memW12_ball_of_ambient_c1 (0 : Domain n) 1 (fun _ : Domain n=>c) contDiff_const

theorem nativeMorreyConstant_hs_zero (n q : ℕ) (c : Ambient q) :
    hsUnitBallL2Class (fun (_ : Domain n) (_ : Fin n)=>(0 : Ambient q))
      (nativeMorreyConstant_memW12 n q c).2.2=0 := by
  apply Lp.ext
  filter_upwards [hsUnitBallL2Class_ae
    (fun (_ : Domain n) (_ : Fin n)=>(0 : Ambient q)) (nativeMorreyConstant_memW12 n q c).2.2,
    Lp.coeFn_zero (Ambient (n*q)) 2 (volume.restrict (ball (0 : Domain n) 1))] with x hx hz
  rw [hx,hz]
  apply PiLp.ext
  intro j
  simp only [hsFlatten,Pi.zero_apply,PiLp.zero_apply]

/-- The literal pair of the constant map L2 class and the zero Morrey gradient. -/
@[expose] def nativeMorreyConstant (n q : ℕ) (ν : ℝ) (c : Ambient q) :
    NativeMorreySobolevSpace n q ν :=
  ⟨((nativeMorreyConstant_memW12 n q c).2.1.toLp (fun _=>c),0),
    nativeMorrey_pair_mem_of_native ν (fun _=>c) (fun _ _=>0)
      (nativeMorreyConstant_memW12 n q c) 0 (by
        rw [map_zero,nativeMorreyConstant_hs_zero n q c])⟩

theorem nativeMorreyConstant_map (n q : ℕ) (ν : ℝ) (c : Ambient q) :
    nativeMorreyMapClass (n:=n) (q:=q) ν (nativeMorreyConstant n q ν c)=
      (nativeMorreyConstant_memW12 n q c).2.1.toLp (fun _=>c) := rfl

theorem nativeMorreyConstant_gradient (n q : ℕ) (ν : ℝ) (c : Ambient q) :
    nativeMorreyGradientClass (n:=n) (q:=q) ν (nativeMorreyConstant n q ν c)=0 := rfl

theorem nativeMorreyConstant_ae (n q : ℕ) (ν : ℝ) (c : Ambient q) :
    ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      (nativeMorreyMapClass (n:=n) (q:=q) ν (nativeMorreyConstant n q ν c)).val x=c :=
  (nativeMorreyConstant_memW12 n q c).2.1.coeFn_toLp

/-- Every native class with this AE constant value equals the literal constant graph. -/
theorem nativeMorreyConstant_eq_iff (n q : ℕ) (ν : ℝ) (c : Ambient q)
    (X : NativeMorreySobolevSpace n q ν) :
    X=nativeMorreyConstant n q ν c ↔
      ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
        (nativeMorreyMapClass (n:=n) (q:=q) ν X).val x=c := by
  constructor
  · intro hX
    rw [hX]
    exact nativeMorreyConstant_ae n q ν c
  · intro hX
    apply nativeMorreyMapClass_injective (n:=n) (q:=q) ν
    apply Lp.ext
    filter_upwards [hX,nativeMorreyConstant_ae n q ν c] with x hx hc
    exact hx.trans hc.symm

theorem nativeMorreyConstant_norm_sq (n q : ℕ) (ν : ℝ) (c : Ambient q) :
    ‖nativeMorreyConstant n q ν c‖^2=volume.real (ball (0 : Domain n) 1)*‖c‖^2 := by
  have hRaw := nativeMorreyConstant_memW12 n q c
  change (max ‖hRaw.2.1.toLp (fun _=>c)‖ ‖(0 : MorreyCoefficientSpace n q ν)‖)^2=_
  rw [norm_zero,max_eq_left (norm_nonneg _)]
  calc
    _=∫x in ball (0 : Domain n) 1,‖(hRaw.2.1.toLp (fun _=>c)) x‖^2 :=
      l2_euclidean_norm_sq _ (hRaw.2.1.toLp (fun _=>c))
    _=∫_x in ball (0 : Domain n) 1,‖c‖^2 := by
      exact integral_congr_ae (hRaw.2.1.coeFn_toLp.mono fun x hx=>congrArg (fun z : Ambient q=>‖z‖^2) hx)
    _=_ := by rw [setIntegral_const,smul_eq_mul]

theorem nativeMorreyConstant_norm (n q : ℕ) (ν : ℝ) (c : Ambient q) :
    ‖nativeMorreyConstant n q ν c‖=Real.sqrt (volume.real (ball (0 : Domain n) 1))*‖c‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg c))).mp
  have hV0 : 0≤volume.real (ball (0 : Domain n) 1) := ENNReal.toReal_nonneg
  rw [mul_pow,Real.sq_sqrt hV0,nativeMorreyConstant_norm_sq]

theorem nativeMorreyContinuousRepresentative_constant
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    (q : ℕ) (c : Ambient q) (x : closedBall (0 : Domain n) 1) :
    nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo
      (nativeMorreyConstant n q ((n : ℝ)-2+γ) c) x=c := by
  have hEq : ContinuousMap.const (closedBall (0 : Domain n) 1) c=
      nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo
        (nativeMorreyConstant n q ((n : ℝ)-2+γ) c) := by
    apply (nativeMorreyContinuousRepresentative_eq_iff n hn γ hγ hγTwo _ _).mpr
    filter_upwards [nativeMorreyConstant_ae n q ((n : ℝ)-2+γ) c] with z hz
    intro _hzBall
    exact hz.symm
  exact (congrArg (fun W : C(closedBall (0 : Domain n) 1,Ambient q)=>W x) hEq).symm

end StationaryHarmonicMaps.Analysis

end
