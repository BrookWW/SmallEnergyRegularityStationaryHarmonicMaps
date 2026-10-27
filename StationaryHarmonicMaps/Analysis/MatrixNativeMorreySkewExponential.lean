module

public import StationaryHarmonicMaps.Analysis.MatrixNativeMorreyExponential
public import StationaryHarmonicMaps.Analysis.SkewMeanZeroNativeMorrey
public import StationaryHarmonicMaps.Geometry.SkewExponentialOrientation

/-!
# Actual special-orthogonal native exponentials

The literal skew kernel fixes the original AE matrix values. Continuity
preserves skewness at every closed-ball point, so the actual native matrix
exponential has orthogonality and determinant1 on the full closed ball.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace StationaryHarmonicMaps.Analysis

/-- Every closed-ball value of the same constrained native class is skew. -/
theorem skew_nativeMorrey_continuous_skew
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (X : SkewMeanZeroNativeMorreySpace n q ((n : ℝ)-2+γ) e)
    (x : closedBall (0 : Domain n) 1) :
    star (e (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo X.val.val x))=
      -(e (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo X.val.val x)) := by
  let ν := (n : ℝ)-2+γ
  let U : MapUnitBallL2 n (q*q) := nativeMorreyMapClass (n:=n) (q:=q*q) ν X.val.val
  let u : Domain n→Ambient (q*q) := U
  have hu : MemLp u 2 (volume.restrict (ball (0 : Domain n) 1)) := Lp.memLp U
  have hMap : nativeMorreyMapClass (n:=n) (q:=q*q) ν X.val.val=hu.toLp u :=
    (Lp.toLp_coeFn U hu).symm
  have hSkew : ∀ᵐz∂volume.restrict (ball (0 : Domain n) 1),star (e (u z))=-(e (u z)) :=
    (mem_skewMeanZeroNativeMorreySubmodule_iff ν e u hu X.val hMap).mp X.property
  let W := nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo X.val.val
  have hW : ∀ᵐz∂volume.restrict (ball (0 : Domain n) 1),∀hz : z∈ball (0 : Domain n) 1,
      W ⟨z,ball_subset_closedBall hz⟩=u z :=
    nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo X.val.val
  have hStar : Continuous (fun z : Ambient (q*q)=>star (e z)) :=
    (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).continuous.comp e.continuous
  have hClosed : IsClosed {z : Ambient (q*q) | star (e z)=-(e z)} :=
    isClosed_eq hStar e.continuous.neg
  have hAll := closedBall_representative_mem_closed_of_ae u W W.continuous hW
    {z : Ambient (q*q) | star (e z)=-(e z)} hClosed hSkew
  exact hAll x

/-- Exponentiating the actual skew native class gives special-orthogonal
matrices at every point of the closed source ball. -/
theorem skew_nativeMorrey_exp_specialOrthogonal
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (X : SkewMeanZeroNativeMorreySpace n q ((n : ℝ)-2+γ) e) :
    let E := e.symm.toContinuousLinearMap
    let R := e.toContinuousLinearMap
    let hRE : ∀T,R (E T)=T := e.apply_symm_apply
    let hER : ∀z,E (R z)=z := e.symm_apply_apply
    let Z := matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER X.val.val
    ∀x : closedBall (0 : Domain n) 1,
      star (e (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo Z x))*
        e (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo Z x)=1 ∧
      (e (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo Z x)).det=1 := by
  intro E R hRE hER Z x
  let S := e (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo X.val.val x)
  have hS : star S=-S := skew_nativeMorrey_continuous_skew n hn γ hγ hγTwo q e X x
  have hPoint : e (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo Z x)=
      NormedSpace.exp S :=
    matrixNativeMorreyExp_evaluation n hn γ hγ hγTwo q E R hRE hER X.val.val x
  have hOrth : star (NormedSpace.exp S)*NormedSpace.exp S=1 := by
    simpa only [one_smul] using (operator_exp_orthogonal_of_skew S hS 1).1
  have hDet : (NormedSpace.exp S).det=1 := by
    simpa only [one_smul] using operator_exp_det_eq_one_of_skew S hS 1
  exact ⟨(congrArg (fun T : Ambient q→L[ℝ]Ambient q=>star T*T) hPoint).trans hOrth,
    (congrArg (fun T : Ambient q→L[ℝ]Ambient q=>T.det) hPoint).trans hDet⟩

/-- The original AE values of the native exponential are special orthogonal. -/
theorem skew_nativeMorrey_exp_ae_specialOrthogonal
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (X : SkewMeanZeroNativeMorreySpace n q ((n : ℝ)-2+γ) e) :
    let ν := (n : ℝ)-2+γ
    let E := e.symm.toContinuousLinearMap
    let R := e.toContinuousLinearMap
    let hRE : ∀T,R (E T)=T := e.apply_symm_apply
    let hER : ∀z,E (R z)=z := e.symm_apply_apply
    let Z := matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER X.val.val
    ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
      star (e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν Z).val x))*
        e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν Z).val x)=1 ∧
      (e ((nativeMorreyMapClass (n:=n) (q:=q*q) ν Z).val x)).det=1 := by
  intro ν E R hRE hER Z
  have hAll := skew_nativeMorrey_exp_specialOrthogonal n hn γ hγ hγTwo q e X
  filter_upwards [nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo Z,
    ae_restrict_mem measurableSet_ball] with x hx hxBall
  have hPoint := hAll ⟨x,ball_subset_closedBall hxBall⟩
  exact (congrArg (fun T : Ambient q→L[ℝ]Ambient q=>star T*T=1 ∧ T.det=1)
    (congrArg e (hx hxBall))).mp hPoint

/-- Any original native representative of the same exponential class has
the same actual special-orthogonal AE values. -/
theorem skew_nativeMorrey_exp_raw_specialOrthogonal
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (e : Ambient (q*q)≃L[ℝ](Ambient q→L[ℝ]Ambient q))
    (X : SkewMeanZeroNativeMorreySpace n q ((n : ℝ)-2+γ) e) :
    let ν := (n : ℝ)-2+γ
    let E := e.symm.toContinuousLinearMap
    let R := e.toContinuousLinearMap
    let hRE : ∀T,R (E T)=T := e.apply_symm_apply
    let hER : ∀z,E (R z)=z := e.symm_apply_apply
    let Z := matrixNativeMorreyExp n hn γ hγ hγTwo q E R hRE hER X.val.val
    ∀(v : Domain n→Ambient (q*q)) (Dv : Domain n→Gradient n (q*q))
      (hv : MemW12 (ballDomain (0 : Domain n) 1) v Dv),
      nativeMorreyMapClass (n:=n) (q:=q*q) ν Z=hv.2.1.toLp v →
      ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),
        star (e (v x))*e (v x)=1 ∧ (e (v x)).det=1 := by
  intro ν E R hRE hER Z v Dv hv hMap
  have hSO := skew_nativeMorrey_exp_ae_specialOrthogonal n hn γ hγ hγTwo q e X
  filter_upwards [hSO,hv.2.1.coeFn_toLp] with x hx hvx
  have hValue : (nativeMorreyMapClass (n:=n) (q:=q*q) ν Z).val x=v x :=
    (congrArg (fun U : MapUnitBallL2 n (q*q)=>U.val x) hMap).trans hvx
  exact (congrArg (fun T : Ambient q→L[ℝ]Ambient q=>star T*T=1 ∧ T.det=1)
    (congrArg e hValue)).mp hx

end StationaryHarmonicMaps.Analysis

end
