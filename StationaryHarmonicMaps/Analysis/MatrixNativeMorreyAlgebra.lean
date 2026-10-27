module

public import StationaryHarmonicMaps.Analysis.MatrixNativeMorreyConstant
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Actual matrix multiplication on intrinsic native Morrey graphs

The full coefficient encoder and decoder preserve multiplication in its
original order. Native multiplication is bounded bilinear for the inherited
native norm; no submultiplicative renorming is installed.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace StationaryHarmonicMaps.Analysis

/-- The literal encoded matrix product, as a genuine bounded bilinear map. -/
@[expose] def matrixMorreyCoefficientProduct {q : ℕ}
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    Ambient (q*q)→L[ℝ]Ambient (q*q)→L[ℝ]Ambient (q*q) :=
  ((ContinuousLinearMap.compL ℝ (Ambient (q*q)) (Ambient q→L[ℝ]Ambient q) (Ambient (q*q))) E).comp
    ((ContinuousLinearMap.compL ℝ (Ambient q) (Ambient q) (Ambient q)).bilinearComp R R)

theorem matrixMorreyCoefficientProduct_apply {q : ℕ}
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (u v : Ambient (q*q)) : matrixMorreyCoefficientProduct E R u v=E (R u*R v) := rfl

/-- Actual matrix multiplication as a continuous bilinear native operation. -/
@[expose] def matrixNativeMorreyMultiplication
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q)) :
    NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)→L[ℝ]
      NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)→L[ℝ]
        NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ) :=
  nativeMorreyBilinear (m:=q*q) (k:=q*q) (q:=q*q) n hn γ hγ hγTwo (matrixMorreyCoefficientProduct E R)

/-- The literal encoded identity with its zero native gradient. -/
@[expose] def matrixNativeMorreyUnit (n q : ℕ) (ν : ℝ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q)) :
    NativeMorreySobolevSpace n (q*q) ν :=
  nativeMorreyConstant n (q*q) ν (E 1)

/-- The actual decoded closed-ball point value of a matrix native class. -/
@[expose] def matrixNativeMorreyEvaluation
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (x : closedBall (0 : Domain n) 1) :
    NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)→L[ℝ](Ambient q→L[ℝ]Ambient q) :=
  R.comp (nativeMorreyEvaluation n hn γ hγ hγTwo (q*q) x)

theorem matrixNativeMorreyMultiplication_point
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (X Y : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ))
    (x : closedBall (0 : Domain n) 1) :
    nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo
      (matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R X Y) x=
      E (R (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo X x)*
        R (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo Y x)) :=
  nativeMorreyContinuousRepresentative_bilinear (m:=q*q) (k:=q*q) (q:=q*q)
    n hn γ hγ hγTwo (matrixMorreyCoefficientProduct E R) X Y x

theorem matrixNativeMorreyEvaluation_mul
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T)
    (X Y : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ))
    (x : closedBall (0 : Domain n) 1) :
    matrixNativeMorreyEvaluation n hn γ hγ hγTwo q R x
      (matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R X Y)=
      matrixNativeMorreyEvaluation n hn γ hγ hγTwo q R x X*
        matrixNativeMorreyEvaluation n hn γ hγ hγTwo q R x Y := by
  change R (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo
    (matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R X Y) x)=
      R (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo X x)*
        R (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo Y x)
  exact (congrArg R (matrixNativeMorreyMultiplication_point n hn γ hγ hγTwo q E R X Y x)).trans (hRE _)

theorem matrixNativeMorreyEvaluation_unit
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (x : closedBall (0 : Domain n) 1) :
    matrixNativeMorreyEvaluation n hn γ hγ hγTwo q R x
      (matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E)=1 := by
  change R (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo
    (nativeMorreyConstant n (q*q) ((n : ℝ)-2+γ) (E 1)) x)=1
  rw [nativeMorreyContinuousRepresentative_constant,hRE]

theorem matrixNativeMorreyMultiplication_assoc
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T)
    (X Y Z : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)) :
    matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R
      (matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R X Y) Z=
      matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R X
        (matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R Y Z) := by
  apply nativeMorreyContinuousRepresentative_injective n hn γ hγ hγTwo (q*q)
  apply ContinuousMap.ext
  intro x
  simp only [matrixNativeMorreyMultiplication_point,hRE,mul_assoc]

theorem matrixNativeMorreyMultiplication_unit_left
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (X : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)) :
    matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R
      (matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E) X=X := by
  apply nativeMorreyContinuousRepresentative_injective n hn γ hγ hγTwo (q*q)
  apply ContinuousMap.ext
  intro x
  rw [matrixNativeMorreyMultiplication_point]
  change E (R (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo
    (nativeMorreyConstant n (q*q) ((n : ℝ)-2+γ) (E 1)) x)*_)=_
  rw [nativeMorreyContinuousRepresentative_constant,hRE,one_mul,hER]

theorem matrixNativeMorreyMultiplication_unit_right
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (X : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)) :
    matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R X
      (matrixNativeMorreyUnit n q ((n : ℝ)-2+γ) E)=X := by
  apply nativeMorreyContinuousRepresentative_injective n hn γ hγ hγTwo (q*q)
  apply ContinuousMap.ext
  intro x
  rw [matrixNativeMorreyMultiplication_point]
  change E (_*R (nativeMorreyContinuousRepresentative (q:=q*q) n hn γ hγ hγTwo
    (nativeMorreyConstant n (q*q) ((n : ℝ)-2+γ) (E 1)) x))=_
  rw [nativeMorreyContinuousRepresentative_constant,hRE,mul_one,hER]

/-- Left multiplication is represented in the actual Banach operator algebra. -/
theorem matrixNativeMorreyLeftMul_mul
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (E : (Ambient q→L[ℝ]Ambient q)→L[ℝ]Ambient (q*q))
    (R : Ambient (q*q)→L[ℝ](Ambient q→L[ℝ]Ambient q))
    (hRE : ∀T,R (E T)=T)
    (X Y : NativeMorreySobolevSpace n (q*q) ((n : ℝ)-2+γ)) :
    matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R
      (matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R X Y)=
      matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R X*
        matrixNativeMorreyMultiplication n hn γ hγ hγTwo q E R Y := by
  apply ContinuousLinearMap.ext
  intro Z
  exact matrixNativeMorreyMultiplication_assoc n hn γ hγ hγTwo q E R hRE X Y Z

end StationaryHarmonicMaps.Analysis

end
