/- Copyright (c) 2026. All rights reserved. -/
module

public import StationaryHarmonicMaps.Analysis.SystemNativeBilinearTest
public import StationaryHarmonicMaps.Analysis.BoundedNativeBilinearProduct
public import StationaryHarmonicMaps.Analysis.BoundedBilinearWeakL2
public import StationaryHarmonicMaps.Geometry.GaugedEnergyAlgebra
public import StationaryHarmonicMaps.Analysis.SobolevCutoff

/-!
# The actual matrix-index frame forcing pairing

Each target component uses the literal rank-one matrix test with the
original inverse-frame column. Complete HS coordinates preserve the
operator order in the original forcing. Genuine native products allow
these tests in the original full matrix natural equation.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The actual matrix test coefficient for one original target component. -/
@[expose] noncomputable def systemMatrixTestCoefficient {m q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q)) (j : Fin q) :
    Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient (q*q)) := by
  let Adj := (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=Ambient q) (F:=Ambient q)).toContinuousLinearMap.comp R
  let J : Ambient m →L[ℝ] Ambient q := Adj.flip (EuclideanSpace.single j 1)
  let K : Ambient q →L[ℝ] (Ambient q →L[ℝ] (Ambient q →L[ℝ] Ambient q)) := InnerProductSpace.rankOne ℝ
  exact ((ContinuousLinearMap.compL ℝ (Ambient q) (Ambient q →L[ℝ] Ambient q) (Ambient (q*q))) E).comp
    (K.flip.comp J)

/-- The matrix test is the literal rank-one operator, encoded in full HS coordinates. -/
theorem systemMatrixTestCoefficient_apply {m q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q)) (j : Fin q)
    (z : Ambient m) (φ : Ambient q) :
    systemMatrixTestCoefficient E R j z φ=
      E (InnerProductSpace.rankOne ℝ φ (star (R z) (EuclideanSpace.single j 1))) := rfl

/-- Full HS pairing with the genuine rank-one test keeps the order Z(P*e). -/
theorem system_encoded_rankOne_pairing {q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (Z : Ambient q →L[ℝ] Ambient q) (φ a : Ambient q) :
    inner ℝ (E Z) (E (InnerProductSpace.rankOne ℝ φ a))=inner ℝ (Z a) φ := by
  let b := EuclideanSpace.basisFun (Fin q) ℝ
  have H := congrArg (fun v : Ambient q=>inner ℝ (Z v) φ) (b.sum_repr' a)
  simp only [map_sum,map_smul,sum_inner,real_inner_smul_left,
    EuclideanSpace.basisFun_apply,b] at H
  rw [encoded_inner_eq_sum_columns E hE]
  simp only [InnerProductSpace.rankOne_apply,real_inner_smul_right]
  calc
    _=∑j : Fin q,inner ℝ (EuclideanSpace.single j 1) a*
        inner ℝ (Z (EuclideanSpace.single j 1)) φ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_comm a]
    _=_ := H

/-- The original forcing Σ Z_i(P*Dv_i) has its actual finite-index
matrix-test expansion; the inverse frame is never exchanged with Z. -/
theorem system_matrix_forcing_finite_pairing {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (Z : Fin n → Ambient q →L[ℝ] Ambient q) (P : Ambient q →L[ℝ] Ambient q)
    (Dv : Gradient n q) (φ : Ambient q) :
    inner ℝ (∑i : Fin n,Z i (star P (Dv i))) φ=
      ∑j : Fin q,∑i : Fin n,(Dv i) j*inner ℝ (E (Z i))
        (E (InnerProductSpace.rankOne ℝ φ (star P (EuclideanSpace.single j 1)))) := by
  let b := EuclideanSpace.basisFun (Fin q) ℝ
  have hSum (v : Ambient q) : (∑j : Fin q,v j • EuclideanSpace.single j 1)=v := by
    simpa only [b,EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using b.sum_repr v
  have hEach (i : Fin n) : inner ℝ (Z i (star P (Dv i))) φ=
      ∑j : Fin q,(Dv i) j*inner ℝ (E (Z i))
        (E (InnerProductSpace.rankOne ℝ φ (star P (EuclideanSpace.single j 1)))) := by
    nth_rw 1 [←hSum (Dv i)]
    simp only [map_sum,map_smul,sum_inner,real_inner_smul_left,system_encoded_rankOne_pairing E hE]
  rw [sum_inner]
  calc
    _=∑i : Fin n,∑j : Fin q,(Dv i) j*inner ℝ (E (Z i))
        (E (InnerProductSpace.rankOne ℝ φ (star P (EuclideanSpace.single j 1)))) :=
      Finset.sum_congr rfl fun i _=>hEach i
    _=_ := Finset.sum_comm

end StationaryHarmonicMaps.Analysis

end
