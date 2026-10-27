module

public import StationaryHarmonicMaps.Analysis.SystemMatrixPairing
public import StationaryHarmonicMaps.Analysis.OrthogonalCoefficientBounds
public import HolderToCK.Analysis.Harmonic.GradientVariance

/-!
# Energy of the actual finite-index matrix tests

The genuine rank-one matrix test retains its full native W0 Leibniz
graph. Orthogonality controls the original inverse-frame basis column,
and the actual bounded test controls the differentiated-frame term.
The estimate displays both fixed encoder/decoder norms and does not
commute the original matrix factors.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric

namespace StationaryHarmonicMaps.Analysis

private theorem norm_sum_sq_le_two {V : Type*} [NormedAddCommGroup V] (v w : V) :
    ‖v+w‖^2≤2*‖v‖^2+2*‖w‖^2 := by
  have H := pow_le_pow_left₀ (norm_nonneg (v+w)) (norm_add_le v w) 2
  nlinarith only [H,sq_nonneg (‖v‖-‖w‖)]

/-- Every actual rank-one matrix W0 test has its quantitative derivative
energy from the original native frame and original bounded W0 test.
The frame bound M is used only for the native product graph; the test
bound H and both fixed coefficient norms are displayed explicitly. -/
theorem system_matrix_native_test_energy_ball {n m q : ℕ}
    (a : Domain n) (r : ℝ) (hr : 0<r)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (P : Domain n → Ambient m) (DP : Domain n → Gradient n m)
    (hP : MemW12 (ballDomain a r) P DP) (M : ℝ)
    (hPBound : ∀ᵐx∂volume.restrict (ball a r),‖P x‖≤M)
    (hOrth : ∀ᵐx∂volume.restrict (ball a r),star (R (P x))*R (P x)=1)
    (φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q)
    (hφ : HasZeroBoundaryValues (ballDomain a r) φ Dφ) (H : ℝ)
    (hφBound : ∀ᵐx∂volume.restrict (ball a r),‖φ x‖≤H) (j : Fin q) :
    let T := fun x=>systemMatrixTestCoefficient E R j (P x) (φ x)
    let DT := fun x i=>systemMatrixTestCoefficient E R j (DP x i) (φ x)+
      systemMatrixTestCoefficient E R j (P x) (Dφ x i)
    HasZeroBoundaryValues (ballDomain a r) T DT ∧
    IntegrableOn (fun x=>hsNormSq (DT x)) (ball a r) volume ∧
    Real.sqrt (∫x in ball a r,hsNormSq (DT x))≤
      2*‖E‖*(‖R‖*|H| *Real.sqrt (∫x in ball a r,hsNormSq (DP x))+
        Real.sqrt (∫x in ball a r,hsNormSq (Dφ x))) := by
  intro T DT
  have hT := zeroBoundary_bounded_native_bilinear_product_ball a r hr P DP hP M hPBound
    (systemMatrixTestCoefficient E R j) φ Dφ hφ H hφBound
  let μ := volume.restrict (ball a r)
  have hDI : Integrable (fun x=>hsNormSq (DP x)) μ := hP.integrable_hsNormSq
  have hφI : Integrable (fun x=>hsNormSq (Dφ x)) μ := hφ.1.integrable_hsNormSq
  have hTI : Integrable (fun x=>hsNormSq (DT x)) μ := hT.1.integrable_hsNormSq
  let A := ‖E‖*‖R‖*|H|
  have hA : 0≤A := mul_nonneg (mul_nonneg (norm_nonneg E) (norm_nonneg R)) (abs_nonneg H)
  have hPoint : ∀ᵐx∂μ,hsNormSq (DT x)≤2*A^2*hsNormSq (DP x)+2*‖E‖^2*hsNormSq (Dφ x) := by
    filter_upwards [hOrth,hφBound] with x hx hxφ
    have hφH : ‖φ x‖≤|H| := hxφ.trans (le_abs_self H)
    have hStarOrth : star (star (R (P x)))*star (R (P x))=1 := by
      simpa only [star_star] using mul_star_eq_one_of_star_mul_eq_one (R (P x)) hx
    have hPj : ‖star (R (P x)) (EuclideanSpace.single j 1)‖=1 := by
      have HH := norm_sq_apply_orthogonal (star (R (P x))) hStarOrth (EuclideanSpace.single j 1)
      simp only [PiLp.norm_single,norm_one,one_pow] at HH
      nlinarith only [HH,norm_nonneg (star (R (P x)) (EuclideanSpace.single j 1))]
    have hDPj (i : Fin n) : ‖star (R (DP x i)) (EuclideanSpace.single j 1)‖≤‖R‖*‖DP x i‖ := by
      calc
        _≤‖star (R (DP x i))‖*‖EuclideanSpace.single j (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
        _=‖R (DP x i)‖ := by
          rw [ContinuousLinearMap.star_eq_adjoint,LinearIsometryEquiv.norm_map,
            PiLp.norm_single,norm_one,mul_one]
        _≤_ := R.le_opNorm _
    have hFirst (i : Fin n) : ‖systemMatrixTestCoefficient E R j (DP x i) (φ x)‖≤A*‖DP x i‖ := by
      rw [systemMatrixTestCoefficient_apply]
      calc
        _≤‖E‖*‖InnerProductSpace.rankOne ℝ (φ x) (star (R (DP x i)) (EuclideanSpace.single j 1))‖ := E.le_opNorm _
        _=‖E‖*(‖φ x‖*‖star (R (DP x i)) (EuclideanSpace.single j 1)‖) := by rw [InnerProductSpace.norm_rankOne]
        _≤‖E‖*(|H| *(‖R‖*‖DP x i‖)) := mul_le_mul_of_nonneg_left
          (mul_le_mul hφH (hDPj i) (norm_nonneg _) (abs_nonneg H)) (norm_nonneg E)
        _=A*‖DP x i‖ := by dsimp only [A];ring
    have hSecond (i : Fin n) : ‖systemMatrixTestCoefficient E R j (P x) (Dφ x i)‖≤‖E‖*‖Dφ x i‖ := by
      rw [systemMatrixTestCoefficient_apply]
      have HE := E.le_opNorm (InnerProductSpace.rankOne ℝ (Dφ x i) (star (R (P x)) (EuclideanSpace.single j 1)))
      simpa only [InnerProductSpace.norm_rankOne,hPj,mul_one] using HE
    have hEach (i : Fin n) : ‖DT x i‖^2≤2*A^2*‖DP x i‖^2+2*‖E‖^2*‖Dφ x i‖^2 := by
      have HF := pow_le_pow_left₀ (norm_nonneg _) (hFirst i) 2
      have HS := pow_le_pow_left₀ (norm_nonneg _) (hSecond i) 2
      have HA := norm_sum_sq_le_two (systemMatrixTestCoefficient E R j (DP x i) (φ x))
        (systemMatrixTestCoefficient E R j (P x) (Dφ x i))
      change ‖DT x i‖^2≤_ at HA
      rw [mul_pow] at HF HS
      nlinarith only [HA,HF,HS]
    calc
      _≤∑i : Fin n,(2*A^2*‖DP x i‖^2+2*‖E‖^2*‖Dφ x i‖^2) := Finset.sum_le_sum fun i _=>hEach i
      _=_ := by simp only [hsNormSq,Finset.sum_add_distrib,Finset.mul_sum]
  have hIntegral : (∫x,hsNormSq (DT x) ∂μ)≤
      2*A^2*(∫x,hsNormSq (DP x) ∂μ)+2*‖E‖^2*(∫x,hsNormSq (Dφ x) ∂μ) := by
    have hRhs : Integrable (fun x=>2*A^2*hsNormSq (DP x)+2*‖E‖^2*hsNormSq (Dφ x)) μ :=
      (hDI.const_mul _).add (hφI.const_mul _)
    have HI := integral_mono_ae hTI hRhs hPoint
    have hSplit : (∫x,2*A^2*hsNormSq (DP x)+2*‖E‖^2*hsNormSq (Dφ x) ∂μ)=
        (∫x,2*A^2*hsNormSq (DP x) ∂μ)+(∫x,2*‖E‖^2*hsNormSq (Dφ x) ∂μ) :=
      integral_add (hDI.const_mul _) (hφI.const_mul _)
    rw [hSplit,integral_const_mul,integral_const_mul] at HI
    exact HI
  let X := A*Real.sqrt (∫x,hsNormSq (DP x) ∂μ)
  let Y := ‖E‖*Real.sqrt (∫x,hsNormSq (Dφ x) ∂μ)
  have hX : 0≤X := mul_nonneg hA (Real.sqrt_nonneg _)
  have hY : 0≤Y := mul_nonneg (norm_nonneg E) (Real.sqrt_nonneg _)
  have hXSq : X^2=A^2*(∫x,hsNormSq (DP x) ∂μ) := by
    dsimp only [X]
    rw [mul_pow,Real.sq_sqrt (integral_nonneg fun _=>hsNormSq_nonneg _)]
  have hYSq : Y^2=‖E‖^2*(∫x,hsNormSq (Dφ x) ∂μ) := by
    dsimp only [Y]
    rw [mul_pow,Real.sq_sqrt (integral_nonneg fun _=>hsNormSq_nonneg _)]
  have hEnergy : (∫x,hsNormSq (DT x) ∂μ)≤(2*(X+Y))^2 := by
    have HI : (∫x,hsNormSq (DT x) ∂μ)≤2*X^2+2*Y^2 := by
      rw [hXSq,hYSq]
      nlinarith only [hIntegral]
    nlinarith only [HI,mul_nonneg hX hY,sq_nonneg (X+Y)]
  refine ⟨hT,hTI,?_⟩
  have HH := Real.sqrt_le_sqrt hEnergy
  rw [Real.sqrt_sq (mul_nonneg (by norm_num) (add_nonneg hX hY))] at HH
  exact HH.trans_eq (by dsimp only [X,Y,A];ring)

end StationaryHarmonicMaps.Analysis

end
