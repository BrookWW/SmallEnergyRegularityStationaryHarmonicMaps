module

public import StationaryHarmonicMaps.Analysis.SystemMatrixTestEnergy
public import StationaryHarmonicMaps.Analysis.NativeSupercriticalTestBound

/-!
# Supercritical energy of the same original matrix tests

The actual W0 test and its original supercritical gradient give the
essential test bound and the forward Ls-to-L2 energy bound. They are
inserted into the literal rank-one matrix Leibniz graph on the original
query, with encoder and decoder norms retained in the fixed constant.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

private theorem matrix_test_gradient_energy_root {n q : ℕ} (s : ℝ) (hs : 2≤s)
    (Dφ : Domain n → Gradient n q) (a : Domain n) (r : ℝ) (hr : 0<r)
    (hDφ : ∀i,MemLp (fun x=>Dφ x i) (ENNReal.ofReal s) (volume.restrict (Metric.ball a r))) :
    Real.sqrt (∫ x in Metric.ball a r,hsNormSq (Dφ x))≤
      (volume.real (Metric.ball (0 : Domain n) 1))^(1/2-1/s)*r^((n : ℝ)/2-(n : ℝ)/s)*
        (∫ x in Metric.ball a r,(Real.sqrt (hsNormSq (Dφ x)))^s)^(1/s) := by
  let μ := volume.restrict (Metric.ball a r)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let g := fun x=>Real.sqrt (hsNormSq (Dφ x))
  have hg0 (x : Domain n) : 0≤g x := Real.sqrt_nonneg _
  have hg : MemLp g (ENNReal.ofReal s) μ := memLp_hsNorm_of_columns Dφ _ hDφ
  have hRoot := integral_norm_rpow_root_le_of_exponent_le g (μ:=μ) (by norm_num : (0 : ℝ)<2) hs hg
  have hSquare (x : Domain n) : (g x)^2=hsNormSq (Dφ x) := Real.sq_sqrt (hsNormSq_nonneg _)
  simp only [Real.norm_of_nonneg (hg0 _),Real.rpow_two,hSquare] at hRoot
  rw [← Real.sqrt_eq_rpow] at hRoot
  have hMu : μ.real univ=volume.real (Metric.ball a r) := measureReal_restrict_apply_univ (Metric.ball a r)
  rw [hMu] at hRoot
  let V := volume.real (Metric.ball (0 : Domain n) 1)
  have hV0 : 0≤V := ENNReal.toReal_nonneg
  have hMass : (volume.real (Metric.ball a r))^(1/2-1/s)=V^(1/2-1/s)*r^((n : ℝ)/2-(n : ℝ)/s) := by
    rw [HolderToCK.ball_volume_real a hr,Real.mul_rpow (pow_nonneg hr.le _) hV0,
      ← Real.rpow_natCast r n,← Real.rpow_mul hr.le]
    have hExp : (n : ℝ)*(1/2-1/s)=(n : ℝ)/2-(n : ℝ)/s := by ring
    rw [hExp,mul_comm]
  rw [hMass] at hRoot
  exact hRoot.trans_eq (by ring)

/-- Original supercritical native W0 test data produce the actual
matrix tests and their scale-correct complete-HS derivative energies. -/
theorem exists_system_matrix_test_supercritical_energy (n : ℕ) (hn : 2≤n)
    (s : ℝ) (hsn : (n : ℝ)<s) (m q : ℕ)
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q)) :
    ∃C : ℝ,0<C ∧ ∀(a : Domain n) (r : ℝ),0<r →
      ∀(P : Domain n → Ambient m) (DP : Domain n → Gradient n m),
      MemW12 (ballDomain a r) P DP → ∀M : ℝ,
      (∀ᵐx∂volume.restrict (ball a r),‖P x‖≤M) →
      (∀ᵐx∂volume.restrict (ball a r),star (R (P x))*R (P x)=1) →
      ∀(φ : Domain n → Ambient q) (Dφ : Domain n → Gradient n q),
        HasZeroBoundaryValues (ballDomain a r) φ Dφ →
        (∀i,MemLp (fun x=>Dφ x i) (ENNReal.ofReal s) (volume.restrict (ball a r))) →
        let T := fun (j : Fin q) x=>systemMatrixTestCoefficient E R j (P x) (φ x)
        let DT := fun (j : Fin q) x i=>systemMatrixTestCoefficient E R j (DP x i) (φ x)+
          systemMatrixTestCoefficient E R j (P x) (Dφ x i)
        IntegrableOn (fun x=>(Real.sqrt (hsNormSq (Dφ x)))^s) (ball a r) volume ∧
        (∀j,HasZeroBoundaryValues (ballDomain a r) (T j) (DT j)) ∧
        ∀j,Real.sqrt (∫x in ball a r,hsNormSq (DT j x))≤
          C*(Real.sqrt (∫x in ball a r,hsNormSq (DP x))*r^(1-(n : ℝ)/s)+r^((n : ℝ)/2-(n : ℝ)/s))*
            (∫x in ball a r,(Real.sqrt (hsNormSq (Dφ x)))^s)^(1/s) := by
  have hnReal : (2 : ℝ)≤n := by exact_mod_cast hn
  have hs2 : 2≤s := hnReal.trans hsn.le
  obtain ⟨A,hA,Hsup⟩ := exists_native_zeroBoundary_supercritical_bound n hn s hsn
  let V := (volume.real (ball (0 : Domain n) 1))^(1/2-1/s)
  let C := 1+2*‖E‖*(‖R‖*A+V)
  have hV : 0≤V := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hRA : 0≤‖R‖*A := mul_nonneg (norm_nonneg R) hA.le
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro a r hr P DP hP M hPBound hOrth φ Dφ hφ hDφ T DT
  let J := (∫x in ball a r,(Real.sqrt (hsNormSq (Dφ x)))^s)^(1/s)
  have hJ : 0≤J := Real.rpow_nonneg (integral_nonneg fun _=>Real.rpow_nonneg (Real.sqrt_nonneg _) _) _
  let H := A*r^(1-(n : ℝ)/s)*J
  have hH : 0≤H := mul_nonneg (mul_nonneg hA.le (Real.rpow_nonneg hr.le _)) hJ
  obtain ⟨hI,hφBound,_hTop⟩ := Hsup q a r φ Dφ hr hφ hDφ
  have hEach (j : Fin q) := system_matrix_native_test_energy_ball a r hr E R P DP hP M hPBound
    hOrth φ Dφ hφ H hφBound j
  have hGrad := matrix_test_gradient_energy_root s hs2 Dφ a r hr hDφ
  have hCA : 2*‖E‖*(‖R‖*A)≤C := by dsimp only [C];nlinarith only [hV,norm_nonneg E]
  have hCV : 2*‖E‖*V≤C := by dsimp only [C];nlinarith only [hRA,norm_nonneg E]
  let X := Real.sqrt (∫x in ball a r,hsNormSq (DP x))*r^(1-(n : ℝ)/s)
  let Y := r^((n : ℝ)/2-(n : ℝ)/s)
  have hX : 0≤X := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hr.le _)
  have hY : 0≤Y := Real.rpow_nonneg hr.le _
  refine ⟨hI,(fun j=>(hEach j).1),?_⟩
  intro j
  have HE := (hEach j).2.2
  rw [abs_of_nonneg hH] at HE
  calc
    _≤2*‖E‖*(‖R‖*H*Real.sqrt (∫x in ball a r,hsNormSq (DP x))+
        Real.sqrt (∫x in ball a r,hsNormSq (Dφ x))) := HE
    _≤2*‖E‖*(‖R‖*H*Real.sqrt (∫x in ball a r,hsNormSq (DP x))+V*Y*J) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hGrad) (mul_nonneg (by norm_num) (norm_nonneg E))
    _=(2*‖E‖*(‖R‖*A))*(X*J)+(2*‖E‖*V)*(Y*J) := by dsimp only [H,X,Y];ring
    _≤C*(X*J)+C*(Y*J) := add_le_add
      (mul_le_mul_of_nonneg_right hCA (mul_nonneg hX hJ))
      (mul_le_mul_of_nonneg_right hCV (mul_nonneg hY hJ))
    _=C*(X+Y)*J := by ring

end StationaryHarmonicMaps.Analysis

end
