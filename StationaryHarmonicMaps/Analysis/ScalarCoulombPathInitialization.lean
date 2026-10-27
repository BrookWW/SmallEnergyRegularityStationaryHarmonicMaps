module

public import StationaryHarmonicMaps.Analysis.ScalarCoulombPathClosedness
public import HarmonicMaps.Analysis.SobolevPoincare
public import StationaryHarmonicMaps.Analysis.CriticalMorreyMeanOscillation
public import StationaryHarmonicMaps.Analysis.NeumannGradientSpace

/-!
# The actual initial special-orthogonal frame of the scalar path

The encoded identity and its zero weak gradient are genuine native data.
At parameter zero the original scalar connection and transformed natural
connection vanish literally, including in zero target dimension.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The actual encoded identity supplies the zero-parameter native SO
frame, its two complete zero critical quantities and all natural tests. -/
theorem identity_frame_zero_scalar_connection_unitBall {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T)
    (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q)) :
    let p := fun _ : Domain n=>E 1
    let Dp := fun (_ : Domain n) (_ : Fin n)=>(0 : Ambient (q*q))
    let Z := fun x i=>star (R (p x))*R (Dp x i)+star (R (p x))*((0 : ℝ) • A x i)*R (p x)
    MemW12 (ballDomain (0 : Domain n) 1) p Dp ∧
    (∀x,star (R (p x))*R (p x)=1 ∧ (R (p x)).det=1) ∧
    criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)=0 ∧
    criticalGradientMorreySquare (fun x i=>E (Z x i)) (ball (0 : Domain n) 1)=0 ∧
    (∀x i,Z x i=0) ∧
    ∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
      MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
      IntegrableOn (fun x=>∑i : Fin n,inner ℝ (E (Z x i)) (Dψ x i)) (ball (0 : Domain n) 1) volume ∧
      (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (E (Z x i)) (Dψ x i))=0 := by
  intro p Dp Z
  have hp : MemW12 (ballDomain (0 : Domain n) 1) p Dp := by
    simpa only [fderiv_fun_const,zero_apply,Pi.zero_apply] using
      memW12_ball_of_ambient_c1 (0 : Domain n) 1 (fun _ : Domain n=>E (1 : Ambient q →L[ℝ] Ambient q)) contDiff_const
  have hOrth (x : Domain n) : star (R (p x))*R (p x)=1 ∧ (R (p x)).det=1 := by
    constructor
    · simp only [p,hRE,star_one,one_mul]
    · change (R (E 1)).det=1
      rw [hRE]
      exact map_one (LinearMap.det : (Ambient q →ₗ[ℝ] Ambient q) →* ℝ)
  have hDZero : criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)=0 := by
    apply le_antisymm
    · unfold criticalGradientMorreySquare
      refine iSup_le fun _=>iSup_le fun _=>?_
      simp only [dirichletEnergy,Dp,hsNormSq,norm_zero,
        zero_pow (by decide : (2 : ℕ)≠0),Finset.sum_const_zero,ENNReal.ofReal_zero,lintegral_zero,mul_zero,le_refl]
    · exact zero_le
  have hZZero (x : Domain n) (i : Fin n) : Z x i=0 := by
    have hz : (0 : ℝ) • A x i=0 := by
      ext v
      simp only [smul_apply,zero_smul,zero_apply]
    change star (R (E 1))*R 0+star (R (E 1))*((0 : ℝ) • A x i)*R (E 1)=0
    simp only [hRE,map_zero,hz,mul_zero,zero_mul,add_zero]
  have hEZ : (fun x i=>E (Z x i))=Dp := funext fun x=>funext fun i=>by rw [hZZero,map_zero]
  refine ⟨hp,hOrth,hDZero,by rw [hEZ,hDZero],hZZero,?_⟩
  intro ψ Dψ _hψ
  simp only [hZZero,map_zero,inner_zero_left,Finset.sum_const_zero,integral_zero]
  exact ⟨integrable_zero _ _ _,True.intro⟩

end StationaryHarmonicMaps.Analysis

end
