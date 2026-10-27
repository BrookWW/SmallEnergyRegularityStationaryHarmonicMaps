module

public import StationaryHarmonicMaps.Analysis.NativeMorreyCoefficientActionExistence
import StationaryHarmonicMaps.Analysis.CriticalMorreyIntegralBounds

/-!
# Contractive inclusion of the actual Morrey coefficient spaces

On the unit ball, stronger nonnegative exponents control weaker ones with
constant one. Small queries compare their actual radius powers; large
queries use the original query (0,1) for the whole energy. The inclusion
preserves the same full-HS L2 class on every original representative.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

noncomputable section

namespace StationaryHarmonicMaps.Analysis

private theorem lowered_raw_growth {n q : ℕ} (μ ν : ℝ) (hμ : 0≤μ) (hμν : μ≤ν)
    (Fr : Domain n→Gradient n q)
    (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (F : MorreyCoefficientSpace n q ν)
    (hF : morreyCoefficientRecover (n:=n) (q:=q) ν F=hsUnitBallL2Class Fr hFr) :
    ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Fr x))≤‖F‖^2*r^μ := by
  have hGrowth := morreyCoefficient_power_growth (n:=n) (q:=q) ν Fr hFr F hF
  have hGlobal : (∫x in ball (0 : Domain n) 1,hsNormSq (Fr x))≤‖F‖^2 := by
    simpa only [inter_self,Real.one_rpow,mul_one] using
      hGrowth 0 (mem_ball_self (by norm_num)) 1 (by norm_num)
  have hI : IntegrableOn (fun x=>hsNormSq (Fr x)) (ball (0 : Domain n) 1) volume :=
    integrable_hsNormSq_of_columns Fr hFr
  intro a ha r hr
  by_cases hrOne : r≤1
  · exact (hGrowth a ha r hr).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hr hrOne hμν) (sq_nonneg _))
  · have hLarge : (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Fr x))≤
        ∫x in ball (0 : Domain n) 1,hsNormSq (Fr x) :=
      setIntegral_mono_set hI (Eventually.of_forall fun _=>hsNormSq_nonneg _)
        (Eventually.of_forall fun _ hx=>hx.2)
    exact (hLarge.trans hGlobal).trans (le_mul_of_one_le_right (sq_nonneg _)
      (Real.one_le_rpow (not_le.mp hrOne).le hμ))

private theorem lowered_class_norm_le {n q : ℕ} (μ : ℝ)
    (Fr : Domain n→Gradient n q)
    (hFr : ∀i,MemLp (fun x=>Fr x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (G : MorreyCoefficientSpace n q μ)
    (hG : morreyCoefficientRecover (n:=n) (q:=q) μ G=hsUnitBallL2Class Fr hFr)
    (K : ℝ) (hK : 0≤K)
    (hGrowth : ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Fr x))≤K^2*r^μ) : ‖G‖≤K := by
  have hSquare : ‖G‖^2≤K^2 := by
    rw [morreyCoefficient_norm_sq μ Fr hFr G hG]
    have hNe : {e : ℝ | ∃a∈ball (0 : Domain n) 1,∃r : ℝ,0<r ∧
        e=r^(-μ)*(∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Fr x))}.Nonempty :=
      ⟨(1 : ℝ)^(-μ)*(∫x in ball (0 : Domain n) 1∩ball (0 : Domain n) 1,hsNormSq (Fr x)),
        0,mem_ball_self (by norm_num),1,by norm_num,rfl⟩
    apply csSup_le hNe
    rintro _ ⟨a,ha,r,hr,rfl⟩
    have hCancel : r^(-μ)*r^μ=1 := by rw [←Real.rpow_add hr,neg_add_cancel,Real.rpow_zero]
    exact (mul_le_mul_of_nonneg_left (hGrowth a ha r hr) (Real.rpow_nonneg hr.le (-μ))).trans_eq
      (by rw [mul_left_comm,hCancel,mul_one])
  exact (sq_le_sq₀ (norm_nonneg G) hK).mp hSquare

private theorem exists_unique_lowered_class {n q : ℕ} (μ ν : ℝ) (hμ : 0≤μ) (hμν : μ≤ν)
    (F : MorreyCoefficientSpace n q ν) :
    ∃! G : MorreyCoefficientSpace n q μ,
      morreyCoefficientRecover (n:=n) (q:=q) μ G=morreyCoefficientRecover (n:=n) (q:=q) ν F ∧
      ‖G‖≤‖F‖ := by
  obtain ⟨Fr,hFr,hF,_hOriginalGrowth⟩ := exists_raw_field_of_morreyCoefficient (n:=n) (q:=q) ν F
  have hGrowth := lowered_raw_growth μ ν hμ hμν Fr hFr F hF
  obtain ⟨G,hG,_hUnique⟩ := (existsUnique_morreyCoefficient_iff_power_growth (n:=n) (q:=q) μ Fr hFr).mpr
    ⟨‖F‖^2,sq_nonneg _,hGrowth⟩
  refine ⟨G,⟨hG.trans hF.symm,lowered_class_norm_le μ Fr hFr G hG ‖F‖ (norm_nonneg _) hGrowth⟩,?_⟩
  rintro H ⟨hH,_hHNorm⟩
  apply morreyCoefficientRecover_injective (n:=n) (q:=q) μ
  exact hH.trans (hF.trans hG.symm)

private def loweredClass {n q : ℕ} (μ ν : ℝ) (hμ : 0≤μ) (hμν : μ≤ν)
    (F : MorreyCoefficientSpace n q ν) : MorreyCoefficientSpace n q μ :=
  (exists_unique_lowered_class μ ν hμ hμν F).choose

private theorem loweredClass_recover {n q : ℕ} (μ ν : ℝ) (hμ : 0≤μ) (hμν : μ≤ν)
    (F : MorreyCoefficientSpace n q ν) :
    morreyCoefficientRecover (n:=n) (q:=q) μ (loweredClass μ ν hμ hμν F)=
      morreyCoefficientRecover (n:=n) (q:=q) ν F :=
  (exists_unique_lowered_class μ ν hμ hμν F).choose_spec.1.1

private theorem loweredClass_norm_le {n q : ℕ} (μ ν : ℝ) (hμ : 0≤μ) (hμν : μ≤ν)
    (F : MorreyCoefficientSpace n q ν) : ‖loweredClass μ ν hμ hμν F‖≤‖F‖ :=
  (exists_unique_lowered_class μ ν hμ hμν F).choose_spec.1.2

private theorem loweredClass_add {n q : ℕ} (μ ν : ℝ) (hμ : 0≤μ) (hμν : μ≤ν)
    (F G : MorreyCoefficientSpace n q ν) :
    loweredClass μ ν hμ hμν (F+G)=loweredClass μ ν hμ hμν F+loweredClass μ ν hμ hμν G := by
  apply morreyCoefficientRecover_injective (n:=n) (q:=q) μ
  calc
    _=morreyCoefficientRecover (n:=n) (q:=q) ν (F+G) := loweredClass_recover μ ν hμ hμν (F+G)
    _=morreyCoefficientRecover (n:=n) (q:=q) ν F+morreyCoefficientRecover (n:=n) (q:=q) ν G :=
      (morreyCoefficientRecover (n:=n) (q:=q) ν).map_add F G
    _=morreyCoefficientRecover (n:=n) (q:=q) μ (loweredClass μ ν hμ hμν F)+
        morreyCoefficientRecover (n:=n) (q:=q) μ (loweredClass μ ν hμ hμν G) :=
      congrArg₂ (fun A B : HSUnitBallL2 n q=>A+B)
        (loweredClass_recover μ ν hμ hμν F).symm (loweredClass_recover μ ν hμ hμν G).symm
    _=_ := ((morreyCoefficientRecover (n:=n) (q:=q) μ).map_add _ _).symm

private theorem loweredClass_smul {n q : ℕ} (μ ν : ℝ) (hμ : 0≤μ) (hμν : μ≤ν)
    (c : ℝ) (F : MorreyCoefficientSpace n q ν) :
    loweredClass μ ν hμ hμν (c • F)=c • loweredClass μ ν hμ hμν F := by
  apply morreyCoefficientRecover_injective (n:=n) (q:=q) μ
  calc
    _=morreyCoefficientRecover (n:=n) (q:=q) ν (c • F) := loweredClass_recover μ ν hμ hμν (c • F)
    _=c • morreyCoefficientRecover (n:=n) (q:=q) ν F :=
      (morreyCoefficientRecover (n:=n) (q:=q) ν).map_smul c F
    _=c • morreyCoefficientRecover (n:=n) (q:=q) μ (loweredClass μ ν hμ hμν F) :=
      congrArg (fun A : HSUnitBallL2 n q=>c • A) (loweredClass_recover μ ν hμ hμν F).symm
    _=_ := ((morreyCoefficientRecover (n:=n) (q:=q) μ).map_smul c _).symm

private def loweringLinearMap (n q : ℕ) (μ ν : ℝ) (hμ : 0≤μ) (hμν : μ≤ν) :
    MorreyCoefficientSpace n q ν→ₗ[ℝ]MorreyCoefficientSpace n q μ :=
  { toFun := loweredClass μ ν hμ hμν
    map_add' := loweredClass_add μ ν hμ hμν
    map_smul' := fun c F=>by simpa only [RingHom.id_apply] using loweredClass_smul μ ν hμ hμν c F }

/-- On the actual unit-ball Morrey carriers, lowering a nonnegative exponent
is a unique contraction preserving the very same full-HS L2 coefficient. -/
theorem existsUnique_morrey_coefficient_exponent_inclusion
    (n q : ℕ) (μ ν : ℝ) (hμ : 0≤μ) (hμν : μ≤ν) :
    ∃! T : MorreyCoefficientSpace n q ν→L[ℝ]MorreyCoefficientSpace n q μ,
      ‖T‖≤1 ∧ ∀F : MorreyCoefficientSpace n q ν,
        morreyCoefficientRecover (n:=n) (q:=q) μ (T F)=morreyCoefficientRecover (n:=n) (q:=q) ν F := by
  let L : MorreyCoefficientSpace n q ν→ₗ[ℝ]MorreyCoefficientSpace n q μ :=
    loweringLinearMap n q μ ν hμ hμν
  have hBound (F : MorreyCoefficientSpace n q ν) : ‖L F‖≤1*‖F‖ := by
    change ‖loweredClass (n:=n) (q:=q) μ ν hμ hμν F‖≤1*‖F‖
    rw [one_mul]
    exact loweredClass_norm_le μ ν hμ hμν F
  let T : MorreyCoefficientSpace n q ν→L[ℝ]MorreyCoefficientSpace n q μ := L.mkContinuous 1 hBound
  have hNorm : ‖T‖≤1 := L.mkContinuous_norm_le (by norm_num) hBound
  refine ⟨T,⟨hNorm,?_⟩,?_⟩
  · intro F
    exact loweredClass_recover μ ν hμ hμν F
  · rintro S ⟨_hSNorm,hS⟩
    apply ContinuousLinearMap.ext
    intro F
    apply morreyCoefficientRecover_injective (n:=n) (q:=q) μ
    exact (hS F).trans (loweredClass_recover μ ν hμ hμν F).symm

end StationaryHarmonicMaps.Analysis

end
