module

public import StationaryHarmonicMaps.Analysis.L2Indicator
public import StationaryHarmonicMaps.Analysis.CompatibleBoundedFamilies
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtEncoding

/-!
# Actual all-query Morrey coefficient Banach space

All positive-radius truncated unit-ball queries give weighted indicators of
the same full-HS L2 class. The fixed query (0,2) recovers that class explicitly.
Compatible bounded families form a Banach space. Actual raw coefficient fields
with finite full power growth have exactly one such class, and every class
has actual raw L2 columns with the same query growth. Its squared norm is
the literal normalized-energy supremum, on this actual finite carrier.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace StationaryHarmonicMaps.Analysis

@[expose] def UnitBallMorreyQuery (n : ℕ) := (ball (0 : Domain n) 1) × PositiveRadius

@[expose] def unitBallMorreyAnchor (n : ℕ) : UnitBallMorreyQuery n :=
  (⟨0,mem_ball_self (by norm_num)⟩,⟨2,by norm_num⟩)

abbrev HSUnitBallL2 (n q : ℕ) := Lp (Ambient (n*q)) 2 (volume.restrict (ball (0 : Domain n) 1))

@[expose] def unitBallMorreyQueryMap {n q : ℕ} (ν : ℝ) (z : UnitBallMorreyQuery n) : HSUnitBallL2 n q →L[ℝ] HSUnitBallL2 n q :=
  (z.2.val^(-ν/2)) • l2Indicator (volume.restrict (ball (0 : Domain n) 1))
    (ball z.1.val z.2.val) measurableSet_ball

@[expose] def morreyCoefficientSubmodule (n q : ℕ) (ν : ℝ) :
    Submodule ℝ (lp (fun _ : UnitBallMorreyQuery n=>HSUnitBallL2 n q) ∞) :=
  compatibleBoundedFamilies (unitBallMorreyQueryMap ν) (unitBallMorreyAnchor n) ((2 : ℝ)^(ν/2))

abbrev MorreyCoefficientSpace (n q : ℕ) (ν : ℝ) := ↥(morreyCoefficientSubmodule n q ν)

instance morreyCoefficientSpace_completeSpace (n q : ℕ) (ν : ℝ) : CompleteSpace (MorreyCoefficientSpace n q ν) := compatibleBoundedFamilies_completeSpace _ _ _

@[expose] def morreyCoefficientRecover {n q : ℕ} (ν : ℝ) : MorreyCoefficientSpace n q ν →L[ℝ] HSUnitBallL2 n q :=
  (((2 : ℝ)^(ν/2)) • lp.evalCLM ℝ (fun _ : UnitBallMorreyQuery n=>HSUnitBallL2 n q) ∞ (unitBallMorreyAnchor n)).comp
    (morreyCoefficientSubmodule n q ν).subtypeL

theorem unitBallMorreyQueryMap_anchor {n q : ℕ} (ν : ℝ) (F : HSUnitBallL2 n q) :
    unitBallMorreyQueryMap ν (unitBallMorreyAnchor n) F=((2 : ℝ)^(-ν/2)) • F := by
  change ((2 : ℝ)^(-ν/2)) • l2Indicator (volume.restrict (ball (0 : Domain n) 1))
    (ball (0 : Domain n) 2) measurableSet_ball F=((2 : ℝ)^(-ν/2)) • F
  congr 1
  apply Lp.ext
  change (l2IndicatorValue (volume.restrict (ball (0 : Domain n) 1))
    (ball (0 : Domain n) 2) measurableSet_ball F : Domain n→Ambient (n*q))=ᵐ[_]F
  filter_upwards [l2IndicatorValue_ae (volume.restrict (ball (0 : Domain n) 1))
    (ball (0 : Domain n) 2) measurableSet_ball F,ae_restrict_mem measurableSet_ball] with x hx hxB
  rw [hx,indicator_of_mem (ball_subset_ball (by norm_num : (1 : ℝ)≤2) hxB)]

theorem morreyCoefficientRecover_injective {n q : ℕ} (ν : ℝ) : Function.Injective (morreyCoefficientRecover (n:=n) (q:=q) ν) :=
  compatibleBoundedFamilies_recovery_injective (unitBallMorreyQueryMap ν) (unitBallMorreyAnchor n) ((2 : ℝ)^(ν/2))

@[expose] def morreyCoefficientFromBounded {n q : ℕ} (ν : ℝ) (F : HSUnitBallL2 n q)
    (hF : BddAbove (Set.range fun z : UnitBallMorreyQuery n=>‖unitBallMorreyQueryMap ν z F‖)) : MorreyCoefficientSpace n q ν := by
  let Z : lp (fun _ : UnitBallMorreyQuery n=>HSUnitBallL2 n q) ∞ := ⟨fun z=>unitBallMorreyQueryMap ν z F,memℓp_infty hF⟩
  have hRecover : (2 : ℝ)^(ν/2) • Z (unitBallMorreyAnchor n)=F := by
    change (2 : ℝ)^(ν/2) • unitBallMorreyQueryMap ν (unitBallMorreyAnchor n) F=F
    rw [unitBallMorreyQueryMap_anchor,smul_smul,← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    have he : ν/2+-ν/2=0 := by ring
    rw [he,Real.rpow_zero,one_smul]
  refine ⟨Z,?_⟩
  change ∀i,Z i=unitBallMorreyQueryMap ν i ((2 : ℝ)^(ν/2) • Z (unitBallMorreyAnchor n))
  intro i
  rw [hRecover]

theorem morreyCoefficientRecover_fromBounded {n q : ℕ} (ν : ℝ) (F : HSUnitBallL2 n q)
    (hF : BddAbove (Set.range fun z : UnitBallMorreyQuery n=>‖unitBallMorreyQueryMap ν z F‖)) : morreyCoefficientRecover ν (morreyCoefficientFromBounded ν F hF)=F := by
  change (2 : ℝ)^(ν/2) • unitBallMorreyQueryMap ν (unitBallMorreyAnchor n) F=F
  rw [unitBallMorreyQueryMap_anchor,smul_smul,← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
  have he : ν/2+-ν/2=0 := by ring
  rw [he,Real.rpow_zero,one_smul]

theorem morreyCoefficient_queries_bdd {n q : ℕ} (ν : ℝ) (Z : MorreyCoefficientSpace n q ν) :
    BddAbove (Set.range fun z : UnitBallMorreyQuery n=>‖unitBallMorreyQueryMap ν z (morreyCoefficientRecover ν Z)‖) := by
  refine ⟨‖Z.val‖,?_⟩
  rintro _ ⟨i,rfl⟩
  have hZi := Z.property i
  change Z.val i=unitBallMorreyQueryMap ν i (morreyCoefficientRecover ν Z) at hZi
  change ‖unitBallMorreyQueryMap ν i (morreyCoefficientRecover ν Z)‖≤‖Z.val‖
  rw [←hZi]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero Z.val i

theorem morreyCoefficientFromBounded_recover {n q : ℕ} (ν : ℝ) (Z : MorreyCoefficientSpace n q ν) :
    morreyCoefficientFromBounded ν (morreyCoefficientRecover ν Z) (morreyCoefficient_queries_bdd ν Z)=Z := by
  apply morreyCoefficientRecover_injective ν
  exact morreyCoefficientRecover_fromBounded ν (morreyCoefficientRecover ν Z) (morreyCoefficient_queries_bdd ν Z)

theorem existsUnique_morreyCoefficient_iff_bounded_queries {n q : ℕ} (ν : ℝ) (F : HSUnitBallL2 n q) :
    (∃! Z : MorreyCoefficientSpace n q ν,morreyCoefficientRecover ν Z=F) ↔
      BddAbove (Set.range fun z : UnitBallMorreyQuery n=>‖unitBallMorreyQueryMap ν z F‖) := by
  constructor
  · rintro ⟨Z,hZ,_⟩
    use ‖Z.val‖
    rintro _ ⟨i,rfl⟩
    have hZi := Z.property i
    change Z.val i=unitBallMorreyQueryMap ν i (morreyCoefficientRecover ν Z) at hZi
    rw [hZ] at hZi
    change ‖unitBallMorreyQueryMap ν i F‖≤‖Z.val‖
    rw [←hZi]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero Z.val i
  · intro hF
    refine ⟨morreyCoefficientFromBounded ν F hF,morreyCoefficientRecover_fromBounded ν F hF,?_⟩
    intro Z hZ
    apply morreyCoefficientRecover_injective ν
    rw [hZ,morreyCoefficientRecover_fromBounded]

theorem unitBallMorreyQueryMap_norm_sq {n q : ℕ} (ν : ℝ) (z : UnitBallMorreyQuery n) (F : HSUnitBallL2 n q) :
    ‖unitBallMorreyQueryMap ν z F‖^2=z.2.val^(-ν)*(∫x in ball z.1.val z.2.val∩ball (0 : Domain n) 1,‖F x‖^2) := by
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let S := ball z.1.val z.2.val
  have hSq : (z.2.val^(-ν/2))^2=z.2.val^(-ν) := by
    rw [←Real.rpow_mul_natCast z.2.property.le]
    congr 1
    norm_num
  have hPoint : (fun x=>‖l2IndicatorValue μ S measurableSet_ball F x‖^2)=ᵐ[μ]
      S.indicator (fun x=>‖F x‖^2) := by
    filter_upwards [l2IndicatorValue_ae μ S measurableSet_ball F] with x hx
    rw [hx]
    by_cases hs : x∈S
    · simp only [indicator_of_mem hs]
    · simp only [indicator_of_notMem hs,norm_zero,zero_pow (by decide : (2 : ℕ)≠0)]
  change ‖z.2.val^(-ν/2) • l2IndicatorValue μ S measurableSet_ball F‖^2=_
  rw [norm_smul,Real.norm_of_nonneg (Real.rpow_nonneg z.2.property.le _),mul_pow,hSq,l2_euclidean_norm_sq]
  congr 1
  rw [integral_congr_ae hPoint,integral_indicator measurableSet_ball]
  rw [Measure.restrict_restrict measurableSet_ball]

@[expose] def hsFlatten {n q : ℕ} (F : Domain n→Gradient n q) : Domain n→Ambient (n*q) :=
  fun x=>WithLp.toLp 2 (fun k : Fin (n*q)=>F x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

@[expose] def hsUnitBallL2Class {n q : ℕ} (F : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1))) : HSUnitBallL2 n q :=
  (StationaryHarmonicMaps.Analysis.memLp_hs_flatten F hF).toLp (hsFlatten F)

theorem hsUnitBallL2Class_query_norm_sq {n q : ℕ} (ν : ℝ) (z : UnitBallMorreyQuery n)
    (F : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    ‖unitBallMorreyQueryMap ν z (hsUnitBallL2Class F hF)‖^2=
      z.2.val^(-ν)*(∫x in ball z.1.val z.2.val∩ball (0 : Domain n) 1,hsNormSq (F x)) := by
  rw [unitBallMorreyQueryMap_norm_sq]
  congr 1
  apply integral_congr_ae
  have hAE : (hsUnitBallL2Class F hF : Domain n→Ambient (n*q))=ᵐ[volume.restrict (ball (0 : Domain n) 1)]hsFlatten F :=
    MemLp.coeFn_toLp (StationaryHarmonicMaps.Analysis.memLp_hs_flatten F hF)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_right hAE] with x hx
  rw [hx]
  exact StationaryHarmonicMaps.Analysis.hs_flatten_norm_sq (F x)

theorem bdd_morreyQueries_iff_power_growth {n q : ℕ} (ν : ℝ) (F : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    BddAbove (Set.range fun z : UnitBallMorreyQuery n=>‖unitBallMorreyQueryMap ν z (hsUnitBallL2Class F hF)‖) ↔
      ∃K : ℝ,0≤K ∧ ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))≤K*r^ν := by
  constructor
  · rintro ⟨C,hC⟩
    refine ⟨|C|^2,sq_nonneg _,?_⟩
    intro a ha r hr
    let z : UnitBallMorreyQuery n := (⟨a,ha⟩,⟨r,hr⟩)
    have hNorm : ‖unitBallMorreyQueryMap ν z (hsUnitBallL2Class F hF)‖≤|C| := (hC ⟨z,rfl⟩).trans (le_abs_self C)
    have hSq := pow_le_pow_left₀ (norm_nonneg _) hNorm 2
    rw [hsUnitBallL2Class_query_norm_sq] at hSq
    change r^(-ν)*(∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))≤|C|^2 at hSq
    have hCancel : r^ν*r^(-ν)=1 := by rw [←Real.rpow_add hr,add_neg_cancel,Real.rpow_zero]
    calc
      _=r^ν*(r^(-ν)*(∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))) := by rw [←mul_assoc,hCancel,one_mul]
      _≤r^ν*|C|^2 := mul_le_mul_of_nonneg_left hSq (Real.rpow_nonneg hr.le _)
      _=_ := mul_comm _ _
  · rintro ⟨K,hK,H⟩
    refine ⟨Real.sqrt K,?_⟩
    rintro _ ⟨z,rfl⟩
    have hGrowth := H z.1.val z.1.property z.2.val z.2.property
    have hCancel : z.2.val^(-ν)*z.2.val^ν=1 := by
      rw [←Real.rpow_add z.2.property,neg_add_cancel,Real.rpow_zero]
    have hSq : ‖unitBallMorreyQueryMap ν z (hsUnitBallL2Class F hF)‖^2≤K := by
      rw [hsUnitBallL2Class_query_norm_sq]
      calc
        _≤z.2.val^(-ν)*(K*z.2.val^ν) := mul_le_mul_of_nonneg_left hGrowth (Real.rpow_nonneg z.2.property.le _)
        _=K := by rw [mul_left_comm,hCancel,mul_one]
    have hRoot := Real.sq_sqrt hK
    have hn := norm_nonneg (unitBallMorreyQueryMap ν z (hsUnitBallL2Class F hF))
    have hs := Real.sqrt_nonneg K
    change ‖unitBallMorreyQueryMap ν z (hsUnitBallL2Class F hF)‖≤Real.sqrt K
    nlinarith only [hSq,hRoot,hn,hs]

theorem existsUnique_morreyCoefficient_iff_power_growth {n q : ℕ} (ν : ℝ) (F : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    (∃! Z : MorreyCoefficientSpace n q ν,morreyCoefficientRecover ν Z=hsUnitBallL2Class F hF) ↔
      ∃K : ℝ,0≤K ∧ ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))≤K*r^ν :=
  (existsUnique_morreyCoefficient_iff_bounded_queries ν (hsUnitBallL2Class F hF)).trans (bdd_morreyQueries_iff_power_growth ν F hF)

theorem morreyCoefficient_norm_sq {n q : ℕ} (ν : ℝ) (F : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (Z : MorreyCoefficientSpace n q ν) (hZ : morreyCoefficientRecover ν Z=hsUnitBallL2Class F hF) :
    ‖Z‖^2=sSup {e : ℝ | ∃a∈ball (0 : Domain n) 1,∃r : ℝ,0<r ∧
      e=r^(-ν)*(∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))} := by
  letI : Nonempty (UnitBallMorreyQuery n) := ⟨unitBallMorreyAnchor n⟩
  have hFamily (i : UnitBallMorreyQuery n) : ‖Z.val i‖^2=
      i.2.val^(-ν)*(∫x in ball i.1.val i.2.val∩ball (0 : Domain n) 1,hsNormSq (F x)) := by
    have hZi := Z.property i
    change Z.val i=unitBallMorreyQueryMap ν i (morreyCoefficientRecover ν Z) at hZi
    rw [hZ] at hZi
    rw [hZi,hsUnitBallL2Class_query_norm_sq]
  have hSet : Set.range (fun i : UnitBallMorreyQuery n=>‖Z.val i‖^2)=
      {e : ℝ | ∃a∈ball (0 : Domain n) 1,∃r : ℝ,0<r ∧
        e=r^(-ν)*(∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))} := by
    ext e
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.1.val,i.1.property,i.2.val,i.2.property,hFamily i⟩
    · rintro ⟨a,ha,r,hr,he⟩
      exact ⟨(⟨a,ha⟩,⟨r,hr⟩),(hFamily (⟨a,ha⟩,⟨r,hr⟩)).trans he.symm⟩
  have hSup := (lp_norm_sq_isLUB Z.val).csSup_eq (Set.range_nonempty _)
  rw [hSet] at hSup
  exact hSup.symm

theorem morreyCoefficient_power_growth {n q : ℕ} (ν : ℝ) (F : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (Z : MorreyCoefficientSpace n q ν) (hZ : morreyCoefficientRecover ν Z=hsUnitBallL2Class F hF) :
    ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
      (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))≤‖Z‖^2*r^ν := by
  intro a ha r hr
  let z : UnitBallMorreyQuery n := (⟨a,ha⟩,⟨r,hr⟩)
  have hZi := Z.property z
  change Z.val z=unitBallMorreyQueryMap ν z (morreyCoefficientRecover ν Z) at hZi
  rw [hZ] at hZi
  have hNorm : ‖unitBallMorreyQueryMap ν z (hsUnitBallL2Class F hF)‖≤‖Z‖ := by
    rw [←hZi]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero Z.val z
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  rw [hsUnitBallL2Class_query_norm_sq] at hSq
  change r^(-ν)*(∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))≤‖Z‖^2 at hSq
  have hCancel : r^ν*r^(-ν)=1 := by rw [←Real.rpow_add hr,add_neg_cancel,Real.rpow_zero]
  calc
    _=r^ν*(r^(-ν)*(∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))) := by rw [←mul_assoc,hCancel,one_mul]
    _≤r^ν*‖Z‖^2 := mul_le_mul_of_nonneg_left hSq (Real.rpow_nonneg hr.le _)
    _=_ := mul_comm _ _

theorem exists_raw_field_of_morreyCoefficient {n q : ℕ} (ν : ℝ) (Z : MorreyCoefficientSpace n q ν) :
    ∃(F : Domain n→Gradient n q)
      (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1))),
      morreyCoefficientRecover ν Z=hsUnitBallL2Class F hF ∧
      ∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
        (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (F x))≤‖Z‖^2*r^ν := by
  let G : HSUnitBallL2 n q := morreyCoefficientRecover ν Z
  let L₀ : Fin n→Ambient (n*q)→ₗ[ℝ]Ambient q := fun i=>
    { toFun := fun z=>WithLp.toLp 2 (fun j : Fin q=>z (finProdFinEquiv (i,j)))
      map_add' := fun z w=>by ext j;rfl
      map_smul' := fun c z=>by ext j;rfl }
  let L : Fin n→Ambient (n*q)→L[ℝ]Ambient q := fun i=>(L₀ i).toContinuousLinearMap
  let F : Domain n→Gradient n q := fun x i=>L i (G x)
  have hF (i : Fin n) : MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1)) :=
    (L i).lipschitz.comp_memLp (map_zero (L i)) (Lp.memLp G)
  have hFlatten : hsFlatten F=(G : Domain n→Ambient (n*q)) := by
    funext x
    ext k
    change G x (finProdFinEquiv (finProdFinEquiv.symm k))=G x k
    rw [finProdFinEquiv.apply_symm_apply]
  have hClass : hsUnitBallL2Class F hF=G := by
    apply Lp.ext
    have hAE : (hsUnitBallL2Class F hF : Domain n→Ambient (n*q))=ᵐ[volume.restrict (ball (0 : Domain n) 1)]hsFlatten F :=
      MemLp.coeFn_toLp (StationaryHarmonicMaps.Analysis.memLp_hs_flatten F hF)
    exact hAE.trans (Eventually.of_forall fun x=>congrFun hFlatten x)
  exact ⟨F,hF,hClass.symm,morreyCoefficient_power_growth ν F hF Z hClass.symm⟩

theorem hsUnitBallL2Class_eq_iff_ae {n q : ℕ} (F G : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hG : ∀i,MemLp (fun x=>G x i) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    hsUnitBallL2Class F hF=hsUnitBallL2Class G hG ↔
      ∀i,(fun x=>F x i)=ᵐ[volume.restrict (ball (0 : Domain n) 1)](fun x=>G x i) := by
  have hEq : hsUnitBallL2Class F hF=hsUnitBallL2Class G hG ↔
      hsFlatten F=ᵐ[volume.restrict (ball (0 : Domain n) 1)]hsFlatten G :=
    MemLp.toLp_eq_toLp_iff (StationaryHarmonicMaps.Analysis.memLp_hs_flatten F hF)
      (StationaryHarmonicMaps.Analysis.memLp_hs_flatten G hG)
  rw [hEq]
  constructor
  · intro H i
    filter_upwards [H] with x hx
    ext j
    have hk := congrArg (fun z : Ambient (n*q)=>z (finProdFinEquiv (i,j))) hx
    change F x (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2=G x
      (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 at hk
    simpa only [finProdFinEquiv.symm_apply_apply] using hk
  · intro H
    filter_upwards [ae_all_iff.mpr H] with x hx
    ext k
    change F x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2=
      G x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    exact congrArg (fun z : Ambient q=>z (finProdFinEquiv.symm k).2) (hx _)

theorem hsUnitBallL2Class_ae {n q : ℕ} (F : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    (hsUnitBallL2Class F hF : Domain n→Ambient (n*q))=ᵐ[volume.restrict (ball (0 : Domain n) 1)]hsFlatten F := by
  change (((StationaryHarmonicMaps.Analysis.memLp_hs_flatten F hF).toLp (hsFlatten F)) : Domain n→Ambient (n*q))=ᵐ[_]hsFlatten F
  exact MemLp.coeFn_toLp _

theorem hsUnitBallL2Class_add {n q : ℕ} (F G : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hG : ∀i,MemLp (fun x=>G x i) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    hsUnitBallL2Class (fun x i=>F x i+G x i) (fun i=>(hF i).add (hG i))=hsUnitBallL2Class F hF+hsUnitBallL2Class G hG := by
  apply Lp.ext
  filter_upwards [hsUnitBallL2Class_ae (fun x i=>F x i+G x i) (fun i=>(hF i).add (hG i)),
    hsUnitBallL2Class_ae F hF,hsUnitBallL2Class_ae G hG,Lp.coeFn_add (hsUnitBallL2Class F hF) (hsUnitBallL2Class G hG)] with x hx hfx hgx hs
  rw [hx,hs]
  simp only [Pi.add_apply]
  rw [hfx,hgx]
  ext k
  rfl

theorem hsUnitBallL2Class_smul {n q : ℕ} (c : ℝ) (F : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1))) :
    hsUnitBallL2Class (fun x i=>c • F x i) (fun i=>(hF i).const_smul c)=c • hsUnitBallL2Class F hF := by
  apply Lp.ext
  filter_upwards [hsUnitBallL2Class_ae (fun x i=>c • F x i) (fun i=>(hF i).const_smul c),
    hsUnitBallL2Class_ae F hF,Lp.coeFn_smul c (hsUnitBallL2Class F hF)] with x hx hfx hs
  rw [hx,hs]
  simp only [Pi.smul_apply]
  rw [hfx]
  ext k
  rfl

theorem morreyCoefficientRecover_add_raw {n q : ℕ} (ν : ℝ) (F G : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hG : ∀i,MemLp (fun x=>G x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (Z Y : MorreyCoefficientSpace n q ν) (hZ : morreyCoefficientRecover ν Z=hsUnitBallL2Class F hF) (hY : morreyCoefficientRecover ν Y=hsUnitBallL2Class G hG) :
    morreyCoefficientRecover ν (Z+Y)=hsUnitBallL2Class (fun x i=>F x i+G x i) (fun i=>(hF i).add (hG i)) := by
  calc
    _=morreyCoefficientRecover ν Z+morreyCoefficientRecover ν Y := (morreyCoefficientRecover (n:=n) (q:=q) ν).map_add Z Y
    _=hsUnitBallL2Class F hF+hsUnitBallL2Class G hG := congrArg₂ (fun A B : HSUnitBallL2 n q=>A+B) hZ hY
    _=_ := (hsUnitBallL2Class_add F G hF hG).symm

theorem morreyCoefficientRecover_smul_raw {n q : ℕ} (ν c : ℝ) (F : Domain n→Gradient n q)
    (hF : ∀i,MemLp (fun x=>F x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (Z : MorreyCoefficientSpace n q ν) (hZ : morreyCoefficientRecover ν Z=hsUnitBallL2Class F hF) :
    morreyCoefficientRecover ν (c • Z)=hsUnitBallL2Class (fun x i=>c • F x i) (fun i=>(hF i).const_smul c) := by
  calc
    _=c • morreyCoefficientRecover ν Z := (morreyCoefficientRecover (n:=n) (q:=q) ν).map_smul c Z
    _=c • hsUnitBallL2Class F hF := congrArg (fun A : HSUnitBallL2 n q=>c • A) hZ
    _=_ := (hsUnitBallL2Class_smul c F hF).symm

end StationaryHarmonicMaps.Analysis

end
