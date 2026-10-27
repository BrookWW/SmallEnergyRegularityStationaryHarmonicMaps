module

public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Closed compatible bounded families

A bounded family has literal linear compatibility with recovery from one
fixed coordinate. These simultaneous equality constraints define a closed
linear subspace and retain the complete inherited supremum norm.
-/

public section

open Set Filter
open scoped ENNReal Topology

noncomputable section

namespace StationaryHarmonicMaps.Analysis

@[expose] def compatibleBoundedFamilies {I H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : I → H →L[ℝ] H) (i₀ : I) (c : ℝ) :
    Submodule ℝ (lp (fun _ : I=>H) ∞) where
  carrier := {Z | ∀i,Z i=T i (c • Z i₀)}
  zero_mem' := by intro i;simp
  add_mem' := by
    intro Z Y hZ hY i
    change Z i+Y i=T i (c • (Z i₀+Y i₀))
    rw [smul_add,map_add,hZ i,hY i]
  smul_mem' := by
    intro a Z hZ i
    change a • Z i=T i (c • (a • Z i₀))
    rw [smul_comm c a,map_smul,hZ i]

theorem isClosed_compatibleBoundedFamilies {I H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : I → H →L[ℝ] H) (i₀ : I) (c : ℝ) : IsClosed (compatibleBoundedFamilies T i₀ c : Set (lp (fun _ : I=>H) ∞)) := by
  change IsClosed {Z : lp (fun _ : I=>H) ∞ | ∀i,Z i=T i (c • Z i₀)}
  have hEq : {Z : lp (fun _ : I=>H) ∞ | ∀i,Z i=T i (c • Z i₀)}=
      ⋂i,{Z : lp (fun _ : I=>H) ∞ | Z i=T i (c • Z i₀)} := by ext Z;simp
  rw [hEq]
  apply isClosed_iInter
  intro i
  exact isClosed_eq (lp.evalCLM ℝ (fun _ : I=>H) ∞ i).continuous
    ((T i).continuous.comp (continuous_const.smul (lp.evalCLM ℝ (fun _ : I=>H) ∞ i₀).continuous))

instance compatibleBoundedFamilies_completeSpace {I H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H] (T : I → H →L[ℝ] H) (i₀ : I) (c : ℝ) : CompleteSpace (compatibleBoundedFamilies T i₀ c) := by
  letI : IsClosed (compatibleBoundedFamilies T i₀ c : Set (lp (fun _ : I=>H) ∞)) := isClosed_compatibleBoundedFamilies T i₀ c
  exact IsClosed.completeSpace_coe

theorem compatibleBoundedFamilies_recovery_injective {I H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : I → H →L[ℝ] H) (i₀ : I) (c : ℝ) :
    Function.Injective (fun Z : compatibleBoundedFamilies T i₀ c=>c • Z.val i₀) := by
  intro Z Y hZY
  apply Subtype.ext
  apply lp.ext
  funext i
  rw [Z.property i,Y.property i]
  exact congrArg (T i) hZY

theorem lp_norm_sq_isLUB {I H : Type*} [NormedAddCommGroup H] [Nonempty I]
    (Z : lp (fun _ : I=>H) ∞) : IsLUB (Set.range fun i=>‖Z i‖^2) (‖Z‖^2) := by
  constructor
  · rintro _ ⟨i,rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (lp.norm_apply_le_norm ENNReal.top_ne_zero Z i) 2
  · intro B hB
    have hB0 : 0≤B := (sq_nonneg ‖Z (Classical.arbitrary I)‖).trans (hB ⟨Classical.arbitrary I,rfl⟩)
    have hNorm : ‖Z‖≤Real.sqrt B := lp.norm_le_of_forall_le (Real.sqrt_nonneg B) fun i=>by
      have hSq : ‖Z i‖^2≤B := hB ⟨i,rfl⟩
      have hRoot := Real.sq_sqrt hB0
      have hn := norm_nonneg (Z i)
      have hs := Real.sqrt_nonneg B
      nlinarith only [hSq,hRoot,hn,hs]
    have hSq := pow_le_pow_left₀ (norm_nonneg Z) hNorm 2
    rw [Real.sq_sqrt hB0] at hSq
    exact hSq

end StationaryHarmonicMaps.Analysis

end
