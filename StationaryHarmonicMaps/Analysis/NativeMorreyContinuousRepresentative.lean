module

public import StationaryHarmonicMaps.Analysis.NativeMorreyContinuousExistence
public import StationaryHarmonicMaps.Analysis.NativeMorreyBilinearProduct

/-!
# The intrinsic native embedding into closed-ball continuous maps

The selected continuous representative is unique among all continuous maps
with the original AE value. The embedding retains the original native norm
and commutes with actual bilinear products at every closed-ball point.
-/

public section

open HarmonicMaps MeasureTheory Set Metric Filter
open scoped ENNReal Topology

noncomputable section

namespace StationaryHarmonicMaps.Analysis

/-- The unique closed-ball continuous representative of the original map class. -/
@[expose] def nativeMorreyContinuousRepresentative
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {q : ℕ} (X : NativeMorreySobolevSpace n q ((n : ℝ)-2+γ)) :
    C(closedBall (0 : Domain n) 1,Ambient q) :=
  Classical.choose (((Classical.choose_spec
    (existsUnique_nativeMorrey_continuous_representative_bound n hn γ hγ hγTwo)).2 q X).1.exists)

theorem nativeMorreyContinuousRepresentative_ae
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {q : ℕ} (X : NativeMorreySobolevSpace n q ((n : ℝ)-2+γ)) :
    ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀hx : x∈ball (0 : Domain n) 1,
      nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo X
        ⟨x,ball_subset_closedBall hx⟩=
        (nativeMorreyMapClass (n:=n) (q:=q) ((n : ℝ)-2+γ) X).val x :=
  Classical.choose_spec (((Classical.choose_spec
    (existsUnique_nativeMorrey_continuous_representative_bound n hn γ hγ hγTwo)).2 q X).1.exists)

/-- The full characterization uses only continuity and the original AE value. -/
theorem nativeMorreyContinuousRepresentative_eq_iff
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {q : ℕ} (X : NativeMorreySobolevSpace n q ((n : ℝ)-2+γ))
    (W : C(closedBall (0 : Domain n) 1,Ambient q)) :
    W=nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo X ↔
      ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀hx : x∈ball (0 : Domain n) 1,
        W ⟨x,ball_subset_closedBall hx⟩=
          (nativeMorreyMapClass (n:=n) (q:=q) ((n : ℝ)-2+γ) X).val x := by
  constructor
  · intro hW
    rw [hW]
    exact nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo X
  · intro hW
    have hUnique := (((Classical.choose_spec
      (existsUnique_nativeMorrey_continuous_representative_bound n hn γ hγ hγTwo)).2 q X).1)
    exact hUnique.unique hW (nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo X)

theorem nativeMorreyContinuousRepresentative_injective
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ) :
    Function.Injective (nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo) := by
  intro X Y hXY
  apply nativeMorreyMapClass_injective (n:=n) (q:=q) ((n : ℝ)-2+γ)
  apply Lp.ext
  filter_upwards [nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo X,
    nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo Y,
    ae_restrict_mem measurableSet_ball] with x hx hy hxBall
  exact (hx hxBall).symm.trans ((congrArg
    (fun W : C(closedBall (0 : Domain n) 1,Ambient q)=>W ⟨x,ball_subset_closedBall hxBall⟩) hXY).trans (hy hxBall))

theorem nativeMorreyContinuousRepresentative_add
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {q : ℕ} (X Y : NativeMorreySobolevSpace n q ((n : ℝ)-2+γ)) :
    nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo (X+Y)=
      nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo X+
        nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo Y := by
  symm
  apply (nativeMorreyContinuousRepresentative_eq_iff n hn γ hγ hγTwo (X+Y) _).mpr
  have hAdd := (nativeMorreyMapClass (n:=n) (q:=q) ((n : ℝ)-2+γ)).map_add X Y
  filter_upwards [nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo X,
    nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo Y,
    Lp.coeFn_add (nativeMorreyMapClass (n:=n) (q:=q) ((n : ℝ)-2+γ) X)
      (nativeMorreyMapClass (n:=n) (q:=q) ((n : ℝ)-2+γ) Y)] with x hx hy hLp
  intro hxBall
  change nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo X ⟨x,ball_subset_closedBall hxBall⟩+
    nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo Y ⟨x,ball_subset_closedBall hxBall⟩=_
  rw [hx hxBall,hy hxBall]
  exact hLp.symm.trans (congrArg (fun U : MapUnitBallL2 n q=>U.val x) hAdd.symm)

theorem nativeMorreyContinuousRepresentative_smul
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {q : ℕ} (c : ℝ) (X : NativeMorreySobolevSpace n q ((n : ℝ)-2+γ)) :
    nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo (c • X)=
      c • nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo X := by
  symm
  apply (nativeMorreyContinuousRepresentative_eq_iff n hn γ hγ hγTwo (c • X) _).mpr
  have hSmul := (nativeMorreyMapClass (n:=n) (q:=q) ((n : ℝ)-2+γ)).map_smul c X
  filter_upwards [nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo X,
    Lp.coeFn_smul c (nativeMorreyMapClass (n:=n) (q:=q) ((n : ℝ)-2+γ) X)] with x hx hLp
  intro hxBall
  change c • nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo X
    ⟨x,ball_subset_closedBall hxBall⟩=_
  rw [hx hxBall]
  exact hLp.symm.trans (congrArg (fun U : MapUnitBallL2 n q=>U.val x) hSmul.symm)

theorem exists_nativeMorreyContinuousRepresentative_bound
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀(q : ℕ) (X : NativeMorreySobolevSpace n q ((n : ℝ)-2+γ)),
      ‖nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo X‖≤C*‖X‖ := by
  obtain ⟨C,hC,hAll⟩ := existsUnique_nativeMorrey_continuous_representative_bound n hn γ hγ hγTwo
  refine ⟨C,hC,?_⟩
  intro q X
  exact (hAll q X).2 _ (nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo X)

/-- The bounded linear embedding into actual closed-ball continuous maps. -/
@[expose] def nativeMorreyContinuousEmbedding
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ) :
    NativeMorreySobolevSpace n q ((n : ℝ)-2+γ)→L[ℝ]
      C(closedBall (0 : Domain n) 1,Ambient q) := by
  let f : NativeMorreySobolevSpace n q ((n : ℝ)-2+γ)→ₗ[ℝ]
      C(closedBall (0 : Domain n) 1,Ambient q) :=
    { toFun := nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo
      map_add' := nativeMorreyContinuousRepresentative_add n hn γ hγ hγTwo
      map_smul' := nativeMorreyContinuousRepresentative_smul n hn γ hγ hγTwo }
  exact f.mkContinuousOfExistsBound (by
    obtain ⟨C,_hC,hAll⟩ := exists_nativeMorreyContinuousRepresentative_bound n hn γ hγ hγTwo
    exact ⟨C,hAll q⟩)

theorem nativeMorreyContinuousEmbedding_apply
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (X : NativeMorreySobolevSpace n q ((n : ℝ)-2+γ)) :
    nativeMorreyContinuousEmbedding n hn γ hγ hγTwo q X=
      nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo X := rfl

/-- The complete bounded embedding is determined by the original AE map
value on every intrinsic native class. -/
theorem nativeMorreyContinuousEmbedding_eq_iff
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (A : NativeMorreySobolevSpace n q ((n : ℝ)-2+γ)→L[ℝ]
      C(closedBall (0 : Domain n) 1,Ambient q)) :
    A=nativeMorreyContinuousEmbedding n hn γ hγ hγTwo q ↔
      ∀X : NativeMorreySobolevSpace n q ((n : ℝ)-2+γ),
        ∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),∀hx : x∈ball (0 : Domain n) 1,
          A X ⟨x,ball_subset_closedBall hx⟩=
            (nativeMorreyMapClass (n:=n) (q:=q) ((n : ℝ)-2+γ) X).val x := by
  constructor
  · intro hA
    subst A
    intro X
    exact nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo X
  · intro hA
    apply ContinuousLinearMap.ext
    intro X
    exact (nativeMorreyContinuousRepresentative_eq_iff n hn γ hγ hγTwo X (A X)).mpr (hA X)

theorem exists_nativeMorreyContinuousEmbedding_norm_bound
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) :
    ∃C : ℝ,0<C ∧ ∀q : ℕ,‖nativeMorreyContinuousEmbedding n hn γ hγ hγTwo q‖≤C := by
  obtain ⟨C,hC,hAll⟩ := exists_nativeMorreyContinuousRepresentative_bound n hn γ hγ hγTwo
  refine ⟨C,hC,?_⟩
  intro q
  exact ContinuousLinearMap.opNorm_le_bound
    (nativeMorreyContinuousEmbedding n hn γ hγ hγTwo q) hC.le (hAll q)

/-- Evaluation at every point of the closed ball is a bounded native functional. -/
@[expose] def nativeMorreyEvaluation
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (x : closedBall (0 : Domain n) 1) :
    NativeMorreySobolevSpace n q ((n : ℝ)-2+γ)→L[ℝ]Ambient q :=
  (ContinuousMap.evalCLM ℝ x).comp (nativeMorreyContinuousEmbedding n hn γ hγ hγTwo q)

theorem nativeMorreyEvaluation_apply
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2) (q : ℕ)
    (x : closedBall (0 : Domain n) 1)
    (X : NativeMorreySobolevSpace n q ((n : ℝ)-2+γ)) :
    nativeMorreyEvaluation n hn γ hγ hγTwo q x X=
      nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo X x := rfl

/-- The selected native product retains the actual bilinear value at every
closed-ball point, including the boundary. -/
theorem nativeMorreyContinuousRepresentative_bilinear
    (n : ℕ) (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγTwo : γ<2)
    {m k q : ℕ} (B : Ambient m→L[ℝ](Ambient k→L[ℝ]Ambient q))
    (X : NativeMorreySobolevSpace n m ((n : ℝ)-2+γ))
    (Y : NativeMorreySobolevSpace n k ((n : ℝ)-2+γ))
    (x : closedBall (0 : Domain n) 1) :
    nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo
      (nativeMorreyBilinearProduct (m:=m) (k:=k) (q:=q) n hn γ hγ hγTwo B X Y) x=
      B (nativeMorreyContinuousRepresentative (q:=m) n hn γ hγ hγTwo X x)
        (nativeMorreyContinuousRepresentative (q:=k) n hn γ hγ hγTwo Y x) := by
  let W : C(closedBall (0 : Domain n) 1,Ambient q) :=
    ⟨fun x=>B (nativeMorreyContinuousRepresentative (q:=m) n hn γ hγ hγTwo X x)
      (nativeMorreyContinuousRepresentative (q:=k) n hn γ hγ hγTwo Y x),
      (B.continuous.comp (nativeMorreyContinuousRepresentative (q:=m) n hn γ hγ hγTwo X).continuous).clm_apply
        (nativeMorreyContinuousRepresentative (q:=k) n hn γ hγ hγTwo Y).continuous⟩
  have hW : W=nativeMorreyContinuousRepresentative (q:=q) n hn γ hγ hγTwo
      (nativeMorreyBilinearProduct (m:=m) (k:=k) (q:=q) n hn γ hγ hγTwo B X Y) := by
    apply (nativeMorreyContinuousRepresentative_eq_iff n hn γ hγ hγTwo _ W).mpr
    filter_upwards [nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo X,
      nativeMorreyContinuousRepresentative_ae n hn γ hγ hγTwo Y,
      nativeMorreyBilinearProduct_ae n hn γ hγ hγTwo B X Y] with z hzX hzY hz
    intro hzBall
    change B _ _=_
    rw [hzX hzBall,hzY hzBall]
    exact hz.symm
  exact (congrArg (fun V : C(closedBall (0 : Domain n) 1,Ambient q)=>V x) hW).symm

end StationaryHarmonicMaps.Analysis

end
