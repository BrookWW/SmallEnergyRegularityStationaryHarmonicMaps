module

public import StationaryHarmonicMaps.Analysis.NaturalCoulombPowerGrowthCompactness
public import StationaryHarmonicMaps.Analysis.SkewCriticalHomotopy
public import Mathlib.Topology.Sequences

/-!
# Closedness of the actual bounded natural Coulomb class along the scalar path

The literal parameter set consists of actual native special-orthogonal
frames for tA with the displayed complete critical and stronger bounds.
The scalar path gives the true strong coefficient convergence. One joint
native subsequence preserves all bounds and natural tests at the limit.
-/

public section

open HarmonicMaps MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The parameter set of actual bounded native natural SO Coulomb frames
for the original scalar connection path is closed. This does not assert
openness or existence at every parameter. -/
theorem isClosed_scalar_path_bounded_natural_coulomb_frames {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀T,R (E T)=T) (hER : ∀z,E (R z)=z)
    (hE : ∀T : Ambient q →L[ℝ] Ambient q,‖E T‖^2=∑j : Fin q,‖T (EuclideanSpace.single j 1)‖^2)
    (A : Domain n → Fin n → (Ambient q →L[ℝ] Ambient q))
    (hA : ∀i,MemLp (fun x=>A x i) 2 (volume.restrict (ball (0 : Domain n) 1)))
    (hAskew : ∀i,∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (A x i)= -A x i)
    (MA MD MZ ν KD KZ : ℝ) (hMA : 0≤MA) (hMD : 0≤MD) (hMZ : 0≤MZ)
    (hKD : 0≤KD) (hKZ : 0≤KZ)
    (hACritical : criticalGradientMorreySquare (fun x i=>E (A x i)) (ball (0 : Domain n) 1)≤ENNReal.ofReal MA) :
    IsClosed {t : ℝ | t∈Icc (0 : ℝ) 1 ∧
      ∃ (p : Domain n → Ambient (q*q)) (Dp : Domain n → Gradient n (q*q)),
        MemW12 (ballDomain (0 : Domain n) 1) p Dp ∧
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),star (R (p x))*R (p x)=1) ∧
        (∀ᵐx∂volume.restrict (ball (0 : Domain n) 1),(R (p x)).det=1) ∧
        criticalGradientMorreySquare Dp (ball (0 : Domain n) 1)≤ENNReal.ofReal MD ∧
        (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
          (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Dp x))≤KD*r^ν) ∧
        let Z := fun x i=>E (star (R (p x))*R (Dp x i)+star (R (p x))*(t • A x i)*R (p x))
        criticalGradientMorreySquare Z (ball (0 : Domain n) 1)≤ENNReal.ofReal MZ ∧
        (∀a∈ball (0 : Domain n) 1,∀r : ℝ,0<r →
          (∫x in ball a r∩ball (0 : Domain n) 1,hsNormSq (Z x))≤KZ*r^ν) ∧
        ∀ (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q)),
          MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ →
          (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ (Z x i) (Dψ x i))=0} := by
  apply isSeqClosed_iff_isClosed.mp
  intro ts t hts ht
  have htIcc : t∈Icc (0 : ℝ) 1 := isClosed_Icc.mem_of_tendsto ht
    (Eventually.of_forall fun k=>(hts k).1)
  choose p Dp hp hOrth hDet hCriticalD hGrowthD hCriticalZ hGrowthZ hNatural using fun k=>(hts k).2
  let μ := volume.restrict (ball (0 : Domain n) 1)
  let As := fun k x i=>E (ts k • A x i)
  let a := fun x i=>E (t • A x i)
  have hAs (k : ℕ) (i : Fin n) : MemLp (fun x=>As k x i) 2 μ :=
    E.lipschitz.comp_memLp (map_zero E) ((hA i).const_smul (ts k))
  have ha (i : Fin n) : MemLp (fun x=>a x i) 2 μ :=
    E.lipschitz.comp_memLp (map_zero E) ((hA i).const_smul t)
  have hStrong (i : Fin n) : Tendsto (fun k=>eLpNorm (fun x=>As k x i-a x i) 2 μ) atTop (𝓝 0) := by
    have H := tendsto_L2_scalar_path μ (fun x=>E (A x i))
      (E.lipschitz.comp_memLp (map_zero E) (hA i)) atTop ts t ht
    simpa only [As,a,map_smul] using H
  obtain ⟨_hAll,hPath,_hL2,_hCriticalPath⟩ :=
    skew_connection_scalar_critical_homotopy.{0,0} E (ball (0 : Domain n) 1) A hA hAskew MA hMA hACritical
  have hCriticalA (k : ℕ) : criticalGradientMorreySquare (As k) (ball (0 : Domain n) 1)≤ENNReal.ofReal MA :=
    hPath (ts k) (hts k).1
  have hCriticalZ' (k : ℕ) : criticalGradientMorreySquare
      (fun x i=>E (star (R (p k x))*R (Dp k x i)+star (R (p k x))*R (As k x i)*R (p k x)))
      (ball (0 : Domain n) 1)≤ENNReal.ofReal MZ := by
    simpa only [As,hRE] using hCriticalZ k
  have hNatural' (k : ℕ) (ψ : Domain n → Ambient (q*q)) (Dψ : Domain n → Gradient n (q*q))
      (hψ : MemW12 (ballDomain (0 : Domain n) 1) ψ Dψ) :
      (∫x in ball (0 : Domain n) 1,∑i : Fin n,inner ℝ
        (E (star (R (p k x))*R (Dp k x i)+star (R (p k x))*R (As k x i)*R (p k x))) (Dψ x i))=0 := by
    simpa only [As,hRE] using hNatural k ψ Dψ hψ
  have hGrowthZ' (k : ℕ) (b : Domain n) (hb : b∈ball (0 : Domain n) 1) (r : ℝ) (hr : 0<r) :
      (∫x in ball b r∩ball (0 : Domain n) 1,hsNormSq (fun i=>
        E (star (R (p k x))*R (Dp k x i)+star (R (p k x))*R (As k x i)*R (p k x))))≤KZ*r^ν := by
    simpa only [As,hRE] using hGrowthZ k b hb r hr
  obtain ⟨σ,v,Dv,_hσ,hv,hvOrth,hvDet,hvCritical,_hStrong,_hWeak,hvGrowth,
    _hZLp,hZCritical,hZTests,hZGrowth⟩ :=
    exists_special_orthogonal_natural_power_growth_limit_unitBall E R hRE hER hE p Dp hp hOrth hDet As a
      hAs ha hStrong hMD hMA hMZ hCriticalD hCriticalA hCriticalZ' hNatural' ν KD KZ hKD hKZ hGrowthD hGrowthZ'
  refine ⟨htIcc,v,Dv,hv,hvOrth,hvDet,hvCritical,(fun b hb r hr=>(hvGrowth b hb r hr).2),?_,?_,?_⟩
  · simpa only [a,hRE] using hZCritical
  · intro b hb r hr
    simpa only [a,hRE] using (hZGrowth b hb r hr).2
  · intro ψ Dψ hψ
    simpa only [a,hRE] using (hZTests ψ Dψ hψ).2

end StationaryHarmonicMaps.Analysis

end
