module

public import HarmonicMaps.Analysis.SobolevL2Closure
import HarmonicMaps.Analysis.L2TranslationContinuity
import HarmonicMaps.Analysis.SmoothWeakGradient
import StratificationTheory.Foundation.SobolevLocalAssembly

/-! The zero extension carries the original compact smooth Dirichlet closure to the whole space. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal Topology

namespace Thesis

/-- The actual compact smooth Dirichlet approximants converge globally after
extending each represented value and column by zero. -/
theorem exists_global_smooth_approximation_of_zeroBoundary {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hu : HasZeroBoundaryValues Ω u D) :
    ∃ (φ : ℕ → Domain n → Ambient q) (hSmooth : ∀ k, ContDiff ℝ ∞ (φ k)),
      (∀ k, HasCompactSupport (φ k) ∧ tsupport (φ k) ⊆ Ω.val) ∧
      Tendsto (fun k => eLpNorm (φ k - Ω.val.indicator u) 2
        (volume : Measure (Domain n))) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun k => eLpNorm
        (fun x => coordinateDerivative (φ k) (hSmooth k) i x - (Ω.val.indicator D) x i)
        2 (volume : Measure (Domain n))) atTop (𝓝 0) := by
  let w := Ω.val.indicator u
  let G := Ω.val.indicator D
  obtain ⟨_,φ,hSmooth,hSupp,hVLim,hDLim⟩ := hu
  let d (k : ℕ) (x : Domain n) (i : Fin n) := coordinateDerivative (φ k) (hSmooth k) i x
  have hVG : Tendsto (fun k => eLpNorm (φ k-w) 2 (volume : Measure (Domain n))) atTop (𝓝 0) := by
    apply hVLim.congr
    intro k
    have he : φ k - w = Ω.val.indicator (φ k - u) := by
      funext x
      by_cases hx : x ∈ Ω.val
      · simp only [w,Pi.sub_apply,indicator_of_mem hx]
      · have h₀ : φ k x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hx ((hSupp k).2 h))
        simp only [w,Pi.sub_apply,indicator_of_notMem hx,h₀,sub_zero]
    rw [he,eLpNorm_indicator_eq_eLpNorm_restrict Ω.property.measurableSet]
  have hDG (i : Fin n) :
      Tendsto (fun k => eLpNorm (fun x => d k x i-G x i) 2 (volume : Measure (Domain n))) atTop (𝓝 0) := by
    apply (hDLim i).congr
    intro k
    have he : (fun x => d k x i-G x i) =
        Ω.val.indicator (fun x => d k x i-D x i) := by
      funext x
      by_cases hx : x ∈ Ω.val
      · simp only [G,indicator_of_mem hx]
      · have h₀ : d k x i = 0 :=
          image_eq_zero_of_notMem_tsupport (f := fun y => d k y i) (fun h => hx ((hSupp k).2
            (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) h)))
        simp only [G,indicator_of_notMem hx,Pi.zero_apply,h₀,sub_zero]
    rw [he,eLpNorm_indicator_eq_eLpNorm_restrict Ω.property.measurableSet]
  exact ⟨φ,hSmooth,hSupp,hVG,hDG⟩

/-- Extending the value and columns by zero preserves the actual weak
Sobolev graph of a field in the compactly supported closure. -/
theorem memW12_univ_zeroExtension_of_zeroBoundary {n q : ℕ} {Ω : OpenDomain n}
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hu : HasZeroBoundaryValues Ω u D) :
    MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) (Ω.val.indicator u) (Ω.val.indicator D) := by
  let w := Ω.val.indicator u
  let G := Ω.val.indicator D
  have hGc (i : Fin n) : (fun x => G x i) = Ω.val.indicator (fun x => D x i) := by
    funext x
    by_cases hx : x ∈ Ω.val
    · simp only [G,indicator_of_mem hx]
    · simp only [G,indicator_of_notMem hx,Pi.zero_apply]
  have hw : MemLp w 2 volume := memLp_zeroExtension Ω.property.measurableSet hu.1.2.1
  have hG (i : Fin n) : MemLp (fun x => G x i) 2 (volume : Measure (Domain n)) := by
    rw [hGc]
    exact memLp_zeroExtension Ω.property.measurableSet (hu.1.2.2 i)
  obtain ⟨φ,hSmooth,hSupp,hVG,hDG⟩ := exists_global_smooth_approximation_of_zeroBoundary hu
  let d (k : ℕ) (x : Domain n) (i : Fin n) := coordinateDerivative (φ k) (hSmooth k) i x
  apply memW12_of_local_sobolev_pair
    (by simpa only [Measure.restrict_univ] using hw)
    (fun i => by simpa only [Measure.restrict_univ] using hG i)
  intro x _
  let V := ballDomain x 1
  refine ⟨1,zero_lt_one,subset_univ _,?_⟩
  letI : IsFiniteMeasure (volume.restrict V.val) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hφ (k : ℕ) : MemW12 V (φ k) (d k) := by
    apply memW12_of_contDiff V (hSmooth k)
    · exact (hSmooth k).continuous.memLp_of_hasCompactSupport (hSupp k).1
        |>.mono_measure Measure.restrict_le_self
    · intro i
      have hCont : Continuous (fun y => d k y i) :=
        (((hSmooth k).continuous_fderiv (by simp)).clm_apply continuous_const)
      exact hCont.memLp_of_hasCompactSupport ((hSupp k).1.fderiv_apply ℝ (EuclideanSpace.single i 1))
        |>.mono_measure Measure.restrict_le_self
  apply MemW12.of_L2_limit hφ (hw.mono_measure Measure.restrict_le_self)
    (fun i => (hG i).mono_measure Measure.restrict_le_self)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hVG
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)
  · intro i
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hDG i)
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)

end Thesis
