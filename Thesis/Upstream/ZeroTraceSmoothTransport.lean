module

public import Thesis.Interpolation.CompactGlobalSobolevApproximation
import StratificationTheory.Foundation.SmoothOpenDomainSobolevPullback
import StratificationTheory.Foundation.DominatedL2Pullback
import HolderToCK.Analysis.Poisson.PotentialRegularityMollification
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Compact graph approximation and the transport of a zero-extended
Dirichlet graph through smooth volume-preserving coordinates. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace Thesis

/-- A globally Sobolev graph supported inside a compact subset of the
domain belongs to its genuine zero-trace closure. -/
theorem hasZeroBoundaryValues_of_compact_global_graph {n q : ℕ} (U : OpenDomain n)
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hu : MemW12 ⟨univ,isOpen_univ⟩ u D) {K : Set (Domain n)} (hK : IsCompact K)
    (hKU : K ⊆ U.val) (hSupp : Function.support u ⊆ K)
    (hD : ∀ j, Function.support (fun x => D x j) ⊆ K) :
    HasZeroBoundaryValues U u D := by
  let ε (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((HolderToCK.compactDataApproximationScale n : ℝ))
  have hε (n : ℕ) : 0 < ε n := ENNReal.ofReal_pos.mpr (HolderToCK.compactDataApproximationScale n).property
  have hLim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal HolderToCK.compactDataApproximationScale_tendsto
  choose f hf hc hs hF hG using fun n => exists_compact_global_sobolev_approximation U hu K hK hKU hSupp hD (hε n)
  have hμ : volume.restrict U.val ≤ volume.restrict (univ : Set (Domain n)) :=
    Measure.restrict_mono_set volume (subset_univ _)
  exact ⟨⟨hu.1.mono (subset_univ _),hu.2.1.mono_measure hμ,fun i => (hu.2.2 i).mono_measure hμ⟩,
    f,hf,fun n => ⟨hc n,hs n⟩,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLim (fun _ => zero_le)
      (fun n => (hF n).le),
    fun i => tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLim (fun _ => zero_le)
      (fun n => (hG n i).le)⟩

private theorem coordinateDerivative_chain {n q : ℕ} (F : Domain n → Domain n)
    (hF : ContDiff ℝ ∞ F) {f : Domain n → Ambient q} (hf : ContDiff ℝ ∞ f)
    (x : Domain n) (i : Fin n) :
    coordinateDerivative (f ∘ F) (hf.comp hF) i x =
      ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • coordinateDerivative f hf j (F x) := by
  let v := fderiv ℝ F x (EuclideanSpace.single i 1)
  have hv : ∑ j : Fin n, v j • EuclideanSpace.single j 1 = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  unfold coordinateDerivative
  rw [fderiv_comp x (hf.differentiable (by simp) (F x)) (hF.differentiable (by simp) x)]
  change fderiv ℝ f (F x) v = ∑ j : Fin n, v j • fderiv ℝ f (F x) (EuclideanSpace.single j 1)
  conv_lhs => rw [← hv]
  simp only [map_sum, map_smul]

/-- A zero-extended Sobolev graph and its compact approximations push
through a smooth volume-preserving chart. The larger target can contain
the whole transformed open set. -/
theorem HasZeroBoundaryValues.smoothPushforward_zeroExtension {n q : ℕ}
    {U V : OpenDomain n} {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hu : HasZeroBoundaryValues U u D)
    (hz : MemW12 ⟨univ,isOpen_univ⟩ (U.val.indicator u) (U.val.indicator D))
    (F : Domain n ≃ₜ Domain n) (hFinv : ContDiff ℝ ∞ (F.symm : Domain n → Domain n))
    (hMP : MeasurePreserving F (volume : Measure (Domain n)) volume)
    (hV : Bornology.IsBounded V.val) (hSub : MapsTo F U.val V.val) :
    ∃ G : Domain n → HarmonicMaps.Gradient n q,
      HasZeroBoundaryValues V ((U.val.indicator u) ∘ F.symm) G := by
  let A : Domain n → Domain n := F.symm
  let μ := volume.restrict V.val
  let u₀ := U.val.indicator u
  let D₀ := U.val.indicator D
  let G (x : Domain n) (i : Fin n) := ∑ j : Fin n, (fderiv ℝ A x (EuclideanSpace.single i 1)) j • D₀ (A x) j
  have hA : MeasurePreserving A (volume : Measure (Domain n)) volume := hMP.symm F.toMeasurableEquiv
  have hAm : AEMeasurable A μ := hA.measurable.aemeasurable
  have hMap : Measure.map A μ ≤ (1 : ℝ≥0∞) • (volume : Measure (Domain n)) := by
    rw [one_smul, ← hA.map_eq]
    exact Measure.map_mono Measure.restrict_le_self hA.measurable
  obtain ⟨L,hL⟩ := hV.isCompact_closure.exists_bound_of_continuousOn
    (hFinv.continuous_fderiv (by simp)).continuousOn
  have hw : MemW12 V (u₀ ∘ A) G := by
    apply memW12_smooth_open_domain_pullback hz V A hFinv.contDiffOn (mapsTo_univ _ _)
      L (fun x hx => hL x (subset_closure hx)) 1 ENNReal.one_ne_top
    rwa [Measure.restrict_univ]
  obtain ⟨_,f,hf,hc,hFconv,hDconv⟩ := hu
  let v (k : ℕ) := f k ∘ A
  let hv (k : ℕ) : ContDiff ℝ ∞ (v k) := (hf k).comp hFinv
  have hS (k : ℕ) : tsupport (v k) = F.symm ⁻¹' tsupport (f k) := tsupport_comp_eq_preimage _ _
  refine ⟨G, hw, v,hv,?_ ,?_ ,?_⟩
  · intro k
    refine ⟨by rw [HasCompactSupport,hS]; exact F.symm.isCompact_preimage.2 (hc k).1,?_⟩
    intro x hx
    rw [hS k] at hx
    have hU : F.symm x ∈ U.val := (hc k).2 hx
    exact F.apply_symm_apply x ▸ hSub hU
  · have hF0 : Tendsto (fun k => eLpNorm (f k - u₀) 2 volume) atTop (𝓝 0) := by
      apply hFconv.congr
      intro k
      have hEq : f k - u₀ = U.val.indicator (f k - u) := by
        funext x
        by_cases hx : x ∈ U.val
        · simp [u₀,indicator_of_mem hx]
        · have hf₀ : f k x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx ((hc k).2 h))
          simp [u₀,indicator_of_notMem hx,hf₀]
      rw [hEq,eLpNorm_indicator_eq_eLpNorm_restrict U.property.measurableSet]
    have hu₀ : AEStronglyMeasurable u₀ (volume : Measure (Domain n)) := by
      simpa only [Measure.restrict_univ] using hz.2.1.aestronglyMeasurable
    exact tendsto_eLpNorm_comp_zero_of_map_le_smul hAm ENNReal.one_ne_top hMap
      (p := 2) (f := fun k => f k - u₀)
      (fun k => (hf k).continuous.aestronglyMeasurable.sub hu₀) hF0
  · intro i
    let Δ (j : Fin n) (k : ℕ) (y : Domain n) := coordinateDerivative (f k) (hf k) j y - D₀ y j
    have hΔ (j : Fin n) (k : ℕ) : AEStronglyMeasurable (Δ j k) (volume : Measure (Domain n)) := by
      have hd₀ : AEStronglyMeasurable (fun y => D₀ y j) (volume : Measure (Domain n)) := by
        simpa only [Measure.restrict_univ] using (hz.2.2 j).aestronglyMeasurable
      exact (((hf k).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.sub hd₀
    have hΔlim (j : Fin n) : Tendsto (fun k => eLpNorm (Δ j k) 2 volume) atTop (𝓝 0) := by
      apply (hDconv j).congr
      intro k
      have hEq : Δ j k = U.val.indicator (fun y => coordinateDerivative (f k) (hf k) j y - D y j) := by
        funext y
        by_cases hy : y ∈ U.val
        · simp [Δ,D₀,indicator_of_mem hy]
        · have hzero : coordinateDerivative (f k) (hf k) j y = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h => hy ((hc k).2
              (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1) h)))
          simp [Δ,D₀,indicator_of_notMem hy,hzero]
      rw [hEq,eLpNorm_indicator_eq_eLpNorm_restrict U.property.measurableSet]
    let a (j : Fin n) (x : Domain n) : ℝ := (fderiv ℝ A x (EuclideanSpace.single i 1)) j
    have ha (j : Fin n) : MemLp (a j) ⊤ μ := by
      have hCont : Continuous (a j) := (EuclideanSpace.proj j).continuous.comp
        ((hFinv.continuous_fderiv (by simp)).clm_apply continuous_const)
      apply memLp_top_of_bound hCont.aestronglyMeasurable L
      filter_upwards [ae_restrict_mem V.property.measurableSet] with x hx
      calc
        ‖a j x‖ ≤ ‖fderiv ℝ A x (EuclideanSpace.single i 1)‖ := PiLp.norm_apply_le _ j
        _ ≤ ‖fderiv ℝ A x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := (fderiv ℝ A x).le_opNorm _
        _ ≤ L := by simpa only [PiLp.norm_single,norm_one,mul_one] using hL x (subset_closure hx)
    have hMeas (j : Fin n) (k : ℕ) : AEStronglyMeasurable ((Δ j k) ∘ A) μ :=
      ((hΔ j k).mono_ac (Measure.absolutelyContinuous_of_le_smul hMap)).comp_aemeasurable hAm
    have hLt (j : Fin n) : Tendsto (fun k => eLpNorm (fun x => a j x • Δ j k (A x)) 2 μ) atTop (𝓝 0) := by
      have hP : Tendsto (fun k => eLpNorm ((Δ j k) ∘ A) 2 μ) atTop (𝓝 0) :=
        tendsto_eLpNorm_comp_zero_of_map_le_smul hAm ENNReal.one_ne_top hMap (p := 2)
          (f := Δ j) (hΔ j) (hΔlim j)
      exact tendsto_eLpNorm_two_bounded_smul_zero (ha j) (hMeas j) hP
    apply (tendsto_eLpNorm_two_finite_sum_zero (fun j k => (ha j).1.smul (hMeas j k)) hLt).congr
    intro k
    congr 1
    funext x
    rw [show coordinateDerivative (v k) (hv k) i x = _ from coordinateDerivative_chain A hFinv (hf k) x i]
    simp only [G,Δ,a,Pi.smul_apply',Function.comp_apply,smul_sub,Finset.sum_sub_distrib]

end Thesis
