module

public import Thesis.Variational.SmoothWallGeometry
import Thesis.Variational.SmoothDomainLocalZeroTrace
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! A continuous interior gradient extends as the actual within derivative
on a smooth closed domain. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff

namespace Thesis

variable {Ω : Set Point} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem hasFDerivWithinAt_of_epigraph_continuous_derivative
    (hΩ : IsSmoothDomain Ω) {f : Point → F} {D : Point → Point →L[ℝ] F}
    (hf : ContinuousOn f (closure Ω)) (hD : ContinuousOn D (closure Ω))
    (hDiff : ∀ x ∈ Ω, HasFDerivAt f (D x) x)
    {x : Point} (hx : x ∈ frontier Ω) :
    HasFDerivWithinAt f (D x) (closure Ω) x := by
  obtain ⟨B,hB⟩ := hΩ.exists_epigraph_box hx
  let E := B.normalEuclideanChart
  let W := (B.flatSlab B.radius).val
  let V := (B.flatRectangle (-B.radius) B.radius).val
  let A := (B.physicalRectangle (-B.radius) B.radius).val
  let y := E.symm x
  have hWA : W = E ⁻¹' Ω ∩ V := by
    ext p
    constructor
    · intro hp
      exact ⟨B.flatSlab_mapsTo_domain le_rfl hp,
        ⟨hp.1,(neg_neg_of_pos B.radius_pos).trans hp.2.1,hp.2.2⟩⟩
    · rintro ⟨hp,hV⟩
      exact ⟨hV.1,(B.normalEuclideanChart_mem_domain_iff le_rfl le_rfl hV).1 hp,hV.2.2⟩
  have hMap : MapsTo E W Ω := B.flatSlab_mapsTo_domain le_rfl
  have hCl : MapsTo E (closure W) (closure Ω) :=
    closure_minimal (hMap.mono_right subset_closure) (isClosed_closure.preimage E.continuous)
  have hNearMap : MapsTo E.symm (closure Ω ∩ A) (closure W) := by
    intro z hz
    have hPre : E.symm z ∈ closure (E ⁻¹' Ω) := by
      rw [← E.preimage_closure]
      change E (E.symm z) ∈ closure Ω
      rw [E.apply_symm_apply]
      exact hz.1
    have hV : E.symm z ∈ V := by
      obtain ⟨p,hp,hEq⟩ := hz.2
      change E p = z at hEq
      rw [← hEq,E.symm_apply_apply]
      exact hp
    rw [hWA]
    exact (B.flatRectangle (-B.radius) B.radius).property.closure_inter ⟨hPre,hV⟩
  have hxA : x ∈ A := B.normalChart_mem_zero hB B.radius_pos
  have hy : y ∈ closure W := hNearMap ⟨frontier_subset_closure hx,hxA⟩
  let g := f ∘ E
  let G (p : Point) := (D (E p)).comp (fderiv ℝ E p)
  have hGc : ContinuousOn G (closure W) :=
    (hD.comp E.continuous.continuousOn hCl).clm_comp
      (B.normalEuclideanChart_smooth.continuous_fderiv (by simp)).continuousOn
  have hG (p : Point) (hp : p ∈ W) : HasFDerivAt g (G p) p :=
    (hDiff (E p) (hMap hp)).comp p (B.normalEuclideanChart_smooth.differentiable (by simp) p).hasFDerivAt
  have hDiffg : DifferentiableOn ℝ g W := fun p hp => (hG p hp).differentiableAt.differentiableWithinAt
  have hLim : Tendsto (fun p => fderiv ℝ g p) (𝓝[W] y) (𝓝 (G y)) := by
    have h := ((hGc y hy).mono subset_closure).tendsto
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (hG p hp).fderiv.symm
  have hGc' : ∀ z ∈ closure W, ContinuousWithinAt g W z :=
    fun z hz => ((hf.comp E.continuous.continuousOn hCl) z hz).mono subset_closure
  have hClosed := hasFDerivWithinAt_closure_of_tendsto_fderiv hDiffg (B.convex_flatSlab B.radius)
    (B.flatSlab B.radius).property hGc' hLim
  have hCom := hClosed.comp x
    (B.normalEuclideanChart_inverse_smooth.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt
    hNearMap
  have hDer : (fderiv ℝ E y).comp (fderiv ℝ E.symm x) = ContinuousLinearMap.id ℝ Point := by
    have h := (B.normalEuclideanChart_smooth.differentiable (by simp) y).hasFDerivAt.comp x
      (B.normalEuclideanChart_inverse_smooth.differentiable (by simp) x).hasFDerivAt
    have hEq : E ∘ E.symm = (id : Point → Point) := funext E.apply_symm_apply
    change HasFDerivAt (E ∘ E.symm) ((fderiv ℝ E y).comp (fderiv ℝ E.symm x)) x at h
    rw [hEq] at h
    simpa only [fderiv_id] using h.fderiv.symm
  have hGx : (G y).comp (fderiv ℝ E.symm x) = D x := by
    unfold G
    rw [ContinuousLinearMap.comp_assoc,hDer,ContinuousLinearMap.comp_id]
    exact congrArg D (E.apply_symm_apply x)
  have hFn : g ∘ E.symm = f := funext fun z => congrArg f (E.apply_symm_apply z)
  change HasFDerivWithinAt (g ∘ E.symm) ((G y).comp (fderiv ℝ E.symm x)) (closure Ω ∩ A) x at hCom
  rw [hFn,hGx] at hCom
  exact hCom.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds ((B.physicalRectangle (-B.radius) B.radius).property.mem_nhds hxA)))

/-- A function continuous on the closed domain, with a continuous
extension of its interior derivative, is C¹ on the closed domain. -/
theorem IsSmoothDomain.contDiffOn_one_of_continuous_derivative
    (hΩ : IsSmoothDomain Ω) {f : Point → F} {D : Point → Point →L[ℝ] F}
    (hf : ContinuousOn f (closure Ω)) (hD : ContinuousOn D (closure Ω))
    (hDiff : ∀ x ∈ Ω, HasFDerivAt f (D x) x) :
    ContDiffOn ℝ 1 f (closure Ω) := by
  have hDer (x : Point) (hx : x ∈ closure Ω) : HasFDerivWithinAt f (D x) (closure Ω) x := by
    by_cases hi : x ∈ Ω
    · exact (hDiff x hi).hasFDerivWithinAt
    · have hFront : x ∈ frontier Ω := by
        rw [frontier,hΩ.1.1.interior_eq]
        exact ⟨hx,hi⟩
      exact hasFDerivWithinAt_of_epigraph_continuous_derivative hΩ hf hD hDiff hFront
  have hC : ContDiffOn ℝ (0 : ℕ∞ω) D (closure Ω) := contDiffOn_zero.mpr hD
  exact (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hΩ.uniqueDiffOn_closure).2
    ⟨(by simp),D,hC,hDer⟩

end Thesis
