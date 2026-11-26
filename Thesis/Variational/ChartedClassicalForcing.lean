module

public import Thesis.Upstream.WeakLpDerivatives
public import Thesis.Definitions
import HolderToCK.Analysis.ClassicalWeakGradient
import HarmonicMaps.Analysis.SobolevAECongruence

/-! Actual weak columns of the closed classical forcing in a smooth chart. -/

public section

noncomputable section

open Filter Function HarmonicMaps MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace Thesis

/-- A classical C¹ source on the physical closure pulls back to its actual
first weak graph on a bounded flat patch. Both the value and each explicit
chart column belong to every (L^p) on that patch. -/
theorem memW12_charted_contDiffOn_one_force {U : Set Point} (V : OpenDomain 3)
    (hB : Bornology.IsBounded V.val) (hU : IsOpen U) (hUd : UniqueDiffOn ℝ (closure U))
    (E : Point → Point) (hE : ContDiff ℝ 1 E) (hInto : MapsTo E V.val U)
    {q : ℕ} {f : Point → Ambient q} (hf : ContDiffOn ℝ 1 f (closure U)) (p : ℝ≥0∞) :
    let D (x : Point) (j : Fin 3) := fderivWithin ℝ f (closure U) (E x) (fderiv ℝ E x (axis j))
    MemW12 V (f ∘ E) D ∧
      MemLp (f ∘ E) p (volume.restrict V.val) ∧
        ∀ j, MemLp (fun x => D x j) p (volume.restrict V.val) := by
  let D (x : Point) (j : Fin 3) := fderivWithin ℝ f (closure U) (E x) (fderiv ℝ E x (axis j))
  let g := f ∘ E
  let μ := (volume : Measure Point).restrict V.val
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hB.measure_lt_top.ne
  have hM : MapsTo E (closure V.val) (closure U) :=
    closure_minimal (hInto.mono_right subset_closure) (isClosed_closure.preimage hE.continuous)
  have hCTop : MemLp g ⊤ μ := HasWeakLpDerivatives.memLp_top_of_continuousOn_closure
    V.property.measurableSet hB (hf.continuousOn.comp hE.continuous.continuousOn hM)
  have hDTop (j : Fin 3) : MemLp (fun x => D x j) ⊤ μ := by
    have hA : ContinuousOn (fun x => fderivWithin ℝ f (closure U) (E x)) (closure V.val) :=
      (hf.continuousOn_fderivWithin hUd le_rfl).comp hE.continuous.continuousOn hM
    have hBCol : Continuous (fun x => fderiv ℝ E x (axis j)) :=
      (hE.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact HasWeakLpDerivatives.memLp_top_of_continuousOn_closure
      V.property.measurableSet hB (hA.clm_apply hBCol.continuousOn)
  let G (x : Point) (j : Fin 3) := fderiv ℝ g x (axis j)
  have hEq : G =ᵐ[μ] D := by
    filter_upwards [ae_restrict_mem V.property.measurableSet] with x hx
    funext j
    have hN : closure U ∈ 𝓝 (E x) := mem_of_superset (hU.mem_nhds (hInto hx)) subset_closure
    have hF := ((hf (E x) (subset_closure (hInto hx))).contDiffAt hN).differentiableAt one_ne_zero
    change fderiv ℝ g x (axis j) = fderivWithin ℝ f (closure U) (E x) (fderiv ℝ E x (axis j))
    rw [fderiv_comp x hF (hE.differentiable one_ne_zero x),ContinuousLinearMap.comp_apply,
      fderivWithin_of_mem_nhds hN]
  have hG : HasWeakGradient V g G := HolderToCK.hasWeakGradient_of_contDiffOn_one V
    (hf.comp hE.contDiffOn (hInto.mono_right subset_closure))
  have hgGraph : MemW12 V g G := by
    refine ⟨hG,hCTop.mono_exponent le_top,fun j => ?_⟩
    exact MemLp.ae_eq (hEq.mono fun _ h => (congrFun h j).symm) ((hDTop j).mono_exponent le_top)
  exact ⟨hgGraph.congr_ae EventuallyEq.rfl hEq,
    hCTop.mono_exponent le_top,fun j => (hDTop j).mono_exponent le_top⟩

end Thesis
