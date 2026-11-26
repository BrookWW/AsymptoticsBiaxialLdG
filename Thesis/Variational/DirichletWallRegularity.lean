module

public import Thesis.Variational.WeakDirichletClosureC2
import Thesis.Variational.FlatWallRegularityFromWeakTangents
import Thesis.Variational.DirichletWallThirdFour
import Thesis.Variational.DirichletPoissonH2

/-! Native second-order regularity at the physical Dirichlet wall. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis

local instance closedDirichletWallContinuousENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

/-- The local reflected weak (W³,⁴) estimate gives the second derivative of
the original continuous representative on the physical domain closure. -/
theorem weakZeroTracePoissonClosureTwo : WeakZeroTracePoissonClosureTwo := by
  apply weakZeroTracePoissonClosureTwo_of_wall
  intro U hU w f v hf hf₂ hPair hv hv₁ _ _ _ a ha
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  let L := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let fv := frobeniusField v
  let ff := frobeniusField f
  have hf' : ContDiffOn ℝ 1 ff (closure U) := L.contDiff.comp_contDiffOn hf
  have hv' : ContinuousOn fv (closure U) := L.continuous.comp_continuousOn hv₁.continuousOn
  have hData := h10_ambientDirichletPoissonData_of_ae_representative hU.1.1 w hf₂ hv hPair
  have hf₀ : MemLp (U.indicator ff) 4 volume := by
    apply (memLp_indicator_iff_restrict hU.1.1.measurableSet).2
    obtain ⟨M,hM⟩ := hU.1.2.2.isCompact_closure.exists_bound_of_continuousOn hf'.continuousOn
    have hMeas := ((frobeniusCoordinateEquiv_memLp_iff μ 2 f).2 hf₂).1
    exact MemLp.of_bound hMeas M
      ((ae_restrict_mem hU.1.1.measurableSet).mono fun x hx => hM x (subset_closure hx))
  have hfEq : ff =ᵐ[μ] U.indicator ff :=
    (ae_restrict_mem hU.1.1.measurableSet).mono fun x hx => (indicator_of_mem hx ff).symm
  obtain ⟨P,r,hPa,hP,hr,hBall,hW₃⟩ :=
    exists_weakDirichletPoisson_wallChart_thirdFour hU ha hData hf₀ hf' hfEq
  let V := upperCoordinateHalfSpace.val ∩ ball (0 : Point) r
  have hO : IsOpen V := upperCoordinateHalfSpace.property.inter isOpen_ball
  have hInto : MapsTo P.flatChart V U :=
    fun x hx => (P.flatChart_mem_domain (hBall hx.2)).2 hx.1
  have hInd : U.indicator fv ∘ P.flatChart =ᵐ[volume.restrict V] fv ∘ P.flatChart :=
    (ae_restrict_mem hO.measurableSet).mono fun x hx => indicator_of_mem (hInto hx) fv
  have hC := P.contDiffWithinAt_of_flat_weakLpDerivatives 2
    (hP.of_le (WithTop.coe_le_coe.mpr le_top)) (hPa.symm ▸ frontier_subset_closure ha)
    hr hBall (p := 4) (by norm_num) hv'
    (by simpa only [ENNReal.ofReal_ofNat] using hW₃.congr_ae hInd)
  rw [hPa] at hC
  have hInv := frobeniusCoordinateEquiv.symm.contDiff.comp_contDiffWithinAt hC
  have hTwo : ContDiffWithinAt ℝ (↑(2 : ℕ) : ℕ∞ω) v (closure U) a := by
    simpa only [Function.comp_def,fv,frobeniusField,frobeniusCoordinateEquiv.symm_apply_apply] using hInv
  exact_mod_cast hTwo

end Thesis
