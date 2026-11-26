module

public import Thesis.Variational.MorreyDomainCharts
public import Thesis.Variational.BoundaryPohozaev
import Thesis.Variational.LocalMorreyFromLp
import Thesis.Variational.SmoothWallGeometry
import Thesis.Foundation.Frobenius
import StratificationTheory.Foundation.DominatedL2Pullback
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! Hölder control of the actual within-closure gradient on physical charts. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped ContDiff ENNReal NNReal Matrix Matrix.Norms.Frobenius Topology

namespace Thesis

local instance morreyColumnOperatorNormed : NormedAddCommGroup (Point →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance morreyColumnOperatorSpace : NormedSpace ℝ (Point →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

private def gradientColumnCoordinates (U : Set Point) (v : Point → S0) (j : Fin 3)
    (x : Point) : Ambient 5 := frobeniusCoordinateEquiv (closureGradient U v x j)

private theorem gradientColumnCoordinates_contDiffOn {U : Set Point} (hU : IsSmoothDomain U)
    {v : Point → S0} (hv : ContDiffOn ℝ 2 v (closure U)) (j : Fin 3) :
    ContDiffOn ℝ 1 (gradientColumnCoordinates U v j) (closure U) := by
  have hD := (ContinuousLinearMap.apply ℝ S0 (axis j)).contDiff.comp_contDiffOn
    (hv.fderivWithin hU.uniqueDiffOn_closure (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2))
  exact frobeniusCoordinateEquiv.toContinuousLinearEquiv.contDiff.comp_contDiffOn hD

private theorem gradientColumnCoordinates_differentiableAt_and_bound {U : Set Point}
    (hU : IsSmoothDomain U) {v : Point → S0} (hv : ContDiffOn ℝ 2 v (closure U))
    (j : Fin 3) {x : Point} (hx : x ∈ U) :
    DifferentiableAt ℝ (gradientColumnCoordinates U v j) x ∧
      ∀ z, ‖fderiv ℝ (gradientColumnCoordinates U v j) x z‖ ≤
        ‖iteratedFDeriv ℝ 2 v x‖ * ‖z‖ := by
  let N := closure U
  let L : (Point →L[ℝ] S0) →L[ℝ] Ambient 5 :=
    frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.apply ℝ S0 (axis j))
  have hOpen := hU.1.1
  have hDiff : ContDiffAt ℝ 2 v x := hv.contDiffAt (mem_of_superset (hOpen.mem_nhds hx) subset_closure)
  have hDerC : ContDiffAt ℝ 1 (fderiv ℝ v) x := hDiff.fderiv_right (by norm_num)
  have hDer : DifferentiableAt ℝ (fderiv ℝ v) x := hDerC.differentiableAt one_ne_zero
  have hComp := L.hasFDerivAt.comp x hDer.hasFDerivAt
  have hEq : (L ∘ fderiv ℝ v) =ᶠ[𝓝 x] gradientColumnCoordinates U v j := by
    filter_upwards [hOpen.mem_nhds hx] with y hy
    have hNy : N ∈ 𝓝 y := mem_of_superset (hOpen.mem_nhds hy) subset_closure
    have hDiffy := (hv.contDiffAt hNy).differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
    have hD := fderivWithin_eq_fderiv (uniqueDiffWithinAt_of_mem_nhds hNy) hDiffy
    change (L ∘ fderiv ℝ v) y = (L ∘ fderivWithin ℝ v N) y
    with_unfolding_all exact congrArg (fun D : Point →L[ℝ] S0 => L D) hD.symm
  have hComp' := hComp.congr_of_eventuallyEq hEq.symm
  refine ⟨hComp'.differentiableAt, fun z => ?_⟩
  rw [hComp'.fderiv]
  change ‖frobeniusCoordinateEquiv ((fderiv ℝ (fderiv ℝ v) x z) (axis j))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  have hPair : (fderiv ℝ (fderiv ℝ v) x z) (axis j) = iteratedFDeriv ℝ 2 v x ![z, axis j] := by
    rw [iteratedFDeriv_two_apply]
    rfl
  rw [hPair]
  have hAxis : ‖axis j‖ = 1 := by simp [axis]
  have hV := (iteratedFDeriv ℝ 2 v x).le_opNorm ![z, axis j]
  simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hAxis, mul_one] using hV

private theorem eLpNorm_mul_pullback_le {U : Set Point} (A : MorreyDomainChart U)
    {p L H : ℝ} (hp : 0 < p) (hL : 0 ≤ L)
    {g : Point → ℝ} (hg : MemLp g (ENNReal.ofReal p) (volume.restrict U))
    (hNorm : eLpNorm g (ENNReal.ofReal p) (volume.restrict U) ≤ ENNReal.ofReal H) :
    let μ := (volume : Measure Point).restrict (ball 0 1)
    let P := (A.chart : Point → Point) ∘ A.fold
    MemLp (fun x => L * g (P x)) (ENNReal.ofReal p) μ ∧
    eLpNorm (fun x => L * g (P x)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (L * (A.density : ℝ) ^ (1 / p) * H) := by
  let μ := (volume : Measure Point).restrict (ball 0 1)
  let P := (A.chart : Point → Point) ∘ A.fold
  have hPm : AEMeasurable P μ := (A.chart.continuous.comp A.fold_lipschitz.continuous).measurable.aemeasurable
  have hgP := memLp_comp_of_map_le_smul hPm ENNReal.coe_ne_top A.map_fold_le hg
  refine ⟨hgP.const_mul L, ?_⟩
  have hE := eLpNorm_comp_le_of_map_le_smul (p := ENNReal.ofReal p) hPm A.map_fold_le hg.1
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofReal hp.le] at hE
  change eLpNorm (L • (g ∘ P)) (ENNReal.ofReal p) μ ≤ _
  rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_of_nonneg hL,
    ENNReal.ofReal_mul (mul_nonneg hL (Real.rpow_nonneg A.density.coe_nonneg _)),
    ENNReal.ofReal_mul hL, ← ENNReal.ofReal_rpow_of_nonneg A.density.coe_nonneg
      (one_div_nonneg.mpr hp.le), ENNReal.ofReal_coe_nnreal, mul_assoc]
  exact mul_le_mul_right ((hE.trans (mul_le_mul_right hNorm _))) _

/-- On the inner part of a physical unit chart, the actual closed-domain
gradient is Hölder with a constant independent of the field and its size. -/
theorem MorreyDomainChart.exists_gradient_holder_of_hessianLp {U : Set Point}
    (A : MorreyDomainChart U) (hU : IsSmoothDomain U)
    {α p : ℝ} (hα : 0 < α) (hα₁ : α < 1) (hp : 3 < p) (hαp : α = 1 - 3 / p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Point → S0) (_ : ContDiffOn ℝ 2 v (closure U))
      (H : ℝ) (_ : 0 ≤ H),
      MemLp (fun x => ‖iteratedFDeriv ℝ 2 v x‖) (ENNReal.ofReal p) (volume.restrict U) →
      eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 v x‖) (ENNReal.ofReal p) (volume.restrict U) ≤ ENNReal.ofReal H →
      ∀ x ∈ A.chart '' ball (0 : Point) (1 / 2), x ∈ closure U →
      ∀ y ∈ A.chart '' ball (0 : Point) (1 / 2), y ∈ closure U →
        ‖closureGradient U v x - closureGradient U v y‖ ≤ C * H * dist x y ^ α := by
  obtain ⟨C₀, hC₀, hMorrey⟩ := exists_unitBall_holder_of_lp_columns hα hα₁
  let P := (A.chart : Point → Point) ∘ A.fold
  let μ := (volume : Measure Point).restrict (ball 0 1)
  have hPmap : MapsTo A.fold (closedBall (0 : Point) 1) (closedBall (0 : Point) 1) :=
    fun _ h => A.core_subset (A.fold_maps h)
  have hPLip : LipschitzOnWith A.lip P (ball (0 : Point) 1) := by
    have h := A.lipschitz.comp A.fold_lipschitz.lipschitzOnWith hPmap
    rw [mul_one] at h
    exact h.mono ball_subset_closedBall
  obtain ⟨T, hT, hTP⟩ := hPLip.extend_finite_dimension
  let L := (lipschitzExtensionConstant Point * A.lip : ℝ≥0)
  let c := (A.density : ℝ) ^ (1 / p)
  have hc : 0 ≤ c := Real.rpow_nonneg A.density.coe_nonneg _
  have hL := L.coe_nonneg
  let I := (A.inverseLip : ℝ) ^ α
  have hI : 0 ≤ I := Real.rpow_nonneg A.inverseLip.coe_nonneg _
  refine ⟨max 1 (C₀ * L * c * I), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro v hv H hH hLp hNorm
  have hPInside : ∀ᵐ z ∂μ, P z ∈ U := by
    have hPm : AEMeasurable P μ :=
      (A.chart.continuous.comp A.fold_lipschitz.continuous).measurable.aemeasurable
    exact ae_of_ae_map hPm ((ae_restrict_mem hU.1.1.measurableSet).filter_mono
      (Measure.absolutelyContinuous_of_le_smul A.map_fold_le).ae_le)
  have hTdiff : ∀ᵐ z ∂μ, DifferentiableAt ℝ T z :=
    (hT.ae_differentiableAt (μ := (volume : Measure Point))).filter_mono
      (ae_mono Measure.restrict_le_self)
  let g (z : Point) := (L : ℝ) * ‖iteratedFDeriv ℝ 2 v (P z)‖
  have hg := eLpNorm_mul_pullback_le A (lt_trans (by norm_num) hp) hL hLp hNorm
  have hColumn (j : Fin 3) (z : Point) (hz : z ∈ ball (0 : Point) (1 / 2))
      (w : Point) (hw : w ∈ ball (0 : Point) (1 / 2)) :
      ‖gradientColumnCoordinates U v j (P z) - gradientColumnCoordinates U v j (P w)‖ ≤
        C₀ * ((L : ℝ) * c * H) * dist z w ^ α := by
    let f := gradientColumnCoordinates U v j
    have hFC : ContDiffOn ℝ 1 (f ∘ A.chart) A.core :=
      (gradientColumnCoordinates_contDiffOn hU hv j).comp
        (A.smooth.of_le (by simp)).contDiffOn A.mapsClosure
    obtain ⟨K, hK⟩ := hFC.exists_lipschitzOnWith one_ne_zero A.core_convex A.core_compact
    have hfLip : LipschitzOnWith K (f ∘ P) (ball (0 : Point) 1) := by
      have h := hK.comp A.fold_lipschitz.lipschitzOnWith A.fold_maps
      rw [mul_one] at h
      exact h.mono ball_subset_closedBall
    have hCols : ∀ᵐ x ∂μ, ∀ i : Fin 3, ‖fderiv ℝ (f ∘ P) x (axis i)‖ ≤ ‖g x‖ := by
      filter_upwards [hPInside, hTdiff, ae_restrict_mem measurableSet_ball] with x hxP hxT hxB i
      have hOn : P =ᶠ[𝓝 x] T := mem_of_superset (isOpen_ball.mem_nhds hxB) hTP
      have hAt : T x = P x := (hTP hxB).symm
      have hF := gradientColumnCoordinates_differentiableAt_and_bound hU hv j hxP
      have hDiff : HasFDerivAt (f ∘ T)
          ((fderiv ℝ f (T x)).comp (fderiv ℝ T x)) x :=
        (hAt ▸ hF.1.hasFDerivAt).comp x hxT.hasFDerivAt
      have hFT : f ∘ P =ᶠ[𝓝 x] f ∘ T := hOn.fun_comp f
      rw [hFT.fderiv_eq, hDiff.fderiv, ContinuousLinearMap.comp_apply, hAt]
      have hAxis : ‖axis i‖ = 1 := by simp [axis]
      have hN : ‖fderiv ℝ T x (axis i)‖ ≤ (L : ℝ) :=
        ((fderiv ℝ T x).le_opNorm _).trans (by
          rw [hAxis, mul_one]
          exact norm_fderiv_le_of_lipschitz ℝ hT)
      have hLe := (hF.2 _).trans (mul_le_mul_of_nonneg_left hN (norm_nonneg _))
      simpa only [g, Real.norm_of_nonneg (mul_nonneg hL (norm_nonneg _)), mul_comm] using hLe
    exact hMorrey 5 (f ∘ P) ⟨K, hfLip⟩ p _ hp hαp (mul_nonneg (mul_nonneg hL hc) hH)
      g hg.1 hg.2 hCols z hz w hw
  rintro x ⟨z, hz, rfl⟩ hx y ⟨w, hw, rfl⟩ hy
  have hzC := A.capturesClosure z hz hx
  have hwC := A.capturesClosure w hw hy
  have hZ : P z = A.chart z := congrArg A.chart (A.fold_fixes hzC)
  have hW : P w = A.chart w := congrArg A.chart (A.fold_fixes hwC)
  have hInv := A.inverse_lipschitz.dist_le_mul (A.chart z) ⟨z, A.core_subset hzC, rfl⟩
    (A.chart w) ⟨w, A.core_subset hwC, rfl⟩
  rw [A.chart.symm_apply_apply, A.chart.symm_apply_apply] at hInv
  have hPower := Real.rpow_le_rpow dist_nonneg hInv hα.le
  rw [Real.mul_rpow A.inverseLip.coe_nonneg dist_nonneg] at hPower
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro j
  have h := hColumn j z hz w hw
  rw [hZ, hW] at h
  change ‖closureGradient U v (A.chart z) j - closureGradient U v (A.chart w) j‖ ≤ _
  have hNormRep :
      ‖closureGradient U v (A.chart z) j - closureGradient U v (A.chart w) j‖ =
      ‖gradientColumnCoordinates U v j (A.chart z) - gradientColumnCoordinates U v j (A.chart w)‖ := by
    change ‖_‖ = ‖frobeniusCoordinateEquiv _ - frobeniusCoordinateEquiv _‖
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  rw [hNormRep]
  calc
    _ ≤ _ := h
    _ ≤ C₀ * ((L : ℝ) * c * H) * (I * dist (A.chart z) (A.chart w) ^ α) :=
      mul_le_mul_of_nonneg_left hPower (by positivity)
    _ = (C₀ * (L : ℝ) * c * I) * H * dist (A.chart z) (A.chart w) ^ α := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hH) (Real.rpow_nonneg dist_nonneg _)

end Thesis
