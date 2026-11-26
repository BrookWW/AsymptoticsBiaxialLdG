module

public import Thesis.Variational.SecondDerivativeCalculus
public import Thesis.Upstream.LpTranslationAverages
public import HolderToCK.Analysis.Poisson.PotentialRegularityMollification
import Mathlib.Analysis.Calculus.Rademacher

/-! Differentiating a compact-kernel mollification of Lipschitz data. -/

public section

noncomputable section

open Filter Function HarmonicMaps HolderToCK MeasureTheory Metric Set
open scoped ContDiff Convolution ENNReal NNReal Topology

namespace Thesis

private theorem compactDataMollification_eq_shifted_integral
    {f : Point → ℝ} (h : PositiveRadius) (x : Point) :
    compactDataMollification f h x = ∫ z, scaledMollifierKernel 3 h (x-z) * f z := by
  rw [compactDataMollification, ← integral_sub_left_eq_self
    (fun z => scaledMollifierKernel 3 h z • f (x-z)) volume x]
  simp only [sub_sub_cancel,smul_eq_mul]

/-- The derivative of a compact mollification is the mollification of the almost
everywhere derivative of a Lipschitz scalar field. -/
theorem coordDeriv_compactDataMollification_of_lipschitz {f : Point → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) (h : PositiveRadius) (j : Fin 3) :
    coordDeriv j (compactDataMollification f h) = compactDataMollification (coordDeriv j f) h := by
  funext x
  let k := scaledMollifierKernel 3 h
  let e := axis j
  let φ (z : Point) := k (x-z)
  have hk : ContDiff ℝ ∞ k := scaledMollifierKernel_contDiff 3 h
  have hkS : HasCompactSupport k := scaledMollifierKernel_hasCompactSupport 3 h
  have hφ : ContDiff ℝ ∞ φ := hk.comp (contDiff_const.sub contDiff_id)
  have hφS : HasCompactSupport φ := hkS.comp_homeomorph (Homeomorph.subLeft x)
  obtain ⟨L, hφL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφS hφ (by simp)
  let A : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hLoc := hf.continuous.locallyIntegrable (μ := (volume : Measure Point))
  have hC := hkS.hasFDerivAt_convolution_right A.flip hLoc (hk.of_le (by simp)) x
  rw [convolution_flip] at hC
  have hDeriv : coordDeriv j (compactDataMollification f h) x = ∫ z, fderiv ℝ k (x-z) e * f z := by
    change fderiv ℝ (k ⋆[A, volume] f) x e = _
    rw [hC.fderiv,convolution_precompR_apply A.flip hLoc (hkS.fderiv ℝ)
      (hk.continuous_fderiv (by simp)) x e]
    rfl
  have hLine (z : Point) : lineDeriv ℝ φ z (-e) = fderiv ℝ k (x-z) e := by
    have hSub := (hasFDerivAt_const (𝕜 := ℝ) x z).sub (hasFDerivAt_id z)
    have hD := ((hk.differentiable (by simp) (x-z)).hasFDerivAt.comp z hSub).hasLineDerivAt (-e)
    rw [show lineDeriv ℝ φ z (-e) = _ from hD.lineDeriv]
    simp
  have hLineF : ∀ᵐ z ∂(volume : Measure Point), lineDeriv ℝ f z e = coordDeriv j f z := by
    filter_upwards [hf.ae_differentiableAt (μ := (volume : Measure Point))] with z hz
    exact (hz.hasFDerivAt.hasLineDerivAt e).lineDeriv
  rw [hDeriv,compactDataMollification_eq_shifted_integral]
  calc
    _ = ∫ z, lineDeriv ℝ φ z (-e) * f z := by simp only [hLine]
    _ = ∫ z, lineDeriv ℝ f z e * φ z :=
      (hf.integral_lineDeriv_mul_eq (μ := volume) hφL hφS e).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hLineF] with z hz
      rw [hz,mul_comm]

theorem measurable_coordDeriv_scalar {f : Point → ℝ} (j : Fin 3) :
    Measurable (coordDeriv j f) :=
  measurable_fderiv_apply_const ℝ f (axis j)

/-- The coordinate derivatives of a Lipschitz field are uniformly bounded. -/
theorem abs_coordDeriv_le_of_lipschitz {f : Point → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (j : Fin 3) (x : Point) : ‖coordDeriv j f x‖ ≤ K := by
  have hAxis : ‖axis j‖ = 1 := by simp [axis]
  exact ((fderiv ℝ f x).le_opNorm (axis j)).trans
    (by simpa only [hAxis,mul_one] using norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x))

/-- The actual coordinate Laplacian commutes with mollification of Lipschitz
data with Lipschitz first derivative columns. -/
theorem laplacian_compactDataMollification_of_lipschitz_columns {f : Point → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f)
    (hCols : ∀ j : Fin 3, ∃ L : ℝ≥0, LipschitzWith L (coordDeriv j f))
    (h : PositiveRadius) :
    laplacian (compactDataMollification f h) = compactDataMollification (laplacian f) h := by
  funext x
  let k := scaledMollifierKernel 3 h
  have hInt (j : Fin 3) : Integrable (fun z => k z * coordDeriv j (coordDeriv j f) (x-z)) volume := by
    obtain ⟨L,hL⟩ := hCols j
    have hM : Measurable (fun z => coordDeriv j (coordDeriv j f) (x-z)) :=
      (measurable_coordDeriv_scalar j).comp (measurable_const.sub measurable_id)
    simpa only [mul_comm] using (scaledMollifierKernel_integrable 3 h).bdd_mul hM.aestronglyMeasurable
      (Eventually.of_forall fun z => abs_coordDeriv_le_of_lipschitz hL j (x-z))
  calc
    _ = ∑ j : Fin 3, compactDataMollification (coordDeriv j (coordDeriv j f)) h x := by
      unfold laplacian
      apply Finset.sum_congr rfl
      intro j _
      rw [coordDeriv_compactDataMollification_of_lipschitz hf]
      obtain ⟨L,hL⟩ := hCols j
      rw [coordDeriv_compactDataMollification_of_lipschitz hL]
    _ = _ := by
      simp only [compactDataMollification,smul_eq_mul,laplacian,Finset.mul_sum]
      rw [integral_finsetSum _ (fun j _ => hInt j)]

/-- Approximate identities converge at every continuity point of measurable data. -/
theorem compactDataMollification_tendsto_of_continuousAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : Point → E} (hf : AEStronglyMeasurable f volume) {x : Point} (hx : ContinuousAt f x) :
    Tendsto (fun n => compactDataMollification f (compactDataApproximationScale n) x)
      atTop (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨r,hr,hR⟩ := Metric.continuousAt_iff.1 hx (ε / 2) (half_pos hε)
  filter_upwards [compactDataApproximationScale_tendsto.eventually (gt_mem_nhds hr)] with n hn
  let h := compactDataApproximationScale n
  have hs : Function.support (scaledMollifierKernel 3 h) ⊆ ball (0 : Point) h.val :=
    (subset_tsupport _).trans ((scaledMollifierKernel_tsupport_subset_halfBall 3 h).trans
      (closedBall_subset_ball (half_lt_self h.property)))
  have hB : dist (compactDataMollification f h x) (f x) ≤ ε / 2 := by
    apply dist_convolution_le (half_pos hε).le hs (scaledMollifierKernel_nonneg 3 h)
      (scaledMollifierKernel_integral_one 3 h) hf
    intro y hy
    exact (hR (hy.trans hn)).le
  exact hB.trans_lt (half_lt_self hε)

end Thesis
