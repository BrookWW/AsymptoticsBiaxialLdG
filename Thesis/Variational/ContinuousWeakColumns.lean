module

public import Thesis.Variational.WeakMorreyClosure
public import Thesis.Upstream.MinimizingSobolev
import Thesis.Variational.SmoothDomainClosedDerivative
import HolderToCK.Analysis.ContinuousMollification
import HolderToCK.Analysis.GradientLinearAlgebra
import HarmonicMaps.Analysis.SobolevAECongruence
import HarmonicMaps.Analysis.SobolevMollificationGradient

/-! Continuous weak columns identify the actual closed-domain derivative. -/

public section

noncomputable section

open Filter HarmonicMaps HolderToCK MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis

/-- The continuous representatives of a weak graph give an actual
Fréchet derivative in its domain. -/
theorem hasFDerivAt_of_continuous_weak_columns
    {n q : ℕ} (U : OpenDomain n)
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hu : MemW12 U u D) (huC : ContinuousOn u U.val)
    (hDC : ∀ j, ContinuousOn (fun x => D x j) U.val)
    {a : Domain n} (ha : a ∈ U.val) :
    HasFDerivAt (𝕜 := ℝ) u (∑ j : Fin n, (PiLp.proj 2 (𝕜 := ℝ) (fun _ => ℝ) j).smulRight (D a j)) a := by
  obtain ⟨R,hR,hInto⟩ := Metric.mem_nhds_iff.mp (U.property.mem_nhds ha)
  let Ω := ballDomain a R
  let W := closedBall a (R/4)
  have hK : closedBall a (R/2) ⊆ Ω.val := closedBall_subset_ball (half_lt_self hR)
  have h' : MemW12 Ω u D :=
    ⟨hu.1.mono hInto,hu.2.1.mono_measure (Measure.restrict_mono_set _ hInto),
      fun j => (hu.2.2 j).mono_measure (Measure.restrict_mono_set _ hInto)⟩
  let h (k : ℕ) : PositiveRadius := ⟨1/((k : ℝ)+1),by positivity⟩
  have hh : Tendsto (fun k => (h k).val) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let P (k : ℕ) := euclideanMollification Ω u h'.integrable_ball (h k)
  let Q (k : ℕ) (j : Fin n) := euclideanMollification Ω (fun x => D x j)
    (h'.column_integrable_domain measure_ball_ne_top j) (h k)
  let B (x : Domain n) : Domain n →L[ℝ] Ambient q :=
    ∑ j : Fin n, (PiLp.proj 2 (𝕜 := ℝ) (fun _ => ℝ) j).smulRight (D x j)
  have hSmooth (k : ℕ) : ContDiff ℝ ∞ (P k) :=
    euclideanMollification_contDiff Ω u h'.integrable_ball (h k)
  have hP : TendstoUniformlyOn P u atTop W :=
    euclideanMollification_tendstoUniformlyOn_closedBall_of_continuous Ω u h'.integrable_ball
      a (by linarith : R/4 < R/2) hK (huC.mono (hK.trans hInto)) h hh
  have hQ (j : Fin n) : TendstoUniformlyOn (fun k => Q k j) (fun x => D x j) atTop W :=
    euclideanMollification_tendstoUniformlyOn_closedBall_of_continuous Ω (fun x => D x j)
      (h'.column_integrable_domain measure_ball_ne_top j) a (by linarith : R/4 < R/2) hK
      ((hDC j).mono (hK.trans hInto)) h hh
  have hSmall : ∀ᶠ k in atTop, (h k).val < R/2 := hh.eventually (Iio_mem_nhds (half_pos hR))
  have hColumn (k : ℕ) (hk : (h k).val < R/2) (x : Domain n) (hx : x ∈ W) (j : Fin n) :
      fderiv ℝ (P k) x (EuclideanSpace.single j 1) = Q k j x := by
    have hSample (y : Domain n) (hy : y ∈ tsupport (scaledMollifierKernel n (h k))) : x-y ∈ Ω.val := by
      have hY := scaledMollifierKernel_tsupport_subset_halfBall n (h k) hy
      have hz : ‖y‖ ≤ (h k).val/2 := by simpa only [mem_closedBall,dist_zero_right] using hY
      have hxa : dist x a ≤ R/4 := hx
      have hDist : dist (x-y) x = ‖y‖ := by rw [dist_eq_norm,sub_sub_cancel_left,norm_neg]
      change dist (x-y) a < R
      exact (dist_triangle (x-y) x a).trans_lt (by linarith only [hDist,hxa,hz,hk,hR])
    exact h'.1.kernelConvolution_coordinateDerivative h'.integrable_ball
      (scaledMollifierKernel_contDiff n (h k)) (scaledMollifierKernel_hasCompactSupport n (h k)) x hSample j
  have hDer : TendstoUniformlyOn (fun k => fderiv ℝ (P k)) B atTop W := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    let d := ε/(Real.sqrt n+1)
    have hd : 0 < d := div_pos hε (by positivity)
    have hAll : ∀ᶠ k in atTop, ∀ j : Fin n, ∀ x ∈ W, dist (D x j) (Q k j x) < d :=
      eventually_all.2 fun j => (Metric.tendstoUniformlyOn_iff.mp (hQ j)) d hd
    filter_upwards [hSmall,hAll] with k hk hApprox x hx
    let L := fderiv ℝ (P k) x - B x
    have hL (j : Fin n) : ‖L (EuclideanSpace.single j 1)‖ ≤ d := by
      change ‖(fderiv ℝ (P k) x - B x) (EuclideanSpace.single j 1)‖ ≤ d
      rw [sub_apply,hColumn k hk x hx j]
      have hb : B x (EuclideanSpace.single j 1) = D x j := columnLinearMap_single (D x) j
      rw [hb,← dist_eq_norm,dist_comm]
      exact (hApprox j x hx).le
    have hLbd := norm_linearMap_le_of_columns_bound L hd.le hL
    rw [dist_comm,dist_eq_norm]
    refine hLbd.trans_lt ?_
    have hE : (Real.sqrt n+1)*d = ε := by
      dsimp only [d]
      field_simp
    nlinarith only [hE,hd]
  let V := ball a (R/4)
  have hVW : V ⊆ W := ball_subset_closedBall
  apply hasFDerivAt_of_tendstoUniformlyOn (s := V) isOpen_ball (hDer.mono hVW)
  · intro k x _
    exact ((hSmooth k).differentiable (by simp) x).hasFDerivAt
  · intro x hx
    exact hP.tendsto_at (hVW hx)
  · exact mem_ball_self (by positivity : 0 < R/4)

/-- A weak first graph with (L^p) second columns, (p>3), upgrades a
continuous representative to class (C^1) on the actual smooth closure. -/
theorem IsSmoothDomain.contDiffOn_one_of_weak_secondColumnsLp
    {U : Set Point} (hU : IsSmoothDomain U) {q : ℕ} {p : ℝ} (hp : 3 < p)
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 ⟨U,hU.1.1⟩ u D) (hC : ContinuousOn u (closure U))
    {H : Point → Fin 3 → HarmonicMaps.Gradient 3 q}
    (hH : ∀ j, MemW12 ⟨U,hU.1.1⟩ (fun x => D x j) (fun x => H x j))
    (hLp : ∀ j i, MemLp (fun x => H x j i) (ENNReal.ofReal p) (volume.restrict U)) :
    ContDiffOn ℝ 1 u (closure U) := by
  choose g hEq hGC using fun j : Fin 3 =>
    hU.exists_weakMorreyClosureRepresentative hp (hH j) (hLp j)
  let G (x : Point) (j : Fin 3) := g j x
  let B (x : Point) : Point →L[ℝ] Ambient q :=
    ∑ j : Fin 3, (PiLp.proj 2 (𝕜 := ℝ) (fun _ => ℝ) j).smulRight (G x j)
  have hDG : D =ᵐ[volume.restrict U] G := by
    filter_upwards [ae_all_iff.2 hEq] with x hx
    exact funext hx
  have hU' : MemW12 ⟨U,hU.1.1⟩ u G := hu.congr_ae EventuallyEq.rfl hDG
  exact hU.contDiffOn_one_of_continuous_derivative (D := B) hC (columnLinearMap_continuousOn hGC)
    (fun x hx => hasFDerivAt_of_continuous_weak_columns ⟨U,hU.1.1⟩ hU'
      (hC.mono subset_closure) (fun j => (hGC j).mono subset_closure) hx)

local instance continuousWeakColumnsTensorENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

/-- The same closed-domain regularity on the literal Frobenius weak graph. -/
theorem IsSmoothDomain.contDiffOn_one_of_tensor_weak_secondColumnsLp
    {U : Set Point} (hU : IsSmoothDomain U) {p : ℝ} (hp : 3 < p)
    {u : Point → S0} {D : Point → Thesis.Gradient}
    (hu : MemH1 U u D) (hC : ContinuousOn u (closure U))
    {H : Point → Fin 3 → Thesis.Gradient}
    (hH : ∀ j, MemH1 U (fun x => D x j) (fun x => H x j))
    (hLp : ∀ j i, MemLp (fun x => H x j i) (ENNReal.ofReal p) (volume.restrict U)) :
    ContDiffOn ℝ 1 u (closure U) := by
  let O : OpenDomain 3 := ⟨U,hU.1.1⟩
  let G (x : Point) (j i : Fin 3) := frobeniusCoordinateEquiv (H x j i)
  have hU' : MemW12 O (frobeniusField u) (frobeniusGradient D) := (memH1_iff_memW12 O _ _).1 hu
  have hC' : ContinuousOn (frobeniusField u) (closure U) :=
    frobeniusCoordinateEquiv.continuous.comp_continuousOn hC
  have hH' (j : Fin 3) : MemW12 O (fun x => frobeniusGradient D x j) (fun x => G x j) :=
    (memH1_iff_memW12 O _ _).1 (hH j)
  have hLp' (j i : Fin 3) : MemLp (fun x => G x j i) (ENNReal.ofReal p) (volume.restrict U) :=
    (frobeniusCoordinateEquiv_memLp_iff _ _ _).2 (hLp j i)
  have hReg := hU.contDiffOn_one_of_weak_secondColumnsLp hp hU' hC' hH' hLp'
  have hUreg := frobeniusCoordinateEquiv.symm.contDiff.comp_contDiffOn hReg
  simpa only [Function.comp_def,frobeniusField,frobeniusCoordinateEquiv.symm_apply_apply] using hUreg

end Thesis
