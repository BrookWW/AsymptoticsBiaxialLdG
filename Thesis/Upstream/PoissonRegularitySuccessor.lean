module

public import Thesis.Upstream.WeakPoissonCoordinates
public import Thesis.Upstream.PoissonGradientBound
import HolderToCK.Analysis.Poisson.WeakHarmonicSmooth
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! The local C^(n+1) bootstrap for the same continuous tensor Poisson field. -/

public section

noncomputable section

open Filter HarmonicMaps HolderToCK MeasureTheory Metric Set
open scoped ContDiff Convolution Laplacian Matrix.Norms.Frobenius Topology

namespace Thesis

private theorem compact_newtonian_contDiff_succ {d q n : ℕ} (hd : 2 ≤ d)
    {g : Domain d → Ambient q} (hg : ContDiff ℝ n g) (hc : HasCompactSupport g) :
    ContDiff ℝ (↑(n+1) : WithTop ℕ∞) (newtonianPotential hd g) := by
  let P := newtonianPotential hd g
  obtain ⟨hP,hCols,_⟩ := compact_continuous_newtonian_regular hd hg.continuous hc
  change ContDiff ℝ (↑(n+1) : WithTop ℕ∞) P
  rw [Nat.cast_add,Nat.cast_one]
  apply contDiff_succ_iff_fderiv_apply.mpr
  refine ⟨hP.differentiable one_ne_zero,by simp,?_⟩
  intro v
  have hRepr : ∑ i : Fin d, v i • EuclideanSpace.single i 1 = v := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  have hEq : (fun x => fderiv ℝ P x v) = fun x =>
      ∑ i : Fin d, v i • potentialGradientColumn i g x := by
    funext x
    calc
      fderiv ℝ P x v = fderiv ℝ P x (∑ i : Fin d, v i • EuclideanSpace.single i 1) :=
        congrArg (fderiv ℝ P x) hRepr.symm
      _ = _ := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
        exact congrArg (fun w : Ambient q => v i • w) (hCols x i)
  rw [hEq]
  apply ContDiff.sum
  intro i _
  have hColumn : ContDiff ℝ n (potentialGradientColumn i g) :=
    hc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (normalizedRadialColumn_locallyIntegrable (by omega : 0 < d) i) hg
  exact hColumn.const_smul (v i)

private theorem exists_compact_forcing_cutoff {q n : ℕ} {Ω : Set Point} (hΩ : IsOpen Ω)
    {x : Point} {r : ℝ} (hr : 0 < r) (hB : closedBall x (2*r) ⊆ Ω)
    {F : Point → Ambient q} (hF : ContDiffOn ℝ n F Ω) :
    ∃ g : Point → Ambient q, ContDiff ℝ n g ∧ HasCompactSupport g ∧ EqOn g F (ball x r) := by
  let χ : ContDiffBump x := ⟨r,2*r,hr,by linarith only [hr]⟩
  let g (y : Point) := χ y • F y
  have hχ : tsupport (χ : Point → ℝ) ⊆ Ω := by rw [χ.tsupport_eq]; exact hB
  have hg : ContDiff ℝ n g := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ Ω
    · exact (χ.contDiff (n := n)).contDiffAt.smul (hF.contDiffAt (hΩ.mem_nhds hy))
    · have hZero : ContDiffAt ℝ n (fun _ : Point => (0 : Ambient q)) y := contDiffAt_const
      apply hZero.congr_of_eventuallyEq
      have hy' : y ∈ (tsupport (χ : Point → ℝ))ᶜ := fun h => hy (hχ h)
      filter_upwards [(isClosed_tsupport (χ : Point → ℝ)).isOpen_compl.mem_nhds hy'] with z hz
      change χ z • F z = 0
      rw [image_eq_zero_of_notMem_tsupport (f := (χ : Point → ℝ)) hz,zero_smul]
  refine ⟨g,hg,χ.hasCompactSupport.smul_right,?_⟩
  intro y hy
  change χ y • F y = F y
  rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy),one_smul]

/-- On an arbitrary open set, continuity of the same weak solution and
C^n regularity of its forcing give C^(n+1) regularity of that solution. -/
theorem IsWeakPoisson.contDiffOn_succ_frobenius {Ω : Set Point} {u : Point → S0}
    {D : Point → Thesis.Gradient} {F : Point → Tensor} (hEq : IsWeakPoisson Ω D F)
    (n : ℕ) (hΩ : IsOpen Ω) (hu : MemH1Loc Ω u D)
    (huC : ContinuousOn u Ω) (hF : ContDiffOn ℝ n F Ω) :
    ContDiffOn ℝ (↑(n+1) : WithTop ℕ∞) u Ω := by
  obtain ⟨huW,hWeak⟩ := hEq.to_frobenius hΩ hu
  let S := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    traceFreeSymmetricPartCLM
  let G := S ∘ F
  let u' := frobeniusField u
  have hG : ContDiffOn ℝ n G Ω := S.contDiff.comp_contDiffOn hF
  have hu'C : ContinuousOn u' Ω :=
    frobeniusCoordinateEquiv.continuous.comp_continuousOn huC
  intro x hx
  obtain ⟨ρ,hρ,hρΩ⟩ := Metric.isOpen_iff.mp hΩ x hx
  let r := ρ/4
  have hr : 0 < r := div_pos hρ (by norm_num)
  have hB : closedBall x (2*r) ⊆ Ω := (closedBall_subset_ball (by dsimp only [r]; linarith only [hρ])).trans hρΩ
  obtain ⟨g,hg,hgc,hgG⟩ := exists_compact_forcing_cutoff hΩ hr hB hG
  let V := ballDomain x r
  have hV : V.val ⊆ Ω := (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith only [hr]))).trans hB
  let P := newtonianPotential (by decide : 2 ≤ 3) g
  let DP (y : Point) (i : Fin 3) := potentialGradientColumn i g y
  have hPC := compact_newtonian_contDiff_succ (by decide : 2 ≤ 3) hg hgc
  obtain ⟨hP₁,hPDeriv,hPWeak⟩ := compact_continuous_newtonian_regular
    (by decide : 2 ≤ 3) hg.continuous hgc
  have hVlarge : V.val ⊆ (ballDomain (0 : Point) (‖x‖+r+1)).val := by
    intro y hy
    have hyx : dist y x < r := hy
    apply mem_ball.mpr
    have hT := dist_triangle y x (0 : Point)
    simp only [dist_zero_right] at hT ⊢
    linarith only [hT,hyx]
  have hPV : MemW12Loc V P DP := by
    have he : (fun y i => fderiv ℝ P y (EuclideanSpace.single i 1)) = DP :=
      funext fun y => funext (hPDeriv y)
    exact he ▸ memW12Loc_of_contDiffOn_one V hP₁.contDiffOn
  have huV := huW.mono hV
  let W := u'-P
  let DW (y : Point) (i : Fin 3) := frobeniusGradient D y i - DP y i
  have hWS : MemW12Loc V W DW := by
    refine ⟨huV.1.sub hPV.1,?_ ,?_⟩
    · intro T hT hTV
      exact (huV.2.1 T hT hTV).sub (hPV.2.1 T hT hTV)
    · intro i T hT hTV
      exact (huV.2.2 i T hT hTV).sub (hPV.2.2 i T hT hTV)
  have hWPoisson : WeakPoissonOn V DW (fun _ => 0) := by
    apply ((hWeak.mono hV).sub ((hPWeak (‖x‖+r+1)).mono hVlarge)).congr EventuallyEq.rfl
    filter_upwards [ae_restrict_mem V.property.measurableSet] with y hy
    change G y - g y = 0
    rw [hgG hy,sub_self]
  have hWC : ContinuousOn W V.val := (hu'C.mono hV).sub hP₁.continuous.continuousOn
  have hW := (hWPoisson.contDiffOn_of_continuous_weak_harmonic (by decide) V hWS hWC).1
  have huVDiff : ContDiffOn ℝ (↑(n+1) : WithTop ℕ∞) u' V.val := by
    have h := (hW.of_le (WithTop.coe_le_coe.mpr le_top)).add hPC.contDiffOn
    exact h.congr (fun y _ => (sub_add_cancel (u' y) (P y)).symm)
  have huV' : ContDiffOn ℝ (↑(n+1) : WithTop ℕ∞) u V.val := by
    have h := frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn huVDiff
    exact h.congr (fun y _ => (frobeniusCoordinateEquiv.symm_apply_apply (u y)).symm)
  exact (huV'.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))).contDiffWithinAt

/-- The successor clause of the original local Poisson regularity interface. -/
theorem interiorPoissonRegularity_contDiffOn_succ {Ω : Set Point} {u : Point → S0}
    {D : Point → Thesis.Gradient} {F : Point → Tensor} (n : ℕ)
    (hΩ : IsOpen Ω) (hu : MemH1Loc Ω u D) (hEq : IsWeakPoisson Ω D F)
    (huC : ContinuousOn u Ω) (hF : ContDiffOn ℝ n F Ω) :
    ContDiffOn ℝ (↑(n+1) : WithTop ℕ∞) u Ω :=
  hEq.contDiffOn_succ_frobenius n hΩ hu huC hF

end Thesis
