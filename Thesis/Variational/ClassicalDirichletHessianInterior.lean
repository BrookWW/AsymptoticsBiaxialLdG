module

public import Thesis.Variational.DirichletPoissonHessianCoordinates
import Thesis.Variational.BoundaryL4CapValue
import Thesis.Variational.BoundaryL4Cutoff
import Thesis.Variational.WholeSpaceLipschitzColumnsHessian
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! A compactly supported cutoff gives the classical interior Hessian estimate. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal Topology

namespace Thesis

/-- A local physical cap with a classical Hessian estimate in terms of bounded
amplitude, Laplacian, and first derivative on the whole domain. -/
def HasScalarDirichletHessianCapBound (U : Set Point) (p : ℝ) (a : Point) : Prop :=
  ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ (u : Point → ℝ) (M F G : ℝ),
    0 ≤ M → 0 ≤ F → 0 ≤ G → ContDiffOn ℝ 2 u (closure U) → EqOn u (fun _ => 0) (frontier U) →
    (∀ x ∈ U, ‖u x‖ ≤ M) → (∀ x ∈ U, ‖laplacian u x‖ ≤ F) →
    (∀ x ∈ U, ‖fderiv ℝ u x‖ ≤ G) →
    eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 u x‖) (ENNReal.ofReal p) (volume.restrict (U∩ball a r)) ≤
      ENNReal.ofReal (C*(M+F+G))

/-- The whole-space operator-norm Hessian estimate on compact twice differentiable fields. -/
def ClassicalScalarWholeSpaceHessianLp (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ u : Point → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
    eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 u x‖) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal C*eLpNorm (laplacian u) (ENNReal.ofReal p) volume

/-- The native whole-space estimate applies to compactly supported C² data. -/
theorem classicalScalarWholeSpaceHessianLp (p : ℝ) (hp : 1 < p) : ClassicalScalarWholeSpaceHessianLp p := by
  obtain ⟨C,hC,hBound⟩ := exists_wholeSpace_scalarPoissonHessianLp_lipschitz_columns p hp
  refine ⟨C,hC,?_⟩
  intro u hu huc
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport huc hu (by norm_num)
  have hCols (j : Fin 3) : ∃ L : ℝ≥0, LipschitzWith L (coordDeriv j u) := by
    have hD : ContDiff ℝ 1 (coordDeriv j u) :=
      (ContinuousLinearMap.apply ℝ ℝ (axis j)).contDiff.comp (hu.fderiv_right (by norm_num))
    exact ContDiff.lipschitzWith_of_hasCompactSupport (huc.fderiv_apply ℝ (axis j)) hD one_ne_zero
  exact hBound u hK huc hCols (Eventually.of_forall fun _ => hu.contDiffAt)

private theorem eLpNorm_of_supported_on_ball_bound {a : Point} {s : ℝ} {q : ℝ≥0∞}
    {g : Point → ℝ} {T : ℝ} (hT : 0 ≤ T) (hB : ∀ x ∈ ball a s, ‖g x‖ ≤ T)
    (hZ : ∀ x ∉ ball a s, g x=0) :
    eLpNorm g q volume ≤ ENNReal.ofReal T*eLpNorm (fun _ : Point => (1:ℝ)) q (volume.restrict (ball a s)) := by
  have hEq : (ball a s).indicator g = g := by
    funext x
    by_cases hx : x ∈ ball a s
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,hZ x hx]
  rw [← hEq,eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
  have hK : (fun _ : Point => T) = T • (fun _ : Point => (1:ℝ)) := by funext x; simp
  have hLe := eLpNorm_mono_ae_real (p := q) ((ae_restrict_mem (μ := (volume : Measure Point))
    measurableSet_ball).mono (fun x hx => hB x hx))
  rw [hK,eLpNorm_const_smul,← ofReal_norm,Real.norm_of_nonneg hT] at hLe
  exact hLe

/-- The physical cutoff Laplacian is bounded by the three original sup norms. -/
theorem scalar_dirichlet_cutoff_laplacian_bound {U : Set Point} (hU : IsOpen U)
    {χ u : Point → ℝ} (hχ : ContDiffOn ℝ 2 χ U) (hu : ContDiffOn ℝ 2 u U)
    {s L M F G : ℝ} (hs : 0 < s) (hL : 0 ≤ L) (hM : 0 ≤ M) (hF : 0 ≤ F) (hG : 0 ≤ G)
    {x : Point} (hx : x ∈ U)
    (hχ₀ : |χ x| ≤ 1) (hχD : ‖fderiv ℝ χ x‖ ≤ L/s) (hχL : |laplacian χ x| ≤ L/s^2)
    (huB : ‖u x‖ ≤ M) (hf : ‖laplacian u x‖ ≤ F) (hGrad : ‖fderiv ℝ u x‖ ≤ G) :
    ‖laplacian (χ*u) x‖ ≤ (1+6*L/s+L/s^2)*(M+F+G) := by
  have h := abs_laplacian_cutoff_mul_le hU hχ hu hx hχ₀
  rw [← Real.norm_eq_abs (laplacian (χ*u) x),← Real.norm_eq_abs (laplacian u x),← Real.norm_eq_abs (u x)] at h
  have h1 := mul_le_mul hχD hGrad (norm_nonneg _) (by positivity : 0 ≤ L/s)
  have h2 := mul_le_mul hχL huB (norm_nonneg _) (by positivity : 0 ≤ L/s^2)
  calc
    _ ≤ F + (6*L/s)*G + (L/s^2)*M := by
      simp only [div_eq_mul_inv] at h1 h2 ⊢
      nlinarith only [h,h1,h2,hf]
    _ ≤ _ := by
      have h1' := mul_le_mul_of_nonneg_left
        (show G≤M+F+G from le_add_of_nonneg_left (add_nonneg hM hF)) (by positivity : 0≤6*L/s)
      have h2' := mul_le_mul_of_nonneg_left
        (show M≤M+F+G from (le_add_of_nonneg_right hF).trans (le_add_of_nonneg_right hG)) (by positivity : 0≤L/s^2)
      have h3' : F≤M+F+G := (le_add_of_nonneg_left hM).trans (le_add_of_nonneg_right hG)
      simp only [div_eq_mul_inv] at h1' h2' ⊢
      nlinarith only [h1',h2',h3']

/-- The actual Hessians of two fields agree on any open set on which the fields agree. -/
theorem iteratedFDeriv_two_eqOn_open_of_eqOn {V : Set Point} (hV : IsOpen V)
    {w u : Point → ℝ} (h : EqOn w u V) : EqOn (iteratedFDeriv ℝ 2 w) (iteratedFDeriv ℝ 2 u) V := by
  intro x hx
  rw [← iteratedFDerivWithin_of_isOpen (f := w) 2 hV hx,
    ← iteratedFDerivWithin_of_isOpen (f := u) 2 hV hx]
  exact iteratedFDerivWithin_congr h hx 2

/-- Cutting off strictly inside the physical domain transfers the whole-space estimate. -/
theorem exists_classicalDirichletHessian_interior_patch_of_wholeSpace
    {p : ℝ} (hWhole : ClassicalScalarWholeSpaceHessianLp p) {U : Set Point} (hU : IsOpen U)
    {a : Point} (ha : a ∈ U) : HasScalarDirichletHessianCapBound U p a := by
  obtain ⟨CI,hCI,hInter⟩ := hWhole
  obtain ⟨s,hs,hS⟩ := Metric.isOpen_iff.1 hU a ha
  obtain ⟨L,hL,hCut⟩ := exists_boundaryL4_cutoff
  obtain ⟨χ,hχ,hχN,hχInner,hχSupport,hχDer⟩ := hCut a hs
  let q := ENNReal.ofReal p
  let J := (eLpNorm (fun _ : Point => (1:ℝ)) q (volume.restrict (ball a s))).toReal
  let K := 1+6*L/s+L/s^2
  let C := CI*K*J
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hK : 0 < K := by dsimp only [K]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hJ' : ENNReal.ofReal J = eLpNorm (fun _ : Point => (1:ℝ)) q (volume.restrict (ball a s)) := by
    letI : IsFiniteMeasure (volume.restrict (ball a s)) := isFiniteMeasure_restrict.2 measure_ball_ne_top
    exact ENNReal.ofReal_toReal (memLp_const (μ := volume.restrict (ball a s)) (p := q) (1:ℝ)).eLpNorm_ne_top
  have hχS : HasCompactSupport χ := (isCompact_closedBall a (3*s/4)).of_isClosed_subset
    (isClosed_tsupport χ) hχSupport
  have hχU : tsupport χ ⊆ ball a s := hχSupport.trans (closedBall_subset_ball (by linarith only [hs]))
  refine ⟨s/2,C,half_pos hs,hC,?_⟩
  intro u M F G hM hF hG hu _ huB hf hGrad
  let w := χ*u
  have hSupp : tsupport w ⊆ tsupport χ := tsupport_mul_subset_left
  have hOut (x : Point) (hx : x ∉ tsupport χ) : w =ᶠ[𝓝 x] (fun _ => 0) :=
    (notMem_tsupport_iff_eventuallyEq.1 hx).mono (fun y hy => by
      change χ y*u y = 0
      rw [show χ y = 0 from hy,zero_mul])
  have hw : ContDiff ℝ 2 w := by
    apply contDiff_iff_contDiffAt.2
    intro x
    by_cases hx : x ∈ U
    · have huAt := (hu x (subset_closure hx)).contDiffAt (mem_of_superset (hU.mem_nhds hx) subset_closure)
      exact ((hχ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt).mul huAt
    · exact contDiffAt_const.congr_of_eventuallyEq (hOut x (fun hxχ => hx (hS (hχU hxχ))))
  have hwS : HasCompactSupport w := hχS.of_isClosed_subset (isClosed_tsupport w) hSupp
  have hLapB (x : Point) (hx : x ∈ ball a s) : ‖laplacian w x‖ ≤ K*(M+F+G) := by
    have hu' : ContDiffOn ℝ 2 u U := hu.mono subset_closure
    have hχ' : ContDiffOn ℝ 2 χ U := (hχ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
    have hχabs : |χ x| ≤ 1 := by rw [abs_of_nonneg (hχN x).1]; exact (hχN x).2
    exact scalar_dirichlet_cutoff_laplacian_bound hU hχ' hu' hs hL.le hM hF hG (hS hx) hχabs
      (hχDer x).1 (hχDer x).2 (huB x (hS hx)) (hf x (hS hx)) (hGrad x (hS hx))
  have hLapZ (x : Point) (hx : x ∉ ball a s) : laplacian w x = 0 :=
    laplacian_eq_zero_of_eventuallyEq_const (hOut x (fun hy => hx (hχU hy)))
  have hN := eLpNorm_of_supported_on_ball_bound (q := q) (by positivity : 0 ≤ K*(M+F+G)) hLapB hLapZ
  rw [← hJ'] at hN
  let V := U∩ball a (s/2)
  have hPlateau : EqOn w u (ball a (s/2)) := fun y hy => by
    change χ y*u y = u y
    rw [hχInner (ball_subset_closedBall hy),one_mul]
  have hEq : (fun x => ‖iteratedFDeriv ℝ 2 w x‖) =ᵐ[volume.restrict V]
      (fun x => ‖iteratedFDeriv ℝ 2 u x‖) :=
    (ae_restrict_mem (hU.inter isOpen_ball).measurableSet).mono fun _ hx =>
      congrArg norm (iteratedFDeriv_two_eqOn_open_of_eqOn isOpen_ball hPlateau hx.2)
  rw [← eLpNorm_congr_ae hEq]
  calc
    _ ≤ eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 w x‖) q volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ ENNReal.ofReal CI*eLpNorm (laplacian w) q volume := hInter w hw hwS
    _ ≤ ENNReal.ofReal CI*(ENNReal.ofReal (K*(M+F+G))*ENNReal.ofReal J) :=
      mul_le_mul_right hN _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ K*(M+F+G)),← ENNReal.ofReal_mul hCI.le]
      congr 1
      dsimp only [C]
      ring

/-- The classical interior cap bound at any point of the domain. -/
theorem exists_classicalDirichletHessian_interior_patch {U : Set Point} (hU : IsOpen U)
    (p : ℝ) (hp : 1 < p) {a : Point} (ha : a ∈ U) : HasScalarDirichletHessianCapBound U p a :=
  exists_classicalDirichletHessian_interior_patch_of_wholeSpace (classicalScalarWholeSpaceHessianLp p hp) hU ha

end Thesis

end
