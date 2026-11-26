module

public import Thesis.External.BoundaryPoisson
public import Thesis.Variational.SmoothWallGeometry
public import Thesis.Variational.ProjectedLaplacian
import Thesis.Variational.BoundaryDefect
import Thesis.Variational.ScaledDefects

/-! The scalar physical-boundary Poisson estimate in Frobenius coordinates. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem abs_frobeniusCoordinate_le_norm (A : S0) (i : Fin 5) :
    |frobeniusCoordinateEquiv A i| ≤ ‖A‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs, ← frobeniusCoordinateEquiv.norm_map A, EuclideanSpace.real_norm_sq_eq]
  exact Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

/-- Applying the scalar estimate in five Frobenius coordinates controls
the actual derivative of a tensor with zero physical trace. The scalar
envelopes for the gradient and forcing are integrated on the outer cap. -/
theorem exists_closed_cap_poisson_gradient_bound_frobenius
    (h : External.ZeroTraceBoundaryPoissonL4GradientEstimate)
    {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧
      ∀ c ∈ frontier U, ∀ r ∈ Ioo 0 R, ∀ (u f : Point → S0) (g G : Point → ℝ),
        let D := U ∩ Metric.ball c r
        let V := closure U ∩ Metric.ball c r
        ContDiffOn ℝ 2 u V →
        EqOn u (fun _ => 0) (frontier U ∩ Metric.ball c r) →
        (∀ x ∈ D, laplacian u x = f x) →
        MemLp f 4 (volume.restrict D) →
        MemLp g 2 (volume.restrict D) → MemLp G 4 (volume.restrict D) →
        (∀ x ∈ D, 0 ≤ g x ∧ ∀ v : Point, ‖(fderiv ℝ u x) v‖ ≤ g x * ‖v‖) →
        (∀ x ∈ D, ‖f x‖ ≤ G x) →
        ∀ x ∈ closure U ∩ Metric.ball c (r / 2), ∀ v : Point,
          ‖(fderivWithin ℝ u (closure U) x) v‖ ≤
            C * (r ^ (-3 / 2 : ℝ) * (eLpNorm g 2 (volume.restrict D)).toReal +
              r ^ (1 / 4 : ℝ) * (eLpNorm G 4 (volume.restrict D)).toReal) * ‖v‖ := by
  obtain ⟨R, C, hR, hC, hBound⟩ := h U hU
  refine ⟨R, 5 * C, hR, mul_pos (by norm_num) hC, ?_⟩
  intro c hc r hr u f g G
  let D := U ∩ Metric.ball c r
  let V := closure U ∩ Metric.ball c r
  change ContDiffOn ℝ 2 u V → _ → _ → _ → _ → _ → _ → _ → _
  intro hu hTrace hEq hFL hGL hHL hGrad hForce x hx v
  have hD : IsOpen D := hU.1.1.inter Metric.isOpen_ball
  have hSub : D ⊆ V := fun y hy => ⟨subset_closure hy.1, hy.2⟩
  let L (i : Fin 5) : S0 →L[ℝ] ℝ := (EuclideanSpace.proj i).comp
    frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let H := r ^ (-3 / 2 : ℝ) * (eLpNorm g 2 (volume.restrict D)).toReal +
    r ^ (1 / 4 : ℝ) * (eLpNorm G 4 (volume.restrict D)).toReal
  have hH : 0 ≤ H := add_nonneg
    (mul_nonneg (Real.rpow_nonneg hr.1.le _) ENNReal.toReal_nonneg)
    (mul_nonneg (Real.rpow_nonneg hr.1.le _) ENNReal.toReal_nonneg)
  have hxBall : x ∈ Metric.ball c r :=
    (Metric.ball_subset_ball (by linarith only [hr.1])) hx.2
  have hNear : Metric.ball c r ∈ 𝓝 x := Metric.isOpen_ball.mem_nhds hxBall
  have hxV : x ∈ V := ⟨hx.1, hxBall⟩
  have hDiff : UniqueDiffWithinAt ℝ V x :=
    (uniqueDiffWithinAt_inter hNear).mpr (hU.uniqueDiffOn_closure _ (hx.1))
  have hCol (i : Fin 5) :
      |frobeniusCoordinateEquiv ((fderivWithin ℝ u (closure U) x) v) i| ≤ C * H * ‖v‖ := by
    let u₁ := L i ∘ u
    let f₁ := L i ∘ f
    have hu₁ : ContDiffOn ℝ 2 u₁ V := (L i).contDiff.comp_contDiffOn hu
    have ht₁ : EqOn u₁ (fun _ => 0) (frontier U ∩ Metric.ball c r) := by
      intro y hy
      change L i (u y) = 0
      rw [hTrace hy, map_zero]
    have hp₁ (y : Point) (hy : y ∈ D) : laplacian u₁ y = f₁ y := by
      calc
        _ = L i (laplacian u y) := laplacian_compCLM hD (hu.mono hSub) hy (L i)
        _ = _ := congrArg (L i) (hEq y hy)
    have hAEM : AEStronglyMeasurable (fderiv ℝ u₁) (volume.restrict D) :=
      ((hu₁.mono hSub).continuousOn_fderiv_of_isOpen hD (by norm_num)).aestronglyMeasurable hD.measurableSet
    have hGrad₁ : ∀ᵐ y ∂volume.restrict D, ‖fderiv ℝ u₁ y‖ ≤ g y := by
      filter_upwards [ae_restrict_mem hD.measurableSet] with y hy
      apply ContinuousLinearMap.opNorm_le_bound _ (hGrad y hy).1
      intro w
      have hUat := ((hu y (hSub hy)).contDiffAt (mem_of_superset (hD.mem_nhds hy) hSub)).differentiableAt
        two_ne_zero
      have hD₁ := ((L i).hasFDerivAt (x := u y)).comp y hUat.hasFDerivAt
      have hV : (fderiv ℝ u₁ y) w = L i ((fderiv ℝ u y) w) :=
        DFunLike.congr_fun hD₁.fderiv w
      rw [hV]
      exact ((abs_frobeniusCoordinate_le_norm ((fderiv ℝ u y) w) i)).trans ((hGrad y hy).2 w)
    have hForce₁ : ∀ᵐ y ∂volume.restrict D, ‖f₁ y‖ ≤ G y := by
      filter_upwards [ae_restrict_mem hD.measurableSet] with y hy
      exact (abs_frobeniusCoordinate_le_norm (f y) i).trans (hForce y hy)
    have hLpG := hGL.mono' hAEM hGrad₁
    have hLpF := hHL.mono' (hFL.continuousLinearMap_comp (L i)).1 hForce₁
    have hGradN := ENNReal.toReal_mono hGL.eLpNorm_ne_top (eLpNorm_mono_ae_real (p := 2) hGrad₁)
    have hForceN := ENNReal.toReal_mono hHL.eLpNorm_ne_top (eLpNorm_mono_ae_real (p := 4) hForce₁)
    have hBound₁ := hBound c hc r hr u₁ f₁ hu₁ ht₁ hp₁ hLpG hLpF x ⟨hx.1, hx.2⟩
    have hB₁ : ‖fderivWithin ℝ u₁ V x‖ ≤ C * H :=
      hBound₁.trans (mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left hGradN (Real.rpow_nonneg hr.1.le _))
        (mul_le_mul_of_nonneg_left hForceN (Real.rpow_nonneg hr.1.le _))) hC.le)
    have hd : (fderivWithin ℝ u₁ V x) v = L i ((fderivWithin ℝ u V x) v) := by
      have hU' := ((hu x hxV).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
      have hD' := ((L i).hasFDerivAt (x := u x)).comp_hasFDerivWithinAt x hU'
      exact DFunLike.congr_fun (hD'.fderivWithin hDiff) v
    rw [show fderivWithin ℝ u V x = fderivWithin ℝ u (closure U) x from fderivWithin_inter hNear] at hd
    have hEval := (fderivWithin ℝ u₁ V x).le_opNorm v
    rw [hd] at hEval
    exact hEval.trans (mul_le_mul_of_nonneg_right hB₁ (norm_nonneg _))
  let z := frobeniusCoordinateEquiv ((fderivWithin ℝ u (closure U) x) v)
  let B := C * H * ‖v‖
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hC.le hH) (norm_nonneg _)
  have hZ : ‖z‖ ≤ 5 * B := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hB)).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    have hSum : (∑ i : Fin 5, z i ^ 2) ≤ ∑ _ : Fin 5, B ^ 2 :=
      Finset.sum_le_sum fun i _ => by
        have hS := pow_le_pow_left₀ (abs_nonneg (z i)) (hCol i) 2
        rwa [sq_abs] at hS
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hSum
    nlinarith only [hSum, sq_nonneg B]
  rw [show ‖z‖ = ‖(fderivWithin ℝ u (closure U) x) v‖ from frobeniusCoordinateEquiv.norm_map _] at hZ
  calc
    _ ≤ 5 * B := hZ
    _ = _ := by dsimp only [B, H]; ring

/-- Applying the scalar estimate in five Frobenius coordinates controls
the actual derivative of a tensor with zero physical trace. The scalar
envelopes for the gradient and forcing are integrated on the outer cap. -/
theorem exists_physical_wall_poisson_gradient_bound_frobenius
    (h : External.ZeroTraceBoundaryPoissonL4GradientEstimate)
    {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧
      ∀ c ∈ frontier U, ∀ r ∈ Ioo 0 R, ∀ (u f : Point → S0) (g G : Point → ℝ),
        let D := U ∩ Metric.ball c r
        let V := closure U ∩ Metric.ball c r
        ContDiffOn ℝ 2 u V →
        EqOn u (fun _ => 0) (frontier U ∩ Metric.ball c r) →
        (∀ x ∈ D, laplacian u x = f x) →
        MemLp f 4 (volume.restrict D) →
        MemLp g 2 (volume.restrict D) → MemLp G 4 (volume.restrict D) →
        (∀ x ∈ D, 0 ≤ g x ∧ ∀ v : Point, ‖(fderiv ℝ u x) v‖ ≤ g x * ‖v‖) →
        (∀ x ∈ D, ‖f x‖ ≤ G x) →
        ∀ x ∈ frontier U ∩ Metric.ball c (r / 2), ∀ v : Point,
          ‖(fderivWithin ℝ u (closure U) x) v‖ ≤
            C * (r ^ (-3 / 2 : ℝ) * (eLpNorm g 2 (volume.restrict D)).toReal +
              r ^ (1 / 4 : ℝ) * (eLpNorm G 4 (volume.restrict D)).toReal) * ‖v‖ := by
  obtain ⟨R, C, hR, hC, hEstimate⟩ := exists_closed_cap_poisson_gradient_bound_frobenius h hU
  refine ⟨R, C, hR, hC, ?_⟩
  intro c hc r hr u f g G
  dsimp only
  intro hu ht hf hF hG hL hDer hForce x hx v
  exact hEstimate c hc r hr u f g G hu ht hf hF hG hL hDer hForce x ⟨frontier_subset_closure hx.1, hx.2⟩ v

theorem continuousOn_classicalGradientNormSq
    {U : Set Point} (hU : IsOpen U) {Q : Point → S0}
    (hQ : ContDiffOn ℝ 2 Q U) :
    ContinuousOn (fun y => gradientNormSq (ClassicalGradient Q y)) U := by
  have hD (i : Fin 3) : ContDiffOn ℝ 1 (coordDeriv i Q) U :=
    (ContinuousLinearMap.apply ℝ S0 (axis i)).contDiff.comp_contDiffOn
      (hQ.fderiv_of_isOpen hU (by norm_num))
  simp only [gradientNormSq_eq_sum_norm_sq, ClassicalGradient]
  exact continuousOn_finsetSum Finset.univ fun j _ => (hD j).continuousOn.norm.pow 2

theorem continuousOn_laplacian_of_contDiffOn_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Point} (hU : IsOpen U) {f : Point → E} (hf : ContDiffOn ℝ 2 f U) :
    ContinuousOn (laplacian f) U := by
  have hD (i : Fin 3) : ContDiffOn ℝ 1 (coordDeriv i f) U :=
    (ContinuousLinearMap.apply ℝ E (axis i)).contDiff.comp_contDiffOn
      (hf.fderiv_of_isOpen hU (by norm_num))
  have hDD (i : Fin 3) : ContDiffOn ℝ 0 (coordDeriv i (coordDeriv i f)) U :=
    (ContinuousLinearMap.apply ℝ E (axis i)).contDiff.comp_contDiffOn
      ((hD i).fderiv_of_isOpen hU (by norm_num))
  unfold laplacian
  exact continuousOn_finsetSum Finset.univ fun i _ => (hDD i).continuousOn

theorem gradientFromColumns_classicalGradient (Q : Point → S0) (x v : Point) :
    gradientFromColumns (ClassicalGradient Q x) v = (fderiv ℝ Q x) v := by
  have hv : (∑ j : Fin 3, v j • axis j) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, axis] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  simp_rw [gradientFromColumns_apply, ClassicalGradient, coordDeriv, ← map_smul, ← map_sum, hv]
  rfl

/-- A fixed ambient trace extension has bounded amplitude, within-closure
first derivative and Laplacian on the compact closure. -/
theorem exists_compact_trace_bounds {U : Set Point} (hU : IsSmoothDomain U)
    {b : Point → S0} (hb : ContDiff ℝ 2 b) :
    ∃ M B₁ B₂ : ℝ, 0 ≤ M ∧ 0 ≤ B₁ ∧ 0 ≤ B₂ ∧
      (∀ x ∈ closure U, ‖b x‖ ≤ M) ∧
      (∀ x ∈ closure U, ∀ v : Point, ‖(fderivWithin ℝ b (closure U) x) v‖ ≤ B₁ * ‖v‖) ∧
      ∀ x ∈ closure U, ‖laplacian b x‖ ≤ B₂ := by
  have hC : IsCompact (closure U) := hU.1.2.2.isCompact_closure
  have hb₁ : ContDiffOn ℝ 1 b (closure U) := (hb.of_le (by norm_num)).contDiffOn
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hb.continuous.continuousOn
  have hG := continuousOn_gradientNormSq (continuousOn_closureGradient_column hU.uniqueDiffOn_closure hb₁)
  obtain ⟨B₀, hB₀⟩ := hC.exists_bound_of_continuousOn hG
  have hL : ContinuousOn (laplacian b) (closure U) :=
    (continuousOn_laplacian_of_contDiffOn_two isOpen_univ hb.contDiffOn).mono (subset_univ _)
  obtain ⟨B₂, hB₂⟩ := hC.exists_bound_of_continuousOn hL
  refine ⟨max M 0, Real.sqrt (max B₀ 0), max B₂ 0, le_max_right _ _, Real.sqrt_nonneg _,
    le_max_right _ _, (fun x hx => (hM x hx).trans (le_max_left _ _)), ?_,
    fun x hx => (hB₂ x hx).trans (le_max_left _ _)⟩
  intro x hx v
  rw [← gradientFromColumns_closureGradient]
  have h := norm_gradientFromColumns_le (closureGradient U b x) v
  have hBnd : gradientNormSq (closureGradient U b x) ≤ max B₀ 0 :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using (hB₀ x hx).trans (le_max_left _ _))
  exact h.trans ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hBnd) (norm_nonneg _)).trans_eq
    (mul_comm _ _))

local instance projectedFieldDerivativeNorm : Norm (S0 →L[ℝ] S0) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ) (E := S0) (F := S0)

/-- The projected map satisfies the physical boundary gradient estimate
after subtracting a fixed extension of its prescribed trace. The two
right-hand envelopes use the exact gradient and projected Laplacian
scales on the outer cap. -/
theorem exists_projected_gradient_bound_on_physical_wall
    (hPoisson : External.ZeroTraceBoundaryPoissonL4GradientEstimate)
    (a : BulkCoefficients) (p : VacuumTubularProjection a)
    {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ R δ C N : ℝ, 0 < R ∧ 0 < δ ∧ 0 < C ∧ 0 ≤ N ∧
      ∀ c ∈ frontier U, ∀ r ∈ Ioo 0 R, ∀ ε : ℝ, 0 < ε →
        ∀ (Q b : Point → S0) (B : ℝ), 0 ≤ B →
          let D := U ∩ Metric.ball c r
          let V := closure U ∩ Metric.ball c r
          let G (x : Point) := gradientNormSq (ClassicalGradient Q x)
          ContDiffOn ℝ 2 Q V → ContDiffOn ℝ 2 b V →
          EqOn Q b (frontier U ∩ Metric.ball c r) →
          (∀ x ∈ frontier U ∩ Metric.ball c r, b x ∈ vacuum a) →
          (∀ x ∈ D, Q x ∈ vacuumTube a δ ∧ ε ^ 2 • (↑(laplacian Q x) : Tensor) = bulkGradient a (Q x)) →
          (∀ x ∈ V, ∀ v : Point, ‖(fderivWithin ℝ b (closure U) x) v‖ ≤ B * ‖v‖) →
          MemLp (fun x => Real.sqrt (G x)) 2 (volume.restrict D) →
          MemLp G 4 (volume.restrict D) →
          MemLp (fun x => ‖laplacian b x‖) 4 (volume.restrict D) →
          ∀ x ∈ frontier U ∩ Metric.ball c (r / 2), ∀ v : Point,
            ‖(fderivWithin ℝ (p.extend ∘ Q) (closure U) x) v‖ ≤
              (B + C * (r ^ (-3 / 2 : ℝ) *
                (eLpNorm (fun y => N * Real.sqrt (G y) + B) 2 (volume.restrict D)).toReal +
                r ^ (1 / 4 : ℝ) *
                (eLpNorm (fun y => N * G y + ‖laplacian b y‖) 4 (volume.restrict D)).toReal)) * ‖v‖ := by
  obtain ⟨RP, C, hRP, hC, hPoisson'⟩ := exists_physical_wall_poisson_gradient_bound_frobenius hPoisson hU
  obtain ⟨δ₁, M, hδ₁, hM, _, hProj⟩ := p.exists_projected_laplacian_quadratic_bound
  let K := Real.sqrt 2 * vacuumRadius a + 1
  obtain ⟨N₀, hN₀⟩ := (isCompact_closedBall (0 : S0) K).exists_bound_of_continuousOn
    (p.contDiff_extend.continuous_fderiv (by simp)).continuousOn
  let N := max M N₀
  let δ := min δ₁ 1
  have hN : 0 ≤ N := hM.le.trans (le_max_left _ _)
  refine ⟨RP, δ, C, N, hRP, lt_min hδ₁ zero_lt_one, hC, hN, ?_⟩
  intro c hc r hr ε hε Q b B hB
  let D := U ∩ Metric.ball c r
  let V := closure U ∩ Metric.ball c r
  let G (x : Point) := gradientNormSq (ClassicalGradient Q x)
  change ContDiffOn ℝ 2 Q V → _ → _ → _ → _ → _ → _ → _ → _ → _
  intro hQ hb hTrace hVac hEuler hData hLg hL₄ hLb x hx v
  let P := p.extend ∘ Q
  let u := fun y => P y - b y
  let F := laplacian u
  let g (y : Point) := N * Real.sqrt (G y) + B
  let f (y : Point) := N * G y + ‖laplacian b y‖
  have hD : IsOpen D := hU.1.1.inter Metric.isOpen_ball
  have hDV : D ⊆ V := fun y hy => ⟨subset_closure hy.1, hy.2⟩
  have hp2 : ContDiff ℝ 2 p.extend := p.contDiff_extend.of_le (WithTop.coe_le_coe.mpr le_top)
  have hP : ContDiffOn ℝ 2 P V := hp2.comp_contDiffOn hQ
  have hu : ContDiffOn ℝ 2 u V := hP.sub hb
  have hTv : EqOn u (fun _ => 0) (frontier U ∩ Metric.ball c r) := by
    intro y hy
    have hyV := hVac y hy
    have hyTube := vacuum_subset_vacuumTube a p.radius_pos hyV
    change p.extend (Q y) - b y = 0
    rw [hTrace hy, p.extend_eq ⟨b y, hyTube⟩, p.project_of_mem hyV, sub_self]
  have hFinite : volume D < ⊤ := (measure_mono inter_subset_right).trans_lt
    ((measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall c r).measure_lt_top)
  letI : IsFiniteMeasure (volume.restrict D) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hgl : MemLp g 2 (volume.restrict D) := (hLg.const_mul N).add (memLp_const B)
  have hfl : MemLp f 4 (volume.restrict D) := (hL₄.const_mul N).add hLb
  have hG (y : Point) : 0 ≤ G y := by
    change 0 ≤ gradientNormSq (ClassicalGradient Q y)
    rw [gradientNormSq_eq_sum_norm_sq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hMaterial (y : Point) (hy : y ∈ D) :
      Q y ∈ Metric.closedBall (0 : S0) K ∧ Q y ∈ vacuumTube a δ₁ := by
    have hT : Metric.infDist (Q y) (vacuum a) < δ := (hEuler y hy).1
    have hT₁ : Q y ∈ vacuumTube a δ₁ := hT.trans_le (min_le_left _ _)
    let P₀ := (spectralVacuumPoint a (Q y)).val
    have hNear : ‖Q y - P₀‖ < 1 := by
      rw [← dist_eq_norm]
      exact (spectralVacuumPoint_dist_eq_infDist a (Q y)).trans_lt (hT.trans_le (min_le_right _ _))
    have hTri := norm_add_le (Q y - P₀) P₀
    rw [sub_add_cancel, vacuum_norm (spectralVacuumPoint a (Q y)).property] at hTri
    have hK : ‖Q y‖ ≤ K := by
      dsimp only [K]
      linarith only [hTri, hNear]
    exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hK, hT₁⟩
  have hGrad (y : Point) (hy : y ∈ D) : 0 ≤ g y ∧ ∀ w : Point,
      ‖(fderiv ℝ u y) w‖ ≤ g y * ‖w‖ := by
    have hyV : V ∈ 𝓝 y := mem_of_superset (hD.mem_nhds hy) hDV
    have hQy := ((hQ y (hDV hy)).contDiffAt hyV).differentiableAt two_ne_zero
    have hby := ((hb y (hDV hy)).contDiffAt hyV).differentiableAt two_ne_zero
    have hPy := ((hp2.differentiable two_ne_zero (Q y)).hasFDerivAt).comp y hQy.hasFDerivAt
    have hDy := (hPy.sub hby.hasFDerivAt).fderiv
    refine ⟨add_nonneg (mul_nonneg hN (Real.sqrt_nonneg _)) hB, ?_⟩
    intro w
    have hEq : (fderiv ℝ u y) w =
        ((fderiv ℝ p.extend (Q y)) ((fderiv ℝ Q y) w)) - (fderiv ℝ b y) w :=
      DFunLike.congr_fun hDy w
    have hPnorm : ‖fderiv ℝ p.extend (Q y)‖ ≤ N :=
      (hN₀ _ (hMaterial y hy).1).trans (le_max_right _ _)
    have hQnorm : ‖(fderiv ℝ Q y) w‖ ≤ ‖w‖ * Real.sqrt (G y) := by
      rw [← gradientFromColumns_classicalGradient]
      exact norm_gradientFromColumns_le _ _
    have hbNorm := hData y (hDV hy) w
    have hCl : closure U ∈ 𝓝 y := mem_of_superset (hU.1.1.mem_nhds hy.1) subset_closure
    rw [fderivWithin_of_mem_nhds hCl] at hbNorm
    rw [hEq]
    calc
      _ ≤ ‖(fderiv ℝ p.extend (Q y)) ((fderiv ℝ Q y) w)‖ + ‖(fderiv ℝ b y) w‖ := norm_sub_le _ _
      _ ≤ N * (‖w‖ * Real.sqrt (G y)) + B * ‖w‖ := add_le_add
        (((fderiv ℝ p.extend (Q y)).le_opNorm ((fderiv ℝ Q y) w)).trans
          (mul_le_mul hPnorm hQnorm (norm_nonneg _) hN)) hbNorm
      _ = _ := by dsimp only [g]; ring
  have hForce (y : Point) (hy : y ∈ D) : ‖F y‖ ≤ f y := by
    have hNorm := (hProj ε hε D hD Q (hQ.mono hDV) y hy (hMaterial y hy).2 (hEuler y hy).2).2
    have hEq : F y = laplacian P y - laplacian b y :=
      laplacian_sub_of_contDiffOn hD (hP.mono hDV) (hb.mono hDV) hy
    rw [hEq]
    exact (norm_sub_le _ _).trans (add_le_add
      (hNorm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hG y))) le_rfl)
  have hFL : MemLp F 4 (volume.restrict D) :=
    hfl.mono' ((continuousOn_laplacian_of_contDiffOn_two hD (hu.mono hDV)).aestronglyMeasurable hD.measurableSet)
      (by filter_upwards [ae_restrict_mem hD.measurableSet] with y hy using hForce y hy)
  have hComp := hPoisson' c hc r hr u F g f hu hTv (fun _ _ => rfl) hFL hgl hfl hGrad hForce x hx v
  have hxB : x ∈ Metric.ball c r := (Metric.ball_subset_ball (by linarith only [hr.1])) hx.2
  have hxV : x ∈ V := ⟨frontier_subset_closure hx.1, hxB⟩
  have hNear : Metric.ball c r ∈ 𝓝 x := Metric.isOpen_ball.mem_nhds hxB
  have hUnique : UniqueDiffWithinAt ℝ V x :=
    (uniqueDiffWithinAt_inter hNear).mpr (hU.uniqueDiffOn_closure x hxV.1)
  have hdP := ((hP x hxV).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  have hdb := ((hb x hxV).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  have hEq : (fderivWithin ℝ u (closure U) x) v =
      (fderivWithin ℝ P (closure U) x) v - (fderivWithin ℝ b (closure U) x) v := by
    have hh := DFunLike.congr_fun ((hdP.sub hdb).fderivWithin hUnique) v
    simpa only [u, Pi.sub_def, sub_apply, V, fderivWithin_inter hNear] using! hh
  have hSum : (fderivWithin ℝ P (closure U) x) v =
      (fderivWithin ℝ u (closure U) x) v + (fderivWithin ℝ b (closure U) x) v := by
    rw [hEq, sub_add_cancel]
  rw [show p.extend ∘ Q = P from rfl, hSum]
  refine (norm_add_le _ _).trans ((add_le_add hComp (hData x hxV v)).trans_eq ?_)
  dsimp only [g, f]
  ring

end Thesis

end
