module

public import Thesis.External.DirichletPoissonRegularity
public import Thesis.Variational.BoundaryExpansionEnergy
public import Thesis.Variational.BoundaryLimit
import Thesis.MeasureGeometry.EnergyMonotonicity
import Thesis.Upstream.InteriorPoissonRegularity

/-! Classical representatives of the global Dirichlet minimizing family. -/

public section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem IsWeakEulerLagrange.exists_closedC1_representative
    (hReg : External.GlobalDirichletPoissonClosureC2)
    {a : BulkCoefficients} {ε : ElasticScale} {U : Set Point}
    (hU : IsSmoothDomain U) {u b : Point → S0} {D : Point → Gradient}
    (hWeak : IsWeakEulerLagrange a ε U u D) (hu : MemH1 U u D)
    (hb : ContDiff ℝ ∞ b) (hTrace : SameTrace U u b D (ClassicalGradient b))
    {M : ℝ} (hM : 0 ≤ M) (hBound : ∀ᵐ x ∂volume.restrict U, ‖u x‖ ≤ M) :
    ∃ v : Point → S0, u =ᵐ[volume.restrict U] v ∧
      ContDiffOn ℝ 1 v (closure U) ∧ EqOn v b (frontier U) ∧ MemH1 U v D ∧
      SameTrace U v b D (ClassicalGradient b) ∧
      IsWeakPoisson U D (fun x => (ε : ℝ)⁻¹ ^ 2 • bulkGradient a (v x)) := by
  let s := (ε : ℝ)⁻¹ ^ 2
  let F (w : Point → S0) (x : Point) := s • bulkGradient a (w x)
  obtain ⟨K, hK, hForce⟩ := exists_bound_bulkGradient_on_norm_le a hM
  have hFB : ∀ᵐ x ∂volume.restrict U, ‖F u x‖ ≤ s * K := by
    filter_upwards [hBound] with x hx
    change ‖s • bulkGradient a (u x)‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ s from sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hForce _ hx) (sq_nonneg _)
  have hFC := (contDiff_bulkGradient a).continuous.const_smul s
  haveI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  letI : ContinuousENorm S0 := SeminormedAddGroup.toContinuousENorm
  let f (x : Point) : S0 := s • bulkForce a (u x)
  have hfM : AEStronglyMeasurable f (volume.restrict U) :=
    ((contDiff_bulkForce a).continuous.const_smul s).comp_aestronglyMeasurable hu.1.1
  have hfB : ∀ᵐ x ∂volume.restrict U, ‖f x‖ ≤ s * K := hFB
  have hfI : IntegrableOn f U volume := Integrable.of_bound hfM (s * K) hfB
  letI : ContinuousENorm Tensor := SeminormedAddGroup.toContinuousENorm
  have hFI : IntegrableOn (F u) U volume := symmetricTraceless.subtypeL.integrable_comp hfI
  have hP : IsWeakPoisson U D (F u) :=
    hWeak.isWeakPoisson hFI.locallyIntegrableOn
  obtain ⟨v, huv, hv₁, hWall⟩ :=
    hReg.c1Representative hU hb hu hTrace hP ⟨s * K, hFB⟩
  have hvH : MemH1 U v D := hu.congr_ae huv EventuallyEq.rfl
  have hTv : SameTrace U v b D (ClassicalGradient b) :=
    hTrace.congr_ae huv EventuallyEq.rfl EventuallyEq.rfl EventuallyEq.rfl
  have hPv : IsWeakPoisson U D (F v) :=
    (hWeak.congr_ae huv EventuallyEq.rfl).isWeakPoisson
      ((hFC.comp_continuousOn (hv₁.continuousOn.mono subset_closure)).locallyIntegrableOn hU.1.1.measurableSet)
  exact ⟨v,huv,hv₁,hWall,hvH,hTv,hPv⟩

/-- The linear global Dirichlet estimates bootstrap the actual material
equation on the closure, while preserving its trace and weak columns. -/
theorem IsWeakEulerLagrange.exists_smoothClosure_representative
    (hReg : External.GlobalDirichletPoissonRegularity)
    {a : BulkCoefficients} {ε : ElasticScale} {U : Set Point}
    (hU : IsSmoothDomain U) {u b : Point → S0} {D : Point → Gradient}
    (hWeak : IsWeakEulerLagrange a ε U u D) (hu : MemH1 U u D)
    (hb : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) b) (hTrace : SameTrace U u b D (ClassicalGradient b))
    {M : ℝ} (hM : 0 ≤ M) (hBound : ∀ᵐ x ∂volume.restrict U, ‖u x‖ ≤ M) :
    ∃ v : Point → S0, u =ᵐ[volume.restrict U] v ∧
      D =ᵐ[volume.restrict U] ClassicalGradient v ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) v (closure U) ∧ EqOn v b (frontier U) ∧
      (∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian v x) : Tensor) = bulkGradient a (v x)) := by
  obtain ⟨v,huv,hv₁,hWall,hvH,hTv,hPv⟩ :=
    hWeak.exists_closedC1_representative hReg.closureC2 hU hu hb hTrace hM hBound
  let s := (ε : ℝ)⁻¹ ^ 2
  let F (w : Point → S0) (x : Point) := s • bulkGradient a (w x)
  have hv : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) v (closure U) := by
    rw [contDiffOn_infty]
    intro n
    induction n with
    | zero => exact hv₁.of_le zero_le_one
    | succ n ih =>
      by_cases hn : n = 0
      · subst n
        exact hv₁
      · have hFn : ContDiffOn ℝ n (F v) (closure U) :=
          (((contDiff_infty.mp (contDiff_bulkGradient a)) n).comp_contDiffOn ih).const_smul s
        exact hReg.contDiffOn_succ n (Nat.pos_of_ne_zero hn) hU hb hvH hTv hPv ih hFn
  obtain ⟨hD, hEuler⟩ :=
    hWeak.classical_of_ae_representative hU.1.1 hu.memH1Loc (hv.mono subset_closure) huv
  exact ⟨v, huv, hD, hv, hWall, hEuler⟩

/-- The actual representative has two derivatives up to the prescribed
wall and all classical derivatives in the open region. -/
theorem IsWeakEulerLagrange.exists_classicalClosure_representative
    (hReg : External.GlobalDirichletPoissonClosureC2)
    {a : BulkCoefficients} {ε : ElasticScale} {U : Set Point}
    (hU : IsSmoothDomain U) {u b : Point → S0} {D : Point → Gradient}
    (hWeak : IsWeakEulerLagrange a ε U u D) (hu : MemH1 U u D)
    (hb : ContDiff ℝ ∞ b) (hTrace : SameTrace U u b D (ClassicalGradient b))
    {M : ℝ} (hM : 0 ≤ M) (hBound : ∀ᵐ x ∂volume.restrict U, ‖u x‖ ≤ M) :
    ∃ v : Point → S0, u =ᵐ[volume.restrict U] v ∧
      D =ᵐ[volume.restrict U] ClassicalGradient v ∧
      (ContDiffOn ℝ 2 v (closure U) ∧ ContDiffOn ℝ ∞ v U) ∧ EqOn v b (frontier U) ∧
      (∀ x ∈ U, (ε : ℝ) ^ 2 • (laplacian v x : S0).val = bulkGradient a (v x)) := by
  obtain ⟨v,huv,hv₁,hWall,hvH,hTv,hPv⟩ :=
    hWeak.exists_closedC1_representative hReg hU hu hb hTrace hM hBound
  let s := (ε : ℝ)⁻¹ ^ 2
  let F (x : Point) := s • bulkGradient a (v x)
  have hF₁ : ContDiffOn ℝ 1 F (closure U) :=
    ((contDiff_bulkGradient a).of_le (WithTop.coe_le_coe.mpr le_top) |>.comp_contDiffOn hv₁).const_smul s
  have hv₂ := hReg.contDiffOn_two hU hb hvH hTv hPv hv₁ hF₁
  have hvI : ContDiffOn ℝ ∞ v U := by
    rw [contDiffOn_infty]
    intro n
    induction n with
    | zero => exact contDiffOn_zero.mpr (hv₁.continuousOn.mono subset_closure)
    | succ n ih =>
      have hF : ContDiffOn ℝ n F U := (((contDiff_infty.mp (contDiff_bulkGradient a)) n
        ).comp_contDiffOn ih).const_smul s
      exact interiorPoissonRegularity.contDiffOn_succ n hU.1.1 hvH.memH1Loc hPv
        (hv₁.continuousOn.mono subset_closure) hF
  obtain ⟨hD,hEuler⟩ := hWeak.classical_of_ae_representative hU.1.1 hu.memH1Loc hvI huv
  exact ⟨v,huv,hD,⟨hv₂,hvI⟩,hWall,hEuler⟩

/-- The prescribed quaternion lift fixes one smooth ambient trace for
all elastic scales. Each global minimizer retains its a.e. values and
weak columns in the classical minimizing family. -/
theorem exists_classical_family_of_global_minimizers_with_smoothLift
    (hReg : External.GlobalDirichletPoissonClosureC2)
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    (T : SobolevTraceOperator U) (hComp : NonexpansiveSobolevTraceComposition U)
    (b : frontier U → Sphere3) (hLift : IsSmoothBoundaryLift U b)
    (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient)
    (hMin : ∀ ε, IsGlobalEnergyMinimizer a ε U (fun x => cover a (b x)) (Q ε) (D ε)) :
    ∃ (B : Point → S0) (Qc : ElasticScale → Point → S0),
      ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) B ∧ (∀ x : frontier U, B x = cover a (b x)) ∧
      (∀ x, B x ∈ vacuum a) ∧
      ∀ ε, Q ε =ᵐ[volume.restrict U] Qc ε ∧ D ε =ᵐ[volume.restrict U] ClassicalGradient (Qc ε) ∧
        (ContDiffOn ℝ 2 (Qc ε) (closure U) ∧ ContDiffOn ℝ ∞ (Qc ε) U) ∧ EqOn (Qc ε) B (frontier U) ∧
        (∀ x ∈ U, ‖Qc ε x‖ ≤ Real.sqrt 2 * vacuumRadius a) ∧
        (∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian (Qc ε) x) : Tensor) = bulkGradient a (Qc ε x)) ∧
        IsGlobalEnergyMinimizer a ε U (fun x => cover a (b x)) (Qc ε) (ClassicalGradient (Qc ε)) := by
  classical
  obtain ⟨g, hg, hUnit, hLiftTrace⟩ := hLift.exists_unit_extension
  let B := ambientQuaternionCover a ∘ g
  have hB : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) B := (contDiff_ambientQuaternionCover a).comp hg
  have hBval (x : frontier U) : B x = cover a (b x) := by
    change ambientQuaternionCover a (g x) = cover a (b x)
    rw [hLiftTrace x]
    rfl
  have hVac (x : Point) : B x ∈ vacuum a :=
    cover_mem_vacuum a ⟨g x, Metric.mem_sphere.mpr (by rw [dist_zero_right, hUnit x])⟩
  let M := Real.sqrt 2 * vacuumRadius a
  have hM : 0 ≤ M := mul_nonneg (Real.sqrt_nonneg _) (vacuumRadius_pos a).le
  have hBnorm : eLpNorm (fun x : frontier U => cover a (b x)) ⊤ (frontierSurfaceMeasure U) ≤ ENNReal.ofReal M := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x =>
      (vacuum_norm (cover_mem_vacuum a (b x))).le)
  have hEach (ε : ElasticScale) :
      ∃ v : Point → S0,
        Q ε =ᵐ[volume.restrict U] v ∧ D ε =ᵐ[volume.restrict U] ClassicalGradient v ∧
          (ContDiffOn ℝ 2 v (closure U) ∧ ContDiffOn ℝ ∞ v U) ∧ EqOn v B (frontier U) ∧
          (∀ x ∈ U, ‖v x‖ ≤ M) ∧
          (∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian v x) : Tensor) = bulkGradient a (v x)) ∧
          IsGlobalEnergyMinimizer a ε U (fun x => cover a (b x)) v (ClassicalGradient v) := by
    have hNorm := (hMin ε).eLpNorm_top_le_vacuumOrTrace hU.1.1 hU.1.2.2 hComp
    have hTnorm : (eLpNorm (fun x : frontier U => cover a (b x)) ⊤ (frontierSurfaceMeasure U)).toReal ≤ M :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hBnorm).trans_eq (ENNReal.toReal_ofReal hM)
    rw [max_eq_left hTnorm] at hNorm
    have hAE : ∀ᵐ x ∂volume.restrict U, ‖Q ε x‖ ≤ M := by
      rw [eLpNorm_exponent_top] at hNorm
      filter_upwards [enorm_ae_le_eLpNormEssSup (Q ε) (volume.restrict U)] with x hx
      apply (ENNReal.ofReal_le_ofReal_iff hM).mp
      rw [ofReal_norm]
      exact hx.trans hNorm
    have hLoc := (hMin ε).isLocalEnergyMinimizer hU.1.1 hU.1.2.2
    have hWeak := isWeakEulerLagrange_of_localEnergyMinimizer_of_eLpNorm_top_le a ε hU.1.1 hLoc hNorm
    have hTB := T.sameTrace_every_smoothLift hU.1.1 hU.1.2.2 (hMin ε).1 (hMin ε).2.1 hB hBval
    obtain ⟨v, huv, hD, hv, hTrace, hEuler⟩ :=
      hWeak.exists_classicalClosure_representative hReg hU (hMin ε).1 hB hTB hM hAE
    have hBV : ∀ x ∈ U, ‖v x‖ ≤ M := by
      have hEq : (fun x => ‖v x‖) =ᵐ[volume.restrict U] fun x => min ‖v x‖ M := by
        filter_upwards [huv, hAE] with x hx hBx
        rw [min_eq_left (hx ▸ hBx)]
      have hC : ContinuousOn (fun x => ‖v x‖) U := (hv.2.continuousOn).norm
      intro x hx
      have h := Measure.eqOn_open_of_ae_eq hEq hU.1.1 hC (hC.inf continuousOn_const) hx
      exact h.le.trans (min_le_right _ _)
    have hMinV : IsGlobalEnergyMinimizer a ε U (fun x => cover a (b x)) v (ClassicalGradient v) := by
      refine ⟨(hMin ε).1.congr_ae huv hD, (hMin ε).2.1.congr_ae huv hD, ?_⟩
      intro y G hy hT
      rw [← energy_congr_of_ae a ε huv hD]
      exact (hMin ε).2.2 y G hy hT
    exact ⟨v, huv, hD, hv, hTrace, hBV, hEuler, hMinV⟩
  choose Qc hQc using hEach
  exact ⟨B, Qc, hB, hBval, hVac, hQc⟩

/-- The regular global limit and boundary energy bounds use the same
classical representatives, prescribed lift, elastic scales and weak
columns as the original Dirichlet minimizing family. -/
theorem exists_classical_global_limit_with_regular_wall_collar
    (hReg : External.GlobalDirichletPoissonClosureC2)
    (hGG : External.LipschitzGaussGreen) (hSard : External.MorseSardPlaneToReal)
    (hPoisson : External.ZeroTraceBoundaryPoissonL4GradientEstimate)
    (hMean : External.ClassicalScalarSubsolutionMeanValue) (hInterior : InteriorPoissonGradientEstimate)
    (a : BulkCoefficients) {U : Set Point} (hU : IsSmoothDomain U)
    (T : SobolevTraceOperator U) (hComp : NonexpansiveSobolevTraceComposition U)
    (hSU : External.SU83BoundaryRegularity)
    (b : frontier U → Sphere3) (hLift : IsSmoothBoundaryLift U b)
    (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient)
    (hMin : ∀ ε, IsGlobalEnergyMinimizer a ε U (fun x => cover a (b x)) (Q ε) (D ε)) :
    ∃ (B : Point → S0) (Qc : ElasticScale → Point → S0) (ε : ℕ → ElasticScale)
      (q : Point → S0) (G : Point → Gradient) (V : Set Point),
      ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) B ∧ (∀ x : frontier U, B x = cover a (b x)) ∧
      (∀ ε, Q ε =ᵐ[volume.restrict U] Qc ε ∧ D ε =ᵐ[volume.restrict U] ClassicalGradient (Qc ε) ∧
        (ContDiffOn ℝ 2 (Qc ε) (closure U) ∧ ContDiffOn ℝ ∞ (Qc ε) U) ∧ EqOn (Qc ε) B (frontier U) ∧
        (∀ x ∈ U, (ε : ℝ) ^ 2 • (↑(laplacian (Qc ε) x) : Tensor) = bulkGradient a (Qc ε x))) ∧
      Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0) ∧
      StrongH1 U (Qc ∘ ε) (fun k => ClassicalGradient (Qc (ε k))) q G ∧
      IsGlobalDirichletMinimizer a U (fun x => cover a (b x)) q G ∧
      (singularSet U q).Finite ∧ IsOpen V ∧ frontier U ⊆ V ∧ U ∩ V ⊆ U \ singularSet U q ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) q (U \ singularSet U q) ∧
      ContDiffOn ℝ 2 q (closure U ∩ V) ∧ (∀ x : frontier U, q x = cover a (b x)) ∧
      G =ᵐ[volume.restrict U] ClassicalGradient q ∧
      (∀ k, MemLp (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (Qc (ε k) x))
        1 (volume.restrict U)) ∧
      Tendsto (fun k => eLpNorm (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (Qc (ε k) x))
        1 (volume.restrict U)) atTop (𝓝 0) ∧
      Tendsto (fun k => energy a (ε k) U (Qc (ε k)) (ClassicalGradient (Qc (ε k)))) atTop
        (𝓝 (dirichletEnergy U G)) ∧
      ∀ c ∈ frontier U, ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ Metric.closedBall c r ⊆ V ∧
        ∀ᶠ k in atTop, ∀ x ∈ U ∩ Metric.ball c (r / 2),
          energyDensity a (ε k) (Qc (ε k) x) (ClassicalGradient (Qc (ε k)) x) ≤ L := by
  obtain ⟨B, Qc, hB, hBval, hBV, hClass⟩ :=
    exists_classical_family_of_global_minimizers_with_smoothLift hReg a hU T hComp b hLift Q D hMin
  have hMinC (ε : ElasticScale) : IsGlobalEnergyMinimizer a ε U (fun x => cover a (b x))
      (Qc ε) (ClassicalGradient (Qc ε)) := (hClass ε).2.2.2.2.2.2
  obtain ⟨ε, q, G, V, hε, hStrong, hqMin, hFinite, hV, hFront, hVreg, hq, hqC, hqT, hGrad, hBulkLp,
    hBulk, hEnergy⟩ := exists_global_energy_limit_with_finite_singular_set_of_smoothBoundaryLift
      a hU T hComp hSU b hLift Qc (fun ε => ClassicalGradient (Qc ε)) hMinC
  have hBH : MemH1 U B (ClassicalGradient B) :=
    memH1Loc_of_contDiffOn isOpen_univ (hB.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
      U hU.1.1 ⟨hU.1.2.2.isCompact_closure, subset_univ _⟩
  have hBTrace : HasSmoothTrace U B (ClassicalGradient B) (fun x => cover a (b x)) :=
    ⟨B, hB, hBval, SameTrace.refl hU.1.1 B _⟩
  let C₀ := (dirichletEnergy U (ClassicalGradient B)).toReal
  have hC₀ : 0 ≤ C₀ := ENNReal.toReal_nonneg
  have hC₀' : ENNReal.ofReal C₀ = dirichletEnergy U (ClassicalGradient B) :=
    ENNReal.ofReal_toReal (dirichletEnergy_lt_top_of_memLp hBH.2.1).ne
  have hCap (k : ℕ) : energy a (ε k) U (Qc (ε k)) (ClassicalGradient (Qc (ε k))) ≤ ENNReal.ofReal C₀ := by
    rw [hC₀', ← energy_eq_dirichlet_of_takesVacuumValues a (ε k) (ClassicalGradient B) (Eventually.of_forall hBV)]
    exact (hMinC (ε k)).2.2 B (ClassicalGradient B) hBH hBTrace
  refine ⟨B, Qc, ε, q, G, V, hB, hBval, ?_, hε, hStrong, hqMin, hFinite, hV, hFront, hVreg,
    hq, hqC, hqT, hGrad, hBulkLp, hBulk, hEnergy, ?_⟩
  · intro ε
    obtain ⟨hUae, hDae, hS, hT, _, hP, _⟩ := hClass ε
    exact ⟨hUae, hDae, hS, hT, hP⟩
  · intro c hc
    exact exists_eventual_energyDensity_bound_on_regular_wall_collar_from_poisson hGG hSard hPoisson hMean
      hInterior a hU hB (fun x _ => hBV x) hV hqC hGrad ε (Qc ∘ ε) hε hStrong hBulkLp hBulk
      (fun k => (hClass (ε k)).2.2.1.2)
      (fun k => (hClass (ε k)).2.2.1.1)
      (fun k => (hClass (ε k)).2.2.2.1)
      (fun k => (hClass (ε k)).2.2.2.2.2.1)
      hC₀ (by norm_num : 0 < (1 : ℝ)) (mul_nonneg (Real.sqrt_nonneg _) (vacuumRadius_pos a).le)
      hCap (fun k => (hClass (ε k)).2.2.2.2.1) (c := c) ⟨hc, hFront hc⟩

end Thesis

end
