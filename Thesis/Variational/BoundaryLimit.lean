module

public import Thesis.External.BoundaryHarmonicMaps
public import Thesis.Upstream.VacuumRegularity
public import Thesis.Variational.VacuumExtension

/-! Finiteness of the singular set of the fixed-trace limit and a common
representative on its interior regular region and boundary collar. -/

public section

open Set Filter MeasureTheory Topology
open scoped BigOperators ContDiff ENNReal NNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

variable {Ω W : Set Point}

private theorem normalizedEnergy_le_of_ae_bound {D : Point → Gradient}
    (x : Point) (r : HarmonicMaps.PositiveRadius) {M : ℝ} (hM : 0 ≤ M)
    (hD : ∀ᵐ y ∂volume.restrict (Metric.ball x r.val), gradientNormSq (D y) ≤ M) :
    HarmonicMaps.normalizedEnergy (frobeniusGradient D) x r ≤
      ENNReal.ofReal ((M * (Real.pi * 4 / 3)) * r.val ^ 2) := by
  have hr : 0 < r.val := r.property
  have hInf :
      (∫⁻ y in Metric.ball x r.val, ENNReal.ofReal (gradientNormSq (D y))) ≤
        ∫⁻ _ in Metric.ball x r.val, ENNReal.ofReal M :=
    lintegral_mono_ae (hD.mono fun _ hy => ENNReal.ofReal_le_ofReal hy)
  calc
    _ = ENNReal.ofReal (r.val⁻¹) *
        ∫⁻ y in Metric.ball x r.val, ENNReal.ofReal (gradientNormSq (D y)) := by
      rw [HarmonicMaps.normalizedEnergy, upstream_dirichletEnergy_eq_gradientNormSq,
        show (2 : ℤ) - (↑(3 : ℕ) : ℤ) = -1 by decide, zpow_neg_one]
    _ ≤ ENNReal.ofReal (r.val⁻¹) * (∫⁻ _ in Metric.ball x r.val, ENNReal.ofReal M) :=
      mul_le_mul_right hInf _
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, EuclideanSpace.volume_ball_fin_three,
        ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (pow_nonneg hr.le 3),
        ← ENNReal.ofReal_mul hM, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
      congr 1
      field_simp [hr.ne']

private theorem continuousOn_classical_gradientNormSq {v : Point → S0}
    (hW : IsOpen W) (hv : ContDiffOn ℝ 1 v W) :
    ContinuousOn (fun x => gradientNormSq (ClassicalGradient v x)) W := by
  simp only [gradientNormSq_eq_sum_norm_sq]
  exact continuousOn_finsetSum Finset.univ fun j _ =>
    ((continuousOn_coordDeriv hW hv j).norm.pow 2)

/-- A locally minimizing field with a (C^1) representative on an open
subset is smooth there in the sense of the intrinsic regular set. -/
theorem subset_regularSet_of_contDiffOn_one_vacuum_minimizer
    (a : BulkCoefficients) (hΩ : IsOpen Ω) {u v : Point → S0} {D : Point → Gradient}
    (hMin : IsLocalDirichletMinimizer a Ω u D) (hW : IsOpen W) (hSub : W ⊆ Ω)
    (hv : ContDiffOn ℝ 1 v W) (huv : u =ᵐ[volume.restrict W] v) :
    W ⊆ Ω \ singularSet Ω u := by
  let U : HarmonicMaps.OpenDomain 3 := ⟨Ω, hΩ⟩
  obtain ⟨δ, _, _, hδ, _, _, hRegularity⟩ := smallEnergySmoothRegularity_of_upstreamTarget a
    (vacuumCompactSmoothEmbeddedTarget a) (vacuumCompactSmoothEmbeddedTarget_carrierSet a)
  have hDG := (hMin.1.mono hSub).ae_eq_classicalGradient hW hv huv
  intro x hx
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hx)
  have hR₀ : Metric.closedBall x (R / 2) ⊆ W :=
    (Metric.closedBall_subset_ball (half_lt_self hR)).trans hRsub
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall x (R / 2)).exists_bound_of_continuousOn
    ((continuousOn_classical_gradientNormSq hW hv).mono hR₀)
  let M := max 0 M₀
  have hM : 0 ≤ M := le_max_left _ _
  let K := M * (Real.pi * 4 / 3)
  have hK : 0 ≤ K := mul_nonneg hM (by positivity)
  let r := min (min (R / 2) 1) (δ / (K + 1))
  have hr : 0 < r := lt_min (lt_min (half_pos hR) zero_lt_one) (div_pos hδ (by positivity))
  have hrR : r ≤ R / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hr₁ : r ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hCl : Metric.closedBall x r ⊆ W := (Metric.closedBall_subset_closedBall hrR).trans hR₀
  have hBall : Metric.ball x r ⊆ W := Metric.ball_subset_closedBall.trans hCl
  have hD : ∀ᵐ y ∂volume.restrict (Metric.ball x r), gradientNormSq (D y) ≤ M := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hBall hDG,
      ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy hyB
    rw [hy]
    exact (Real.le_norm_self _).trans ((hM₀ y (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall hrR) hyB)).trans (le_max_right _ _))
  have hSmall : K * r ^ 2 ≤ δ := calc
    _ ≤ K * r := mul_le_mul_of_nonneg_left (by nlinarith only [mul_nonneg hr.le (sub_nonneg.mpr hr₁)]) hK
    _ ≤ (K + 1) * r := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hr.le
    _ ≤ (K + 1) * (δ / (K + 1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ = _ := by field_simp [show K + 1 ≠ 0 by positivity]
  let ρ : HarmonicMaps.PositiveRadius := ⟨r, hr⟩
  have hE : HarmonicMaps.normalizedEnergy (frobeniusGradient D) x ρ ≤ ENNReal.ofReal δ :=
    (normalizedEnergy_le_of_ae_bound x ρ hM hD).trans (ENNReal.ofReal_le_ofReal hSmall)
  obtain ⟨z, hz, huz, _⟩ := hRegularity U u D hMin x ρ (hCl.trans hSub) hE
  have hBall' : Metric.ball x (r / 2) ⊆ Ω :=
    (Metric.ball_subset_ball (half_le_self hr.le)).trans (hBall.trans hSub)
  exact mem_diff_singularSet_iff.mpr ⟨Metric.ball x (r / 2), z, Metric.isOpen_ball,
    Metric.mem_ball_self (half_pos hr), hBall', hz, huz⟩

theorem HasZeroTrace.congr_ae {u v : Point → S0} {D G : Point → Gradient}
    (h : HasZeroTrace Ω u D)
    (huv : u =ᵐ[volume.restrict Ω] v) (hDG : D =ᵐ[volume.restrict Ω] G) :
    HasZeroTrace Ω v G := by
  refine ⟨h.1.congr_ae huv hDG, fun δ hδ => ?_⟩
  obtain ⟨φ, hφ, hK, hU, hErr⟩ := h.2 δ hδ
  refine ⟨φ, hφ, hK, hU, ?_⟩
  rw [← h1Deviation_congr_ae huv EventuallyEq.rfl hDG EventuallyEq.rfl]
  exact hErr

theorem SameTrace.congr_ae {u u' v v' : Point → S0} {D D' G G' : Point → Gradient}
    (h : SameTrace Ω u v D G)
    (hu : u =ᵐ[volume.restrict Ω] u') (hv : v =ᵐ[volume.restrict Ω] v')
    (hD : D =ᵐ[volume.restrict Ω] D') (hG : G =ᵐ[volume.restrict Ω] G') :
    SameTrace Ω u' v' D' G' :=
  HasZeroTrace.congr_ae h (hu.sub hv) (hD.sub hG)

theorem HasSmoothTrace.congr_ae {b : frontier Ω → S0} {u v : Point → S0} {D G : Point → Gradient}
    (h : HasSmoothTrace Ω u D b)
    (huv : u =ᵐ[volume.restrict Ω] v) (hDG : D =ᵐ[volume.restrict Ω] G) :
    HasSmoothTrace Ω v G b := by
  obtain ⟨B, hB, hb, hSame⟩ := h
  exact ⟨B, hB, hb, hSame.congr_ae huv EventuallyEq.rfl hDG EventuallyEq.rfl⟩

theorem TakesVacuumValues.congr_ae {a : BulkCoefficients} {u v : Point → S0}
    (h : TakesVacuumValues a Ω u) (huv : u =ᵐ[volume.restrict Ω] v) :
    TakesVacuumValues a Ω v := by
  change ∀ᵐ x ∂volume.restrict Ω, v x ∈ vacuum a
  filter_upwards [h, huv] with x hx heq
  rwa [← heq]

theorem dirichletEnergy_congr_ae {D G : Point → Gradient} (h : D =ᵐ[volume.restrict Ω] G) :
    dirichletEnergy Ω D = dirichletEnergy Ω G :=
  lintegral_congr_ae (h.mono fun _ hx =>
    congrArg (fun A : Gradient => ENNReal.ofReal ((1 / 2 : ℝ) * gradientNormSq A)) hx)

theorem IsGlobalDirichletMinimizer.congr_ae
    {a : BulkCoefficients} {b : frontier Ω → S0} {u v : Point → S0} {D G : Point → Gradient}
    (h : IsGlobalDirichletMinimizer a Ω b u D)
    (huv : u =ᵐ[volume.restrict Ω] v) (hDG : D =ᵐ[volume.restrict Ω] G) :
    IsGlobalDirichletMinimizer a Ω b v G := by
  refine ⟨h.1.congr_ae huv hDG, h.2.1.congr_ae huv hDG, h.2.2.1.congr_ae huv, ?_⟩
  intro z J hz ht hVac
  rw [← dirichletEnergy_congr_ae hDG]
  exact h.2.2.2 z J hz ht hVac

theorem StrongH1.congr_ae_limit
    {u : ℕ → Point → S0} {D : ℕ → Point → Gradient}
    {v w : Point → S0} {G H : Point → Gradient}
    (h : StrongH1 Ω u D v G) (hvw : v =ᵐ[volume.restrict Ω] w) (hGH : G =ᵐ[volume.restrict Ω] H) :
    StrongH1 Ω u D w H :=
  ⟨h.1, h.2.1.congr_ae hvw hGH,
    h.2.2.congr (fun _ => h1Deviation_congr_ae EventuallyEq.rfl hvw EventuallyEq.rfl hGH)⟩

/-- A global vacuum minimizer on a smooth bounded domain has one representative
that is smooth off its finite interior singular set and is (C^2) in a
neighborhood of the entire boundary in the closed domain. -/
theorem IsGlobalDirichletMinimizer.exists_boundary_regularRepresentative
    {a : BulkCoefficients} {b : frontier Ω → S0} {u : Point → S0} {D : Point → Gradient}
    (hMin : IsGlobalDirichletMinimizer a Ω b u D) (hΩ : IsSmoothDomain Ω)
    (hSU : External.SU83BoundaryRegularity) :
    ∃ (V : Set Point) (q : Point → S0), IsOpen V ∧ frontier Ω ⊆ V ∧
      q =ᵐ[volume.restrict Ω] u ∧ IsGlobalDirichletMinimizer a Ω b q D ∧
      (singularSet Ω q).Finite ∧ Ω ∩ V ⊆ Ω \ singularSet Ω q ∧
      ContDiffOn ℝ ∞ q (Ω \ singularSet Ω q) ∧ ContDiffOn ℝ 2 q (closure Ω ∩ V) ∧
      (∀ x : frontier Ω, q x = b x) ∧ D =ᵐ[volume.restrict Ω] ClassicalGradient q := by
  classical
  have hOpen : IsOpen Ω := hΩ.1.1
  obtain ⟨V, v, hV, hbV, huv, hv, hvb⟩ := hSU a Ω hΩ b u D hMin
  have hLocal := hMin.isLocalDirichletMinimizer hOpen
  let W := Ω ∩ V
  have hW : IsOpen W := hOpen.inter hV
  have hWsub : W ⊆ Ω := inter_subset_left
  have hWcl : W ⊆ closure Ω ∩ V := inter_subset_inter_left _ subset_closure
  have hvW : ContDiffOn ℝ 1 v W := (hv.of_le (by norm_num)).mono hWcl
  have hWreg : W ⊆ Ω \ singularSet Ω u :=
    subset_regularSet_of_contDiffOn_one_vacuum_minimizer a hOpen hLocal hW hWsub hvW huv.symm
  let K := closure Ω \ V
  have hK : IsCompact K := hΩ.1.2.2.isCompact_closure.diff hV
  have hKΩ : K ⊆ Ω := by
    intro x hx
    by_contra hxΩ
    exact hx.2 (hbV (show x ∈ frontier Ω from by
      rw [frontier, hOpen.interior_eq]
      exact ⟨hx.1, hxΩ⟩))
  have hSK : singularSet Ω u ⊆ K := by
    intro x hx
    exact ⟨subset_closure hx.1, fun hxV => (hWreg ⟨hx.1, hxV⟩).2 hx⟩
  have hFin : (singularSet Ω u).Finite :=
    ((locallyFiniteIn_singularSet_of_vacuum_minimizer a hOpen hLocal) K hK hKΩ).subset
      (fun x hx => ⟨hx, hSK hx⟩)
  obtain ⟨w, hwu, hw⟩ := exists_regularRepresentative u hOpen
  have hvw : EqOn v w W :=
    Measure.eqOn_open_of_ae_eq (huv.trans (ae_restrict_of_ae_restrict_of_subset hWsub hwu.symm))
      hW hvW.continuousOn (hw.continuousOn.mono hWreg)
  let q : Point → S0 := (closure Ω ∩ V).piecewise v w
  have hqV : EqOn q v (closure Ω ∩ V) := fun _ hx =>
    Set.piecewise_eq_of_mem (closure Ω ∩ V) v w hx
  have hqw : EqOn q w Ω := by
    intro x hx
    by_cases h : x ∈ V
    · exact (hqV ⟨subset_closure hx, h⟩).trans (hvw ⟨hx, h⟩)
    · exact Set.piecewise_eq_of_notMem (closure Ω ∩ V) v w (fun hx' => h hx'.2)
  have hqwAE : q =ᵐ[volume.restrict Ω] w :=
    (ae_restrict_mem hOpen.measurableSet).mono fun _ hx => hqw hx
  have hqu : q =ᵐ[volume.restrict Ω] u := hqwAE.trans hwu
  have hSq : singularSet Ω q = singularSet Ω u := singularSet_congr_ae hqu
  have hqFin : (singularSet Ω q).Finite := hSq.symm ▸ hFin
  have hqMin := hMin.congr_ae hqu.symm EventuallyEq.rfl
  have hqSmooth : ContDiffOn ℝ ∞ q (Ω \ singularSet Ω q) := by
    rw [hSq]
    exact hw.congr (hqw.mono sdiff_subset)
  have hD :
      D =ᵐ[volume.restrict (Ω \ singularSet Ω q)] ClassicalGradient q :=
    (hqMin.1.memH1Loc.mono sdiff_subset).ae_eq_classicalGradient
      (isOpen_diff_singularSet q) (hqSmooth.of_le (by simp)) EventuallyEq.rfl
  have hNull : ∀ᵐ x ∂(volume : Measure Point), x ∉ singularSet Ω q := by
    rw [ae_iff]
    push Not
    change (volume : Measure Point) (singularSet Ω q) = 0
    exact hqFin.measure_zero (volume : Measure Point)
  have hMeasure : (volume : Measure Point).restrict (Ω \ singularSet Ω q) = volume.restrict Ω :=
    Measure.restrict_congr_set
      (hNull.mono fun _ hx => propext ⟨And.left, fun hmem => ⟨hmem, hx⟩⟩)
  rw [hMeasure] at hD
  refine ⟨V, q, hV, hbV, hqu, hqMin, hqFin, hSq.symm ▸ hWreg, hqSmooth, hv.congr hqV, ?_, hD⟩
  intro x
  exact (hqV ⟨frontier_subset_closure x.2, hbV x.2⟩).trans (hvb x)

/-- A global strong limit from the prescribed family, with one representative
on the interior regular region and the boundary collar. The selected scales,
derivatives, and scaled bulk convergence are those of the same limit. -/
theorem exists_global_energy_limit_with_finite_singular_set_of_smoothBoundaryLift
    (a : BulkCoefficients) (hΩ : IsSmoothDomain Ω)
    (T : SobolevTraceOperator Ω) (hComp : NonexpansiveSobolevTraceComposition Ω)
    (hSU : External.SU83BoundaryRegularity)
    (b : frontier Ω → Sphere3) (hLift : IsSmoothBoundaryLift Ω b)
    (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient)
    (hMin : ∀ ε, IsGlobalEnergyMinimizer a ε Ω (fun x => cover a (b x)) (Q ε) (D ε)) :
    ∃ (ε : ℕ → ElasticScale) (q : Point → S0) (G : Point → Gradient) (V : Set Point),
      Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0) ∧
      StrongH1 Ω (Q ∘ ε) (D ∘ ε) q G ∧
      IsGlobalDirichletMinimizer a Ω (fun x => cover a (b x)) q G ∧
      (singularSet Ω q).Finite ∧ IsOpen V ∧ frontier Ω ⊆ V ∧ Ω ∩ V ⊆ Ω \ singularSet Ω q ∧
      ContDiffOn ℝ ∞ q (Ω \ singularSet Ω q) ∧ ContDiffOn ℝ 2 q (closure Ω ∩ V) ∧
      (∀ x : frontier Ω, q x = cover a (b x)) ∧ G =ᵐ[volume.restrict Ω] ClassicalGradient q ∧
      (∀ k, MemLp (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (Q (ε k) x))
        1 (volume.restrict Ω)) ∧
      Tendsto (fun k => eLpNorm (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (Q (ε k) x))
        1 (volume.restrict Ω)) atTop (𝓝 0) ∧
      Tendsto (fun k => energy a (ε k) Ω (Q (ε k)) (D (ε k))) atTop
        (𝓝 (dirichletEnergy Ω G)) := by
  obtain ⟨ε, v, G, hε, hStrong, hvMin, hBulkLp, hBulk, hEnergy⟩ :=
    exists_global_energy_limit_of_smoothBoundaryLift a hΩ.1 T hComp b hLift Q D hMin
  obtain ⟨V, q, hV, hFront, hqv, hqMin, hFinite, hVreg, hSmooth, hCollar, hTrace, hGrad⟩ :=
    hvMin.exists_boundary_regularRepresentative hΩ hSU
  exact ⟨ε, q, G, V, hε, hStrong.congr_ae_limit hqv.symm EventuallyEq.rfl, hqMin,
    hFinite, hV, hFront, hVreg, hSmooth, hCollar, hTrace, hGrad, hBulkLp, hBulk, hEnergy⟩

private theorem exists_local_gradientNormSq_bound_of_contDiffOn_two
    {V : Set Point} (hΩ : IsOpen Ω) (hV : IsOpen V) {q : Point → S0}
    (hq : ContDiffOn ℝ 2 q (closure Ω ∩ V))
    {z : Point} (hz : z ∈ closure Ω ∩ V) :
    ∃ (O : Set Point) (M : ℝ), IsOpen O ∧ z ∈ O ∧ O ⊆ V ∧ 0 ≤ M ∧
      ∀ y ∈ Ω ∩ O, gradientNormSq (ClassicalGradient q y) ≤ M := by
  let S := closure Ω ∩ V
  have hzS : z ∈ S := hz
  have hq₂ : ContDiffWithinAt ℝ (1 + 1) q S z := hq z hz
  obtain ⟨U, hU, _, _, T, hDeriv, hTC⟩ :=
    (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 1) (by simp)).mp hq₂
  rw [insert_eq_of_mem hzS] at hU
  let B := ‖T z‖ + 1
  have hBN : {y | ‖T y‖ < B} ∈ 𝓝[S] z :=
    hTC.continuousWithinAt.norm (Iio_mem_nhds (lt_add_of_pos_right _ zero_lt_one))
  obtain ⟨O, hO, hzO, hOS⟩ := mem_nhdsWithin.mp (inter_mem hU hBN)
  refine ⟨O ∩ V, 3 * B ^ 2, hO.inter hV, ⟨hzO, hz.2⟩, inter_subset_right,
    mul_nonneg (by norm_num) (sq_nonneg _), ?_⟩
  intro y hy
  have hyW : y ∈ Ω ∩ V := ⟨hy.1, hy.2.2⟩
  have hyS : y ∈ S := ⟨subset_closure hy.1, hy.2.2⟩
  have hT := hOS ⟨hy.2.1, hyS⟩
  have hSN : S ∈ 𝓝 y :=
    mem_of_superset ((hΩ.inter hV).mem_nhds hyW) (inter_subset_inter_left _ subset_closure)
  have hF := (hDeriv y hT.1).hasFDerivAt hSN
  have hColumns (j : Fin 3) : ‖ClassicalGradient q y j‖ ≤ B := by
    have hAxis : ‖axis j‖ = 1 := by simp [axis]
    rw [ClassicalGradient, coordDeriv, hF.fderiv]
    exact ((T y).le_opNorm (axis j)).trans (by rw [hAxis, mul_one]; exact hT.2.le)
  rw [gradientNormSq_eq_sum_norm_sq]
  calc
    _ ≤ ∑ _ : Fin 3, B ^ 2 :=
      Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hColumns j) 2)
    _ = _ := by simp [nsmul_eq_mul]

/-- A (C^2) collar representative has a uniformly bounded actual classical
gradient on a smaller open neighborhood of each compact part of the collar. -/
theorem exists_gradientNormSq_bound_on_compact_collar
    {V K : Set Point} (hΩ : IsOpen Ω) (hV : IsOpen V) {q : Point → S0}
    (hq : ContDiffOn ℝ 2 q (closure Ω ∩ V))
    (hK : IsCompact K) (hKsub : K ⊆ closure Ω ∩ V) :
    ∃ (O : Set Point) (M : ℝ), IsOpen O ∧ K ⊆ O ∧ O ⊆ V ∧ 0 ≤ M ∧
      ∀ y ∈ Ω ∩ O, gradientNormSq (ClassicalGradient q y) ≤ M := by
  classical
  have hLocal (z : K) := exists_local_gradientNormSq_bound_of_contDiffOn_two
    hΩ hV hq (hKsub z.property)
  choose O M hO hx hSub hM hGrad using hLocal
  have hCover : K ⊆ ⋃ z : K, O z := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hx ⟨z, hz⟩⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover O hO hCover
  refine ⟨⋃ z ∈ I, O z, ∑ z ∈ I, M z, isOpen_biUnion (fun z _ => hO z), hI,
    iUnion₂_subset (fun z _ => hSub z), Finset.sum_nonneg (fun z _ => hM z), ?_⟩
  intro y hy
  obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp hy.2
  exact (hGrad z y ⟨hy.1, hyz⟩).trans (Finset.single_le_sum (fun z _ => hM z) hz)

end Thesis

end
