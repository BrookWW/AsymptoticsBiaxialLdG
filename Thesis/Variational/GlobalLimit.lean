module

public import Thesis.Variational.GlobalComparison
public import Thesis.Variational.StrongComparison
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! Sobolev boundary traces in Frobenius coordinates and global strong convergence. -/

public section

open Set Filter MeasureTheory Topology
open scoped BigOperators ContDiff ENNReal NNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance globalLimitContinuousENormS0 : ContinuousENorm S0 := @SeminormedAddGroup.toContinuousENorm S0 inferInstance

variable {Ω : Set Point}

/-- The map and the three weak gradient columns in the product of their
Frobenius-coordinate L² spaces. -/
abbrev SobolevL2Coordinates (Ω : Set Point) :=
  PiLp 2 (fun _ : Fin 4 => Lp (HarmonicMaps.Ambient 5) 2 (volume.restrict Ω))

/-- The boundary trace in Frobenius-coordinate L², with normalized surface measure. -/
abbrev SobolevTraceL2 (Ω : Set Point) :=
  Lp (HarmonicMaps.Ambient 5) 2 (frontierSurfaceMeasure Ω)

private def frobeniusLp {μ : Measure Point} {u : Point → S0} (hu : MemLp u 2 μ) :
    Lp (HarmonicMaps.Ambient 5) 2 μ :=
  ((frobeniusCoordinateEquiv_memLp_iff μ 2 u).mpr hu).toLp (frobeniusField u)

private theorem frobeniusLp_sub {μ : Measure Point} {u v : Point → S0}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    frobeniusLp (hu.sub hv) = frobeniusLp hu - frobeniusLp hv := by
  calc
    _ = _ :=
      MemLp.toLp_congr _ (((frobeniusCoordinateEquiv_memLp_iff μ 2 u).mpr hu).sub
        ((frobeniusCoordinateEquiv_memLp_iff μ 2 v).mpr hv))
        (Eventually.of_forall fun x => map_sub frobeniusCoordinateEquiv (u x) (v x))
    _ = _ := MemLp.toLp_sub _ _

private theorem inner_frobeniusLp_eq_integral {μ : Measure Point} {u : Point → S0}
    (hu : MemLp u 2 μ) (w : Lp (HarmonicMaps.Ambient 5) 2 μ) :
    inner ℝ (frobeniusLp hu) w = ∫ x, inner ℝ (frobeniusField u x) (w x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((frobeniusCoordinateEquiv_memLp_iff μ 2 u).mpr hu).coeFn_toLp]
    with x hx
  exact congrArg (fun A => inner ℝ A (w x)) hx

/-- Actual Sobolev data as one point in the Hilbert product of L² spaces. -/
def sobolevL2Point {u : Point → S0} {D : Point → Gradient} (hu : MemH1 Ω u D) :
    SobolevL2Coordinates Ω :=
  WithLp.toLp 2 (Fin.cases (frobeniusLp hu.1) fun j : Fin 3 => frobeniusLp (hu.2.1 j))

theorem sobolevL2Point_eq_upstream {u : Point → S0} {D : Point → Gradient}
    (hu : MemH1 Ω u D) (hΩ : IsOpen Ω)
    (hw : HarmonicMaps.MemW12 ⟨Ω,hΩ⟩ (frobeniusField u) (frobeniusGradient D)) :
    sobolevL2Point hu = WithLp.toLp 2
      (Fin.cases (hw.2.1.toLp (frobeniusField u))
        fun j : Fin 3 => (hw.2.2 j).toLp (fun x => frobeniusGradient D x j)) := by
  unfold sobolevL2Point frobeniusLp
  rfl

private theorem sobolevL2Point_sub {u v : Point → S0} {D G : Point → Gradient}
    (hu : MemH1 Ω u D) (hv : MemH1 Ω v G) :
    sobolevL2Point (hu.sub hv) = sobolevL2Point hu - sobolevL2Point hv := by
  ext1 i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact frobeniusLp_sub hu.1 hv.1
  · exact frobeniusLp_sub (hu.2.1 j) (hv.2.1 j)

/-- A bounded trace on the L² Sobolev graph, extended linearly and continuously
to its ambient Hilbert product. Its kernel on the graph is the intrinsic
zero-trace closure, and it agrees with restriction for smooth fields. -/
structure SobolevTraceOperator (Ω : Set Point) where
  operator : SobolevL2Coordinates Ω →L[ℝ] SobolevTraceL2 Ω
  kernel : ∀ {u : Point → S0} {D : Point → Gradient} (hu : MemH1 Ω u D),
    operator (sobolevL2Point hu) = 0 ↔ HasZeroTrace Ω u D
  smooth : ∀ {B : Point → S0}, ContDiff ℝ ∞ B →
    ∀ hB : MemH1 Ω B (ClassicalGradient B),
      (operator (sobolevL2Point hB) : frontier Ω → HarmonicMaps.Ambient 5)
        =ᵐ[frontierSurfaceMeasure Ω] fun x => frobeniusCoordinateEquiv (B x)

abbrev SobolevTraceOperator.trace (T : SobolevTraceOperator Ω)
    {u : Point → S0} {D : Point → Gradient} (hu : MemH1 Ω u D) : SobolevTraceL2 Ω :=
  T.operator (sobolevL2Point hu)

theorem SobolevTraceOperator.trace_eq_iff_sameTrace (T : SobolevTraceOperator Ω)
    {u v : Point → S0} {D G : Point → Gradient} (hu : MemH1 Ω u D) (hv : MemH1 Ω v G) :
    T.trace hu = T.trace hv ↔ SameTrace Ω u v D G := by
  change T.operator (sobolevL2Point hu) = T.operator (sobolevL2Point hv) ↔
    HasZeroTrace Ω (u - v) (D - G)
  rw [← sub_eq_zero, ← map_sub, ← sobolevL2Point_sub]
  exact T.kernel (hu.sub hv)

private theorem memH1_of_contDiff_of_bounded (hΩ : IsOpen Ω) (hBound : Bornology.IsBounded Ω)
    {B : Point → S0} (hB : ContDiff ℝ ∞ B) : MemH1 Ω B (ClassicalGradient B) :=
  memH1Loc_of_contDiffOn isOpen_univ (hB.of_le (by simp)).contDiffOn Ω hΩ
    ⟨hBound.isCompact_closure, subset_univ _⟩

/-- The intrinsic smooth-lift class is the Sobolev trace class of the boundary
datum, using any smooth extension of that datum. -/
theorem SobolevTraceOperator.hasSmoothTrace_iff_trace_eq (T : SobolevTraceOperator Ω)
    (hΩ : IsOpen Ω) (hBound : Bornology.IsBounded Ω)
    {b : frontier Ω → S0} {u B : Point → S0} {D : Point → Gradient}
    (hu : MemH1 Ω u D) (hB : ContDiff ℝ ∞ B) (hb : ∀ x : frontier Ω, B x = b x) :
    HasSmoothTrace Ω u D b ↔
      (T.trace hu : frontier Ω → HarmonicMaps.Ambient 5) =ᵐ[frontierSurfaceMeasure Ω]
        fun x => frobeniusCoordinateEquiv (b x) := by
  constructor
  · rintro ⟨C, hC, hCb, huC⟩
    have hCH := memH1_of_contDiff_of_bounded hΩ hBound hC
    rw [(T.trace_eq_iff_sameTrace hu hCH).mpr huC]
    exact (T.smooth hC hCH).trans (Eventually.of_forall fun x => congrArg frobeniusCoordinateEquiv (hCb x))
  · intro h
    have hBH := memH1_of_contDiff_of_bounded hΩ hBound hB
    have hBtrace := (T.smooth hB hBH).trans (Eventually.of_forall fun x => congrArg frobeniusCoordinateEquiv (hb x))
    refine ⟨B, hB, hb, (T.trace_eq_iff_sameTrace hu hBH).mp ?_⟩
    exact Lp.ext (h.trans hBtrace.symm)

theorem SobolevTraceOperator.sameTrace_every_smoothLift (T : SobolevTraceOperator Ω)
    (hΩ : IsOpen Ω) (hBound : Bornology.IsBounded Ω)
    {b : frontier Ω → S0} {u B : Point → S0} {D : Point → Gradient}
    (hu : MemH1 Ω u D) (hTrace : HasSmoothTrace Ω u D b)
    (hB : ContDiff ℝ ∞ B) (hb : ∀ x : frontier Ω, B x = b x) :
    SameTrace Ω u B D (ClassicalGradient B) := by
  have hBH := memH1_of_contDiff_of_bounded hΩ hBound hB
  have hU := (T.hasSmoothTrace_iff_trace_eq hΩ hBound hu hB hb).mp hTrace
  have hBtrace := (T.smooth hB hBH).trans (Eventually.of_forall fun x => congrArg frobeniusCoordinateEquiv (hb x))
  exact (T.trace_eq_iff_sameTrace hu hBH).mp (Lp.ext (hU.trans hBtrace.symm))

private theorem tendsto_inner_sobolevL2Point
    {u : ℕ → Point → S0} {D : ℕ → Point → Gradient} {v : Point → S0} {G : Point → Gradient}
    (hu : ∀ k, MemH1 Ω (u k) (D k)) (hv : MemH1 Ω v G)
    (hU : WeakL2FrobeniusConvergence Ω u v)
    (hD : ∀ j : Fin 3, WeakL2FrobeniusConvergence Ω (fun k x => D k x j) (fun x => G x j))
    (w : SobolevL2Coordinates Ω) :
    Tendsto (fun k => inner ℝ (sobolevL2Point (hu k)) w) atTop
      (𝓝 (inner ℝ (sobolevL2Point hv) w)) := by
  have hTerm (i : Fin 4) :
      Tendsto (fun k => inner ℝ (sobolevL2Point (hu k) i) (w i)) atTop
        (𝓝 (inner ℝ (sobolevL2Point hv i) (w i))) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change Tendsto (fun k => inner ℝ (frobeniusLp (hu k).1) (w 0)) atTop
        (𝓝 (inner ℝ (frobeniusLp hv.1) (w 0)))
      simp_rw [inner_frobeniusLp_eq_integral]
      exact (weakL2FrobeniusConvergence_iff_upstream Ω _ _).mp hU (w 0)
    · change Tendsto (fun k => inner ℝ (frobeniusLp ((hu k).2.1 j)) (w j.succ)) atTop
        (𝓝 (inner ℝ (frobeniusLp (hv.2.1 j)) (w j.succ)))
      simp_rw [inner_frobeniusLp_eq_integral]
      exact (weakL2FrobeniusConvergence_iff_upstream Ω _ _).mp (hD j) (w j.succ)
  simpa only [PiLp.inner_apply] using tendsto_finsetSum (s := Finset.univ) (fun i _ => hTerm i)

/-- Pairing the traces with any fixed boundary L² field preserves weak
convergence of the actual map and derivative columns. -/
theorem SobolevTraceOperator.tendsto_inner_trace (T : SobolevTraceOperator Ω)
    {u : ℕ → Point → S0} {D : ℕ → Point → Gradient} {v : Point → S0} {G : Point → Gradient}
    (hu : ∀ k, MemH1 Ω (u k) (D k)) (hv : MemH1 Ω v G)
    (hU : WeakL2FrobeniusConvergence Ω u v)
    (hD : ∀ j : Fin 3, WeakL2FrobeniusConvergence Ω (fun k x => D k x j) (fun x => G x j))
    (w : SobolevTraceL2 Ω) :
    Tendsto (fun k => inner ℝ (T.trace (hu k)) w) atTop (𝓝 (inner ℝ (T.trace hv) w)) := by
  let L : SobolevL2Coordinates Ω →L[ℝ] ℝ := (innerSL ℝ w).comp T.operator
  let z := (InnerProductSpace.toDual ℝ (SobolevL2Coordinates Ω)).symm L
  have hEq (x : SobolevL2Coordinates Ω) :
      inner ℝ (T.operator x) w = inner ℝ x z := by
    calc
      _ = inner ℝ w (T.operator x) := real_inner_comm _ _
      _ = L x := rfl
      _ = inner ℝ z x := (InnerProductSpace.toDual_symm_apply (x := x) (y := L)).symm
      _ = _ := real_inner_comm _ _
  simp_rw [SobolevTraceOperator.trace, hEq]
  exact tendsto_inner_sobolevL2Point hu hv hU hD z

theorem SobolevTraceOperator.hasZeroTrace_of_weakL2 (T : SobolevTraceOperator Ω)
    {u : ℕ → Point → S0} {D : ℕ → Point → Gradient} {v : Point → S0} {G : Point → Gradient}
    (hu : ∀ k, MemH1 Ω (u k) (D k)) (hv : MemH1 Ω v G)
    (hU : WeakL2FrobeniusConvergence Ω u v)
    (hD : ∀ j : Fin 3, WeakL2FrobeniusConvergence Ω (fun k x => D k x j) (fun x => G x j))
    (hZero : ∀ k, HasZeroTrace Ω (u k) (D k)) : HasZeroTrace Ω v G := by
  let w := T.trace hv
  have h₁ := T.tendsto_inner_trace hu hv hU hD w
  have h₂ : Tendsto (fun k => inner ℝ (T.trace (hu k)) w) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr
    intro k
    have hTr : T.trace (hu k) = 0 := (T.kernel (hu k)).mpr (hZero k)
    rw [hTr, inner_zero_left]
  exact (T.kernel hv).mp (inner_self_eq_zero.mp (tendsto_nhds_unique h₁ h₂))

/-- The fixed Dirichlet class is weakly closed for actual Sobolev data. -/
theorem SobolevTraceOperator.hasSmoothTrace_of_weakL2 (T : SobolevTraceOperator Ω)
    (hΩ : IsOpen Ω) (hBound : Bornology.IsBounded Ω)
    {b : frontier Ω → S0} {u : ℕ → Point → S0} {D : ℕ → Point → Gradient}
    {v : Point → S0} {G : Point → Gradient}
    (hu : ∀ k, MemH1 Ω (u k) (D k)) (hv : MemH1 Ω v G)
    (hU : WeakL2FrobeniusConvergence Ω u v)
    (hD : ∀ j : Fin 3, WeakL2FrobeniusConvergence Ω (fun k x => D k x j) (fun x => G x j))
    (hTrace : ∀ k, HasSmoothTrace Ω (u k) (D k) b) : HasSmoothTrace Ω v G b := by
  obtain ⟨B, hB, hb, _⟩ := hTrace 0
  have hBH := memH1_of_contDiff_of_bounded hΩ hBound hB
  have hEqual (k : ℕ) : T.trace (hu k) = T.trace hBH :=
    (T.trace_eq_iff_sameTrace (hu k) hBH).mpr
      (T.sameTrace_every_smoothLift hΩ hBound (hu k) (hTrace k) hB hb)
  let w := T.trace hv - T.trace hBH
  have h₁ := T.tendsto_inner_trace hu hv hU hD w
  have h₂ : Tendsto (fun k => inner ℝ (T.trace (hu k)) w) atTop
      (𝓝 (inner ℝ (T.trace hBH) w)) :=
    tendsto_const_nhds.congr (fun k => (congrArg (fun x => inner ℝ x w) (hEqual k)).symm)
  have hEqual' := tendsto_nhds_unique h₁ h₂
  have hw : inner ℝ w w = 0 := by
    change inner ℝ (T.trace hv - T.trace hBH) w = 0
    rw [inner_sub_left, hEqual', sub_self]
  exact ⟨B, hB, hb, (T.trace_eq_iff_sameTrace hv hBH).mp (sub_eq_zero.mp (inner_self_eq_zero.mp hw))⟩

private theorem IsGlobalEnergyMinimizer.energy_le_dirichlet_of_vacuum
    {a : BulkCoefficients} {ε : ElasticScale} {b : frontier Ω → S0}
    {u w : Point → S0} {D H : Point → Gradient}
    (h : IsGlobalEnergyMinimizer a ε Ω b u D)
    (hw : MemH1 Ω w H) (ht : HasSmoothTrace Ω w H b) (hVac : TakesVacuumValues a Ω w) :
    energy a ε Ω u D ≤ dirichletEnergy Ω H :=
  (h.2.2 w H hw ht).trans_eq (energy_eq_dirichlet_of_takesVacuumValues a ε H hVac)

/-- Global strong compactness for a prescribed sequence of scales, given one
finite-energy vacuum competitor with the fixed boundary trace. The limit is a
global Dirichlet minimizer, the total energies converge, and the scaled bulk
potential converges to zero in L¹. -/
theorem exists_global_energy_limit_subsequence_of_vacuum_competitor
    (a : BulkCoefficients) (hΩ : IsBoundedDomain Ω)
    (T : SobolevTraceOperator Ω) (hComp : NonexpansiveSobolevTraceComposition Ω)
    (b : frontier Ω → S0) (ε : ℕ → ElasticScale)
    (hε : Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0))
    (u : ℕ → Point → S0) (D : ℕ → Point → Gradient)
    (hMin : ∀ k, IsGlobalEnergyMinimizer a (ε k) Ω b (u k) (D k))
    {w : Point → S0} {H : Point → Gradient}
    (hw : MemH1 Ω w H) (hwt : HasSmoothTrace Ω w H b) (hwVac : TakesVacuumValues a Ω w) :
    ∃ (κ : ℕ → ℕ) (v : Point → S0) (G : Point → Gradient),
      StrictMono κ ∧ StrongH1 Ω (u ∘ κ) (D ∘ κ) v G ∧ IsGlobalDirichletMinimizer a Ω b v G ∧
      (∀ k, MemLp (fun x => (ε (κ k) : ℝ)⁻¹ ^ 2 * bulkPotential a (u (κ k) x))
        1 (volume.restrict Ω)) ∧
      Tendsto (fun k => eLpNorm (fun x => (ε (κ k) : ℝ)⁻¹ ^ 2 * bulkPotential a (u (κ k) x))
        1 (volume.restrict Ω)) atTop (𝓝 0) ∧
      Tendsto (fun k => energy a (ε (κ k)) Ω (u (κ k)) (D (κ k))) atTop
        (𝓝 (dirichletEnergy Ω G)) := by
  have hFinite : (volume : Measure Point) Ω ≠ ⊤ := hΩ.2.2.measure_lt_top.ne
  have hWfin := dirichletEnergy_lt_top_of_memLp hw.2.1
  let E := (dirichletEnergy Ω H).toReal
  let R := max (Real.sqrt 2 * vacuumRadius a) (eLpNorm b ⊤ (frontierSurfaceMeasure Ω)).toReal
  let M := max E R
  have hM : 0 ≤ M := ENNReal.toReal_nonneg.trans (le_max_left _ _)
  have hCompare (k : ℕ) := (hMin k).energy_le_dirichlet_of_vacuum hw hwt hwVac
  have hBounds (k : ℕ) : energy a (ε k) Ω (u k) (D k) ≤ ENNReal.ofReal M ∧
      eLpNorm (u k) ⊤ (volume.restrict Ω) ≤ ENNReal.ofReal M := by
    constructor
    · calc
        _ ≤ dirichletEnergy Ω H := hCompare k
        _ = ENNReal.ofReal E := (ENNReal.ofReal_toReal hWfin.ne).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (le_max_left _ _)
    · exact ((hMin k).eLpNorm_top_le_vacuumOrTrace hΩ.1 hΩ.2.2 hComp).trans
        (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  obtain ⟨κ, v, G, hκ, hu, hv, hvVac, _, hStrong, _, hWeak, hGrad⟩ :=
    exists_vacuum_weak_subsequence_of_bounded_energy a hΩ.1 hFinite ε hε u D
      (fun k => (hMin k).1.memH1Loc) M hM hBounds
  have hU (k : ℕ) : MemH1 Ω (u (κ k)) (D (κ k)) := hu (κ k)
  have hTrace : HasSmoothTrace Ω v G b := T.hasSmoothTrace_of_weakL2 hΩ.1 hΩ.2.2
    hU hv hWeak hGrad (fun k => (hMin (κ k)).2.1)
  have hVmin : IsGlobalDirichletMinimizer a Ω b v G := by
    refine ⟨hv, hTrace, hvVac, fun z J hz hzt hzVac => ?_⟩
    have hlim := dirichletEnergy_le_liminf_of_weak_frobenius (fun k => (hU k).2.1) hv.2.1 hGrad
    have hPointwise (k : ℕ) : dirichletEnergy Ω (D (κ k)) ≤ dirichletEnergy Ω J := by
      calc
        _ ≤ energy a (ε (κ k)) Ω (u (κ k)) (D (κ k)) := by
          rw [energy_eq_dirichlet_add_scaledPotential _ _ _ (hU k).2.1]
          exact le_add_right le_rfl
        _ ≤ dirichletEnergy Ω J := (hMin (κ k)).energy_le_dirichlet_of_vacuum hz hzt hzVac
    exact hlim.trans ((liminf_le_liminf (Eventually.of_forall hPointwise)).trans_eq (liminf_const _))
  have hUpper :
      atTop.limsup (fun k => energy a (ε (κ k)) Ω (u (κ k)) (D (κ k))) ≤ dirichletEnergy Ω G :=
    (limsup_le_limsup (Eventually.of_forall fun k =>
      (hMin (κ k)).energy_le_dirichlet_of_vacuum hv hTrace hvVac)).trans_eq (limsup_const _)
  obtain ⟨hSob, hBulkLp, hBulk, hEnergy⟩ :=
    strongH1_and_scaledPotential_of_limsup_energy_le_dirichlet a (ε ∘ κ)
      hU hv hStrong hGrad (fun k => ((hCompare (κ k)).trans_lt hWfin).ne) hUpper
  exact ⟨κ, v, G, hκ, hSob, hVmin, hBulkLp, hBulk, hEnergy⟩

/-- Select a sequence of elastic scales for a global minimizing family with
one fixed vacuum extension of the trace. -/
theorem exists_global_energy_limit_of_vacuum_competitor
    (a : BulkCoefficients) (hΩ : IsBoundedDomain Ω)
    (T : SobolevTraceOperator Ω) (hComp : NonexpansiveSobolevTraceComposition Ω)
    (b : frontier Ω → S0) (Q : ElasticScale → Point → S0) (D : ElasticScale → Point → Gradient)
    (hMin : ∀ ε, IsGlobalEnergyMinimizer a ε Ω b (Q ε) (D ε))
    {w : Point → S0} {H : Point → Gradient}
    (hw : MemH1 Ω w H) (hwt : HasSmoothTrace Ω w H b) (hwVac : TakesVacuumValues a Ω w) :
    ∃ (ε : ℕ → ElasticScale) (v : Point → S0) (G : Point → Gradient),
      Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0) ∧
      StrongH1 Ω (Q ∘ ε) (D ∘ ε) v G ∧ IsGlobalDirichletMinimizer a Ω b v G ∧
      (∀ k, MemLp (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (Q (ε k) x))
        1 (volume.restrict Ω)) ∧
      Tendsto (fun k => eLpNorm (fun x => (ε k : ℝ)⁻¹ ^ 2 * bulkPotential a (Q (ε k) x))
        1 (volume.restrict Ω)) atTop (𝓝 0) ∧
      Tendsto (fun k => energy a (ε k) Ω (Q (ε k)) (D (ε k))) atTop
        (𝓝 (dirichletEnergy Ω G)) := by
  let initial (k : ℕ) : ElasticScale := ⟨1 / ((k : ℝ) + 2), by
    have hk := Nat.cast_nonneg (α := ℝ) k
    refine ⟨by positivity, (div_lt_iff₀ (by positivity)).2 ?_⟩
    linarith only [hk]⟩
  have hε : Tendsto (fun k => (initial k : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_add_atTop_iff_nat 1).2 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [initial, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h
  obtain ⟨κ, v, G, hκ, hSob, hVmin, hBulkLp, hBulk, hEnergy⟩ :=
    exists_global_energy_limit_subsequence_of_vacuum_competitor a hΩ T hComp b initial hε
      (Q ∘ initial) (D ∘ initial) (fun k => hMin (initial k)) hw hwt hwVac
  exact ⟨initial ∘ κ, v, G, hε.comp hκ.tendsto_atTop, hSob, hVmin, hBulkLp, hBulk, hEnergy⟩

end Thesis

end
