module

public import Thesis.Upstream.WeakPoissonCoordinates
import Thesis.Upstream.PoissonBoundedForcing
import Thesis.Upstream.WeakHarmonicRepresentative
import HolderToCK.Analysis.RepresentativeGluing

/-! Continuous representatives for the original weak graph with bounded forcing. -/

public section

noncomputable section

open Filter HarmonicMaps HolderToCK MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

private theorem exists_compact_bounded_forcing_eq_on_ball {q : ℕ}
    {c : Point} {r M : ℝ} {F : Point → Ambient q}
    (hI : IntegrableOn F (ball c r)) (hM : 0 ≤ M)
    (hF : ∀ᵐ x ∂volume.restrict (ball c r), ‖F x‖ ≤ M) :
    ∃ g : Point → Ambient q, Integrable g volume ∧ MemLp g 2 volume ∧ HasCompactSupport g ∧
      (∀ x, ‖g x‖ ≤ M) ∧ g =ᵐ[volume.restrict (ball c r)] F := by
  classical
  let U := ball c r
  let F' := hI.aestronglyMeasurable.mk F
  have hF' : StronglyMeasurable F' := hI.aestronglyMeasurable.stronglyMeasurable_mk
  let s : Set (Ambient q) := {z | ‖z‖ ≤ M}
  have hs : MeasurableSet s := (isClosed_le continuous_norm continuous_const).measurableSet
  let V := F' ⁻¹' s
  have hV : MeasurableSet V := hF'.measurable hs
  let h := V.indicator F'
  let g := U.indicator h
  have hh : StronglyMeasurable h := hF'.indicator hV
  have hbound (x : Point) : ‖h x‖ ≤ M := by
    by_cases hx : x ∈ V
    · rw [show h x = F' x from indicator_of_mem hx _]
      exact hx
    · rw [show h x = 0 from indicator_of_notMem hx _, norm_zero]
      exact hM
  have hU : MeasurableSet U := measurableSet_ball
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.2 measure_ball_ne_top
  have hLp (p : ℝ≥0∞) : MemLp g p volume :=
    (memLp_indicator_iff_restrict hU).2
      (MemLp.of_bound hh.aestronglyMeasurable M (Eventually.of_forall hbound))
  have hgc : HasCompactSupport g := (isCompact_closedBall c r).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (support_indicator_subset.trans ball_subset_closedBall) isClosed_closedBall)
  have hgB (x : Point) : ‖g x‖ ≤ M := by
    by_cases hx : x ∈ U
    · rw [show g x = h x from indicator_of_mem hx _]
      exact hbound x
    · rw [show g x = 0 from indicator_of_notMem hx _, norm_zero]
      exact hM
  refine ⟨g, memLp_one_iff_integrable.mp (hLp 1), hLp 2, hgc, hgB, ?_⟩
  filter_upwards [ae_restrict_mem (μ := volume) hU, hI.aestronglyMeasurable.ae_eq_mk, hF]
    with x hx he hn
  have hIn : x ∈ V := by
    change ‖F' x‖ ≤ M
    exact (congrArg (fun y : Ambient q => ‖y‖) he).symm.le.trans hn
  exact (indicator_of_mem hx h).trans ((indicator_of_mem hIn F').trans he.symm)

private theorem exists_local_continuous_poisson_representative {q : ℕ}
    {Ω : OpenDomain 3} {u : Point → Ambient q} {Du : Point → HarmonicMaps.Gradient 3 q}
    {F : Point → Ambient q} (hu : MemW12Loc Ω u Du)
    (hEq : WeakPoissonOn Ω Du F) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ᵐ x ∂volume.restrict Ω.val, ‖F x‖ ≤ M)
    {c : Point} {r : ℝ} (hR : closedBall c r ⊆ Ω.val) :
    ∃ v : Point → Ambient q, u =ᵐ[volume.restrict (ball c r)] v ∧ ContinuousOn v (ball c r) := by
  let U := ballDomain c r
  have hUΩ : U.val ⊆ Ω.val := ball_subset_closedBall.trans hR
  have hI : IntegrableOn F U.val :=
    (hEq.1.integrableOn_compact_subset hR (isCompact_closedBall c r)).mono_set ball_subset_closedBall
  obtain ⟨g, hg, hg₂, hcg, hgB, he⟩ := exists_compact_bounded_forcing_eq_on_ball hI hM
    (ae_restrict_of_ae_restrict_of_subset hUΩ hF)
  let P := newtonianPotential (by decide : 2 ≤ 3) g
  let Dp (x : Point) (i : Fin 3) := potentialGradientColumn i g x
  obtain ⟨hP, hGraph⟩ := bounded_compact_newtonian_weakGraph hg hg₂ hcg hgB
  obtain ⟨hPW, hPweak⟩ := hGraph U isBounded_ball
  have hv := hu.mono hUΩ
  have hp := hPW.to_memW12Loc
  have hSubW : MemW12Loc U (u - P) (fun x i => Du x i - Dp x i) := by
    refine ⟨hv.1.sub hp.1, ?_, ?_⟩
    · intro K hK hKU
      exact (hv.2.1 K hK hKU).sub (hp.2.1 K hK hKU)
    · intro i K hK hKU
      exact (hv.2.2 i K hK hKU).sub (hp.2.2 i K hK hKU)
  have hSubEq : WeakPoissonOn U (fun x i => Du x i - Dp x i) (fun _ => 0) := by
    apply ((hEq.mono hUΩ).sub hPweak).congr EventuallyEq.rfl
    filter_upwards [he] with x hx
    rw [hx, sub_self]
  obtain ⟨w, hwEq, hwC⟩ := hSubEq.exists_continuousRepresentative_of_zero (by decide : 2 ≤ 3) hSubW
  have hwAE : u =ᵐ[volume.restrict U.val] (w + P) := by
    filter_upwards [hwEq] with x hx
    exact sub_eq_iff_eq_add.1 hx
  exact ⟨w + P, hwAE, hwC.add hP.continuousOn⟩

private theorem exists_continuous_ambient_poisson_representative {q : ℕ}
    {Ω : OpenDomain 3} {u : Point → Ambient q} {Du : Point → HarmonicMaps.Gradient 3 q}
    {F : Point → Ambient q} (hu : MemW12Loc Ω u Du)
    (hEq : WeakPoissonOn Ω Du F) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ᵐ x ∂volume.restrict Ω.val, ‖F x‖ ≤ M) :
    ∃ v : Point → Ambient q, u =ᵐ[volume.restrict Ω.val] v ∧ ContinuousOn v Ω.val := by
  classical
  have hLocal (x : Ω.val) :
      ∃ r : ℝ, 0 < r ∧ closedBall x.val r ⊆ Ω.val := by
    obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 Ω.property x.val x.property
    exact ⟨r / 2, half_pos hr, (closedBall_subset_ball (half_lt_self hr)).trans hB⟩
  choose r hr hR using hLocal
  let U (x : Ω.val) := ball x.val (r x)
  have hV (x : Ω.val) : ∃ v : Point → Ambient q,
      u =ᵐ[volume.restrict (U x)] v ∧ ContinuousOn v (U x) :=
    exists_local_continuous_poisson_representative hu hEq hM hF (hR x)
  choose v hvAE hvC using hV
  have hCover : Ω.val ⊆ ⋃ x, U x := fun x hx => mem_iUnion.2
    ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨w, hwC, hwAE, _⟩ := continuous_representatives_glue u Ω.val Ω.property U v
    (fun _ => isOpen_ball) hvC (fun x => (hvAE x).symm) hCover
  exact ⟨w, hwAE.symm, hwC⟩

/-- Bounded right hand side gives a continuous representative of the
original symmetric-traceless tensor map. -/
theorem IsWeakPoisson.exists_continuousRepresentative_of_bounded
    {Ω : Set Point} {u : Point → S0} {D : Point → Thesis.Gradient} {F : Point → Tensor}
    (hEq : IsWeakPoisson Ω D F) (hΩ : IsOpen Ω) (hu : MemH1Loc Ω u D)
    (hBound : ∃ M : ℝ, ∀ᵐ x ∂volume.restrict Ω, ‖F x‖ ≤ M) :
    ∃ v : Point → S0, u =ᵐ[volume.restrict Ω] v ∧ ContinuousOn v Ω := by
  obtain ⟨M, hM⟩ := hBound
  obtain ⟨hu', hEq'⟩ := hEq.to_frobenius hΩ hu
  have hB : ∀ᵐ x ∂volume.restrict Ω,
      ‖frobeniusCoordinateEquiv (traceFreeSymmetricPart (F x))‖ ≤ max M 0 := by
    filter_upwards [hM] with x hx
    rw [frobeniusCoordinateEquiv.norm_map]
    exact (norm_traceFreeSymmetricPart_le _).trans (hx.trans (le_max_left _ _))
  obtain ⟨w, hw, hwC⟩ := exists_continuous_ambient_poisson_representative hu' hEq'
    (le_max_right M 0) hB
  refine ⟨frobeniusCoordinateEquiv.symm ∘ w, ?_,
    frobeniusCoordinateEquiv.symm.continuous.comp_continuousOn hwC⟩
  filter_upwards [hw] with x hx
  exact (frobeniusCoordinateEquiv.symm_apply_apply (u x)).symm.trans
    (congrArg frobeniusCoordinateEquiv.symm hx)

end Thesis
