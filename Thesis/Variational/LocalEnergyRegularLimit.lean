module

public import Thesis.Variational.BoundedEnergyRegularLimit
public import Thesis.Variational.VacuumHarmonicVariation
import Thesis.Variational.BoundaryLimit
import StratificationTheory.Compactness.CofinalCompactExhaustion
import Mathlib.Topology.MetricSpace.Thickening

/-! Local energy compactness on an open complement, with one common subsequence. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal Matrix.Norms.Frobenius Topology

namespace Thesis

/-- Along any vanishing prescribed scales, open-local energy caps suffice for
the strong vacuum limit, the full weak equation and its regular representative. -/
theorem exists_local_vacuum_regular_limit_of_projectionLayer (a : BulkCoefficients)
    (hProj : HasPenalizedProjectionLayer a) {W : Set Point} (hW : IsOpen W)
    (ε : ℕ → ElasticScale) (hε : Tendsto (fun k => (ε k : ℝ)) atTop (𝓝 0))
    (u : ℕ → Point → S0) (D : ℕ → Point → Gradient)
    (hMin : ∀ k, IsLocalEnergyMinimizer a (ε k) W (u k) (D k))
    (M : ℝ) (hM : 0 < M) (hNorm : ∀ k, ∀ᵐ x ∂volume.restrict W, ‖u k x‖ ≤ M)
    (hFin : ∀ k, energy a (ε k) W (u k) (D k) ≠ ⊤)
    (hLocal : ∀ U : Set Point, IsOpen U → CompactlyContained U W →
      ∃ B > (0 : ℝ), ∀ k, energy a (ε k) U (u k) (D k) ≤ ENNReal.ofReal B) :
    ∃ (κ : ℕ → ℕ) (Q₀ : Point → S0) (D₀ : Point → Gradient),
      StrictMono κ ∧ IsLocalDirichletMinimizer a W Q₀ D₀ ∧
      WeakLaplacianEq W D₀ (harmonicRhs a Q₀ D₀) ∧
      StrongH1Loc W (u ∘ κ) (D ∘ κ) Q₀ D₀ ∧
      ConvergesScaledPotentialLoc a W (ε ∘ κ) (u ∘ κ) ∧
      LocallyFiniteIn W (singularSet W Q₀) ∧
      ContDiffOn ℝ ∞ Q₀ (W \ singularSet W Q₀) ∧
      D₀ =ᵐ[volume.restrict (W \ singularSet W Q₀)] ClassicalGradient Q₀ := by
  let Ω : HarmonicMaps.OpenDomain 3 := ⟨W, hW⟩
  have hBall (c : Point) (r : ℝ) (hr : 0 < r) (hrW : closedBall c r ⊆ W) :
      CompactlyContained (ball c r) W := by
    unfold CompactlyContained
    rw [closure_ball c hr.ne']
    exact ⟨isCompact_closedBall _ _, hrW⟩
  have hBound (c : Point) (r : ℝ) (hr : 0 < r) (hrW : closedBall c r ⊆ W) :
      ∃ B > (0 : ℝ), ∀ k, energy a (ε k) (ball c r) (u k) (D k) ≤ ENNReal.ofReal B :=
    hLocal _ isOpen_ball (hBall c r hr hrW)
  have hData (c : Point) (r : ℝ) (hr : 0 < r) (hrW : closedBall c r ⊆ W) :
      ∃ B C : ℝ≥0, (∀ k, (∫ x in ball c r, ‖u k x‖ ^ 2) ≤ B) ∧
        ∀ k, (∫⁻ x in ball c r, ENNReal.ofReal (gradientNormSq (D k x))) ≤ C := by
    let U := ball c r
    letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.2 measure_ball_ne_top
    obtain ⟨A, hA, hEnergy⟩ := hBound c r hr hrW
    let B : ℝ≥0 := ⟨M ^ 2 * (volume U).toReal, by positivity⟩
    let C : ℝ≥0 := ⟨2 * A, by positivity⟩
    refine ⟨B, C, ?_, ?_⟩
    · intro k
      have hS := (hMin k).1 U isOpen_ball (hBall c r hr hrW)
      have hB := ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hrW) (hNorm k)
      calc
        _ ≤ ∫ _ in U, M ^ 2 := integral_mono_ae (hS.1.integrable_norm_pow (by decide))
          (integrable_const _) (hB.mono fun x hx => pow_le_pow_left₀ (norm_nonneg (u k x)) hx 2)
        _ = (B : ℝ) := by
          change (∫ _ in U, M ^ 2) = M ^ 2 * (volume U).toReal
          simp [integral_const, smul_eq_mul, measureReal_def, mul_comm]
    · intro k
      exact (lintegral_gradientNormSq_le_twice_energy a (ε k) U (u k) (D k)).trans
        ((mul_le_mul_right (hEnergy k) _).trans_eq (by
          rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
          exact ENNReal.ofReal_eq_coe_nnreal C.property))
  obtain ⟨κ, v, G, hκ, hv, hCompact⟩ :=
    exists_tensor_rellich_subsequence_local Ω u D (fun k => (hMin k).1) hData
  let f := u ∘ κ
  let J := D ∘ κ
  let δ := ε ∘ κ
  have hδ : Tendsto (fun k => (δ k : ℝ)) atTop (𝓝 0) := hε.comp hκ.tendsto_atTop
  have hF (k : ℕ) : HarmonicMaps.MemW12Loc Ω (frobeniusField (f k)) (frobeniusGradient (J k)) :=
    (memH1Loc_iff_memW12Loc Ω _ _).1 (hMin (κ k)).1
  have hV : HarmonicMaps.MemW12Loc Ω (frobeniusField v) (frobeniusGradient G) :=
    (memH1Loc_iff_memW12Loc Ω _ _).1 hv
  have hVac : TakesVacuumValues a W v := by
    obtain ⟨K, hK, hKW, _, hCover, _⟩ :=
      StratificationTheory.Compactness.exists_cofinal_compact_exhaustion_openDomain Ω
    change ∀ᵐ x ∂volume.restrict Ω.val, v x ∈ vacuum a
    rw [← hCover, ae_restrict_iUnion_iff]
    intro i
    obtain ⟨r, hr, hrW⟩ := (hK i).exists_cthickening_subset_open hW (hKW i)
    let U := thickening r (K i)
    have hKU : K i ⊆ U := self_subset_thickening hr _
    have hCl : closure U ⊆ cthickening r (K i) := closure_thickening_subset_cthickening _ _
    have hUW : CompactlyContained U W :=
      ⟨(hK i).cthickening.of_isClosed_subset isClosed_closure hCl, hCl.trans hrW⟩
    obtain ⟨B, _, hB⟩ := hLocal U isOpen_thickening hUW
    have hfMeas (k : ℕ) : AEStronglyMeasurable (f k) (volume.restrict (K i)) :=
      ((frobeniusCoordinateEquiv_memLp_iff (volume.restrict (K i)) 2 (f k)).mp
        ((hF k).2.1 (K i) (hK i) (hKW i))).aestronglyMeasurable
    have hvMeas : AEStronglyMeasurable v (volume.restrict (K i)) :=
      ((frobeniusCoordinateEquiv_memLp_iff (volume.restrict (K i)) 2 v).mp
        (hV.2.1 (K i) (hK i) (hKW i))).aestronglyMeasurable
    have hMeasure := tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hfMeas hvMeas
      (hCompact _ (hK i) (hKW i)).1
    obtain ⟨s, hs, hAE⟩ := hMeasure.exists_seq_tendsto_ae
    exact takesVacuumValues_of_ae_tendsto_of_energy_bound a (K i) (δ ∘ s)
      (hδ.comp hs.tendsto_atTop) (f ∘ s) (J ∘ s) v (fun k => hfMeas (s k)) hvMeas hAE B
      (fun k => (lintegral_mono_set hKU).trans (hB (κ (s k))))
  have hS (c : Point) (r : ℝ) (_ : 0 < r) (hrW : closedBall c r ⊆ W) :
      Tendsto (fun k => eLpNorm (f k - v) 2 (volume.restrict (ball c r))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hCompact _ (isCompact_closedBall c r) hrW).1 (fun _ => zero_le)
      (fun k => eLpNorm_mono_measure _ (Measure.restrict_mono_set _ ball_subset_closedBall))
  have hL (c : Point) (r : ℝ) (_ : 0 < r) (hrW : closedBall c r ⊆ W) (i : Fin 3) :
      WeakL2FrobeniusConvergence (ball c r) (fun k x => J k x i) (fun x => G x i) :=
    WeakL2FrobeniusConvergence.mono ((hCompact _ (isCompact_closedBall c r) hrW).2 i)
      measurableSet_ball ball_subset_closedBall
  obtain ⟨hStrong, hPot, hVMin⟩ := strongH1Loc_and_minimizing_of_penalizedProjectionLayer a hProj hW
    δ hδ f J v G (fun k => hMin (κ k)) hv hVac M hM (fun k => hNorm (κ k))
    (fun k => hFin (κ k)) (fun c r hr hR => by
      obtain ⟨B, hB, hE⟩ := hBound c r hr hR
      exact ⟨B, hB, fun k => hE (κ k)⟩) hS hL
  obtain ⟨hFinite, w, hwEq, hwLoc, hwSmooth, hwGrad⟩ :=
    vacuum_minimizer_exists_regularRepresentative a hW hVMin
  have hwMin : IsLocalDirichletMinimizer a W w G := by
    refine ⟨hwLoc, hVac.congr_ae hwEq.symm, ?_⟩
    intro c r hr hrW z E hz hzN hzT
    have hEq := ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hrW) hwEq
    exact hVMin.2.2 c r hr hrW z E hz hzN
      (hzT.congr_ae EventuallyEq.rfl hEq EventuallyEq.rfl EventuallyEq.rfl)
  have hStrong' : StrongH1Loc W f J w G := by
    intro V hV hVW
    exact (hStrong V hV hVW).congr_ae_limit
      (ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hVW.2) hwEq.symm) EventuallyEq.rfl
  have hSing := singularSet_congr_ae hwEq
  rw [← hSing] at hFinite hwSmooth hwGrad
  exact ⟨κ, w, G, hκ, hwMin, (hwMin.weakLaplacianEq_harmonicRhs hW).2, hStrong', hPot, hFinite, hwSmooth, hwGrad⟩

end Thesis
