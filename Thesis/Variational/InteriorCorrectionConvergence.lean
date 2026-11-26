module

public import Thesis.External.InteriorCorrectionEstimates

/-! Local smooth extraction for the actual first-correction equation. -/

public section

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance interiorCorrectionConvergenceCoefficientNormed :
    NormedAddCommGroup ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance interiorCorrectionConvergenceCoefficientSpace :
    NormedSpace ℝ ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance interiorCorrectionConvergenceTensorENorm : ContinuousENorm S0 :=
  SeminormedAddGroup.toContinuousENorm

private theorem eventually_uniform_on_finitely_many_orders
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → Point → E) (K : Set Point) (j : ℕ)
    (h : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (F n) x‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ k ≤ j, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (F n) x‖ ≤ C := by
  classical
  choose C hC hBound using h
  let L := ∑ k ∈ Finset.range (j+1), C k
  refine ⟨L, Finset.sum_nonneg fun k _ => hC k, ?_⟩
  filter_upwards [(Filter.eventually_all_finset (Finset.range (j+1))).2 fun k _ => hBound k] with n hn
  intro k hk x hx
  have hK : k ∈ Finset.range (j+1) := Finset.mem_range.2 (Nat.lt_succ_iff.mpr hk)
  exact (hn k hK x hx).trans (Finset.single_le_sum (fun i _ => hC i) hK)

/-- The actual linear equations and compact derivative bounds on their
coefficients and sources give one local smooth correction subsequence. -/
theorem exists_smooth_correction_subsequence_of_linear_system
    (hEst : External.InteriorLinearPoissonSystemDerivativeEstimate)
    (hCompact : External.SmoothLocalJetCompactness)
    {U : Set Point} (hU : IsOpen U)
    (A : ℕ → Point → (S0 × Gradient) →L[ℝ] S0) (W F : ℕ → Point → S0)
    (hA : ∀ n, ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (A n) U)
    (hW : ∀ n, ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (W n) U)
    (hF : ∀ n, ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (F n) U)
    (hEq : ∀ n, ∀ x ∈ U, laplacian (W n) x + A n x (W n x, ClassicalGradient (W n) x) = F n x)
    {E : ℝ} (hE : 0 ≤ E)
    (hL2 : ∀ᶠ n in atTop, MemLp (W n) 2 (volume.restrict U) ∧
      eLpNorm (W n) 2 (volume.restrict U) ≤ ENNReal.ofReal E)
    (hAB : ∀ K : Set Point, IsCompact K → K ⊆ U → ∀ k : ℕ,
      ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (A n) x‖ ≤ M)
    (hFB : ∀ K : Set Point, IsCompact K → K ⊆ U → ∀ k : ℕ,
      ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (F n) x‖ ≤ D) :
    ∃ (κ : ℕ → ℕ) (v : Point → S0), StrictMono κ ∧ ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) v U ∧
      ∀ j : ℕ, 2 ≤ j → ConvergesCjLoc j U (W ∘ κ) v := by
  apply hCompact U hU W hW
  intro K hK hKU j
  have hLocal (c : K) : ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ x ∈ Metric.ball (c : Point) r, ‖iteratedFDeriv ℝ j (W n) x‖ ≤ C := by
    obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hKU c.property))
    let R := r / 2
    have hR : 0 < R := half_pos hr
    let B := Metric.ball (c : Point) R
    let V := Metric.closedBall (c : Point) R
    have hVU : V ⊆ U := (Metric.closedBall_subset_ball (half_lt_self hr)).trans hB
    have hBU : B ⊆ U := Metric.ball_subset_closedBall.trans hVU
    obtain ⟨M,hM,hMB⟩ := eventually_uniform_on_finitely_many_orders A V (j+2)
      (hAB V (isCompact_closedBall _ _) hVU)
    obtain ⟨D,hD,hDB⟩ := eventually_uniform_on_finitely_many_orders F V (j+2)
      (hFB V (isCompact_closedBall _ _) hVU)
    obtain ⟨C,hC,hEstC⟩ := hEst c R hR j M hM
    refine ⟨R/2, C*(E+D), half_pos hR, mul_nonneg hC.le (add_nonneg hE hD), ?_⟩
    filter_upwards [hL2, hMB, hDB] with n hnL hnM hnD
    have hL : MemLp (W n) 2 (volume.restrict B) := hnL.1.mono_measure (Measure.restrict_mono hBU le_rfl)
    have hN : eLpNorm (W n) 2 (volume.restrict B) ≤ ENNReal.ofReal E :=
      (eLpNorm_mono_measure (W n) (Measure.restrict_mono hBU le_rfl)).trans hnL.2
    exact hEstC (A n) (W n) (F n) E D ((hA n).mono hBU) ((hW n).mono hBU) ((hF n).mono hBU)
      hE hD hL hN (fun y hy => hEq n y (hBU hy))
      (fun k hk y hy => hnM k hk y (Metric.ball_subset_closedBall hy))
      (fun k hk y hy => hnD k hk y (Metric.ball_subset_closedBall hy))
  choose r C hr hC hBound using hLocal
  let V (c : K) := Metric.ball (c : Point) (r c)
  have hCover : K ⊆ ⋃ c : K, V c := fun c hc =>
    mem_iUnion.2 ⟨⟨c,hc⟩, Metric.mem_ball_self (hr ⟨c,hc⟩)⟩
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover V (fun _ => Metric.isOpen_ball) hCover
  refine ⟨∑ c ∈ I, C c, Finset.sum_nonneg fun c _ => hC c, ?_⟩
  filter_upwards [(Filter.eventually_all_finset I).2 fun c _ => hBound c] with n hn x hx
  obtain ⟨y,hy,hyB⟩ := mem_iUnion₂.1 (hI hx)
  exact (hn y hy x hyB).trans (Finset.single_le_sum (fun c _ => hC c) hy)

end Thesis

end
