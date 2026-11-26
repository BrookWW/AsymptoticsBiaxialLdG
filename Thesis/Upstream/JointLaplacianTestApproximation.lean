module

public import Thesis.Upstream.WholeSpaceLaplacianTestDensity
import SupportingAnalysis.Poisson.SquareBound
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Common compact-test approximations in the two norms used by weak regularity. -/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set
open scoped ContDiff ENNReal NNReal Topology

namespace Thesis

private def scalarApproximationRadius (n : ℕ) : ℝ := ((n : ℝ)+1)⁻¹

private theorem scalarApproximationRadius_pos (n : ℕ) : 0 < scalarApproximationRadius n := by
  unfold scalarApproximationRadius
  positivity

private theorem tendsto_scalarApproximationRadius :
    Tendsto (fun n : ℕ => ENNReal.ofReal (scalarApproximationRadius n)) atTop (𝓝 0) := by
  have h : Tendsto scalarApproximationRadius atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹) atTop (𝓝 0)
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h

private theorem exists_compactSmooth_approximation_two_four {f : Point → ℝ}
    (hfc : HasCompactSupport f) (hf : MemLp f 4 volume) :
    ∃ v : ℕ → Point → ℝ, (∀ n, ContDiff ℝ ∞ (v n) ∧ HasCompactSupport (v n)) ∧
      Tendsto (fun n => eLpNorm (v n-f) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (v n-f) 4 volume) atTop (𝓝 0) := by
  obtain ⟨R,hR⟩ := hfc.isCompact.isBounded.exists_norm_le
  let L := max R 0+1
  have hL : 0 < L := by dsimp only [L]; positivity
  let b : ContDiffBump (0 : Point) := ⟨L,L+1,hL,lt_add_one _⟩
  let S := closedBall (0 : Point) (L+1)
  have hfs : tsupport f ⊆ closedBall (0 : Point) L :=
    fun x hx => mem_closedBall_zero_iff.mpr
      ((hR x hx).trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)))
  have hb (x : Point) : ‖(b : Point → ℝ) x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg b.nonneg]
    exact b.le_one
  choose v hv using fun n : ℕ => hf.exist_eLpNorm_sub_le (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)
    (by norm_num) (scalarApproximationRadius_pos n)
  let w (n : ℕ) (x : Point) := (b : Point → ℝ) x * v n x
  have hF : ∀ n, ContDiff ℝ ∞ (w n) ∧ HasCompactSupport (w n) :=
    fun n => ⟨b.contDiff.mul (hv n).2.1,b.hasCompactSupport.mul_right⟩
  have hs (n : ℕ) : support (w n-f) ⊆ S :=
    (support_sub _ _).trans (union_subset
      ((support_mul_subset_left _ _).trans ((subset_tsupport _).trans b.tsupport_eq.le))
      ((subset_tsupport _).trans (hfs.trans (closedBall_subset_closedBall (le_add_of_nonneg_right zero_le_one)))))
  have hF₄ (n : ℕ) : eLpNorm (w n-f) 4 volume ≤ ENNReal.ofReal (scalarApproximationRadius n) := by
    refine (eLpNorm_mono_ae (Eventually.of_forall fun x => ?_)).trans (hv n).2.2
    change ‖(b : Point → ℝ) x*v n x-f x‖ ≤ ‖f x-v n x‖
    have hFix : (b : Point → ℝ) x*f x = f x := by
      by_cases hx : x ∈ tsupport f
      · rw [b.one_of_mem_closedBall (hfs hx),one_mul]
      · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero]
    conv_lhs => rw [← hFix,← mul_sub]
    rw [norm_mul,← norm_sub_rev]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb x)
  have hT₄ : Tendsto (fun n => eLpNorm (w n-f) 4 volume) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_scalarApproximationRadius
      (fun _ => zero_le) hF₄
  let C := volume S ^ (1/(2 : ℝ)-1/(4 : ℝ))
  have hC : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_closedBall_lt_top.ne
  have hF₂ (n : ℕ) : eLpNorm (w n-f) 2 volume ≤ eLpNorm (w n-f) 4 volume*C := by
    have hEq : S.indicator (w n-f) = w n-f := indicator_eq_self.mpr (hs n)
    have hA := ((hF n).1.continuous.aestronglyMeasurable.sub hf.1).mono_measure
      (Measure.restrict_le_self (s := S) (μ := volume))
    have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := (2 : ℝ≥0∞))
      (q := (4 : ℝ≥0∞)) (by norm_num) hA
    have hEq₂ : eLpNorm (w n-f) 2 volume = eLpNorm (w n-f) 2 (volume.restrict S) :=
      (congrArg (fun v => eLpNorm v 2 volume) hEq.symm).trans
        (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall)
    rw [hEq₂]
    refine hh.trans ?_
    rw [Measure.restrict_apply MeasurableSet.univ,univ_inter]
    change eLpNorm (w n-f) 4 (volume.restrict S)*C ≤ _
    have hQ : eLpNorm (w n-f) 4 (volume.restrict S) ≤ eLpNorm (w n-f) 4 volume :=
      eLpNorm_restrict_le (w n-f) 4 volume S
    exact mul_le_mul' hQ le_rfl
  have hLim := ENNReal.Tendsto.mul_const (b := C) hT₄ (Or.inr hC)
  refine ⟨w,hF,?_,hT₄⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_mul] using hLim) (fun _ => zero_le) hF₂

/-- A compactly supported square- and fourth-integrable force has one
compact smooth test-Laplacian approximation in both original norms. -/
theorem exists_joint_compactSmooth_laplacian_test_approximation {f : Point → ℝ}
    (hfc : HasCompactSupport f) (hf : MemLp f 4 volume) :
    ∃ φ : ℕ → Point → ℝ, (∀ n, ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n)) ∧
      Tendsto (fun n => eLpNorm (laplacian (φ n)-f) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (laplacian (φ n)-f) 4 volume) atTop (𝓝 0) := by
  obtain ⟨v,hv,hT₂,hT₄⟩ := exists_compactSmooth_approximation_two_four hfc hf
  choose ψ hψ hLap using fun n => exists_compactSmooth_laplacian_test_approximation (hv n).1 (hv n).2
  have hChoose (n : ℕ) : ∃ k : ℕ,
      eLpNorm (laplacian (ψ n k)-v n) 2 volume < ENNReal.ofReal (scalarApproximationRadius n) ∧
      eLpNorm (laplacian (ψ n k)-v n) 4 volume < ENNReal.ofReal (scalarApproximationRadius n) := by
    have hPos := ENNReal.ofReal_pos.mpr (scalarApproximationRadius_pos n)
    have h₂ := (hLap n 2 (by decide)).eventually_lt_const hPos
    have h₄ := (hLap n 4 (by decide)).eventually_lt_const hPos
    simpa only [Nat.cast_ofNat] using (h₂.and h₄).exists
  choose k hk using hChoose
  let φ (n : ℕ) := ψ n (k n)
  have hNorm (p : ℝ≥0∞) (hp : 1 ≤ p)
       : ∀ n, eLpNorm (laplacian (φ n)-f) p volume ≤
        eLpNorm (laplacian (φ n)-v n) p volume + eLpNorm (v n-f) p volume := by
    intro n
    rw [show laplacian (φ n)-f = (laplacian (φ n)-v n)+(v n-f) by abel]
    have hΔ := (SupportingAnalysis.smooth_compact_laplacian (hψ n (k n)).1 (hψ n (k n)).2).1.continuous
    exact eLpNorm_add_le (hΔ.aestronglyMeasurable.sub (hv n).1.continuous.aestronglyMeasurable)
      ((hv n).1.continuous.aestronglyMeasurable.sub hf.1) hp
  have hTotal (p : ℝ≥0∞) (hp : 1 ≤ p)
      (he : ∀ n : ℕ, eLpNorm (laplacian (φ n)-v n) p volume ≤ ENNReal.ofReal (scalarApproximationRadius n))
      (ht : Tendsto (fun n => eLpNorm (v n-f) p volume) atTop (𝓝 0)) :
      Tendsto (fun n => eLpNorm (laplacian (φ n)-f) p volume) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [zero_add] using tendsto_scalarApproximationRadius.add ht) (fun _ => zero_le) (fun n => ?_)
    exact (hNorm p hp n).trans (add_le_add (he n) le_rfl)
  exact ⟨φ,fun n => hψ n (k n),
    hTotal 2 (by norm_num) (fun n => (hk n).1.le) hT₂,
    hTotal 4 (by norm_num) (fun n => (hk n).2.le) hT₄⟩

end Thesis
