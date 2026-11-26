module

public import SupportingAnalysis.Poisson.ConvolutionScaling

/-! Extension of compact-kernel weak convolution estimates to all integrable inputs. -/

public section

open MeasureTheory Set Metric
open scoped Convolution ENNReal Topology

set_option autoImplicit false

namespace SupportingAnalysis

/-- A weak bound for a compact kernel extends from compactly supported integrable data by
localizing the input on balls that contain all points used by the convolution. -/
theorem weakScalarConvolutionBound_of_compact_input {d : ℕ}
    {k : E d → ℝ} {C : ℝ} (hk : Integrable k) (hkc : HasCompactSupport k) (hC : 0 ≤ C)
    (hWeak : ∀ g : E d → ℝ, Integrable g → HasCompactSupport g →
      ∀ t : ℝ, 0 < t →
        volume {x : E d | t < |(k ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x|} ≤
          ENNReal.ofReal (C * (∫ x, |g x|) / t)) :
    WeakScalarConvolutionBound k C := by
  intro g hg
  refine ⟨(hk.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hg).aemeasurable, ?_⟩
  intro t ht
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (0 : E d) |>.mp
    (hkc.isBounded.subset (subset_tsupport k))
  let A : Set (E d) := {x | t < |(k ⋆[ContinuousLinearMap.mul ℝ ℝ] g) x|}
  let Aₙ (n : ℕ) : Set (E d) := A ∩ ball 0 (n : ℝ)
  have hCover : A = ⋃ n : ℕ, Aₙ n := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      exact mem_iUnion.mpr ⟨n, hx, mem_ball_zero_iff.mpr hn⟩
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact hn.1
  have hMono : Monotone Aₙ := fun _ _ h => inter_subset_inter_right A
    (ball_subset_ball (Nat.cast_le.mpr h))
  change volume A ≤ _
  rw [hCover, hMono.measure_iUnion]
  refine iSup_le fun n => ?_
  let B : Set (E d) := closedBall 0 ((n : ℝ) + R)
  let gₙ : E d → ℝ := B.indicator g
  have hgₙ : Integrable gₙ := hg.indicator measurableSet_closedBall
  have hgₙc : HasCompactSupport gₙ :=
    HasCompactSupport.intro' (isCompact_closedBall 0 _) isClosed_closedBall
      (fun _ hx => indicator_of_notMem hx g)
  have hsub : Aₙ n ⊆ {x : E d | t < |(k ⋆[ContinuousLinearMap.mul ℝ ℝ] gₙ) x|} := by
    intro x hx
    have hB (y : E d) (hy : y ∈ Function.support k) : x - y ∈ B := by
      apply mem_closedBall_zero_iff.mpr
      exact (norm_sub_le x y).trans
        (add_le_add (mem_ball_zero_iff.mp hx.2).le (mem_closedBall_zero_iff.mp (hR hy)))
    rw [mem_setOf_eq, scalarConvolution_indicator_eq_of_support hB]
    exact hx.1
  have hNorm : (∫ x, |gₙ x|) ≤ ∫ x, |g x| := by
    apply integral_mono hgₙ.abs hg.abs
    intro x
    by_cases hx : x ∈ B
    · simp only [gₙ, indicator_of_mem hx, le_refl]
    · simpa only [gₙ, indicator_of_notMem hx, abs_zero] using abs_nonneg (g x)
  calc
    volume (Aₙ n) ≤ volume {x : E d | t < |(k ⋆[ContinuousLinearMap.mul ℝ ℝ] gₙ) x|} :=
      measure_mono hsub
    _ ≤ ENNReal.ofReal (C * (∫ x, |gₙ x|) / t) := hWeak _ hgₙ hgₙc t ht
    _ ≤ ENNReal.ofReal (C * (∫ x, |g x|) / t) :=
      ENNReal.ofReal_le_ofReal <| div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hNorm hC) ht.le

end SupportingAnalysis
