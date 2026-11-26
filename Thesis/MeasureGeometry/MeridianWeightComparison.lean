module

public import Thesis.MeasureGeometry.MeridianCylinderMass
public import Thesis.MeasureGeometry.CylinderUpperLimit

/-! The constant edge weight recovered from the actual meridian comparisons. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace Thesis.MeasureGeometry

/-- A comparison on arbitrarily small physical cylinders with one fixed
meridian cost identifies the weight of the actual line. The end-height
subsequence is local to the comparison and leaves the ambient weak limit
and its actual representatives unchanged. -/
theorem edge_weight_eq_meridian_cost_of_comparisons
    {ν : ℕ → FiniteMeasure Point} {μ : FiniteMeasure Point}
    (hWeak : Tendsto ν atTop (𝓝 μ))
    {V : Set Point} (x e : Point) (he : ‖e‖ = 1) {s b k C : ℝ}
    (hs : 0 < s) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hLocal : (μ : Measure Point).restrict V = (ENNReal.ofReal b • HausdorffOne.restrict
      ((fun y : Point => x + y) '' ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point))).restrict V)
    (hComparison : ∀ R > 0, ∃ r ∈ Ioo 0 R,
      translatedClosedAxisCylinder x e r (-(2*s)) (2*s) ⊆ V ∧
        ∀ ξ > 0, ∀ᶠ n : ℕ in atTop,
          ∃ lo ∈ Ioo (-s) (-(s/2)), ∃ hi ∈ Ioo (s/2) s,
            k - ξ ≤ ((ν n : Measure Point) (translatedAxisCylinder x e r lo hi)).toReal / (hi-lo) ∧
            ((ν n : Measure Point) (translatedAxisCylinder x e r lo hi)).toReal / (hi-lo) ≤
              k + C * (r/s) + ξ) :
    b = k := by
  classical
  have hClose (η : ℝ) (hη : 0 < η) : |b-k| ≤ η := by
    let R := η * s / (4*(C+1))
    have hR : 0 < R := div_pos (mul_pos hη hs) (mul_pos (by norm_num) (by linarith only [hC]))
    obtain ⟨r, hr, hRsub, hE⟩ := hComparison R hR
    have hBound : C * (r/s) ≤ η/2 := by
      have hh := (lt_div_iff₀ (show 0 < 4*(C+1) by linarith only [hC])).mp hr.2
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hs).mpr
      nlinarith only [hh, hr.1, hη, hs]
    let ξ := η/4
    have hξ : 0 < ξ := div_pos hη (by norm_num)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hE ξ hξ)
    let Cmp (n : ℕ) (p : ℝ × ℝ) :=
      k-ξ ≤ ((ν n : Measure Point) (translatedAxisCylinder x e r p.1 p.2)).toReal / (p.2-p.1) ∧
        ((ν n : Measure Point) (translatedAxisCylinder x e r p.1 p.2)).toReal / (p.2-p.1) ≤ k+C*(r/s)+ξ
    let H : Set (ℝ × ℝ) := Icc (-s) (-(s/2)) ×ˢ Icc (s/2) s
    have hCh (n : ℕ) : ∃ p ∈ H, N ≤ n → Cmp n p := by
      by_cases hn : N ≤ n
      · obtain ⟨lo, hlo, hi, hhi, hL, hU⟩ := hN n hn
        exact ⟨(lo,hi), ⟨Ioo_subset_Icc_self hlo, Ioo_subset_Icc_self hhi⟩, fun _ => ⟨hL,hU⟩⟩
      · have hLo : (-s) ∈ Icc (-s) (-(s/2)) := ⟨le_rfl, by linarith only [hs]⟩
        have hHi : s ∈ Icc (s/2) s := ⟨by linarith only [hs], le_rfl⟩
        exact ⟨(-s,s),⟨hLo,hHi⟩, fun he => (hn he).elim⟩
    choose p hp hP using hCh
    have hH : IsCompact H := isCompact_Icc.prod isCompact_Icc
    obtain ⟨y, hy, σ, hσ, hσp⟩ := hH.tendsto_subseq hp
    have hν_sub : Tendsto (ν ∘ σ) atTop (𝓝 μ) := hWeak.comp hσ.tendsto_atTop
    have hlo : Tendsto (fun n => (p (σ n)).1) atTop (𝓝 y.1) := continuous_fst.continuousAt.tendsto.comp hσp
    have hhi : Tendsto (fun n => (p (σ n)).2) atTop (𝓝 y.2) := continuous_snd.continuousAt.tendsto.comp hσp
    have hMass := tendsto_moving_heightCylinder_mass_of_local_weight hν_sub x e he hb hr.1 hs
      hLocal hRsub hlo hhi hy.1 hy.2
    have hCmp : ∀ᶠ n in atTop, Cmp (σ n) (p (σ n)) :=
      (tendsto_atTop.mp hσ.tendsto_atTop N).mono (fun n hn => hP (σ n) hn)
    have hL : k-ξ ≤ b := le_of_tendsto_of_tendsto tendsto_const_nhds hMass (hCmp.mono fun n hn => hn.1)
    have hU : b ≤ k+C*(r/s)+ξ := le_of_tendsto hMass (hCmp.mono fun n hn => hn.2)
    dsimp only [ξ] at hL hU
    exact abs_le.mpr ⟨by linarith only [hL,hη], by linarith only [hU,hBound,hη]⟩
  have h := le_of_forall_pos_le_add (a := |b-k|) (b := 0) fun η hη => by simpa only [zero_add] using hClose η hη
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

end Thesis.MeasureGeometry
