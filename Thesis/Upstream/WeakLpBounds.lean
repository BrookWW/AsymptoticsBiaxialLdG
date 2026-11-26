module

public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! A higher integral norm bound persists under weak convergence in L². -/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace Thesis

/-- A uniform real `L^p` norm bound passes to an almost everywhere limit. -/
theorem eLpNorm_le_of_ae_tendsto_of_uniform_norm {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] {p : ℝ} (hp : 0 < p) {g : ℕ → X → E} {f : X → E} {M : ℝ≥0∞}
    (hg : ∀ n, AEStronglyMeasurable (g n) μ)
    (hLim : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (f x)))
    (hBound : ∀ n, eLpNorm (g n) (ENNReal.ofReal p) μ ≤ M) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ M := by
  have hp₀ : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le,one_div] at hBound ⊢
  apply (ENNReal.rpow_inv_le_iff hp).2
  have hEq : (fun x => ‖f x‖ₑ^p) =ᵐ[μ] fun x => atTop.liminf (fun n => ‖g n x‖ₑ^p) := by
    filter_upwards [hLim] with x hx
    exact ((ENNReal.continuous_rpow_const.comp continuous_enorm).continuousAt.tendsto.comp hx).liminf_eq.symm
  rw [lintegral_congr_ae hEq]
  refine (lintegral_liminf_le' (fun n => (hg n).enorm.pow_const _)).trans ?_
  exact liminf_le_of_frequently_le' (Frequently.of_forall fun n => (ENNReal.rpow_inv_le_iff hp).1 (hBound n))

private theorem convex_eLpNorm_sublevel_in_L2 {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (C : ℝ≥0∞) :
    Convex ℝ {f : Lp E 2 μ | eLpNorm f p μ ≤ C} := by
  intro x hx y hy a b ha hb hab
  change eLpNorm ((a • x+b • y : Lp E 2 μ) : X → E) p μ ≤ C
  have hx' : eLpNorm (x : X → E) p μ ≤ C := hx
  have hy' : eLpNorm (y : X → E) p μ ≤ C := hy
  have hEq : ((a • x+b • y : Lp E 2 μ) : X → E) =ᵐ[μ]
      (a • (x : X → E) + b • (y : X → E)) :=
    (Lp.coeFn_add (a • x) (b • y)).trans ((Lp.coeFn_smul a x).add (Lp.coeFn_smul b y))
  rw [eLpNorm_congr_ae hEq]
  refine (eLpNorm_add_le ((Lp.memLp x).1.const_smul a) ((Lp.memLp y).1.const_smul b) hp).trans ?_
  rw [eLpNorm_const_smul,eLpNorm_const_smul,← ofReal_norm,← ofReal_norm,
    Real.norm_of_nonneg ha,Real.norm_of_nonneg hb]
  calc
    _ ≤ ENNReal.ofReal a * C + ENNReal.ofReal b * C :=
      add_le_add (mul_le_mul_right hx' _) (mul_le_mul_right hy' _)
    _ = C := by rw [← add_mul,← ENNReal.ofReal_add ha hb,hab,ENNReal.ofReal_one,one_mul]

private theorem isClosed_eLpNorm_sublevel_in_L2 {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {p : ℝ} (hp : 0 < p) (C : ℝ≥0∞) :
    IsClosed {f : Lp E 2 μ | eLpNorm f (ENNReal.ofReal p) μ ≤ C} := by
  apply isSeqClosed_iff_isClosed.mp
  intro f v hv hLim
  obtain ⟨κ,_,hAe⟩ := (tendstoInMeasure_of_tendsto_Lp hLim).exists_seq_tendsto_ae
  exact eLpNorm_le_of_ae_tendsto_of_uniform_norm hp
    (fun n => (Lp.memLp (f (κ n))).1) hAe (fun n => hv (κ n))

/-- An (L^p) bound on a sequence passes to its weak (L^2) limit for
every finite real exponent (pgeq 1). -/
theorem eLpNorm_le_of_weak_L2_limit {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} {p : ℝ} (hp : 1 ≤ p) {C : ℝ≥0∞}
    (f : ℕ → Lp E 2 μ) (v : Lp E 2 μ)
    (h : ∀ z : Lp E 2 μ, Tendsto (fun n => inner ℝ (f n) z) atTop (𝓝 (inner ℝ v z)))
    (hBound : ∀ n, eLpNorm (f n) (ENNReal.ofReal p) μ ≤ C) :
    eLpNorm v (ENNReal.ofReal p) μ ≤ C := by
  let K := {z : Lp E 2 μ | eLpNorm z (ENNReal.ofReal p) μ ≤ C}
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hK : Convex ℝ K := convex_eLpNorm_sublevel_in_L2 hp' C
  have hClosed : IsClosed K := isClosed_eLpNorm_sublevel_in_L2 (zero_lt_one.trans_le hp) C
  change v ∈ K
  by_contra hV
  obtain ⟨L,a,hL,hLa⟩ := geometric_hahn_banach_closed_point hK hClosed hV
  let z := (InnerProductSpace.toDual ℝ (Lp E 2 μ)).symm L
  have he (y : Lp E 2 μ) : inner ℝ y z = L y :=
    (real_inner_comm z y).trans InnerProductSpace.toDual_symm_apply
  have hT : Tendsto (fun n => L (f n)) atTop (𝓝 (L v)) := by
    simpa only [he] using h z
  have hLe : L v ≤ a :=
    le_of_tendsto hT (Eventually.of_forall fun n => (hL (f n) (hBound n)).le)
  exact (not_lt_of_ge hLe) hLa

end Thesis
