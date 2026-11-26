module

public import Thesis.MeasureGeometry.CylinderMass
import Mathlib.Topology.UrysohnsLemma

/-! Uniform mass comparison for the moving cylinders at a line tangent. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace Thesis.MeasureGeometry

/-- A one-dimensional linear tangent admits a unit axial direction. -/
theorem exists_unit_axis_of_finrank_one (L : Submodule ℝ Point) (hL : Module.finrank ℝ L = 1) :
    ∃ e : Point, ‖e‖ = 1 ∧ Submodule.span ℝ {e} = L := by
  haveI : Nontrivial L := Module.finrank_pos_iff.1 (hL ▸ Nat.zero_lt_one)
  obtain ⟨u, hu⟩ := exists_ne (0 : L)
  have hu' : (u : Point) ≠ 0 := fun h => hu (Subtype.ext h)
  let e : Point := ‖(u : Point)‖⁻¹ • (u : Point)
  have he_mem : e ∈ L := L.smul_mem _ u.property
  have he_norm : ‖e‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.2 hu')]
  have he_ne : e ≠ 0 := norm_ne_zero_iff.1 (he_norm ▸ one_ne_zero)
  exact ⟨e, he_norm, Submodule.eq_of_le_of_finrank_le
    ((Submodule.span_singleton_le_iff_mem e L).2 he_mem) (by rw [finrank_span_singleton he_ne, hL])⟩

private theorem compactCutoff_mass_lower {K : Set Point} (hK : IsCompact K) {μ : Measure Point}
    [IsFiniteMeasureOnCompacts μ] {f : C(Point, ℝ)} (hc : HasCompactSupport f)
    (h₀ : ∀ x, 0 ≤ f x) (hOne : EqOn f 1 K) :
    (μ K).toReal ≤ ∫ x, f x ∂μ := by
  have hi := f.continuous.integrable_of_hasCompactSupport hc (μ := μ)
  calc
    (μ K).toReal = ∫ x in K, f x ∂μ := by
      rw [setIntegral_congr_fun hK.isClosed.measurableSet hOne]
      change (μ K).toReal = ∫ x in K, (1 : ℝ) ∂μ
      rw [setIntegral_const, smul_eq_mul, mul_one]
      rfl
    _ ≤ _ := setIntegral_le_integral hi (Eventually.of_forall h₀)

private theorem compactCutoff_mass_upper {U K : Set Point} (hU : MeasurableSet U) (hK : IsCompact K)
    (hUK : U ⊆ K) {μ : Measure Point} [IsFiniteMeasureOnCompacts μ] {f : C(Point, ℝ)}
    (hc : HasCompactSupport f) (h₁ : ∀ x, f x ≤ 1) (hZero : EqOn f 0 Uᶜ) :
    (∫ x, f x ∂μ) ≤ (μ U).toReal := by
  have hi := f.continuous.integrable_of_hasCompactSupport hc (μ := μ)
  have hf := (measure_mono hUK).trans_lt (hK.measure_lt_top (μ := μ))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) (fun x hx => hZero hx)]
  calc
    (∫ x in U, f x ∂μ) ≤ ∫ _ in U, (1 : ℝ) ∂μ :=
      setIntegral_mono_on hi.integrableOn (integrableOn_const hf.ne) hU (fun x _ => h₁ x)
    _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_one]; rfl

private theorem weightedLine_openCylinder_mass {e : Point} (he : ‖e‖ = 1) {b r lo hi : ℝ}
    (hb : 0 ≤ b) (hr : 0 < r) (hlh : lo ≤ hi) :
    ((ENNReal.ofReal b • HausdorffOne.restrict ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point))
      (openAxisCylinder e r lo hi)).toReal = b * (hi - lo) := by
  rw [Measure.smul_apply, smul_eq_mul, hausdorffOne_axis_openCylinder he hr,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hb, ENNReal.toReal_ofReal (sub_nonneg.mpr hlh)]

private theorem weightedLine_closedCylinder_mass {e : Point} (he : ‖e‖ = 1) {b r lo hi : ℝ}
    (hb : 0 ≤ b) (hr : 0 ≤ r) (hlh : lo ≤ hi) :
    ((ENNReal.ofReal b • HausdorffOne.restrict ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point))
      (closedAxisCylinder e r lo hi)).toReal = b * (hi - lo) := by
  rw [Measure.smul_apply, smul_eq_mul, hausdorffOne_axis_closedCylinder he hr,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hb, ENNReal.toReal_ofReal (sub_nonneg.mpr hlh)]

private theorem finiteOnCompacts_weightedAxis {e : Point} (he : ‖e‖ = 1) (b : ℝ) :
    IsFiniteMeasureOnCompacts
      (ENNReal.ofReal b • HausdorffOne.restrict ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point)) := by
  have hne : e ≠ 0 := norm_ne_zero_iff.1 (he ▸ one_ne_zero)
  exact flat_line_finite_on_compacts _ (finrank_span_singleton hne) b

/-- Compare all cylinders in the manuscript's compact parameter ranges
against the same tangent line, with the scale limit taken after the
sequence limit. -/
theorem eventually_uniform_movingCylinder_mass
    {ν : ℝ → ℕ → Measure Point} {μ : ℝ → Measure Point}
    (hνfin : ∀ s n, IsFiniteMeasureOnCompacts (ν s n))
    (hSeq : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), SupportingAnalysis.VagueOn univ atTop (ν s) (μ s))
    {e : Point} (he : ‖e‖ = 1) {b : ℝ} (hb : 0 < b)
    (hFlat : SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ)) μ
      (ENNReal.ofReal b • HausdorffOne.restrict ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point)))
    {δ ξ : ℝ} (hδ : 0 < δ) (hξ : 0 < ξ) :
    ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ r ∈ Icc δ (2 * δ), ∀ lo ∈ Icc (-1 : ℝ) (-1 / 2),
        ∀ hi ∈ Icc (1 / 2 : ℝ) 1,
          |((ν s n) (openAxisCylinder e r lo hi)).toReal - b * (hi - lo)| < ξ := by
  let τ := ENNReal.ofReal b • HausdorffOne.restrict ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point)
  letI : IsFiniteMeasureOnCompacts τ := finiteOnCompacts_weightedAxis he b
  let P : Set (ℝ × ℝ) := Icc (-1 : ℝ) (-1 / 2) ×ˢ Icc (1 / 2 : ℝ) 1
  have hP : IsCompact P := isCompact_Icc.prod isCompact_Icc
  let γ := min (1 / 16 : ℝ) (ξ / (48 * b))
  have hγ : 0 < γ := lt_min (by norm_num) (div_pos hξ (mul_pos (by norm_num) hb))
  have hγ₁ : γ ≤ (1 / 16 : ℝ) := min_le_left _ _
  have hγ₂ : 48 * b * γ ≤ ξ := by
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 48) hb)).mp (min_le_right (1 / 16 : ℝ) (ξ / (48 * b)))
    simpa only [γ, mul_comm γ] using h
  let N (p : P) : Set (ℝ × ℝ) := {q | |q.1 - p.val.1| < γ ∧ |q.2 - p.val.2| < γ}
  have hN (p : P) : IsOpen (N p) := by
    exact (isOpen_lt ((continuous_fst.sub continuous_const).abs) continuous_const).inter
      (isOpen_lt ((continuous_snd.sub continuous_const).abs) continuous_const)
  have hPN : P ⊆ ⋃ p, N p := by
    intro p hp
    apply mem_iUnion.mpr
    exact ⟨⟨p, hp⟩, by simp only [N, mem_setOf_eq, sub_self, abs_zero, hγ, and_self]⟩
  obtain ⟨J, hJ⟩ := hP.elim_finite_subcover N hN hPN
  have hOne (p : P) :
      ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        ∀ r ∈ Icc δ (2 * δ), ∀ q ∈ N p,
          |((ν s n) (openAxisCylinder e r q.1 q.2)).toReal - b * (q.2 - q.1)| < ξ := by
    let lo := p.val.1
    let hi := p.val.2
    let A₀ := closedAxisCylinder e (δ / 4) (lo + 2 * γ) (hi - 2 * γ)
    let A₁ := openAxisCylinder e (δ / 2) (lo + γ) (hi - γ)
    let B₀ := closedAxisCylinder e (2 * δ) (lo - γ) (hi + γ)
    let B₁ := openAxisCylinder e (3 * δ) (lo - 2 * γ) (hi + 2 * γ)
    have hA₀ : IsCompact A₀ := isCompact_closedAxisCylinder he _ _ _
    have hB₀ : IsCompact B₀ := isCompact_closedAxisCylinder he _ _ _
    have hA₁ : IsOpen A₁ := isOpen_openAxisCylinder _ _ _ _
    have hB₁ : IsOpen B₁ := isOpen_openAxisCylinder _ _ _ _
    have hA01 : A₀ ⊆ A₁ := closedAxisCylinder_subset_openAxisCylinder _ (by linarith)
      (by linarith) (by linarith)
    have hB01 : B₀ ⊆ B₁ := closedAxisCylinder_subset_openAxisCylinder _ (by linarith)
      (by linarith) (by linarith)
    obtain ⟨f, hf₁, hf₀, hfc, hf⟩ := exists_continuous_one_zero_of_isCompact hA₀ hA₁.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hA01)
    obtain ⟨g, hg₁, hg₀, hgc, hg⟩ := exists_continuous_one_zero_of_isCompact hB₀ hB₁.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hB01)
    have hA : b * (hi - lo - 4 * γ) ≤ ∫ x, f x ∂τ := by
      have h := compactCutoff_mass_lower hA₀ hfc (fun x => (hf x).1) hf₁ (μ := τ)
      have hLo : lo ≤ -1 / 2 := p.property.1.2
      have hHi : 1 / 2 ≤ hi := p.property.2.1
      change (τ (closedAxisCylinder e (δ / 4) (lo + 2 * γ) (hi - 2 * γ))).toReal ≤ _ at h
      rw [weightedLine_closedCylinder_mass he hb.le (by positivity) (by linarith only [hLo, hHi, hγ₁])] at h
      linarith only [h]
    have hB : (∫ x, g x ∂τ) ≤ b * (hi - lo + 4 * γ) := by
      have h := compactCutoff_mass_upper hB₁.measurableSet (isCompact_closedAxisCylinder he _ _ _)
        (openAxisCylinder_subset_closedAxisCylinder _ _ _ _) hgc (fun x => (hg x).2) hg₀ (μ := τ)
      have hLo : lo ≤ -1 / 2 := p.property.1.2
      have hHi : 1 / 2 ≤ hi := p.property.2.1
      change _ ≤ (τ (openAxisCylinder e (3 * δ) (lo - 2 * γ) (hi + 2 * γ))).toReal at h
      rw [weightedLine_openCylinder_mass he hb.le (by positivity) (by linarith only [hLo, hHi, hγ])] at h
      linarith only [h]
    have hfLim := hFlat (f : Point → ℝ) f.continuous hfc (subset_univ _)
    have hgLim := hFlat (g : Point → ℝ) g.continuous hgc (subset_univ _)
    have hfEventually := (tendsto_order.1 hfLim).1 _ (show ∫ x, f x ∂τ - ξ / 4 < ∫ x, f x ∂τ by linarith)
    have hgEventually := (tendsto_order.1 hgLim).2 _ (show ∫ x, g x ∂τ < ∫ x, g x ∂τ + ξ / 4 by linarith)
    filter_upwards [hSeq, hfEventually, hgEventually] with s hS hfS hgS
    have hfLim := hS (f : Point → ℝ) f.continuous hfc (subset_univ _)
    have hgLim := hS (g : Point → ℝ) g.continuous hgc (subset_univ _)
    have hfEventually := (tendsto_order.1 hfLim).1 _ (show ∫ x, f x ∂μ s - ξ / 4 < ∫ x, f x ∂μ s by linarith)
    have hgEventually := (tendsto_order.1 hgLim).2 _ (show ∫ x, g x ∂μ s < ∫ x, g x ∂μ s + ξ / 4 by linarith)
    filter_upwards [hfEventually, hgEventually] with n hfN hgN
    letI := hνfin s n
    intro r hr q hq
    obtain ⟨hql, hqh⟩ := hq
    change |q.1 - lo| < γ at hql
    change |q.2 - hi| < γ at hqh
    let D := openAxisCylinder e r q.1 q.2
    have hDA : A₁ ⊆ D := by
      intro x hx
      refine ⟨hx.1.trans_le ((by linarith : δ / 2 ≤ δ).trans hr.1), ?_, ?_⟩
      · exact (show q.1 < lo + γ by linarith only [(abs_lt.mp hql).2]).trans hx.2.1
      · exact hx.2.2.trans (show hi - γ < q.2 by linarith only [(abs_lt.mp hqh).1])
    have hDB : D ⊆ B₀ := by
      intro x hx
      exact ⟨hx.1.le.trans hr.2, (show lo - γ ≤ q.1 by linarith only [(abs_lt.mp hql).1]).trans hx.2.1.le,
        hx.2.2.le.trans (show q.2 ≤ hi + γ by linarith only [(abs_lt.mp hqh).2])⟩
    have hDfin : ((ν s n) D) ≠ ⊤ := ((measure_mono hDB).trans_lt (hB₀.measure_lt_top (μ := ν s n))).ne
    have hMass₀ : (∫ x, f x ∂ν s n) ≤ ((ν s n) D).toReal :=
      (compactCutoff_mass_upper hA₁.measurableSet (isCompact_closedAxisCylinder he _ _ _)
        (openAxisCylinder_subset_closedAxisCylinder _ _ _ _) hfc (fun x => (hf x).2) hf₀).trans
        (ENNReal.toReal_mono hDfin (measure_mono hDA))
    have hMass₁ : ((ν s n) D).toReal ≤ ∫ x, g x ∂ν s n := by
      exact (ENNReal.toReal_mono (hB₀.measure_lt_top (μ := ν s n)).ne (measure_mono hDB)).trans
        (compactCutoff_mass_lower hB₀ hgc (fun x => (hg x).1) hg₁)
    change |((ν s n) D).toReal - b * (q.2 - q.1)| < ξ
    apply abs_lt.mpr
    have hH₀ := mul_le_mul_of_nonneg_left
      (show hi - lo - 2 * γ ≤ q.2 - q.1 by linarith only [(abs_lt.mp hql).2, (abs_lt.mp hqh).1]) hb.le
    have hH₁ := mul_le_mul_of_nonneg_left
      (show q.2 - q.1 ≤ hi - lo + 2 * γ by linarith only [(abs_lt.mp hql).1, (abs_lt.mp hqh).2]) hb.le
    constructor <;> linarith only [hA, hB, hfS, hgS, hfN, hgN, hH₀, hH₁, hMass₀, hMass₁, hγ₂, hξ]
  have hAll := (eventually_all_finset J).2 (fun p _ => hOne p)
  filter_upwards [hAll] with s hs
  have hAll := (eventually_all_finset J).2 hs
  filter_upwards [hAll] with n hn
  intro r hr lo hlo hi hhi
  obtain ⟨p, hp, hMem⟩ := mem_iUnion₂.mp (hJ (show (lo, hi) ∈ P from ⟨hlo, hhi⟩))
  exact hn p hp r hr (lo, hi) hMem

/-- Ambient tests on the original weak-* sequence give vague tests after
every fixed positive blow-up. -/
theorem vagueOn_oneBlowup_of_weakStarOnClosure {Ω : Set Point}
    {ν : ℕ → Measure Point} {μ : Measure Point}
    (hν : ∀ n, ν n (closure Ω)ᶜ = 0) (hμ : μ (closure Ω)ᶜ = 0)
    (hWeak : WeakStarOnClosure Ω ν μ) (x : Point) {s : ℝ} (hs : 0 < s) :
    SupportingAnalysis.VagueOn univ atTop
      (fun n => SupportingAnalysis.blownUpMeasure (d := 1) x s (ν n))
      (SupportingAnalysis.blownUpMeasure (d := 1) x s μ) := by
  intro φ hφ _ _
  let f (y : Point) := φ (s⁻¹ • (y - x))
  have hAffine : Continuous (fun y : Point => s⁻¹ • (y - x)) := by fun_prop
  have hf : Continuous f := hφ.comp hAffine
  let g : C(closure Ω, ℝ) := ⟨fun y => f y, hf.comp continuous_subtype_val⟩
  have hEq (m : Measure Point) (hm : m (closure Ω)ᶜ = 0) :
      (∫ y, f y ∂m) = ∫ z, g z ∂m.comap ((↑) : closure Ω → Point) := by
    let j : closure Ω → Point := Subtype.val
    have hj : MeasurableEmbedding j := MeasurableEmbedding.subtype_coe isClosed_closure.measurableSet
    have hj' : Measure.map j (Measure.comap j m) = m := by
      rw [map_comap_subtype_coe isClosed_closure.measurableSet]
      apply Measure.restrict_eq_self_of_ae_mem
      rw [ae_iff]
      exact hm
    change (∫ y, f y ∂m) = ∫ z, f (j z) ∂m.comap j
    rw [← hj.integral_map, hj']
  have hv := (hWeak g).const_mul s⁻¹
  simp only [← hEq _ hμ] at hv
  have hn (n : ℕ) : (∫ y, φ y ∂SupportingAnalysis.blownUpMeasure (d := 1) x s (ν n)) =
      s⁻¹ * ∫ z, g z ∂(ν n).comap ((↑) : closure Ω → Point) := by
    rw [integral_oneBlowup x hs hφ]
    exact congrArg (s⁻¹ * ·) (hEq _ (hν n))
  simp_rw [hn, integral_oneBlowup x hs hφ]
  exact hv

/-- Evaluation of the blow-up on a measurable set uses the exact dilated
physical set and the factor one over the scale. -/
theorem oneBlowup_toReal_apply {μ : Measure Point} (x : Point) {s : ℝ} (hs : 0 < s)
    {A : Set Point} (hA : MeasurableSet A) :
    ((SupportingAnalysis.blownUpMeasure (d := 1) x s μ) A).toReal =
      (μ ((fun z : Point => x + s • z) '' A)).toReal / s := by
  let f (y : Point) := s⁻¹ • (y - x)
  let g (z : Point) := x + s • z
  have hf : Measurable f := by dsimp only [f]; fun_prop
  have hg (z : Point) : f (g z) = z := by
    simp [f, g, smul_smul, inv_mul_cancel₀ hs.ne']
  have hf' (y : Point) : g (f y) = y := by
    simp [f, g, smul_smul, mul_inv_cancel₀ hs.ne', add_sub_cancel]
  have hP : f ⁻¹' A = g '' A := by
    ext y
    constructor
    · intro hy
      exact ⟨f y, hy, hf' y⟩
    · rintro ⟨z, hz, rfl⟩
      show f (g z) ∈ A
      rwa [hg]
  rw [SupportingAnalysis.blownUpMeasure, Measure.smul_apply, smul_eq_mul, Nat.cast_one,
    zpow_neg, zpow_one, Measure.map_apply hf hA, hP,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr hs.le), div_eq_mul_inv, mul_comm]

/-- Uniform moving-cylinder mass for the original physical energy measures
and their actual flat tangent. -/
theorem eventually_uniform_weakStar_movingCylinder_mass
    {Ω : Set Point} {ν : ℕ → Measure Point} {μ : Measure Point} {x e : Point}
    (hνfin : ∀ n, IsFiniteMeasure (ν n))
    (hν : ∀ n, ν n (closure Ω)ᶜ = 0) (hμ : μ (closure Ω)ᶜ = 0)
    (hWeak : WeakStarOnClosure Ω ν μ)
    (he : ‖e‖ = 1) {b : ℝ} (hb : 0 < b)
    (hFlat : SupportingAnalysis.VagueOn univ (𝓝[>] (0 : ℝ))
      (fun s => SupportingAnalysis.blownUpMeasure (d := 1) x s μ)
      (ENNReal.ofReal b • HausdorffOne.restrict ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point)))
    {δ ξ : ℝ} (hδ : 0 < δ) (hξ : 0 < ξ) :
    ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ r ∈ Icc δ (2 * δ), ∀ lo ∈ Icc (-1 : ℝ) (-1 / 2),
        ∀ hi ∈ Icc (1 / 2 : ℝ) 1,
        |(ν n ((fun z : Point => x + s • z) '' openAxisCylinder e r lo hi)).toReal / s -
          b * (hi - lo)| < ξ := by
  let v (s : ℝ) (n : ℕ) := SupportingAnalysis.blownUpMeasure (d := 1) x s (ν n)
  have hF (s : ℝ) (n : ℕ) : IsFiniteMeasureOnCompacts (v s n) := by
    letI := hνfin n
    letI := SupportingAnalysis.blownUpMeasure_isFiniteMeasure (d := 1) x s (ν n)
    infer_instance
  have hS : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), SupportingAnalysis.VagueOn univ atTop (v s)
      (SupportingAnalysis.blownUpMeasure (d := 1) x s μ) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact vagueOn_oneBlowup_of_weakStarOnClosure hν hμ hWeak x hs
  filter_upwards [eventually_uniform_movingCylinder_mass hF hS he hb hFlat hδ hξ,
    self_mem_nhdsWithin] with s hs hPos
  filter_upwards [hs] with n hn r hr lo hlo hi hhi
  rw [← oneBlowup_toReal_apply x hPos (isOpen_openAxisCylinder e r lo hi).measurableSet]
  exact hn r hr lo hlo hi hhi

/-- A closed cylindrical ring excludes the axial line by its positive
inner transverse radius. -/
def closedAxisAnnularCylinder (e : Point) (r₀ r₁ lo hi : ℝ) : Set Point :=
  closedAxisCylinder e r₁ lo hi ∩ {x | r₀ ≤ cylinderTransverseRadius e x}

theorem isCompact_closedAxisAnnularCylinder {e : Point} (he : ‖e‖ = 1) (r₀ r₁ lo hi : ℝ) :
    IsCompact (closedAxisAnnularCylinder e r₀ r₁ lo hi) :=
  (isCompact_closedAxisCylinder he r₁ lo hi).inter_right
    (isClosed_le continuous_const (continuous_cylinderTransverseRadius e))

/-- A compact annular cylinder away from the axis has vanishing rescaled
mass at a weighted line tangent. -/
theorem eventually_small_annularCylinder_at_line {ι : Type} {l : Filter ι}
    {ν : ι → Measure Point} (hfin : ∀ i, IsFiniteMeasureOnCompacts (ν i))
    {e : Point} (he : ‖e‖ = 1) {b : ℝ}
    (hFlat : SupportingAnalysis.VagueOn univ l ν
      (ENNReal.ofReal b • HausdorffOne.restrict ((Submodule.span ℝ {e} : Submodule ℝ Point) : Set Point)))
    {r₀ r₁ lo hi ξ : ℝ} (h₀ : 0 < r₀) (hξ : 0 < ξ) :
    ∀ᶠ i in l, ((ν i) (closedAxisAnnularCylinder e r₀ r₁ lo hi)).toReal < ξ := by
  let L : Set Point := (Submodule.span ℝ {e} : Submodule ℝ Point)
  let τ := ENNReal.ofReal b • HausdorffOne.restrict L
  let A := closedAxisAnnularCylinder e r₀ r₁ lo hi
  have hA : IsCompact A := isCompact_closedAxisAnnularCylinder he _ _ _ _
  have hL : IsClosed L := Submodule.closed_of_finiteDimensional _
  have hD : Disjoint A L := by
    apply disjoint_left.mpr
    intro y hy hyL
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hyL
    have h : r₀ ≤ cylinderTransverseRadius e (s • e) := hy.2
    rw [cylinderTransverseRadius_smul_unit he] at h
    exact h₀.not_ge h
  obtain ⟨f, hf₁, hf₀, hfc, hf⟩ := exists_continuous_one_zero_of_isCompact hA hL hD
  have hZero : (∫ y, f y ∂τ) = 0 := by
    dsimp only [τ]
    rw [integral_smul_measure, setIntegral_congr_fun hL.measurableSet hf₀]
    simp
  have hLim := hFlat (f : Point → ℝ) f.continuous hfc (subset_univ _)
  rw [show (∫ y, f y ∂(ENNReal.ofReal b • HausdorffOne.restrict L)) = 0 from hZero] at hLim
  filter_upwards [(tendsto_order.1 hLim).2 ξ hξ] with i hi
  letI := hfin i
  exact (compactCutoff_mass_lower hA hfc (fun y => (hf y).1) hf₁).trans_lt hi

end Thesis.MeasureGeometry
