module

public import Thesis.Upstream.AmbientWeakPartialAlgebra
public import Thesis.Upstream.LpTranslationAverages
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Prod
import HarmonicMaps.Analysis.L2TranslationContinuity

/-! The normalized finite difference in a coordinate is the segment average of its weak derivative. -/

public section

noncomputable section

open Filter Function HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace Thesis

private abbrev unitSegmentMeasure : Measure ℝ := volume.restrict (Ioc 0 1)

private instance unitSegmentMeasureProbability : IsProbabilityMeasure unitSegmentMeasure :=
  ⟨by simp [unitSegmentMeasure,Real.volume_Ioc]⟩

private theorem scalarDifferenceQuotient_eq_average {φ : Point → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (i : Fin 3) {h : ℝ} (hh : h ≠ 0) (x : Point) :
    ambientDifferenceQuotient i h φ x = ∫ t, coordDeriv i φ (x+t • (h • axis i)) ∂unitSegmentMeasure := by
  let z := h • axis i
  have hT := map_add_eq_sum_add_integral_iteratedFDeriv (x := x) (y := z) (n := 0)
    (fun t _ => (hφ.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt (x := x+t • z))
  have hE : φ (x+z) = φ x + h * ∫ t, coordDeriv i φ (x+t • z) ∂unitSegmentMeasure := by
    simpa [unitSegmentMeasure,iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,z,coordDeriv,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),integral_const_mul,smul_eq_mul] using hT
  change h⁻¹*(φ (x+z)-φ x) = _
  rw [hE,add_sub_cancel_left,← mul_assoc,inv_mul_cancel₀ hh,one_mul]

private theorem coordDeriv_comp_sub_translation (φ : Point → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (i : Fin 3) (z x : Point) :
    coordDeriv i (fun y => φ (y-z)) x = coordDeriv i φ (x-z) := by
  have hA := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const z)
  have hP := ((hφ.differentiable (by simp) (x-z)).hasFDerivAt.comp x hA).fderiv
  change fderiv ℝ (fun y : Point => φ (y-z)) x = _ at hP
  change fderiv ℝ (fun y => φ (y-z)) x (axis i) = fderiv ℝ φ (x-z) (axis i)
  rw [hP]
  rfl

private theorem integrable_test_smul_whole {q : ℕ} {u : Point → Ambient q} (hu : Integrable u)
    {φ : Point → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => φ x • u x) :=
  hu.smul_of_top_right (hφ.memLp_top_of_hasCompactSupport hc _)

private theorem integrable_prod_translated_test_pair {q : ℕ} {u : Point → Ambient q}
    (hM : StronglyMeasurable u) (hu : Integrable u) {φ : Point → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (z : Point) :
    Integrable (Function.uncurry fun (t : ℝ) (x : Point) => φ (x-t • z) • u x)
      (unitSegmentMeasure.prod (volume : Measure Point)) := by
  obtain ⟨C,hC⟩ := hφ.bounded_above_of_compact_support hc
  have hP : Continuous (fun w : ℝ × Point => φ (w.2-w.1 • z)) := hφ.comp (by fun_prop)
  refine ((hu.norm.const_mul C).comp_snd unitSegmentMeasure).mono' ?_ ?_
  · exact (hP.stronglyMeasurable.smul (hM.comp_measurable measurable_snd)).aestronglyMeasurable
  · apply Eventually.of_forall
    intro w
    change ‖φ (w.2-w.1 • z) • u w.2‖ ≤ C*‖u w.2‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

private theorem integrable_prod_shift_of_integrable {q : ℕ} {E : Point → Ambient q}
    (hE : StronglyMeasurable E) (hI : Integrable E) (z : Point) :
    Integrable (Function.uncurry fun (t : ℝ) (x : Point) => E (x+t • z))
      (unitSegmentMeasure.prod (volume : Measure Point)) := by
  let F (t : ℝ) (x : Point) := E (x+t • z)
  have hP : StronglyMeasurable (Function.uncurry F) := hE.comp_measurable (by
    change Measurable (fun w : ℝ × Point => w.2+w.1 • z)
    fun_prop)
  apply (integrable_prod_iff hP.aestronglyMeasurable).2
  have hPt (t : ℝ) : Integrable (F t) (volume : Measure Point) :=
    hI.comp_add_right (t • z)
  refine ⟨Eventually.of_forall hPt,?_⟩
  have he (t : ℝ) : (∫ x, ‖F t x‖) = ∫ x, ‖E x‖ :=
    integral_add_right_eq_self (fun y => ‖E y‖) (t • z)
  change Integrable (fun t => ∫ x, ‖F t x‖) unitSegmentMeasure
  simp only [he]
  exact integrable_const _

private theorem integral_test_smul_ambientDifferenceQuotient {q : ℕ}
    {f : Point → Ambient q} (hf : Integrable f) {φ : Point → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (i : Fin 3) (h : ℝ) :
    (∫ x, φ x • ambientDifferenceQuotient i h f x) =
      -(∫ x, ambientDifferenceQuotient i (-h) φ x • f x) := by
  let z := h • axis i
  have hF : Integrable (fun x => f (x+z)) := hf.comp_add_right z
  have hTest : Continuous (fun x : Point => φ (x-z)) := hφ.comp (by fun_prop)
  have hTestC : HasCompactSupport (fun x : Point => φ (x-z)) := hc.comp_homeomorph (Homeomorph.addRight (-z))
  have hI₁ := integrable_test_smul_whole hF hφ hc
  have hI₂ := integrable_test_smul_whole hf hφ hc
  have hI₃ := integrable_test_smul_whole hf hTest hTestC
  have he : (∫ x, φ x • f (x+z)) = ∫ x, φ (x-z) • f x := by
    simpa only [add_sub_cancel_right] using
      (integral_add_right_eq_self (fun x : Point => φ (x-z) • f x) z)
  have hL (x : Point) : φ x • ambientDifferenceQuotient i h f x =
      h⁻¹ • (φ x • f (x+z)-φ x • f x) := by
    rw [ambientDifferenceQuotient,smul_comm,smul_sub]
    rfl
  have hR (x : Point) : ambientDifferenceQuotient i (-h) φ x • f x =
      (-h)⁻¹ • (φ (x-z) • f x-φ x • f x) := by
    rw [ambientDifferenceQuotient,smul_assoc,sub_smul]
    change (-h)⁻¹ • (φ (x+(-h) • axis i) • f x-φ x • f x) = _
    rw [neg_smul,← sub_eq_add_neg]
  simp_rw [hL,hR]
  rw [integral_smul,integral_smul,integral_sub hI₁ hI₂,integral_sub hI₃ hI₂,he,inv_neg,neg_smul,neg_neg]

/-- The derivative average along the segment used by a normalized finite difference. -/
@[expose] def coordinateSegmentAverage {q : ℕ} (i : Fin 3) (h : ℝ)
    (E : Point → Ambient q) (x : Point) : Ambient q :=
  ∫ t in Ioc (0:ℝ) 1, E (x+t • (h • axis i))

private theorem coordinateSegmentAverage_congr_ae {q : ℕ}
    {E E' : Point → Ambient q} (hE : E =ᵐ[(volume : Measure Point)] E') (i : Fin 3) (h : ℝ) :
    coordinateSegmentAverage i h E =ᵐ[(volume : Measure Point)] coordinateSegmentAverage i h E' := by
  let z := h • axis i
  let S (t : ℝ) (x : Point) := x+t • z
  have hS : Measurable (Function.uncurry S) := by
    change Measurable (fun w : ℝ × Point => w.2+w.1 • z)
    fun_prop
  have hSkew := (MeasurePreserving.id unitSegmentMeasure).skew_product hS
    (Eventually.of_forall fun t => (measurePreserving_add_right (volume : Measure Point) (t • z)).map_eq)
  have hMp : MeasurePreserving (fun w : Point × ℝ => S w.2 w.1)
      ((volume : Measure Point).prod unitSegmentMeasure) volume :=
    measurePreserving_snd.comp (hSkew.comp Measure.measurePreserving_swap)
  have h := Measure.ae_ae_of_ae_prod (hMp.quasiMeasurePreserving.ae hE)
  exact h.mono fun _ he => integral_congr_ae he

private theorem coordinateSegmentAverage_integral_test {q : ℕ} {u E : Point → Ambient q}
    (huM : StronglyMeasurable u) (hEM : StronglyMeasurable E) (hu : Integrable u) (hE : Integrable E)
    {i : Fin 3} (hWeak : IsWeakAmbientCoordinatePartial univ i u E) {h : ℝ} (hh : h ≠ 0)
    {φ : Point → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x • ambientDifferenceQuotient i h u x) = ∫ x, φ x • coordinateSegmentAverage i h E x := by
  let z := h • axis i
  let φ₁ := coordDeriv i φ
  have hD : Continuous φ₁ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDC : HasCompactSupport φ₁ := hc.fderiv_apply ℝ (axis i)
  have hF1 := integrable_prod_translated_test_pair huM hu hD hDC z
  have hF2 := integrable_prod_translated_test_pair hEM hE hφ.continuous hc z
  have hF3 := integrable_prod_shift_of_integrable hEM hE z
  have hF4 : Integrable (Function.uncurry fun (t : ℝ) (x : Point) => φ x • E (x+t • z))
      (unitSegmentMeasure.prod (volume : Measure Point)) := by
    obtain ⟨C,hC⟩ := hφ.continuous.bounded_above_of_compact_support hc
    have hTop : MemLp (fun w : ℝ × Point => φ w.2) ∞ (unitSegmentMeasure.prod (volume : Measure Point)) :=
      memLp_top_of_bound (hφ.continuous.stronglyMeasurable.comp_measurable measurable_snd).aestronglyMeasurable
        C (Eventually.of_forall fun w => hC w.2)
    exact hF3.smul_of_top_right hTop
  have hPair (t : ℝ) : (∫ x, φ₁ (x-t • z) • u x) = -(∫ x, φ (x-t • z) • E x) := by
    let φt (x : Point) := φ (x-t • z)
    have hφt : ContDiff ℝ ∞ φt := hφ.comp (contDiff_id.sub contDiff_const)
    have hcφt : HasCompactSupport φt := hc.comp_homeomorph (Homeomorph.addRight (-(t • z)))
    have h := hWeak φt hφt hcφt (subset_univ _)
    simp only [Measure.restrict_univ] at h
    change (∫ x, coordDeriv i φt x • u x) = -(∫ x, φt x • E x) at h
    simpa only [φt,coordDeriv_comp_sub_translation φ hφ i] using h
  have hSeg (x : Point) : ambientDifferenceQuotient i (-h) φ x =
      ∫ t, φ₁ (x-t • z) ∂unitSegmentMeasure := by
    simpa only [φ₁,z,neg_smul,smul_neg,sub_eq_add_neg] using
      scalarDifferenceQuotient_eq_average hφ i (neg_ne_zero.mpr hh) x
  calc
    _ = -(∫ x, ambientDifferenceQuotient i (-h) φ x • u x) :=
      integral_test_smul_ambientDifferenceQuotient hu hφ.continuous hc i h
    _ = -(∫ x, ∫ t, φ₁ (x-t • z) • u x ∂unitSegmentMeasure) := by
      simp_rw [hSeg,integral_smul_const]
    _ = -(∫ t, (∫ x, φ₁ (x-t • z) • u x) ∂unitSegmentMeasure) :=
      congrArg Neg.neg (integral_integral_swap hF1).symm
    _ = ∫ t, (∫ x, φ (x-t • z) • E x) ∂unitSegmentMeasure := by
      rw [← integral_neg]
      simp only [hPair,neg_neg]
    _ = ∫ t, (∫ x, φ x • E (x+t • z)) ∂unitSegmentMeasure := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro t
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self (fun x => φ (x-t • z) • E x) (t • z)).symm
    _ = ∫ x, ∫ t, φ x • E (x+t • z) ∂unitSegmentMeasure := integral_integral_swap hF4
    _ = _ := by simp only [coordinateSegmentAverage,z,integral_smul]

private theorem coordinateSegmentAverage_eq_differenceQuotient_of_integrable {q : ℕ}
    {u E : Point → Ambient q} (huM : StronglyMeasurable u) (hEM : StronglyMeasurable E)
    (hu : Integrable u) (hE : Integrable E) {i : Fin 3} (hWeak : IsWeakAmbientCoordinatePartial univ i u E)
    {h : ℝ} (hh : h ≠ 0) :
    ambientDifferenceQuotient i h u =ᵐ[(volume : Measure Point)] coordinateSegmentAverage i h E := by
  let D := ambientDifferenceQuotient i h u
  let A := coordinateSegmentAverage i h E
  have hDL : Integrable D := memLp_one_iff_integrable.1
    (memLp_ambientDifferenceQuotient (memLp_one_iff_integrable.2 hu) i h)
  have hAL : Integrable A := by
    apply memLp_one_iff_integrable.1
    have hEM' : MemLp E (ENNReal.ofReal (1:ℝ)) (volume : Measure Point) := by
      rw [ENNReal.ofReal_one]
      exact memLp_one_iff_integrable.2 hE
    change MemLp (fun x => ∫ t, E (x+t • (h • axis i)) ∂unitSegmentMeasure) 1 (volume : Measure Point)
    simpa only [ENNReal.ofReal_one] using
      (memLp_translationAverage_le unitSegmentMeasure (θ := fun t : ℝ => t • (h • axis i))
        (by fun_prop) hEM (p := 1) le_rfl hEM').1
  have hLoc : LocallyIntegrableOn (D-A) univ (volume : Measure Point) :=
    (hDL.sub hAL).locallyIntegrable.locallyIntegrableOn _
  have h0 : ∀ᵐ x ∂(volume : Measure Point), x ∈ (univ : Set Point) → (D-A) x=0 := by
    apply isOpen_univ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hLoc
    intro φ hφ hc _
    have hI₁ := integrable_test_smul_whole hDL hφ.continuous hc
    have hI₂ := integrable_test_smul_whole hAL hφ.continuous hc
    simp_rw [Pi.sub_apply,smul_sub]
    rw [integral_sub hI₁ hI₂,coordinateSegmentAverage_integral_test huM hEM hu hE hWeak hh hφ hc,sub_self]
  exact h0.mono fun x hx => sub_eq_zero.mp (hx (mem_univ x))

private theorem memLp_weakCoordinatePartial_integrable_of_compact {q : ℕ}
    {u E : Point → Ambient q} (hc : HasCompactSupport u) (hE : MemLp E 2 (volume : Measure Point))
    {i : Fin 3} (hWeak : IsWeakAmbientCoordinatePartial univ i u E) : Integrable E := by
  let K := tsupport u
  let V := Kᶜ
  have hV : IsOpen V := (isClosed_tsupport u).isOpen_compl
  have hLoc : LocallyIntegrableOn E V (volume : Measure Point) := by
    apply (locallyIntegrableOn_iff hV.isLocallyClosed).2
    intro A _ hA
    letI : IsFiniteMeasure ((volume : Measure Point).restrict A) := isFiniteMeasure_restrict.2 hA.measure_lt_top.ne
    exact (hE.mono_measure Measure.restrict_le_self).integrable (by norm_num)
  have hZero : ∀ᵐ x ∂(volume : Measure Point), x ∈ V → E x = 0 := by
    apply hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero hLoc
    intro φ hφ hφc hφV
    have h := hWeak φ hφ hφc (subset_univ _)
    simp only [Measure.restrict_univ] at h
    have hD : tsupport (coordinateDerivative φ hφ i) ⊆ V :=
      (tsupport_fderiv_apply_subset ℝ (axis i)).trans hφV
    have h₀ : (∫ x, coordinateDerivative φ hφ i x • u x) = 0 := by
      apply integral_eq_zero_of_ae
      apply Eventually.of_forall
      intro x
      change coordinateDerivative φ hφ i x • u x = 0
      by_cases hx : x ∈ V
      · rw [image_eq_zero_of_notMem_tsupport (show x ∉ tsupport u from hx),smul_zero]
      · rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hD ht)),zero_smul]
    rw [h₀] at h
    exact neg_eq_zero.mp h.symm
  let E₀ := K.indicator E
  have hEq : E =ᵐ[(volume : Measure Point)] E₀ := by
    filter_upwards [hZero] with x hx
    by_cases hxK : x ∈ K
    · exact (indicator_of_mem hxK E).symm
    · rw [show E₀ x = 0 from indicator_of_notMem hxK E]
      exact hx hxK
  have hc₀ : HasCompactSupport E₀ := HasCompactSupport.intro hc (fun x hx => indicator_of_notMem hx E)
  have h₀ := hE.ae_eq hEq
  have hi : Integrable E₀ := memLp_one_iff_integrable.1 (h₀.mono_exponent_of_measure_support_ne_top
    (fun x hx => image_eq_zero_of_notMem_tsupport hx) hc₀.measure_lt_top.ne (by norm_num : (1:ℝ≥0∞)≤2)
    )
  exact hi.congr hEq.symm

private theorem ambientDifferenceQuotient_congr_ae {q : ℕ} {u v : Point → Ambient q}
    (h : u =ᵐ[(volume : Measure Point)] v) (i : Fin 3) (s : ℝ) :
    ambientDifferenceQuotient i s u =ᵐ[(volume : Measure Point)] ambientDifferenceQuotient i s v := by
  have hS := (measurePreserving_add_right (volume : Measure Point) (s • axis i)).quasiMeasurePreserving.ae h
  filter_upwards [h,hS] with x hx hy
  change s⁻¹ • (u (x+s • axis i)-u x) = s⁻¹ • (v (x+s • axis i)-v x)
  rw [hx,hy]

/-- The normalized difference agrees almost everywhere with the segment average
of the actual weak directional derivative. -/
theorem ambientDifferenceQuotient_ae_eq_coordinateSegmentAverage {q : ℕ}
    {u E : Point → Ambient q} (hu : MemLp u 2 (volume : Measure Point)) (hc : HasCompactSupport u)
    (hE : MemLp E 2 (volume : Measure Point)) {i : Fin 3}
    (hWeak : IsWeakAmbientCoordinatePartial univ i u E) {s : ℝ} (hs : s ≠ 0) :
    ambientDifferenceQuotient i s u =ᵐ[(volume : Measure Point)] coordinateSegmentAverage i s E := by
  have huI : Integrable u := memLp_one_iff_integrable.1 (hu.mono_exponent_of_measure_support_ne_top
    (fun x hx => image_eq_zero_of_notMem_tsupport hx) hc.measure_lt_top.ne (by norm_num : (1:ℝ≥0∞)≤2)
    )
  have hEI : Integrable E := memLp_weakCoordinatePartial_integrable_of_compact hc hE hWeak
  let u₀ := hu.1.mk u
  let E₀ := hE.1.mk E
  have huAE : u =ᵐ[(volume : Measure Point)] u₀ := hu.1.ae_eq_mk
  have hEAE : E =ᵐ[(volume : Measure Point)] E₀ := hE.1.ae_eq_mk
  have hW : IsWeakAmbientCoordinatePartial univ i u₀ E₀ :=
    hWeak.congr_ae (by simpa only [Measure.restrict_univ] using huAE)
      (by simpa only [Measure.restrict_univ] using hEAE)
  have hEq := coordinateSegmentAverage_eq_differenceQuotient_of_integrable hu.1.stronglyMeasurable_mk
    hE.1.stronglyMeasurable_mk (huI.congr huAE) (hEI.congr hEAE) hW hs
  exact (ambientDifferenceQuotient_congr_ae huAE i s).trans
    (hEq.trans (coordinateSegmentAverage_congr_ae hEAE i s).symm)

/-- The normalized coordinate difference is bounded by the (L^p) norm of the actual partial. -/
theorem ambientDifferenceQuotient_eLpNorm_le_weakPartial {q : ℕ}
    {u E : Point → Ambient q} (hu : MemLp u 2 (volume : Measure Point)) (hc : HasCompactSupport u)
    (hE₂ : MemLp E 2 (volume : Measure Point)) {i : Fin 3}
    (hWeak : IsWeakAmbientCoordinatePartial univ i u E) {p : ℝ} (hp : 1 ≤ p)
    (hEp : MemLp E (ENNReal.ofReal p) (volume : Measure Point)) (s : ℝ) :
    MemLp (ambientDifferenceQuotient i s u) (ENNReal.ofReal p) (volume : Measure Point) ∧
      eLpNorm (ambientDifferenceQuotient i s u) (ENNReal.ofReal p) (volume : Measure Point) ≤
        eLpNorm E (ENNReal.ofReal p) (volume : Measure Point) := by
  by_cases hs : s=0
  · subst s
    have hZ : ambientDifferenceQuotient i 0 u = 0 := by
      funext x
      simp [ambientDifferenceQuotient]
    rw [hZ,eLpNorm_zero]
    exact ⟨MemLp.zero,zero_le⟩
  have hEq := ambientDifferenceQuotient_ae_eq_coordinateSegmentAverage hu hc hE₂ hWeak hs
  let E₀ := hEp.1.mk E
  have hAE : E =ᵐ[(volume : Measure Point)] E₀ := hEp.1.ae_eq_mk
  have h := memLp_translationAverage_le unitSegmentMeasure (θ := fun t : ℝ => t • (s • axis i))
    (by fun_prop) hEp.1.stronglyMeasurable_mk hp (hEp.ae_eq hAE)
  have he := hEq.trans (coordinateSegmentAverage_congr_ae hAE i s)
  change MemLp (coordinateSegmentAverage i s E₀) (ENNReal.ofReal p) (volume : Measure Point) ∧ _ at h
  refine ⟨h.1.ae_eq he.symm,?_⟩
  rw [eLpNorm_congr_ae he,eLpNorm_congr_ae hAE]
  exact h.2

/-- The actual normalized differences converge strongly in (L²) to the
displayed weak partial as the nonzero displacement vanishes. -/
theorem tendsto_eLpNorm_ambientDifferenceQuotient_sub_weakPartial {q : ℕ} {ι : Type*}
    {u E : Point → Ambient q} (hu : MemLp u 2 (volume : Measure Point)) (hc : HasCompactSupport u)
    (hE : MemLp E 2 (volume : Measure Point)) {i : Fin 3}
    (hWeak : IsWeakAmbientCoordinatePartial univ i u E)
    {l : Filter ι} {s : ι → ℝ} (hs : Tendsto s l (𝓝 0)) (hs0 : ∀ᶠ j in l, s j ≠ 0) :
    Tendsto (fun j => eLpNorm (ambientDifferenceQuotient i (s j) u-E) 2 (volume : Measure Point))
      l (𝓝 0) := by
  let E₀ := hE.1.mk E
  have hAE : E =ᵐ[(volume : Measure Point)] E₀ := hE.1.ae_eq_mk
  have hEM : StronglyMeasurable E₀ := hE.1.stronglyMeasurable_mk
  have hE₀ : MemLp E₀ 2 (volume : Measure Point) := hE.ae_eq hAE
  have hEI : Integrable E₀ := (memLp_weakCoordinatePartial_integrable_of_compact hc hE hWeak).congr hAE
  have hTr := HarmonicMaps.tendsto_eLpNorm_translation_sub hE₀
  apply ENNReal.tendsto_nhds_zero.2
  intro ε hε
  obtain ⟨R,hR₀,hR⟩ := exists_between hε
  have hRN : R ≠ ⊤ := (hR.trans_le le_top).ne
  have hNear : ∀ᶠ z : Point in 𝓝 0, eLpNorm (fun x => E₀ (x-z)-E₀ x) 2 (volume : Measure Point) < R :=
    hTr.eventually (Iio_mem_nhds hR₀)
  obtain ⟨δ,hδ,hB⟩ := Metric.mem_nhds_iff.1 hNear
  have hSmall : ∀ᶠ j in l, |s j| < δ :=
    (Metric.tendsto_nhds.1 hs δ hδ).mono fun _ hj => by simpa only [Real.dist_eq,sub_zero] using hj
  filter_upwards [hSmall,hs0] with j hj hj0
  let z := s j • axis i
  let P (x : Point) (t : ℝ) := E₀ (x+t • z)-E₀ x
  have hz : ‖z‖ = |s j| := by
    dsimp only [z]
    rw [norm_smul,Real.norm_eq_abs,show ‖axis i‖=1 by simp [axis],mul_one]
  have hP : StronglyMeasurable (Function.uncurry P) := by
    have hS : Measurable (fun y : Point × ℝ => y.1+y.2 • z) := by fun_prop
    exact (hEM.comp_measurable hS).sub (hEM.comp_measurable measurable_fst)
  have hSlice : ∀ᵐ t ∂unitSegmentMeasure,
      eLpNorm (fun x => P x t) (ENNReal.ofReal (2:ℝ)) (volume : Measure Point) ≤ R := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with t ht
    have htz : -(t • z) ∈ Metric.ball (0:Point) δ := by
      rw [mem_ball_zero_iff,norm_neg,norm_smul,Real.norm_of_nonneg (show 0 < t from ht.1).le]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt (hz ▸ hj)
    have hBound : eLpNorm (fun x => E₀ (x - (-(t • z)))-E₀ x) 2 (volume : Measure Point) < R := hB htz
    simpa only [P,sub_neg_eq_add,ENNReal.ofReal_ofNat] using hBound.le
  have hAvg := (memLp_parameterAverage_le unitSegmentMeasure hP (by norm_num : (1:ℝ) ≤ 2) hRN hSlice).2
  have hEq := ambientDifferenceQuotient_ae_eq_coordinateSegmentAverage hu hc hE hWeak hj0
  have hEqAvg := coordinateSegmentAverage_congr_ae hAE i (s j)
  have hProd := integrable_prod_shift_of_integrable hEM hEI z
  have hFun : (ambientDifferenceQuotient i (s j) u-E) =ᵐ[(volume : Measure Point)]
      fun x => ∫ t, P x t ∂unitSegmentMeasure := by
    filter_upwards [hEq,hEqAvg,hAE,hProd.prod_left_ae] with x hx hxA hxE hxI
    change ambientDifferenceQuotient i (s j) u x-E x = ∫ t, P x t ∂unitSegmentMeasure
    rw [hx,hxA,hxE]
    change (∫ t, E₀ (x+t • z) ∂unitSegmentMeasure)-E₀ x =
      ∫ t, E₀ (x+t • z)-E₀ x ∂unitSegmentMeasure
    change Integrable (fun t => E₀ (x+t • z)) unitSegmentMeasure at hxI
    rw [integral_sub hxI (integrable_const _),integral_const,measureReal_def,measure_univ,
      ENNReal.toReal_one,one_smul]
  rw [eLpNorm_congr_ae hFun]
  exact (by simpa only [ENNReal.ofReal_ofNat] using hAvg :
    eLpNorm (fun x => ∫ t, P x t ∂unitSegmentMeasure) 2 (volume : Measure Point) ≤ R).trans hR.le

end Thesis

end
