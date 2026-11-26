module

public import Thesis.Interpolation.LipschitzSobolevPullback
import StratificationTheory.Compactness.SobolevTranslationBound
import StratificationTheory.Foundation.CylinderSobolevAlgebra
import Mathlib.MeasureTheory.Function.L2Space

/-! Global Sobolev translations and difference quotients with their actual weak columns. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal NNReal Topology RealInnerProductSpace

namespace Thesis

/-- The finite difference in a coordinate direction, divided by the displacement. -/
@[expose] def ambientDifferenceQuotient {n : ℕ} {E : Type*}
    [Sub E] [SMul ℝ E] (i : Fin n) (h : ℝ) (v : Domain n → E) (x : Domain n) : E :=
  h⁻¹ • (v (x + h • EuclideanSpace.single i 1) - v x)

/-- Translation of a global weak graph translates all displayed columns. -/
theorem memW12_translate_univ {n q : ℕ} {u : Domain n → Ambient q}
    {D : Domain n → HarmonicMaps.Gradient n q}
    (hu : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) u D) (z : Domain n) :
    MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) (fun x => u (x+z)) (fun x i => D (x+z) i) := by
  let F := (IsometryEquiv.addRight z).toHomeomorph
  let Ω : OpenDomain n := ⟨univ,isOpen_univ⟩
  have hV : (⟨F ⁻¹' Ω.val, Ω.property.preimage F.continuous⟩ : OpenDomain n) = Ω :=
    Subtype.ext (preimage_univ)
  have hK : LipschitzWith 1 (F : Domain n → Domain n) := (IsometryEquiv.addRight z).isometry.lipschitz
  have hL : LipschitzWith 1 (F.symm : Domain n → Domain n) := (IsometryEquiv.addRight z).symm.isometry.lipschitz
  have h := memW12_lipschitz_homeomorph_preimage F hK hL Ω u D hu
  rw [hV] at h
  have hF (x : Domain n) : fderiv ℝ F x = ContinuousLinearMap.id ℝ (Domain n) :=
    (((hasFDerivAt_id x).add_const z)).fderiv
  have hEq : (fun x i => ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • D (F x) j) =
      fun x i => D (x+z) i := by
    funext x i
    rw [hF,ContinuousLinearMap.id_apply]
    simp only [PiLp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl
  rwa [hEq] at h

/-- The difference quotient of a global weak graph has the corresponding
difference quotients of its derivative columns. -/
theorem memW12_differenceQuotient_univ {n q : ℕ} {u : Domain n → Ambient q}
    {D : Domain n → HarmonicMaps.Gradient n q}
    (hu : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) u D) (i : Fin n) (h : ℝ) :
    MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) (ambientDifferenceQuotient i h u)
      (fun x j => ambientDifferenceQuotient i h (fun y => D y j) x) :=
  StratificationTheory.memW12_const_smul h⁻¹ ((memW12_translate_univ hu (h • EuclideanSpace.single i 1)).sub hu)

/-- Translation and finite difference quotients preserve (L^p) membership. -/
theorem memLp_ambientDifferenceQuotient {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} {v : Domain n → E}
    (hv : MemLp v p volume) (i : Fin n) (h : ℝ) :
    MemLp (ambientDifferenceQuotient i h v) p volume :=
  ((hv.comp_measurePreserving (measurePreserving_add_right volume
    (h • (EuclideanSpace.single i (1 : ℝ) : Domain n)))).sub hv).const_smul h⁻¹

/-- The whole-space translation estimate for the actual columns is obtained
by exhaustion from the interior version. -/
theorem integral_globalSobolev_translation_sq_le {n q : ℕ}
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hu : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) u D) (z : Domain n) :
    (∫ x, ‖u (x+z)-u x‖^2) ≤ ‖z‖^2 * ∫ x, hsNormSq (D x) := by
  have hMap : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hu.2.1
  have hColumns : ∀ i, MemLp (fun x => D x i) 2 (volume : Measure (Domain n)) :=
    fun i => by simpa only [Measure.restrict_univ] using hu.2.2 i
  have hDiff : MemLp (fun x => u (x+z)-u x) 2 volume :=
    (hMap.comp_measurePreserving (measurePreserving_add_right volume z)).sub hMap
  have hDiffInt : Integrable (fun x => ‖u (x+z)-u x‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm hDiff.1).mp hDiff
  have hEnergy : Integrable (fun x => hsNormSq (D x)) volume :=
    integrable_hsNormSq_of_memLp_columns hColumns
  let R (k : ℕ) := (k : ℝ) + ‖z‖ + 1
  have hStep (k : ℕ) : (∫ x in ball (0 : Domain n) (k : ℝ), ‖u (x+z)-u x‖^2) ≤
      ‖z‖^2 * ∫ x, hsNormSq (D x) := by
    have hr : 0 < R k := by dsimp only [R]; positivity
    have hMargin : (k : ℝ) + ‖z‖ < R k := lt_add_one _
    have hSob : MemW12 (ballDomain (0 : Domain n) (R k)) u D :=
      ⟨hu.1.mono (subset_univ _),hMap.restrict _,fun i => (hColumns i).restrict _⟩
    refine (StratificationTheory.Compactness.memW12_translation_L2_square_le
      (0 : Domain n) hr z hMargin hSob).trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    exact setIntegral_le_integral hEnergy (Eventually.of_forall fun _ => hsNormSq_nonneg _)
  have hMono : Monotone (fun k : ℕ => ball (0 : Domain n) (k : ℝ)) :=
    fun _ _ h => ball_subset_ball (Nat.cast_le.mpr h)
  have hlim : Tendsto (fun k : ℕ => ∫ x in ball (0 : Domain n) (k : ℝ), ‖u (x+z)-u x‖^2) atTop
      (𝓝 (∫ x, ‖u (x+z)-u x‖^2)) := by
    have h := tendsto_setIntegral_of_monotone (fun _ => measurableSet_ball) hMono hDiffInt.integrableOn
    simpa only [iUnion_ball_nat,Measure.restrict_univ] using h
  exact le_of_tendsto hlim (Eventually.of_forall hStep)

/-- The (L^2) norm of a normalized Sobolev difference quotient does not
exceed that of the full weak gradient. -/
theorem integral_globalSobolev_differenceQuotient_sq_le {n q : ℕ}
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q}
    (hu : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain n) u D) (i : Fin n) {h : ℝ} (hh : h ≠ 0) :
    (∫ x, ‖ambientDifferenceQuotient i h u x‖^2) ≤ ∫ x, hsNormSq (D x) := by
  let z : Domain n := h • EuclideanSpace.single i 1
  have hT := integral_globalSobolev_translation_sq_le hu z
  have hz : ‖z‖ = |h| := by rw [show z = h • EuclideanSpace.single i 1 from rfl,
    norm_smul,Real.norm_eq_abs,PiLp.norm_single,norm_one,mul_one]
  calc
    _ = h⁻¹ ^ 2 * ∫ x, ‖u (x+z)-u x‖^2 := by
      simp only [ambientDifferenceQuotient,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,← integral_const_mul,z]
    _ ≤ h⁻¹ ^ 2 * (‖z‖^2 * ∫ x, hsNormSq (D x)) := mul_le_mul_of_nonneg_left hT (sq_nonneg _)
    _ = _ := by
      rw [hz,sq_abs,← mul_assoc,← mul_pow,inv_mul_cancel₀ hh,one_pow,one_mul]

/-- The pointwise real pairing of two actual (L^2) fields is integrable. -/
theorem integrable_inner_of_memLp_two {X E : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure X} {v w : X → E} (hv : MemLp v 2 μ) (hw : MemLp w 2 μ) :
    Integrable (fun x => inner ℝ (v x) (w x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hv.toLp v) (hw.toLp w)).congr
  filter_upwards [hv.coeFn_toLp,hw.coeFn_toLp] with x hx hy
  rw [hx,hy]

/-- The discrete integration by parts formula on the whole space. -/
theorem integral_inner_ambientDifferenceQuotient_right {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v w : Domain n → E} (hv : MemLp v 2 volume) (hw : MemLp w 2 volume)
    (i : Fin n) (h : ℝ) :
    (∫ x, inner ℝ (v x) (ambientDifferenceQuotient i (-h) w x)) =
      -(∫ x, inner ℝ (ambientDifferenceQuotient i h v x) (w x)) := by
  let z : Domain n := h • EuclideanSpace.single i 1
  have hShiftV : MemLp (fun y => v (y+z)) 2 volume :=
    hv.comp_measurePreserving (measurePreserving_add_right volume z)
  have hShiftW : MemLp (fun y => w (y-z)) 2 volume := by
    simpa only [Function.comp_def,sub_eq_add_neg] using
      hw.comp_measurePreserving (measurePreserving_add_right volume (-z))
  have hTrans :
      (∫ x, inner ℝ (v x) (w (x-z))) = ∫ x, inner ℝ (v (x+z)) (w x) := by
    have h := integral_add_right_eq_self (μ := (volume : Measure (Domain n)))
      (fun x => inner ℝ (v x) (w (x-z))) z
    simpa only [add_sub_cancel_right] using h.symm
  have hLeft (x : Domain n) :
      inner ℝ (v x) (ambientDifferenceQuotient i (-h) w x) =
        -(h⁻¹) * (inner ℝ (v x) (w (x-z)) - inner ℝ (v x) (w x)) := by
    rw [ambientDifferenceQuotient,neg_smul,← sub_eq_add_neg,inv_neg,real_inner_smul_right,inner_sub_right]
  have hRight (x : Domain n) :
      inner ℝ (ambientDifferenceQuotient i h v x) (w x) =
        h⁻¹ * (inner ℝ (v (x+z)) (w x) - inner ℝ (v x) (w x)) := by
    rw [ambientDifferenceQuotient,real_inner_smul_left,inner_sub_left]
  simp_rw [hLeft,hRight]
  rw [integral_const_mul,integral_const_mul,
    integral_sub (integrable_inner_of_memLp_two hv hShiftW) (integrable_inner_of_memLp_two hv hw),
    integral_sub (integrable_inner_of_memLp_two hShiftV hw) (integrable_inner_of_memLp_two hv hw),
    hTrans,neg_mul]

end Thesis
