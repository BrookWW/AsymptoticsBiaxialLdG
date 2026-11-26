module

public import Thesis.Interpolation.EdgeProjectionLayer
import Thesis.StressEnergy
import StratificationTheory.Foundation.CylinderCoordinateMeasure
import StratificationTheory.Foundation.IntervalWeakRepresentative
import StratificationTheory.Interpolation.CubicalEdgeInterpolationGraph
import StratificationTheory.Interpolation.CubicalEdgeInterpolationEnergy

/-! The affine side interpolation in the native edge and radial coordinates. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Matrix.Norms.Frobenius Topology

namespace Thesis

/-- The two real coordinates used for the native edge rectangle. -/
def edgeRectangleCoordinates : Plane ≃L[ℝ] ℝ × ℝ :=
  let one := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).trans (one.prodCongr one)

private theorem edgeRectangleCoordinates_apply (x : Plane) :
    edgeRectangleCoordinates x =
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1) x).1 0,
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1) x).2 0) := rfl

theorem measurePreserving_edgeRectangleCoordinates :
    MeasurePreserving edgeRectangleCoordinates (volume : Measure Plane)
      ((volume : Measure ℝ).prod volume) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)
  let one := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let C := e.trans (ContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℝ (HarmonicMaps.Domain 1)) one)
  have hC : MeasurePreserving C volume ((volume : Measure (HarmonicMaps.Domain 1)).prod volume) :=
    StratificationTheory.measurePreserving_cylinder_coordinates 1
  have hP := StratificationTheory.measurePreserving_domainOne_eval.prod
    (MeasurePreserving.id (volume : Measure ℝ))
  exact hP.comp hC

/-- The open native rectangle between the two traces. The radial coordinate
runs from zero to the positive layer thickness. -/
def edgeRectangleDomain (l r h : ℝ) : HarmonicMaps.OpenDomain 2 :=
  ⟨edgeRectangleCoordinates ⁻¹' (Ioo l r ×ˢ Ioo 0 h),
    ((isOpen_Ioo.prod isOpen_Ioo).preimage edgeRectangleCoordinates.continuous)⟩

/-- Affine interpolation of the projected trace at zero and the original
trace at the top of the rectangle. -/
def edgeRectangleField (h : ℝ) (u v : ℝ → S0) (x : Plane) : S0 :=
  let y := edgeRectangleCoordinates x
  (y.2 / h) • u y.1 + (1 - y.2 / h) • v y.1

/-- The actual edge and radial columns of the affine rectangular field in
Frobenius coordinates. -/
def edgeRectangleGradient (h : ℝ) (u v g k : ℝ → S0) : Plane → HarmonicMaps.Gradient 2 5 :=
  fun x =>
    let y := edgeRectangleCoordinates x
    let α := y.2 / h
    Fin.addCases (motive := fun _ : Fin (1 + 1) => HarmonicMaps.Ambient 5)
      (fun _ : Fin 1 => (1 - α) • frobeniusCoordinateEquiv (k y.1) + α • frobeniusCoordinateEquiv (g y.1))
      (fun _ : Fin 1 => h⁻¹ • (frobeniusCoordinateEquiv (u y.1) - frobeniusCoordinateEquiv (v y.1)))

private theorem memLp_two_continuousOn_edge {E : Type*} [NormedAddCommGroup E]
    {u : ℝ → E} {l r : ℝ} (hu : ContinuousOn u (Icc l r)) :
    MemLp u 2 (volume.restrict (Ioo l r)) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  letI : IsFiniteMeasure (volume.restrict (Ioo l r)) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top⟩
  exact MemLp.of_bound ((hu.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo) B
    ((ae_restrict_mem measurableSet_Ioo).mono fun x hx => hB x (Ioo_subset_Icc_self hx))

private theorem interval_increments_comp_frobenius {u g : ℝ → S0} {l r : ℝ} (hlr : l < r)
    (hg : MemLp g 2 (volume.restrict (Ioo l r)))
    (hinc : ∀ s ∈ Icc l r, ∀ t ∈ Icc l r, u t - u s = ∫ x in s..t, g x) :
    ∀ s ∈ Icc l r, ∀ t ∈ Icc l r, frobeniusCoordinateEquiv (u t) - frobeniusCoordinateEquiv (u s) =
      ∫ x in s..t, frobeniusCoordinateEquiv (g x) := by
  intro s hs t ht
  letI : CompleteSpace S0 := complete_of_proper
  let L := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hst : uIcc s t ⊆ uIcc l r := by
    rw [uIcc_of_le hlr.le]
    apply Icc_subset_Icc
    · exact le_min hs.1 ht.1
    · exact max_le hs.2 ht.2
  have hI := (StratificationTheory.intervalIntegrable_of_memLp_two hlr.le hg).mono_set hst
  change L (u t) - L (u s) = ∫ x in s..t, L (g x)
  rw [L.intervalIntegral_comp_comm hI, ← map_sub, hinc s hs t ht]

/-- The native Sobolev graph of the affine side has the displayed columns
and the sharp rectangular gradient estimate in the same coordinates. -/
theorem edgeRectangle_memW12_and_gradient_energy {l r h : ℝ} {u v g k : ℝ → S0}
    (hlr : l < r) (hh : 0 < h) (hu : ContinuousOn u (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (hg : MemLp g 2 (volume.restrict (Ioo l r))) (hk : MemLp k 2 (volume.restrict (Ioo l r)))
    (hU : ∀ s ∈ Icc l r, ∀ t ∈ Icc l r, u t - u s = ∫ x in s..t, g x)
    (hV : ∀ s ∈ Icc l r, ∀ t ∈ Icc l r, v t - v s = ∫ x in s..t, k x) :
    let Ω := edgeRectangleDomain l r h
    let W := fun x => frobeniusCoordinateEquiv (edgeRectangleField h u v x)
    let D := edgeRectangleGradient h u v g k
    HarmonicMaps.MemW12 Ω W D ∧
      Integrable (fun x => HarmonicMaps.hsNormSq (D x)) (volume.restrict Ω.val) ∧
      (∫ x in Ω.val, HarmonicMaps.hsNormSq (D x)) ≤
        h / 2 * ((∫ t in Ioo l r, ‖k t‖ ^ 2) + ∫ t in Ioo l r, ‖g t‖ ^ 2) +
        h⁻¹ * ∫ t in Ioo l r, ‖v t - u t‖ ^ 2 := by
  intro Ω W D
  let e := frobeniusCoordinateEquiv
  have hLp (w : ℝ → S0) (hw : MemLp w 2 (volume.restrict (Ioo l r))) :
      MemLp (fun t => e (w t)) 2 (volume.restrict (Ioo l r)) :=
    (frobeniusCoordinateEquiv_memLp_iff _ _ _).2 hw
  have hF := hLp v (memLp_two_continuousOn_edge hv)
  have hG := hLp u (memLp_two_continuousOn_edge hu)
  have hF' := hLp k hk
  have hG' := hLp g hg
  have hGraph := StratificationTheory.interval_pair_memW12_rectangle hlr hh
    hF hG hF' hG' EventuallyEq.rfl EventuallyEq.rfl
    (interval_increments_comp_frobenius hlr hk hV) (interval_increments_comp_frobenius hlr hg hU)
  have hEnergy := StratificationTheory.interval_pair_rectangle_gradient_energy hh
    hF hG hF' hG' EventuallyEq.rfl EventuallyEq.rfl
  have hW (x : Plane) : W x = (1 - (edgeRectangleCoordinates x).2 / h) • e (v (edgeRectangleCoordinates x).1) +
      ((edgeRectangleCoordinates x).2 / h) • e (u (edgeRectangleCoordinates x).1) := by
    simp only [W, edgeRectangleField, e, map_add, map_smul]
    exact add_comm _ _
  constructor
  · rw [funext hW]
    simpa only [sub_zero, Ω, D, edgeRectangleDomain, edgeRectangleGradient, edgeRectangleCoordinates_apply,
      mem_preimage, mem_prod] using! hGraph
  · have hNorm (s : ℝ) : ‖e (v s) - e (u s)‖ ^ 2 = ‖v s - u s‖ ^ 2 := by
      rw [← map_sub e, e.norm_map]
    simp only [sub_zero, hNorm, LinearIsometryEquiv.norm_map] at hEnergy
    exact ⟨hEnergy.1, hEnergy.2.1⟩

private theorem closedRectangle_integrable {f : ℝ × ℝ → ℝ} {l r h : ℝ}
    (hf : ContinuousOn f (Icc l r ×ˢ Icc 0 h)) :
    IntegrableOn f (Ioo l r ×ˢ Ioo 0 h) ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  let μ := (volume : Measure ℝ).prod (volume : Measure ℝ)
  have hfi : IntegrableOn f (Icc l r ×ˢ Icc 0 h) μ :=
    hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact hfi.mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

private theorem integral_native_edgeRectangle {f : ℝ × ℝ → ℝ} {l r h : ℝ}
    (hf : IntegrableOn f (Ioo l r ×ˢ Ioo 0 h) ((volume : Measure ℝ).prod volume)) :
    IntegrableOn (fun x => f (edgeRectangleCoordinates x)) (edgeRectangleDomain l r h).val ∧
      (∫ x in (edgeRectangleDomain l r h).val, f (edgeRectangleCoordinates x)) =
        ∫ t in Ioo (0 : ℝ) h, ∫ s in Ioo l r, f (s, t) := by
  have hMP := measurePreserving_edgeRectangleCoordinates.restrict_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo : MeasurableSet (Ioo l r ×ˢ Ioo (0 : ℝ) h))
  have hi := hMP.integrable_comp_of_integrable hf
  refine ⟨hi, ?_⟩
  have hEq := hMP.integral_comp edgeRectangleCoordinates.toHomeomorph.measurableEmbedding f
  have hFubini : Integrable f (((volume : Measure ℝ).restrict (Ioo l r)).prod
      (volume.restrict (Ioo 0 h))) := by
    rw [Measure.prod_restrict]
    exact hf
  rw [← Measure.prod_restrict] at hEq
  exact hEq.trans (integral_prod_symm _ hFubini)

/-- Bulk energy on the affine radial face is at most its thickness times
the edge bulk energy, with the coefficient of the segment bound. -/
theorem edgeRectangle_bulkPotential_bound (a : BulkCoefficients) {l r h C : ℝ}
    {u v : ℝ → S0} (hH : 0 < h) (hC : 0 ≤ C)
    (hu : ContinuousOn u (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (hSegment : ∀ s ∈ Icc l r, ∀ t ∈ Icc (0 : ℝ) 1,
      bulkPotential a (t • u s + (1 - t) • v s) ≤ C * t ^ 2 * bulkPotential a (u s)) :
    IntegrableOn (fun x => bulkPotential a (edgeRectangleField h u v x)) (edgeRectangleDomain l r h).val ∧
      (∫ x in (edgeRectangleDomain l r h).val, bulkPotential a (edgeRectangleField h u v x)) ≤
        C * h * ∫ s in Ioo l r, bulkPotential a (u s) := by
  let f : ℝ × ℝ → ℝ := fun y => bulkPotential a ((y.2 / h) • u y.1 + (1 - y.2 / h) • v y.1)
  let b : ℝ → ℝ := fun s => bulkPotential a (u s)
  have hB : ContinuousOn b (Icc l r) := (contDiff_bulkPotential a).continuous.comp_continuousOn hu
  have hu' : ContinuousOn (fun y : ℝ × ℝ => u y.1) (Icc l r ×ˢ Icc 0 h) :=
    hu.comp continuous_fst.continuousOn (fun _ hy => hy.1)
  have hv' : ContinuousOn (fun y : ℝ × ℝ => v y.1) (Icc l r ×ˢ Icc 0 h) :=
    hv.comp continuous_fst.continuousOn (fun _ hy => hy.1)
  have hAlpha : Continuous (fun y : ℝ × ℝ => y.2 / h) := continuous_snd.div_const h
  have hf : ContinuousOn f (Icc l r ×ˢ Icc 0 h) := (contDiff_bulkPotential a).continuous.comp_continuousOn
    ((hAlpha.continuousOn.smul hu').add ((continuousOn_const.sub hAlpha.continuousOn).smul hv'))
  have hD : ContinuousOn (fun y : ℝ × ℝ => C * b y.1) (Icc l r ×ˢ Icc 0 h) :=
    continuousOn_const.mul (hB.comp continuous_fst.continuousOn fun _ hy => hy.1)
  have hLe (x : ℝ × ℝ) (hx : x ∈ Ioo l r ×ˢ Ioo 0 h) : f x ≤ C * b x.1 := by
    have hτ : x.2 / h ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hx.2.1.le hH.le,
      (div_le_one hH).2 hx.2.2.le⟩
    have hτ₂ : (x.2 / h) ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hτ.1 hτ.2 2
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ₂ hC)
      (bulkPotential_nonneg a (u x.1))
    exact (hSegment x.1 (Ioo_subset_Icc_self hx.1) (x.2 / h) hτ).trans
      (by simpa only [mul_one] using hmul)
  obtain ⟨hfi, _⟩ := integral_native_edgeRectangle (closedRectangle_integrable hf)
  obtain ⟨hDi, hDEq⟩ := integral_native_edgeRectangle (closedRectangle_integrable hD)
  have hA : MeasurableSet (edgeRectangleDomain l r h).val := (edgeRectangleDomain l r h).property.measurableSet
  refine ⟨hfi, ?_⟩
  change (∫ x in (edgeRectangleDomain l r h).val, f (edgeRectangleCoordinates x)) ≤ _
  calc
    _ ≤ ∫ x in (edgeRectangleDomain l r h).val, C * b (edgeRectangleCoordinates x).1 :=
      setIntegral_mono_on hfi hDi hA fun x hx => hLe _ hx
    _ = _ := by
      rw [hDEq]
      change (∫ _ in Ioo (0 : ℝ) h, ∫ s in Ioo l r, C * b s) = C * h * ∫ s in Ioo l r, b s
      simp only [setIntegral_const, Real.volume_real_Ioo, sub_zero, max_eq_left hH.le, smul_eq_mul,
        integral_const_mul]
      ring

/-- The native radial side energy retains the tangential derivative, the
trace discrepancy and the bulk potential on the same projected segment. -/
theorem edgeRectangle_penalizedEnergy_bound (a : BulkCoefficients) (ε : ElasticScale)
    {l r h C : ℝ} {u v g k : ℝ → S0}
    (hlr : l < r) (hh : 0 < h) (hC : 0 ≤ C)
    (hu : ContinuousOn u (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (hg : MemLp g 2 (volume.restrict (Ioo l r))) (hk : MemLp k 2 (volume.restrict (Ioo l r)))
    (hU : ∀ s ∈ Icc l r, ∀ t ∈ Icc l r, u t - u s = ∫ x in s..t, g x)
    (hV : ∀ s ∈ Icc l r, ∀ t ∈ Icc l r, v t - v s = ∫ x in s..t, k x)
    (hGrad : ∀ s ∈ Icc l r, ‖k s‖ ≤ C * ‖g s‖)
    (hGap : ∀ s ∈ Icc l r, ‖u s - v s‖ ^ 2 ≤ C * bulkPotential a (u s))
    (hSeg : ∀ s ∈ Icc l r, ∀ t ∈ Icc (0 : ℝ) 1,
      bulkPotential a (t • u s + (1 - t) • v s) ≤ C * t ^ 2 * bulkPotential a (u s)) :
    let Ω := edgeRectangleDomain l r h
    let W := edgeRectangleField h u v
    let D := edgeRectangleGradient h u v g k
    (∫ x in Ω.val, (1 / 2 : ℝ) * HarmonicMaps.hsNormSq (D x) +
      (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (W x)) ≤
        (h / 4) * (1 + C ^ 2) * (∫ s in Ioo l r, ‖g s‖ ^ 2) +
        ((C / 2) * h⁻¹ + (ε : ℝ)⁻¹ ^ 2 * (C * h)) * ∫ s in Ioo l r, bulkPotential a (u s) := by
  intro Ω W D
  obtain ⟨_, hD, hDE⟩ := edgeRectangle_memW12_and_gradient_energy hlr hh hu hv hg hk hU hV
  obtain ⟨hW, hWE⟩ := edgeRectangle_bulkPotential_bound a hh hC hu hv hSeg
  let x := ∫ s in Ioo l r, ‖g s‖ ^ 2
  let y := ∫ s in Ioo l r, bulkPotential a (u s)
  have hgi : IntegrableOn (fun s => ‖g s‖ ^ 2) (Ioo l r) :=
    MemLp.integrable_norm_pow (p := 2) hg (by decide)
  have hki : IntegrableOn (fun s => ‖k s‖ ^ 2) (Ioo l r) :=
    MemLp.integrable_norm_pow (p := 2) hk (by decide)
  have hN : ∫ s in Ioo l r, ‖k s‖ ^ 2 ≤ C ^ 2 * x := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hki (hgi.const_mul _) measurableSet_Ioo
    intro s hs
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hGrad s (Ioo_subset_Icc_self hs)) 2
  have hb : IntegrableOn (fun s => bulkPotential a (u s)) (Ioo l r) := by
    have hb' : ContinuousOn (fun s => bulkPotential a (u s)) (Icc l r) :=
      (contDiff_bulkPotential a).continuous.comp_continuousOn hu
    exact (hb'.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hpLp := (memLp_two_continuousOn_edge hv).sub (memLp_two_continuousOn_edge hu)
  have hpi : IntegrableOn (fun s => ‖v s - u s‖ ^ 2) (Ioo l r) :=
    MemLp.integrable_norm_pow (p := 2) hpLp (by decide)
  have hP : ∫ s in Ioo l r, ‖v s - u s‖ ^ 2 ≤ C * y := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hpi (hb.const_mul _) measurableSet_Ioo
    intro s hs
    rw [norm_sub_rev]
    exact hGap s (Ioo_subset_Icc_self hs)
  have hG : (∫ z in Ω.val, HarmonicMaps.hsNormSq (D z)) ≤
      h / 2 * (C ^ 2 * x + x) + h⁻¹ * (C * y) :=
    hDE.trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hN le_rfl) (by positivity))
      (mul_le_mul_of_nonneg_left hP (inv_nonneg.mpr hh.le)))
  rw [integral_add (hD.const_mul _) (hW.const_mul _), integral_const_mul, integral_const_mul]
  calc
    _ ≤ (1 / 2 : ℝ) * (h / 2 * (C ^ 2 * x + x) + h⁻¹ * (C * y)) +
      (ε : ℝ)⁻¹ ^ 2 * (C * h * y) :=
      add_le_add (mul_le_mul_of_nonneg_left hG (by norm_num)) (mul_le_mul_of_nonneg_left hWE (sq_nonneg _))
    _ = _ := by
      change _ = (h / 4) * (1 + C ^ 2) * x + ((C / 2) * h⁻¹ + (ε : ℝ)⁻¹ ^ 2 * (C * h)) * y
      ring

end Thesis
