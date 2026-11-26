module

public import Thesis.Variational.OddWallReflection
public import Thesis.Variational.EllipticPatchGeometry
public import Thesis.Upstream.AmbientWeakPartialAlgebra
import Thesis.Variational.SmoothDomainTraceChart
import StratificationTheory.Foundation.ReflectedRectangleTraceGluing
import StratificationTheory.Foundation.CoordinateRectangleTrace
import StratificationTheory.Foundation.SobolevLocalAssembly
import HarmonicMaps.Analysis.SobolevAECongruence
import HarmonicMaps.Analysis.SobolevDifference
import HarmonicMaps.SobolevRestriction

/-! Weak Hessians of odd reflection through a flat zero-trace wall. -/

public section

noncomputable section

open Filter Function HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace Thesis

/-- Normal reflection changes the sign of only the third coordinate. -/
@[expose] def flatReflectionSign (i : Fin 3) : ℝ := if i=2 then -1 else 1

theorem flatReflectionSign_tangential {i : Fin 3} (hi : i ≠ 2) : flatReflectionSign i = 1 :=
  if_neg hi

@[simp] theorem flatReflectionSign_normal : flatReflectionSign 2 = -1 := if_pos rfl

theorem normalReflection_axis (i : Fin 3) : normalReflection (axis i) = flatReflectionSign i • axis i := by
  apply PiLp.ext
  intro j
  fin_cases i <;> fin_cases j <;> simp [axis,normalReflection,flatReflectionSign]

private theorem memW12_restrict_openDomain {q : ℕ} {V W : OpenDomain 3}
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 W u D) (hV : V.val ⊆ W.val) : MemW12 V u D := by
  have hμ := Measure.restrict_mono_set (volume : Measure Point) hV
  exact ⟨hu.1.mono hV,hu.2.1.mono_measure hμ,fun j => (hu.2.2 j).mono_measure hμ⟩

private theorem locallyIntegrableOn_of_restrict_memLp_two {q : ℕ} {U : OpenDomain 3}
    {u : Point → Ambient q} (hu : MemLp u 2 (volume.restrict U.val)) : LocallyIntegrableOn u U.val volume := by
  apply (locallyIntegrableOn_iff U.property.isLocallyClosed).mpr
  intro K hKU hK
  letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact (hu.mono_measure (Measure.restrict_mono_set volume hKU)).integrable (by norm_num)

/-- A displayed tangential derivative of every first column supplies the full
weak gradient of the corresponding tangential column by mixed derivatives. -/
theorem memW12_tangential_column_of_all_second_partials {q : ℕ} {U : OpenDomain 3}
    {u : Point → Ambient q} {D T : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 U u D) (i : Fin 3)
    (hT : ∀ j, MemLp (fun x => T x j) 2 (volume.restrict U.val))
    (hMixed : ∀ j, IsWeakAmbientCoordinatePartial U.val i (fun x => D x j) (fun x => T x j)) :
    MemW12 U (fun x => D x i) T := by
  refine ⟨⟨hu.1.2.1 i,fun j => locallyIntegrableOn_of_restrict_memLp_two (hT j),?_⟩,hu.2.2 i,hT⟩
  intro j φ hφ hc hS
  exact (IsWeakAmbientCoordinatePartial.mixed hu.1 (hMixed j)) φ hφ hc hS

/-- Exact weak columns under the normal reflection on the actual inverse image. -/
theorem memW12_normalReflection_preimage {q : ℕ} {U : OpenDomain 3}
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q} (hu : MemW12 U u D) :
    MemW12 (⟨normalReflection ⁻¹' U.val,U.property.preimage normalReflection.continuous⟩ : OpenDomain 3)
      (u ∘ normalReflection) (fun x i => flatReflectionSign i • D (normalReflection x) i) := by
  let R := normalReflection.toContinuousLinearEquiv
  have h := memW12_continuousLinearEquiv_preimage R hu
  have hEq : (fun x i => ∑ j : Fin 3, (R (EuclideanSpace.single i 1)) j • D (R x) j) =
      (fun x i => flatReflectionSign i • D (normalReflection x) i) := by
    funext x i
    change (∑ j : Fin 3, (normalReflection (axis i)) j • D (normalReflection x) j) = _
    rw [normalReflection_axis]
    fin_cases i <;> simp [axis,flatReflectionSign]
  rw [hEq] at h
  exact h

private abbrev reflectedWeakLowerHalf : OpenDomain 3 := ⟨negativeWallHalf,isOpen_negativeWallHalf⟩
private abbrev reflectedWeakWholeSpace : OpenDomain 3 := ⟨univ,isOpen_univ⟩

private theorem normalReflection_mem_upper_iff_negative (x : Point) :
    normalReflection x ∈ upperCoordinateHalfSpace.val ↔ x ∈ negativeWallHalf := by
  change 0 < normalReflection x 2 ↔ x 2 < 0
  rw [normalReflection_height,neg_pos]

private theorem normalReflection_mem_negative_iff_upper (x : Point) :
    normalReflection x ∈ negativeWallHalf ↔ x ∈ upperCoordinateHalfSpace.val := by
  change normalReflection x 2 < 0 ↔ 0 < x 2
  rw [normalReflection_height,neg_lt_zero]

private theorem memW12_normalReflection_lower {q : ℕ}
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 upperCoordinateHalfSpace u D) :
    MemW12 reflectedWeakLowerHalf (u ∘ normalReflection)
      (fun x i => flatReflectionSign i • D (normalReflection x) i) := by
  have h := memW12_normalReflection_preimage hu
  have he : (⟨normalReflection ⁻¹' upperCoordinateHalfSpace.val,
      upperCoordinateHalfSpace.property.preimage normalReflection.continuous⟩ : OpenDomain 3) = reflectedWeakLowerHalf :=
    Subtype.ext (Set.ext fun x => normalReflection_mem_upper_iff_negative x)
  rwa [he] at h

private theorem memW12_normalReflection_whole {q : ℕ}
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 reflectedWeakWholeSpace u D) :
    MemW12 reflectedWeakWholeSpace (u ∘ normalReflection)
      (fun x i => flatReflectionSign i • D (normalReflection x) i) := by
  have h := memW12_normalReflection_preimage hu
  have he : (⟨normalReflection ⁻¹' reflectedWeakWholeSpace.val,
      reflectedWeakWholeSpace.property.preimage normalReflection.continuous⟩ : OpenDomain 3) = reflectedWeakWholeSpace :=
    Subtype.ext (preimage_univ : normalReflection ⁻¹' (univ : Set Point) = univ)
  rwa [he] at h

/-- Even reflection of a field on the positive side, with zero value on the null plane. -/
@[expose] def evenFlatWallWeakValue {q : ℕ} (u : Point → Ambient q) (x : Point) : Ambient q :=
  upperCoordinateHalfSpace.val.indicator u x +
    upperCoordinateHalfSpace.val.indicator u (normalReflection x)

/-- Reflected gradient columns for even reflection. The normal column is odd. -/
@[expose] def evenFlatWallWeakColumns {q : ℕ} (D : Point → HarmonicMaps.Gradient 3 q)
    (x : Point) (i : Fin 3) : Ambient q :=
  upperCoordinateHalfSpace.val.indicator (fun y => D y i) x +
    flatReflectionSign i • upperCoordinateHalfSpace.val.indicator (fun y => D y i) (normalReflection x)

private theorem evenFlatWallWeak_eq_upper {q : ℕ} (u : Point → Ambient q)
    (D : Point → HarmonicMaps.Gradient 3 q) {x : Point} (hx : x ∈ upperCoordinateHalfSpace.val) :
    evenFlatWallWeakValue u x = u x ∧ evenFlatWallWeakColumns D x = D x := by
  have hxN : x ∉ negativeWallHalf := fun hy => lt_asymm (show 0 < x 2 from hx) hy
  have hR : normalReflection x ∉ upperCoordinateHalfSpace.val :=
    fun h => hxN ((normalReflection_mem_upper_iff_negative x).1 h)
  refine ⟨?_,funext fun i => ?_⟩
  · simp only [evenFlatWallWeakValue,indicator_of_mem hx,indicator_of_notMem hR,add_zero]
  · simp only [evenFlatWallWeakColumns,indicator_of_mem hx,indicator_of_notMem hR,smul_zero,add_zero]

/-- The even extension retains the original field on the open positive side. -/
theorem evenFlatWallWeakValue_eq_upper {q : ℕ} (u : Point → Ambient q) {x : Point}
    (hx : x ∈ upperCoordinateHalfSpace.val) : evenFlatWallWeakValue u x = u x :=
  (evenFlatWallWeak_eq_upper u (0 : Point → HarmonicMaps.Gradient 3 q) hx).1

private theorem evenFlatWallWeak_eq_lower {q : ℕ} (u : Point → Ambient q)
    (D : Point → HarmonicMaps.Gradient 3 q) {x : Point} (hx : x ∈ negativeWallHalf) :
    evenFlatWallWeakValue u x = u (normalReflection x) ∧
      evenFlatWallWeakColumns D x = fun i => flatReflectionSign i • D (normalReflection x) i := by
  have hxN : x ∉ upperCoordinateHalfSpace.val := fun hy => lt_asymm (show x 2 < 0 from hx) hy
  have hR := (normalReflection_mem_upper_iff_negative x).2 hx
  refine ⟨?_,funext fun i => ?_⟩
  · simp only [evenFlatWallWeakValue,indicator_of_mem hR,indicator_of_notMem hxN,zero_add]
  · simp only [evenFlatWallWeakColumns,indicator_of_mem hR,indicator_of_notMem hxN,zero_add]

private def reflectionRectangle (A : OpenDomain 2) (l r : ℝ) : OpenDomain 3 :=
  ⟨{x : Point | (normalCoordinateEquiv x).1 ∈ A.val ∧ (normalCoordinateEquiv x).2 0 ∈ Ioo l r},
    (A.property.preimage (continuous_fst.comp normalCoordinateEquiv.continuous)).inter
      (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp normalCoordinateEquiv.continuous)))⟩

private theorem normalCoordinateEquiv_height (x : Point) : (normalCoordinateEquiv x).2 0 = x 2 := rfl

private theorem normalCoordinateEquiv_normalReflection (x : Point) :
    normalCoordinateEquiv.symm ((normalCoordinateEquiv x).1,-(normalCoordinateEquiv x).2) =
      normalReflection x := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

private theorem ae_off_flat_wall : ∀ᵐ x ∂(volume : Measure Point), x 2 ≠ 0 := by
  rw [ae_iff]
  simpa only [not_ne_iff] using normal_plane_volume_zero

private theorem memW12_evenFlatWall_on_rectangle {q : ℕ} (A : OpenDomain 2)
    [IsFiniteMeasure ((volume : Measure (Domain 2)).restrict A.val)]
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 upperCoordinateHalfSpace u D) :
    ∃ δ : ℝ, 0 < δ ∧ MemW12 (reflectionRectangle A (-δ) δ)
      (evenFlatWallWeakValue u) (evenFlatWallWeakColumns D) := by
  have hPos₀ : MemW12 (reflectionRectangle A 0 1) u D :=
    memW12_restrict_openDomain hu (fun _ hx => hx.2.1)
  obtain ⟨T,hT,_⟩ := exists_unique_L2_trace_of_memW12_rectangle A (by norm_num : 0 < (1:ℝ)) hPos₀
  obtain ⟨δ,hδ,K,hK⟩ := exists_reflected_rectangle_weak_gluing A
    (by norm_num : 0 < (1:ℝ)) (by norm_num : 0 < (1:ℝ)) u u D D hPos₀ hPos₀ T T hT hT rfl
  let V := reflectionRectangle A (-δ) δ
  let w (y : Point) := if y 2 < 0 then u (normalReflection y) else u y
  have hw : MemW12 V w K := by
    let w₀ (y : Point) := if (normalCoordinateEquiv y).2 0 < 0 then
      u (normalCoordinateEquiv.symm ((normalCoordinateEquiv y).1,-(normalCoordinateEquiv y).2)) else u y
    have he : w₀ = w := by
      funext y
      simp only [w₀,w,normalCoordinateEquiv_height,normalCoordinateEquiv_normalReflection]
    change MemW12 V w₀ K at hK
    rwa [he] at hK
  let L : OpenDomain 3 := ⟨V.val∩negativeWallHalf,V.property.inter isOpen_negativeWallHalf⟩
  let R : OpenDomain 3 := ⟨V.val∩upperCoordinateHalfSpace.val,V.property.inter upperCoordinateHalfSpace.property⟩
  have hKR : K =ᵐ[volume.restrict R.val] D := by
    have hwR := memW12_restrict_openDomain (V := R) hw inter_subset_left
    have huR := memW12_restrict_openDomain (V := R) hu inter_subset_right
    apply hwR.1.ae_eq_of_ae_eq_map huR.1
    filter_upwards [ae_restrict_mem R.property.measurableSet] with y hy
    exact if_neg (not_lt_of_gt (show 0 < y 2 from hy.2))
  have hKL : K =ᵐ[volume.restrict L.val] fun y i => flatReflectionSign i • D (normalReflection y) i := by
    have hwL := memW12_restrict_openDomain (V := L) hw inter_subset_left
    have huL := memW12_restrict_openDomain (V := L) (memW12_normalReflection_lower hu) inter_subset_right
    apply hwL.1.ae_eq_of_ae_eq_map huL.1
    filter_upwards [ae_restrict_mem L.property.measurableSet] with y hy
    exact if_pos hy.2
  have hKRa := (ae_restrict_iff' R.property.measurableSet).1 hKR
  have hKLa := (ae_restrict_iff' L.property.measurableSet).1 hKL
  have hA : ∀ᵐ y ∂volume, y ∈ V.val →
      w y = evenFlatWallWeakValue u y ∧ K y = evenFlatWallWeakColumns D y := by
    filter_upwards [hKRa,hKLa,ae_off_flat_wall] with y hyR hyL hy₀ hyV
    rcases lt_or_gt_of_ne hy₀ with hy | hy
    · obtain ⟨hW,hD⟩ := evenFlatWallWeak_eq_lower u D hy
      exact ⟨(if_pos hy).trans hW.symm,(hyL ⟨hyV,hy⟩).trans hD.symm⟩
    · obtain ⟨hW,hD⟩ := evenFlatWallWeak_eq_upper u D hy
      exact ⟨(if_neg (not_lt_of_gt hy)).trans hW.symm,(hyR ⟨hyV,hy⟩).trans hD.symm⟩
  have hAE := (ae_restrict_iff' V.property.measurableSet).2 hA
  exact ⟨δ,hδ,hw.congr_ae (hAE.mono fun _ h => h.1) (hAE.mono fun _ h => h.2)⟩

/-- An arbitrary half-space Sobolev graph extends evenly with its exact reflected columns. -/
theorem memW12_evenFlatWallWeakReflection {q : ℕ} {u : Point → Ambient q}
    {D : Point → HarmonicMaps.Gradient 3 q} (hu : MemW12 upperCoordinateHalfSpace u D) :
    MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (evenFlatWallWeakValue u) (evenFlatWallWeakColumns D) := by
  let S := upperCoordinateHalfSpace.val
  have hS : MeasurableSet S := upperCoordinateHalfSpace.property.measurableSet
  have hR := normalReflection.measurePreserving
  have hu₀ : MemLp (S.indicator u) 2 volume := (memLp_indicator_iff_restrict hS).2 hu.2.1
  have hDu₀ (i : Fin 3) : MemLp (S.indicator (fun x => D x i)) 2 volume :=
    (memLp_indicator_iff_restrict hS).2 (hu.2.2 i)
  have huLp : MemLp (evenFlatWallWeakValue u) 2 volume := hu₀.add (hu₀.comp_measurePreserving hR)
  have hDLp (i : Fin 3) : MemLp (fun x => evenFlatWallWeakColumns D x i) 2 volume :=
    (hDu₀ i).add (((hDu₀ i).comp_measurePreserving hR).const_smul (flatReflectionSign i))
  have hRight : MemW12 upperCoordinateHalfSpace (evenFlatWallWeakValue u) (evenFlatWallWeakColumns D) := by
    have hAE := (ae_restrict_mem (μ := (volume : Measure Point)) hS).mono fun _ hx => evenFlatWallWeak_eq_upper u D hx
    exact hu.congr_ae (hAE.mono fun _ h => h.1.symm) (hAE.mono fun _ h => h.2.symm)
  have hLeft : MemW12 reflectedWeakLowerHalf (evenFlatWallWeakValue u) (evenFlatWallWeakColumns D) := by
    have hAE := (ae_restrict_mem (μ := (volume : Measure Point)) isOpen_negativeWallHalf.measurableSet).mono fun _ hx =>
      evenFlatWallWeak_eq_lower u D hx
    exact (memW12_normalReflection_lower hu).congr_ae (hAE.mono fun _ h => h.1.symm)
      (hAE.mono fun _ h => h.2.symm)
  apply memW12_of_local_sobolev_pair
    (show MemLp (evenFlatWallWeakValue u) 2 (volume.restrict univ) from by rwa [Measure.restrict_univ])
    (fun i => show MemLp (fun x => evenFlatWallWeakColumns D x i) 2 (volume.restrict univ) from by
      simpa only [Measure.restrict_univ] using hDLp i)
  intro x _
  have hLocal : ∃ V : OpenDomain 3, x ∈ V.val ∧
      MemW12 V (evenFlatWallWeakValue u) (evenFlatWallWeakColumns D) := by
    rcases lt_trichotomy (x 2) (0:ℝ) with h | h | h
    · exact ⟨reflectedWeakLowerHalf,h,hLeft⟩
    · let A : OpenDomain 2 := ⟨ball (normalCoordinateEquiv x).1 1,isOpen_ball⟩
      letI : IsFiniteMeasure (volume.restrict A.val) := isFiniteMeasure_restrict.2 measure_ball_ne_top
      obtain ⟨δ,hδ,hW⟩ := memW12_evenFlatWall_on_rectangle A hu
      refine ⟨reflectionRectangle A (-δ) δ,⟨mem_ball_self one_pos,?_⟩,hW⟩
      rw [normalCoordinateEquiv_height,h]
      exact ⟨neg_lt_zero.mpr hδ,hδ⟩
    · exact ⟨upperCoordinateHalfSpace,h,hRight⟩
  obtain ⟨V,hxV,hV⟩ := hLocal
  obtain ⟨r,hr,hSub⟩ := Metric.isOpen_iff.1 V.property x hxV
  exact ⟨r,hr,subset_univ _,memW12_restrict_openDomain hV hSub⟩

private theorem memW12_gradient_zeroExtended_of_off_upper_zero {q : ℕ}
    {u : Point → Ambient q} {D E : Point → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 reflectedWeakWholeSpace u E) (hU : MemW12 upperCoordinateHalfSpace u D)
    (hZero : ∀ x ∉ upperCoordinateHalfSpace.val, u x = 0) :
    MemW12 reflectedWeakWholeSpace u (fun x j => upperCoordinateHalfSpace.val.indicator (fun y => D y j) x) := by
  have hRight : E =ᵐ[volume.restrict upperCoordinateHalfSpace.val] D :=
    (memW12_restrict_openDomain hu (subset_univ _)).1.ae_eq hU.1
  have hLeft : E =ᵐ[volume.restrict reflectedWeakLowerHalf.val] (0 : Point → HarmonicMaps.Gradient 3 q) := by
    have huL := memW12_restrict_openDomain (V := reflectedWeakLowerHalf) hu (subset_univ _)
    apply huL.1.ae_eq_of_ae_eq_map (MemW12.zero reflectedWeakLowerHalf).1
    filter_upwards [ae_restrict_mem reflectedWeakLowerHalf.property.measurableSet] with x hx
    exact hZero x (fun hy => lt_asymm (show x 2 < 0 from hx) hy)
  have hRight' := (ae_restrict_iff' upperCoordinateHalfSpace.property.measurableSet).1 hRight
  have hLeft' := (ae_restrict_iff' reflectedWeakLowerHalf.property.measurableSet).1 hLeft
  apply hu.congr_ae EventuallyEq.rfl
  simp only [Measure.restrict_univ]
  filter_upwards [hRight',hLeft',ae_off_flat_wall] with x hxR hxL hx₀
  rcases lt_or_gt_of_ne hx₀ with hx | hx
  · funext j
    have hxN : x ∉ upperCoordinateHalfSpace.val := fun h => lt_asymm hx h
    rw [indicator_of_notMem hxN]
    exact congrFun (hxL hx) j
  · funext j
    rw [indicator_of_mem (show x ∈ upperCoordinateHalfSpace.val from hx)]
    exact congrFun (hxR hx) j

/-- Odd reflection of the original zero-extended weak value. -/
@[expose] def oddFlatWallWeakValue {q : ℕ} (u : Point → Ambient q) (x : Point) : Ambient q :=
  u x-u (normalReflection x)

/-- The tangential weak columns reflect oddly and the normal column evenly. -/
@[expose] def oddFlatWallWeakColumns {q : ℕ} (D : Point → HarmonicMaps.Gradient 3 q)
    (x : Point) (i : Fin 3) : Ambient q := D x i-flatReflectionSign i • D (normalReflection x) i

/-- A weak Hessian entry reflects with a sign for each normal index and for the odd field. -/
@[expose] def oddFlatWallWeakHessian {q : ℕ} (H : Point → Fin 3 → HarmonicMaps.Gradient 3 q)
    (x : Point) (i j : Fin 3) : Ambient q :=
  upperCoordinateHalfSpace.val.indicator (fun y => H y i j) x -
    (flatReflectionSign i*flatReflectionSign j) •
      upperCoordinateHalfSpace.val.indicator (fun y => H y i j) (normalReflection x)

/-- The original upper-side values of every displayed Hessian row are preserved. -/
theorem oddFlatWallWeakHessian_eq_upper {q : ℕ} (H : Point → Fin 3 → HarmonicMaps.Gradient 3 q)
    {x : Point} (hx : x ∈ upperCoordinateHalfSpace.val) : oddFlatWallWeakHessian H x = H x := by
  have hR : normalReflection x ∉ upperCoordinateHalfSpace.val := fun h =>
    lt_asymm (show 0 < x 2 from hx) ((normalReflection_mem_upper_iff_negative x).1 h)
  funext i j
  simp only [oddFlatWallWeakHessian,indicator_of_mem hx,indicator_of_notMem hR,smul_zero,sub_zero]

/-- The second weak derivatives on the opposite half are the reflected upper entries. -/
theorem oddFlatWallWeakHessian_eq_lower {q : ℕ} (H : Point → Fin 3 → HarmonicMaps.Gradient 3 q)
    {x : Point} (hx : x ∈ negativeWallHalf) (i j : Fin 3) : oddFlatWallWeakHessian H x i j =
      -(flatReflectionSign i*flatReflectionSign j) • H (normalReflection x) i j := by
  have hN : x ∉ upperCoordinateHalfSpace.val := fun h => lt_asymm (show x 2 < 0 from hx) h
  have hR := (normalReflection_mem_upper_iff_negative x).2 hx
  rw [oddFlatWallWeakHessian,indicator_of_notMem hN,indicator_of_mem hR,zero_sub,neg_smul]

/-- The odd reflection of the original zero-extended solution has the exact
second weak graph, using the full H¹ tangential columns and the half-space
H¹ graph of the normal column. -/
theorem memW12_oddFlatWallWeakHessian_reflection {q : ℕ}
    {u : Point → Ambient q} {D : Point → HarmonicMaps.Gradient 3 q}
    {H : Point → Fin 3 → HarmonicMaps.Gradient 3 q}
    (hu : MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) u D)
    (hD₀ : ∀ x ∉ upperCoordinateHalfSpace.val, D x = 0)
    (hUpper : ∀ i, MemW12 upperCoordinateHalfSpace (fun x => D x i) (fun x => H x i))
    (hTangential : ∀ i ≠ (2 : Fin 3), ∃ T : Point → HarmonicMaps.Gradient 3 q,
      MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (fun x => D x i) T) :
    MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3) (oddFlatWallWeakValue u) (oddFlatWallWeakColumns D) ∧
      ∀ i, MemW12 (⟨univ,isOpen_univ⟩ : OpenDomain 3)
        (fun x => oddFlatWallWeakColumns D x i) (fun x => oddFlatWallWeakHessian H x i) := by
  refine ⟨hu.sub (memW12_normalReflection_whole hu),?_⟩
  intro i
  by_cases hi : i=2
  · subst i
    have hGraph := memW12_evenFlatWallWeakReflection (hUpper 2)
    have hI : upperCoordinateHalfSpace.val.indicator (fun x => D x 2) = fun x => D x 2 := by
      funext x
      by_cases hx : x ∈ upperCoordinateHalfSpace.val
      · exact indicator_of_mem hx _
      · rw [indicator_of_notMem hx,hD₀ x hx,Pi.zero_apply]
    have hVal : evenFlatWallWeakValue (fun x => D x 2) = fun x => oddFlatWallWeakColumns D x 2 := by
      funext x
      simp only [evenFlatWallWeakValue,hI,oddFlatWallWeakColumns,flatReflectionSign_normal,
        neg_one_smul,sub_neg_eq_add]
    have hCols : evenFlatWallWeakColumns (fun x => H x 2) = fun x => oddFlatWallWeakHessian H x 2 := by
      funext x j
      simp only [evenFlatWallWeakColumns,oddFlatWallWeakHessian,flatReflectionSign_normal,
        neg_one_mul,neg_smul,sub_neg_eq_add]
    rwa [hVal,hCols] at hGraph
  · obtain ⟨T,hT⟩ := hTangential i hi
    have hX := memW12_gradient_zeroExtended_of_off_upper_zero hT (hUpper i)
      (fun x hx => congrFun (hD₀ x hx) i)
    have hGraph := hX.sub (memW12_normalReflection_whole hX)
    let H₀ (x : Point) (j : Fin 3) := upperCoordinateHalfSpace.val.indicator (fun y => H y i j) x
    have hValue : ((fun x => D x i) - (fun x => D x i) ∘ normalReflection) =
        fun x => oddFlatWallWeakColumns D x i := by
      funext x
      simp only [Pi.sub_apply,Function.comp_apply,oddFlatWallWeakColumns,flatReflectionSign_tangential hi,one_smul]
    have hCols : (fun x j => H₀ x j-flatReflectionSign j • H₀ (normalReflection x) j) =
        fun x => oddFlatWallWeakHessian H x i := by
      funext x j
      simp only [H₀,oddFlatWallWeakHessian,flatReflectionSign_tangential hi,one_mul]
    change MemW12 reflectedWeakWholeSpace ((fun x => D x i) - (fun x => D x i) ∘ normalReflection)
      (fun x j => H₀ x j-flatReflectionSign j • H₀ (normalReflection x) j) at hGraph
    rwa [hValue,hCols] at hGraph

end Thesis

end
