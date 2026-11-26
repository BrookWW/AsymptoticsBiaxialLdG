module

public import Thesis.Interpolation.SphericalShellAngular
public import Thesis.Interpolation.SphericalShellBudgets
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import StratificationTheory.Foundation.UnitCubeAffineCoordinates

/-! The actual cap L² classes obtained by transporting and adding the original face curves. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal Topology Matrix.Norms.Frobenius

namespace Thesis

private theorem exists_L2Curve_pullback_of_map_le_smul {T X Y E : Type*} [TopologicalSpace T]
    [MeasurableSpace X] [MeasurableSpace Y] [NormedAddCommGroup E]
    {μ : Measure X} {ν : Measure Y} {F : X → Y} (hF : Measurable F)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hMap : Measure.map F μ ≤ c • ν) (H : C(T, Lp E 2 ν)) :
    ∃ K : C(T, Lp E 2 μ), ∀ t, (K t : X → E) =ᵐ[μ] fun x => H t (F x) := by
  have hMem (t : T) : MemLp (fun x => H t (F x)) 2 μ :=
    (((Lp.memLp (H t)).of_measure_le_smul hc hMap).comp_of_map hF.aemeasurable)
  let K₀ (t : T) := (hMem t).toLp (fun x => H t (F x))
  have hCont : Continuous K₀ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun s : T => fun x => H s (F x)) hMem
      (fun x => H t (F x)) (hMem t)).mpr
    have hLim : Tendsto (fun s : T => eLpNorm (fun y => H s y - H t y) 2 ν) (𝓝 t) (𝓝 0) :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun s : T => H s) (H t)).mp (H.continuous.tendsto t)
    let C := c ^ (1 / (2 : ℝ≥0∞)).toReal
    have hC : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hc
    have hLim' := ENNReal.Tendsto.const_mul hLim (Or.inr hC)
    rw [mul_zero] at hLim'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLim' (fun _ => zero_le) (fun s => ?_)
    have hm := ((Lp.memLp (H s)).sub (Lp.memLp (H t))).of_measure_le_smul hc hMap
    have hp : eLpNorm (fun x => H s (F x) - H t (F x)) 2 μ =
        eLpNorm (fun y => H s y - H t y) 2 (Measure.map F μ) :=
      (eLpNorm_map_measure hm.aestronglyMeasurable hF.aemeasurable).symm
    change eLpNorm (fun x => H s (F x) - H t (F x)) 2 μ ≤ _
    rw [hp]
    exact eLpNorm_le_of_measure_le_smul hMap
  exact ⟨⟨K₀, hCont⟩, fun t => (hMem t).coeFn_toLp⟩

private theorem exists_L2Curve_indicator_extension {T X E : Type*} [TopologicalSpace T] [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {S : Set X} (hS : MeasurableSet S)
    (H : C(T, Lp E 2 (μ.restrict S))) :
    ∃ K : C(T, Lp E 2 μ), ∀ t, (K t : X → E) =ᵐ[μ] S.indicator (H t) := by
  have hMem (t : T) : MemLp (S.indicator (H t : X → E)) 2 μ :=
    (memLp_indicator_iff_restrict hS).mpr (Lp.memLp (H t))
  let K₀ (t : T) := (hMem t).toLp _
  have hCont : Continuous K₀ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun s : T => S.indicator (H s : X → E)) hMem _ (hMem t)).mpr
    have hLim : Tendsto (fun s : T => eLpNorm (fun x => H s x - H t x) 2 (μ.restrict S)) (𝓝 t) (𝓝 0) :=
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun s : T => H s) (H t)).mp (H.continuous.tendsto t)
    have hEq (s : T) : S.indicator (H s : X → E) - S.indicator (H t : X → E) =
        S.indicator (fun x => H s x - H t x) := by
      funext x
      by_cases hx : x ∈ S <;> simp [hx]
    simpa only [hEq, eLpNorm_indicator_eq_eLpNorm_restrict hS] using hLim
  exact ⟨⟨K₀, hCont⟩, fun t => (hMem t).coeFn_toLp⟩

private theorem exists_L2Curve_merge_disjoint {T X E J : Type*} [TopologicalSpace T] [MeasurableSpace X]
    [NormedAddCommGroup E] [Fintype J] {μ : Measure X} (S : J → Set X)
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) (hm : ∀ j, MeasurableSet (S j))
    (H : ∀ j, C(T, Lp E 2 (μ.restrict (S j)))) :
    ∃ K : C(T, Lp E 2 μ), ∀ j t, (K t : X → E) =ᵐ[μ.restrict (S j)] (H j t : X → E) := by
  classical
  have hEach (j : J) := exists_L2Curve_indicator_extension (hm j) (H j)
  choose F hF using hEach
  let K : C(T, Lp E 2 μ) := ∑ j, F j
  refine ⟨K, fun j t => ?_⟩
  have hEval : (K t : X → E) =ᵐ[μ] fun x => ∑ i : J, F i t x := by
    have h : K t = ∑ i : J, F i t := by simp only [K, ContinuousMap.sum_apply]
    rw [h]
    exact Lp.coeFn_fun_finsetSum _ _
  filter_upwards [ae_restrict_of_ae hEval, ae_restrict_of_ae (ae_all_iff.mpr fun i => hF i t), ae_restrict_mem (hm j)]
    with x hVal hFx hx
  rw [hVal]
  simp_rw [hFx]
  rw [Finset.sum_eq_single j]
  · exact indicator_of_mem hx _
  · intro i _ hi
    exact indicator_of_notMem (fun hx' => Set.disjoint_left.mp (hd hi) hx' hx) _
  · exact fun hf => (hf (Finset.mem_univ j)).elim

private theorem ae_of_ae_restrict_cover {X J : Type*} [MeasurableSpace X] [Fintype J]
    {μ : Measure X} (S : J → Set X) (hm : ∀ j, MeasurableSet (S j))
    (hCover : ∀ᵐ x ∂μ, ∃ j, x ∈ S j) {P : X → Prop}
    (hEach : ∀ j, ∀ᵐ x ∂μ.restrict (S j), P x) : ∀ᵐ x ∂μ, P x := by
  have hAll : ∀ᵐ x ∂μ, ∀ j, x ∈ S j → P x := ae_all_iff.mpr (fun j => (ae_restrict_iff' (hm j)).mp (hEach j))
  filter_upwards [hAll, hCover] with x hP hx
  obtain ⟨j, hj⟩ := hx
  exact hP j hj

private theorem shellCapRadius_mem_open {h : ℝ} (hh : 0 < h) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    shellCapRadius h t ∈ Ioo (1 - h) 1 := by
  have hL : 0 < (h / 2) * (t + 1) := mul_pos (half_pos hh) (by linarith only [ht.1])
  have hR : 0 < (h / 2) * (1 - t) := mul_pos (half_pos hh) (by linarith only [ht.2])
  unfold shellCapRadius
  exact ⟨by nlinarith only [hL], by nlinarith only [hR]⟩

private theorem shellCap_slice_mem_cell {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32)) (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    (f : ShellCellIndex m) {s : Domain 2} (hs : s ∈ (unitCellCube 2).val) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    shellCapRadius h t • shellCapAngularPoint c h f.val s ∈ (sphericalCellOpenDomain c h f.val).val := by
  change _ ∈ interior (sphericalClosedCell c h f.val)
  rw [sphericalClosedCell_interior hh' hc hm f.property]
  let p := unitToPhysicalCellFace h s
  have hp := unitToPhysicalCellFace_open_box hh hs
  exact ⟨((p 0, p 1), shellCapRadius h t),
    ⟨⟨mem_iInter.mp hp 0, mem_iInter.mp hp 1⟩, shellCapRadius_mem_open hh ht⟩, rfl⟩

variable {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}
variable {G : PenalizedSphereFaces a B h v hv}
variable {I : ∀ f : ShellCellIndex G.grid.level, ProjectedCellInnerFace G f}

/-- The original cap traces assembled on the true unit sphere, before
rescaling their common interval to the physical radii. -/
structure NormalizedShellCapClasses (W : PenalizedFilledShell G I) where
  chart : ∀ f : ShellCellIndex G.grid.level, ShellAngularInverse G.grid.center h f.val
  curve : C(Icc (-1 : ℝ) 1, Lp (Ambient 5) 2 tensorSphereMeasure)
  pulls : ∀ f t, (curve t : UnitTensorSphere → Ambient 5)
    =ᵐ[tensorSphereMeasure.restrict (shellAngularSpherePatch G.grid.center h f.val)]
      fun θ => (W.cell f).unit.trace 2 t ((chart f).inverse θ.val)
  slice : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
    (curve ⟨t, ht.1.le, ht.2.le⟩ : UnitTensorSphere → Ambient 5) =ᵐ[tensorSphereMeasure]
      fun θ => sphericalShellPiecewiseField G.grid.center h (fun f => (W.cell f).field) (shellCapRadius h t • θ.val)
  outer : curve ⟨1, by norm_num, le_rfl⟩ = hv.1.toLp (fun θ => frobeniusCoordinateEquiv (v θ))
  inner : ∀ f,
    (curve ⟨-1, le_rfl, by norm_num⟩ : UnitTensorSphere → Ambient 5)
      =ᵐ[tensorSphereMeasure.restrict (shellAngularSpherePatch G.grid.center h f.val)]
        fun θ => (I f).field (unitToPhysicalCellFace h ((chart f).inverse θ.val))

/-- Transport all original cap curves through their actual angular
coordinates, preserving the native upper class and all native inner faces. -/
theorem exists_normalizedShellCapClasses (W : PenalizedFilledShell G I) (hSmall : h ≤ 1 / 32) :
    Nonempty (NormalizedShellCapClasses W) := by
  classical
  let c := G.grid.center
  let J := ShellCellIndex G.grid.level
  let F (f : J) := shellAngularSpherePatch c h f.val
  let μ := (volume : Measure (Domain 2)).restrict (unitCellCube 2).val
  let T := Icc (-1 : ℝ) 1
  have hh := G.ht_pos
  have hh' : h ≤ 1 / 2 := hSmall.trans (by norm_num)
  have hc (i : Fin 3) : c i ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(G.grid.offset_mem i).1, (G.grid.offset_mem i).2.le.trans hSmall⟩
  have hm := G.grid.radius_mem
  let A (f : J) := Classical.choice (exists_shellAngularInverse hh hc hm f.property)
  let inverse (f : J) : UnitTensorSphere → Domain 2 := (A f).inverse ∘ Subtype.val
  let H (f : J) : C(T, Lp (Ambient 5) 2 μ) := (W.cell f).unit.trace 2
  have hP (f : J) : MeasurableSet (F f) := (A f).patch_measurable.preimage measurable_subtype_coe
  have hCover : ∀ᵐ θ ∂tensorSphereMeasure, ∃ f : J, θ ∈ F f := ae_shellAngularSpherePatch_cover hh hc hm
  have hMap (f : J) : Measure.map (inverse f) (tensorSphereMeasure.restrict (F f)) ≤ ENNReal.ofReal ((32 * h) ^ 2) • μ :=
    (A f).map_sphere_measure (shellAngularPatch_subset_sphere hh hc hm f.property)
  have hM (f : J) : Measurable (inverse f) := (A f).measurable.comp measurable_subtype_coe
  have hQ (f : J) : Measure.QuasiMeasurePreserving (inverse f) (tensorSphereMeasure.restrict (F f)) μ :=
    ⟨hM f, Measure.absolutelyContinuous_of_le_smul (hMap f)⟩
  have hPull (f : J) := exists_L2Curve_pullback_of_map_le_smul (hM f) ENNReal.ofReal_ne_top (hMap f) (H f)
  choose K hK using hPull
  obtain ⟨C, hC⟩ := exists_L2Curve_merge_disjoint F (pairwiseDisjoint_shellAngularSpherePatch hh hh' hc hm) hP K
  have hEq (f : J) (t : T) : (C t : UnitTensorSphere → Ambient 5)
      =ᵐ[tensorSphereMeasure.restrict (F f)] fun θ => H f t (inverse f θ) :=
    (hC f t).trans (hK f t)
  refine ⟨{ chart := A
            curve := C
            pulls := hEq
            slice := ?_
            outer := ?_
            inner := ?_ }⟩
  · have hSlices := ae_all_iff.mpr (fun f : J => (W.cell f).trace_slice (2 : Fin 3))
    filter_upwards [hSlices] with t hSlices ht
    let τ : T := ⟨t, ht.1.le, ht.2.le⟩
    apply ae_of_ae_restrict_cover F hP hCover
    intro f
    obtain ⟨hs, hF⟩ := hSlices f ht
    have hF' : (H f τ : Domain 2 → Ambient 5) =ᵐ[μ]
        fun x => (W.cell f).field (normalizedShellCellPoint c h f.val (unitCellFacePoint (2, true) x t)) := by
      change (H f τ) = _ at hF
      rw [hF]
      exact hs.coeFn_toLp
    refine (hEq f τ).trans (Filter.EventuallyEq.trans ((hQ f).ae hF') ?_)
    filter_upwards [ae_restrict_mem (hP f)] with θ hθ
    let x := inverse f θ
    have hX : x ∈ (unitCellCube 2).val := (A f).inverse_mem θ.val hθ
    have hΘ : shellCapAngularPoint c h f.val x = θ.val := (A f).right_inv θ.val hθ
    have hy : shellCapRadius h t • θ.val ∈ (sphericalCellOpenDomain c h f.val).val := by
      rw [← hΘ]
      exact shellCap_slice_mem_cell hh hh' hc hm f hX ht
    change (W.cell f).field (normalizedShellCellPoint c h f.val (unitCellFacePoint (2, true) x t)) = _
    rw [normalizedShellCellPoint_cap_slice, hΘ]
    exact (sphericalShellPiecewise_eq_on_cell hh hh' hc hm (fun f => (W.cell f).field)
      (fun f => (W.cell f).derivative) f hy).1.symm
  · apply Lp.ext
    refine Filter.EventuallyEq.trans (ae_of_ae_restrict_cover F hP hCover (P := fun θ => C ⟨1, by norm_num, le_rfl⟩ θ =
      frobeniusCoordinateEquiv (v θ)) ?_) hv.1.coeFn_toLp.symm
    intro f
    let τ : T := ⟨1, by norm_num, le_rfl⟩
    have hF' : (H f τ : Domain 2 → Ambient 5) =ᵐ[μ] ((W.faceFamily f).toUnit hh).face (2, true) :=
      (W.cell f).unit.trace_end 2 true
    refine (hEq f τ).trans (Filter.EventuallyEq.trans ((hQ f).ae hF') ?_)
    filter_upwards [ae_restrict_mem (hP f)] with θ hθ
    let x := inverse f θ
    let z := unitToPhysicalCellFace h x
    have hX : x ∈ (unitCellCube 2).val := (A f).inverse_mem θ.val hθ
    have hz : z ∈ (tensorGridOpenParameterBox 2 h).val := unitToPhysicalCellFace_open_box hh hX
    obtain ⟨η, hη, hVal⟩ := G.face_eq f z (Ioo_subset_Icc_self (mem_iInter.mp hz 0)) (Ioo_subset_Icc_self (mem_iInter.mp hz 1))
    have hΘ : shellCapAngularPoint c h f.val x = θ.val := (A f).right_inv θ.val hθ
    have hEta : η = θ := Subtype.ext (hη.trans hΘ)
    change ((W.faceFamily f).toUnit hh).face (2, true) x = _
    rw [(W.faceFamily f).toUnit_face, Function.comp_apply, W.face_eq]
    change frobeniusCoordinateEquiv (G.face f z) = _
    rw [hVal, hEta]
  · intro f
    let τ : T := ⟨-1, le_rfl, by norm_num⟩
    have hF' : (H f τ : Domain 2 → Ambient 5) =ᵐ[μ] ((W.faceFamily f).toUnit hh).face (2, false) :=
      (W.cell f).unit.trace_end 2 false
    refine (hEq f τ).trans (Filter.EventuallyEq.trans ((hQ f).ae hF') ?_)
    apply Eventually.of_forall
    intro θ
    change ((W.faceFamily f).toUnit hh).face (2, false) (inverse f θ) = _
    rw [(W.faceFamily f).toUnit_face, Function.comp_apply, W.face_eq]
    rfl

/-- The true radial L² trace of the global shell graph, including the
original outer sphere class and the actual compatible vacuum inner classes. -/
structure PhysicalShellCapClasses (W : PenalizedFilledShell G I) where
  normalized : NormalizedShellCapClasses W
  trace : RadialL2Trace (1 - h) 1
  represents : RepresentsRadialL2Trace 0 W.tensorField trace
  outer : trace ⟨1, sub_le_self _ G.ht_pos.le, le_rfl⟩ = hv.1.toLp (fun θ => frobeniusCoordinateEquiv (v θ))
  inner_eq : trace ⟨1 - h, le_rfl, sub_le_self _ G.ht_pos.le⟩ = normalized.curve ⟨-1, le_rfl, by norm_num⟩
  vacuum_ae : ∀ᵐ θ ∂tensorSphereMeasure,
    frobeniusCoordinateEquiv.symm ((trace ⟨1 - h, le_rfl, sub_le_self _ G.ht_pos.le⟩) θ) ∈ vacuum a

private noncomputable def shellCapTime (h r : ℝ) : ℝ := (h / 2)⁻¹ * (r - (1 - h / 2))

private theorem shellCapTime_eq_div (h r : ℝ) : shellCapTime h r = (r - (1 - h / 2)) / (h / 2) := by
  simp only [shellCapTime, div_eq_mul_inv, mul_comm]

private theorem shellCapTime_closed {h : ℝ} (hh : 0 < h) (r : Icc (1 - h) (1 : ℝ)) :
    shellCapTime h r.val ∈ Icc (-1 : ℝ) 1 := by
  rw [shellCapTime_eq_div]
  exact ⟨(le_div_iff₀ (half_pos hh)).mpr (by linarith only [r.property.1]),
    (div_le_iff₀ (half_pos hh)).mpr (by linarith only [r.property.2])⟩

private theorem shellCapTime_open {h : ℝ} (hh : 0 < h) {r : ℝ} (hr : r ∈ Ioo (1 - h) 1) :
    shellCapTime h r ∈ Ioo (-1 : ℝ) 1 := by
  rw [shellCapTime_eq_div]
  exact ⟨(lt_div_iff₀ (half_pos hh)).mpr (by linarith only [hr.1]),
    (div_lt_iff₀ (half_pos hh)).mpr (by linarith only [hr.2])⟩

private theorem shellCapRadius_time {h : ℝ} (hh : 0 < h) (r : ℝ) : shellCapRadius h (shellCapTime h r) = r := by
  unfold shellCapTime shellCapRadius
  rw [← mul_assoc, mul_inv_cancel₀ (half_pos hh).ne', one_mul]
  ring

private theorem shellCapTime_upper {h : ℝ} (hh : 0 < h) : shellCapTime h 1 = 1 := by
  rw [shellCapTime_eq_div, show (1 : ℝ) - (1 - h / 2) = h / 2 by ring, div_self (half_pos hh).ne']

private theorem shellCapTime_lower {h : ℝ} (hh : 0 < h) : shellCapTime h (1 - h) = -1 := by
  rw [shellCapTime_eq_div, show (1 - h) - (1 - h / 2) = -(h / 2) by ring, neg_div, div_self (half_pos hh).ne']

private theorem shellCapTime_quasiMeasurePreserving {h : ℝ} (hh : 0 < h) :
    Measure.QuasiMeasurePreserving (shellCapTime h) (volume : Measure ℝ) volume := by
  have hS := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero (half_pos hh).ne')
  have hA := (measurePreserving_add_right (volume : Measure ℝ) (-(1 - h / 2))).quasiMeasurePreserving
  have hComp := hS.comp hA
  convert hComp using 1
  funext r
  change (h / 2)⁻¹ * (r - (1 - h / 2)) = (h / 2)⁻¹ * (r + -(1 - h / 2))
  rw [← sub_eq_add_neg]

private noncomputable def shellCapTimeMap {h : ℝ} (hh : 0 < h) : C(Icc (1 - h) (1 : ℝ), Icc (-1 : ℝ) 1) :=
  ⟨fun r => ⟨shellCapTime h r.val, shellCapTime_closed hh r⟩,
    (((continuous_const : Continuous fun _ : ℝ => (h / 2)⁻¹).mul
      (continuous_id.sub continuous_const)).comp continuous_subtype_val).subtype_mk _⟩

private theorem representsRadialL2Trace_of_ae_classes {h : ℝ} {u : Point → S0} (H : RadialL2Trace (1 - h) 1)
    (hRaw : ∀ᵐ r : ℝ ∂volume, ∀ hr : r ∈ Ioo (1 - h) 1,
      (H ⟨r, hr.1.le, hr.2.le⟩ : UnitTensorSphere → Ambient 5) =ᵐ[tensorSphereMeasure]
        fun θ => frobeniusField u (0 + r • θ.val)) : RepresentsRadialL2Trace 0 u H := by
  unfold RepresentsRadialL2Trace
  filter_upwards [hRaw] with r hrRaw rI
  let t : Icc (1 - h) (1 : ℝ) := ⟨r, rI.1.le, rI.2.le⟩
  have hEq := hrRaw rI
  have hm := (Lp.memLp (H t)).ae_eq hEq
  refine ⟨hm, ?_⟩
  apply Lp.ext
  exact hEq.trans hm.coeFn_toLp.symm

private theorem represents_shellCapTimeMap {h : ℝ} (hh : 0 < h) {u : Point → S0} {w : Point → Ambient 5}
    (hField : frobeniusField u = w) (A : C(Icc (-1 : ℝ) 1, Lp (Ambient 5) 2 tensorSphereMeasure))
    (hRaw : ∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (-1 : ℝ) 1,
      (A ⟨t, ht.1.le, ht.2.le⟩ : UnitTensorSphere → Ambient 5) =ᵐ[tensorSphereMeasure]
        fun θ => w (shellCapRadius h t • θ.val)) :
    RepresentsRadialL2Trace 0 u (A.comp (shellCapTimeMap hh)) := by
  apply representsRadialL2Trace_of_ae_classes
  filter_upwards [(shellCapTime_quasiMeasurePreserving hh).ae hRaw] with r hr hrI
  let t : Icc (1 - h) (1 : ℝ) := ⟨r, hrI.1.le, hrI.2.le⟩
  change (A ⟨shellCapTime h r, shellCapTime_closed hh t⟩ : UnitTensorSphere → Ambient 5) =ᵐ[tensorSphereMeasure]
    fun θ => frobeniusField u (0 + r • θ.val)
  rw [hField]
  simpa only [shellCapRadius_time hh, zero_add] using hr (shellCapTime_open hh hrI)

private theorem NormalizedShellCapClasses.inner_vacuum_ae {W : PenalizedFilledShell G I}
    (A : NormalizedShellCapClasses W) (hSmall : h ≤ 1 / 32) :
    ∀ᵐ θ ∂tensorSphereMeasure, frobeniusCoordinateEquiv.symm (A.curve ⟨-1, le_rfl, by norm_num⟩ θ) ∈ vacuum a := by
  let c := G.grid.center
  let J := ShellCellIndex G.grid.level
  let F (f : J) := shellAngularSpherePatch c h f.val
  let μ := (volume : Measure (Domain 2)).restrict (unitCellCube 2).val
  let U := (tensorGridOpenParameterBox 2 h).val
  have hh := G.ht_pos
  have hCenter (i : Fin 3) : c i ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(G.grid.offset_mem i).1, (G.grid.offset_mem i).2.le.trans hSmall⟩
  have hCover : ∀ᵐ θ ∂tensorSphereMeasure, ∃ f : J, θ ∈ F f :=
    ae_shellAngularSpherePatch_cover hh hCenter G.grid.radius_mem
  have hMeas (f : J) : MeasurableSet (F f) := (A.chart f).patch_measurable.preimage measurable_subtype_coe
  have hAffineMeas : Measurable (unitToPhysicalCellFace h) := by unfold unitToPhysicalCellFace; fun_prop
  have hAff : Measure.map (unitToPhysicalCellFace h) μ =
      ENNReal.ofReal (((h / 2) ^ (2 : ℕ))⁻¹) • (volume : Measure (Domain 2)).restrict U :=
    StratificationTheory.map_affine_unit_cube_volume 2 hh
  have hQA : Measure.QuasiMeasurePreserving (unitToPhysicalCellFace h) μ ((volume : Measure (Domain 2)).restrict U) :=
    ⟨hAffineMeas, Measure.absolutelyContinuous_of_le_smul hAff.le⟩
  apply ae_of_ae_restrict_cover F hMeas hCover
  intro f
  have hMap := (A.chart f).map_sphere_measure (shellAngularPatch_subset_sphere hh hCenter G.grid.radius_mem f.property)
  have hQInv : Measure.QuasiMeasurePreserving ((A.chart f).inverse ∘ (Subtype.val : UnitTensorSphere → Point))
      (tensorSphereMeasure.restrict (F f)) μ :=
    ⟨(A.chart f).measurable.comp measurable_subtype_coe, Measure.absolutelyContinuous_of_le_smul hMap⟩
  have hIv := hQInv.ae (hQA.ae (I f).vacuum_ae)
  filter_upwards [A.inner f, hIv] with θ hθ hvac
  rw [hθ]
  exact hvac

/-- Rescale the same native cap curve onto the actual closed radial interval. -/
theorem exists_physicalShellCapClasses (W : PenalizedFilledShell G I) (hSmall : h ≤ 1 / 32) :
    Nonempty (PhysicalShellCapClasses W) := by
  obtain ⟨A⟩ := exists_normalizedShellCapClasses W hSmall
  have hh := G.ht_pos
  let H : RadialL2Trace (1 - h) 1 := A.curve.comp (shellCapTimeMap hh)
  have hOuter : H ⟨1, sub_le_self _ hh.le, le_rfl⟩ = hv.1.toLp (fun θ => frobeniusCoordinateEquiv (v θ)) := by
    change A.curve ⟨shellCapTime h 1, _⟩ = _
    rw [show (⟨shellCapTime h 1, shellCapTime_closed hh ⟨1, sub_le_self _ hh.le, le_rfl⟩⟩ : Icc (-1 : ℝ) 1) =
      ⟨1, by norm_num, le_rfl⟩ from Subtype.ext (shellCapTime_upper hh)]
    exact A.outer
  have hInner : H ⟨1 - h, le_rfl, sub_le_self _ hh.le⟩ = A.curve ⟨-1, le_rfl, by norm_num⟩ := by
    change A.curve ⟨shellCapTime h (1 - h), _⟩ = _
    apply congrArg A.curve (Subtype.ext (shellCapTime_lower hh))
  have hTrace := represents_shellCapTimeMap hh W.frobenius_tensorField A.curve A.slice
  exact ⟨⟨A, H, hTrace, hOuter, hInner, hInner.symm ▸ A.inner_vacuum_ae hSmall⟩⟩

/-- The cap's actual vacuum tensor representative comes from the same native
inner trace class on the sphere. -/
@[expose] noncomputable def PhysicalShellCapClasses.innerTensor {W : PenalizedFilledShell G I}
    (A : PhysicalShellCapClasses W) (θ : UnitTensorSphere) : S0 :=
  frobeniusCoordinateEquiv.symm ((A.trace ⟨1 - h, le_rfl, sub_le_self _ G.ht_pos.le⟩) θ)

theorem PhysicalShellCapClasses.innerTensor_memLp {W : PenalizedFilledShell G I} (A : PhysicalShellCapClasses W) :
    MemLp (fun θ => frobeniusCoordinateEquiv (A.innerTensor θ)) 2 tensorSphereMeasure := by
  have hEq : (fun θ => frobeniusCoordinateEquiv (A.innerTensor θ)) =
      (A.trace ⟨1 - h, le_rfl, sub_le_self _ G.ht_pos.le⟩ : UnitTensorSphere → Ambient 5) :=
    funext fun θ => frobeniusCoordinateEquiv.apply_symm_apply _
  rw [hEq]
  exact Lp.memLp _

theorem PhysicalShellCapClasses.innerTensor_eq_on_patch {W : PenalizedFilledShell G I} (A : PhysicalShellCapClasses W)
    (f : ShellCellIndex G.grid.level) :
    (fun θ => frobeniusCoordinateEquiv (A.innerTensor θ)) =ᵐ[tensorSphereMeasure.restrict (shellAngularSpherePatch G.grid.center h f.val)]
      fun θ => (I f).field (unitToPhysicalCellFace h ((A.normalized.chart f).inverse θ.val)) := by
  have hEq : (fun θ => frobeniusCoordinateEquiv (A.innerTensor θ)) =
      (A.trace ⟨1 - h, le_rfl, sub_le_self _ G.ht_pos.le⟩ : UnitTensorSphere → Ambient 5) :=
    funext fun θ => frobeniusCoordinateEquiv.apply_symm_apply _
  rw [hEq, A.inner_eq]
  exact A.normalized.inner f

end Thesis
