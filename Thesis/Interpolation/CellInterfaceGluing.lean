module

public import Thesis.Interpolation.SphericalCellInterfaces
import StratificationTheory.Foundation.CoordinateTraceWeakGluing
import StratificationTheory.Foundation.IsometricCoordinateTraceGluing
import StratificationTheory.Foundation.BoundedFiberL2Trace
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Weak gluing on one flat interface from the original continuous side values. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped Topology

namespace Thesis

/-- An open normal slab over an arbitrary open base in a Euclidean hyperplane. -/
@[expose] noncomputable def cellInterfaceSlab {n : ℕ} (U : OpenDomain n) (l r : ℝ) : OpenDomain (n + 1) :=
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  ⟨{z | (e z).1 ∈ U.val ∧ (e z).2 0 ∈ Ioo l r},
    (U.property.preimage (continuous_fst.comp e.continuous)).inter
      (isOpen_Ioo.preimage ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
        (continuous_snd.comp e.continuous)))⟩

/-- The same open base with both normal endpoints included. -/
@[expose] def cellInterfaceClosedSlab {n : ℕ} (U : OpenDomain n) (l r : ℝ) : Set (Domain (n + 1)) :=
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
  {z | (e z).1 ∈ U.val ∧ (e z).2 0 ∈ Icc l r}

/-- The native Euclidean point with tangential parameter `x` and normal
coordinate `t`. -/
@[expose] noncomputable def cellInterfacePoint {n : ℕ} (x : Domain n) (t : ℝ) : Domain (n + 1) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm
    (x, EuclideanSpace.single 0 t)

private theorem cellInterfacePoint_mem_closedSlab {n : ℕ} {U : OpenDomain n} {l r t : ℝ} {x : Domain n}
    (hx : x ∈ U.val) (ht : t ∈ Icc l r) : cellInterfacePoint x t ∈ cellInterfaceClosedSlab U l r := by
  simp only [cellInterfacePoint, cellInterfaceClosedSlab, ContinuousLinearEquiv.apply_symm_apply,
    mem_setOf_eq, PiLp.single_apply, ite_true]
  exact ⟨hx, ht⟩

private theorem continuous_cellInterfacePoint {n : ℕ} :
    Continuous (fun p : Domain n × ℝ => cellInterfacePoint p.1 p.2) := by
  have hSingle : Continuous (fun t : ℝ => EuclideanSpace.single (0 : Fin 1) t) := by
    have hEq (t : ℝ) : EuclideanSpace.single (0 : Fin 1) t = t • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
      apply PiLp.ext
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp only [PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one]
    rw [funext hEq]
    exact continuous_id.smul continuous_const
  exact (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)).symm.continuous.comp
    (continuous_fst.prodMk (hSingle.comp continuous_snd))

private theorem exists_L2_trace_continuous_closedSlab {n q : ℕ} (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)] {l r : ℝ} (hlr : l < r)
    {u : Domain (n + 1) → Ambient q} (hu : ContinuousOn u (cellInterfaceClosedSlab U l r)) {B : ℝ}
    (hB : ∀ z ∈ cellInterfaceClosedSlab U l r, ‖u z‖ ≤ B) :
    let μ := (volume : Measure (Domain n)).restrict U.val
    ∃ H : C(Icc l r, Lp (Ambient q) 2 μ),
      ∀ t : Icc l r, ∃ h : MemLp (fun x => u (cellInterfacePoint x t.val)) 2 μ, H t = h.toLp _ := by
  intro μ
  let f : Domain n × ℝ → Ambient q := fun p => u (cellInterfacePoint p.1 p.2)
  have hMeas : ∀ᵐ t : ℝ ∂volume, ∀ _ht : t ∈ Ioo l r, AEStronglyMeasurable (fun x => f (x, t)) μ := by
    refine Eventually.of_forall fun t ht => ?_
    have hc : ContinuousOn (fun x => u (cellInterfacePoint x t)) U.val :=
      hu.comp (continuous_cellInterfacePoint.comp (continuous_id.prodMk continuous_const)).continuousOn
        (fun _ hx => cellInterfacePoint_mem_closedSlab hx (Ioo_subset_Icc_self ht))
    exact hc.aestronglyMeasurable U.property.measurableSet
  have hCont : ∀ᵐ x ∂μ, ContinuousOn (fun t => f (x, t)) (Icc l r) := by
    filter_upwards [ae_restrict_mem U.property.measurableSet] with x hx
    exact hu.comp (continuous_cellInterfacePoint.comp (continuous_const.prodMk continuous_id)).continuousOn
      (fun _ ht => cellInterfacePoint_mem_closedSlab hx ht)
  have hBound : ∀ᵐ x ∂μ, ∀ t ∈ Icc l r, ‖f (x, t)‖ ≤ B := by
    filter_upwards [ae_restrict_mem U.property.measurableSet] with x hx
    exact fun t ht => hB _ (cellInterfacePoint_mem_closedSlab hx ht)
  obtain ⟨H, hH, _⟩ := StratificationTheory.exists_continuous_L2_trace_of_bounded_fiber_continuity μ hlr
    hMeas hCont hBound
  exact ⟨H, hH⟩

/-- Bounded continuous representatives on the two closed local sides give
one weak graph whenever their actual common interface values agree. -/
theorem memW12_cellInterface_glue {n q : ℕ} (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)]
    {l t r : ℝ} (hlt : l < t) (htr : t < r)
    {u v : Domain (n + 1) → Ambient q} {Du Dv : Domain (n + 1) → HarmonicMaps.Gradient (n + 1) q}
    (hu : MemW12 (cellInterfaceSlab U l t) u Du) (hv : MemW12 (cellInterfaceSlab U t r) v Dv)
    (huCont : ContinuousOn u (cellInterfaceClosedSlab U l t))
    (hvCont : ContinuousOn v (cellInterfaceClosedSlab U t r)) {B : ℝ}
    (huBound : ∀ z ∈ cellInterfaceClosedSlab U l t, ‖u z‖ ≤ B)
    (hvBound : ∀ z ∈ cellInterfaceClosedSlab U t r, ‖v z‖ ≤ B)
    (hSame : ∀ x ∈ U.val, u (cellInterfacePoint x t) = v (cellInterfacePoint x t)) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    MemW12 (cellInterfaceSlab U l r) (fun z => if (e z).2 0 < t then u z else v z)
      (fun z i => if (e z).2 0 < t then Du z i else Dv z i) := by
  classical
  intro e
  obtain ⟨H, hH⟩ := exists_L2_trace_continuous_closedSlab U hlt huCont huBound
  obtain ⟨K, hK⟩ := exists_L2_trace_continuous_closedSlab U htr hvCont hvBound
  have hMatch : H ⟨t, hlt.le, le_rfl⟩ = K ⟨t, le_rfl, htr.le⟩ := by
    obtain ⟨hp, hP⟩ := hH ⟨t, hlt.le, le_rfl⟩
    obtain ⟨hq, hQ⟩ := hK ⟨t, le_rfl, htr.le⟩
    rw [hP, hQ]
    apply MemLp.toLp_congr
    filter_upwards [ae_restrict_mem U.property.measurableSet] with x hx
    exact hSame x hx
  exact (StratificationTheory.memW12_coordinate_piecewise_of_matching_L2_traces U hlt htr u v Du Dv
    hu hv H K (Eventually.of_forall fun _ hx => hH ⟨_, hx.1.le, hx.2.le⟩)
    (Eventually.of_forall fun _ hx => hK ⟨_, hx.1.le, hx.2.le⟩) hMatch).1

/-- The actual Euclidean slab in a specified isometric frame. -/
@[expose] noncomputable def rotatedCellInterfaceSlab {n : ℕ} (U : OpenDomain n)
    (Q : Domain (n + 1) ≃ₗᵢ[ℝ] Domain (n + 1)) (l r : ℝ) : OpenDomain (n + 1) :=
  ⟨Q.symm ⁻¹' (cellInterfaceSlab U l r).val, (cellInterfaceSlab U l r).property.preimage Q.symm.continuous⟩

/-- Local glue in the original ambient coordinates, retaining the original
physical columns rather than assuming a weak derivative at the interface. -/
theorem memW12_rotatedCellInterface_glue {n q : ℕ} (U : OpenDomain n)
    [IsFiniteMeasure ((volume : Measure (Domain n)).restrict U.val)]
    (Q : Domain (n + 1) ≃ₗᵢ[ℝ] Domain (n + 1)) {l t r : ℝ} (hlt : l < t) (htr : t < r)
    {u v : Domain (n + 1) → Ambient q} {Du Dv : Domain (n + 1) → HarmonicMaps.Gradient (n + 1) q}
    (hu : MemW12 (rotatedCellInterfaceSlab U Q l t) u Du) (hv : MemW12 (rotatedCellInterfaceSlab U Q t r) v Dv)
    (huCont : ContinuousOn (u ∘ Q) (cellInterfaceClosedSlab U l t))
    (hvCont : ContinuousOn (v ∘ Q) (cellInterfaceClosedSlab U t r)) {B : ℝ}
    (huBound : ∀ z ∈ cellInterfaceClosedSlab U l t, ‖u (Q z)‖ ≤ B)
    (hvBound : ∀ z ∈ cellInterfaceClosedSlab U t r, ‖v (Q z)‖ ≤ B)
    (hSame : ∀ x ∈ U.val, u (Q (cellInterfacePoint x t)) = v (Q (cellInterfacePoint x t))) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := 1)
    MemW12 (rotatedCellInterfaceSlab U Q l r) (fun z => if (e (Q.symm z)).2 0 < t then u z else v z)
      (fun z i => if (e (Q.symm z)).2 0 < t then Du z i else Dv z i) := by
  classical
  intro e
  obtain ⟨H, hH⟩ := exists_L2_trace_continuous_closedSlab U hlt huCont huBound
  obtain ⟨K, hK⟩ := exists_L2_trace_continuous_closedSlab U htr hvCont hvBound
  have hMatch : H ⟨t, hlt.le, le_rfl⟩ = K ⟨t, le_rfl, htr.le⟩ := by
    obtain ⟨hp, hP⟩ := hH ⟨t, hlt.le, le_rfl⟩
    obtain ⟨hq, hQ⟩ := hK ⟨t, le_rfl, htr.le⟩
    rw [hP, hQ]
    apply MemLp.toLp_congr
    filter_upwards [ae_restrict_mem U.property.measurableSet] with x hx
    exact hSame x hx
  exact (StratificationTheory.memW12_isometric_piecewise_of_matching_L2_traces U hlt htr Q u v Du Dv
    hu hv H K (Eventually.of_forall fun _ hx => hH ⟨_, hx.1.le, hx.2.le⟩)
    (Eventually.of_forall fun _ hx => hK ⟨_, hx.1.le, hx.2.le⟩) hMatch).1

/-- Every nonzero linear interface has an isometric normal frame in the
original ambient space. -/
theorem exists_cellInterface_normalFrame (L : Point →L[ℝ] ℝ) (hL : L ≠ 0) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    ∃ (Q : Point ≃ₗᵢ[ℝ] Point) (s : ℝ), 0 < s ∧ ∀ z : Point, L z = s * (e (Q.symm z)).2 0 := by
  intro e
  let n := (InnerProductSpace.toDual ℝ Point).symm L
  have hDual (z : Point) : inner ℝ n z = L z := InnerProductSpace.toDual_symm_apply
  have hn : n ≠ 0 := by
    intro hn
    apply hL
    ext z
    rw [← hDual z, hn, inner_zero_left, zero_apply]
  let s := ‖n‖
  let t : Point := s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have hs : 0 < s := norm_pos_iff.mpr hn
  have ht : ‖t‖ = ‖n‖ := by
    simp only [t, norm_smul, Real.norm_of_nonneg hs.le, PiLp.norm_single, norm_one, mul_one, s]
  let Q := (ℝ ∙ (t - n))ᗮ.reflection
  have hQ : Q t = n := Submodule.reflection_sub ht
  refine ⟨Q, s, hs, fun z => ?_⟩
  calc
    L z = inner ℝ (Q t) (Q (Q.symm z)) := by rw [hQ, Q.apply_symm_apply, hDual]
    _ = inner ℝ t (Q.symm z) := Q.inner_map_map _ _
    _ = s * (e (Q.symm z)).2 0 := by
      simp only [t, real_inner_smul_left, EuclideanSpace.inner_single_left, map_one, one_mul]
      rfl

/-- Each radial line is an actual codimension-two coordinate flat in a
suitable isometric frame. -/
theorem exists_cellVertex_radialLineFrame (x : Point) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 2)
    ∃ Q : Point ≃ₗᵢ[ℝ] Point, ∀ s : ℝ, (e (Q (s • x))).2 = 0 := by
  intro e
  let v : Point := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let t : Point := ‖x‖ • v
  have ht : ‖x‖ = ‖t‖ := by
    simp only [t, v, norm_smul, Real.norm_of_nonneg (norm_nonneg x), PiLp.norm_single, norm_one, mul_one]
  let Q := (ℝ ∙ (x - t))ᗮ.reflection
  have hQ : Q x = t := Submodule.reflection_sub ht
  have hv : (e v).2 = 0 := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  refine ⟨Q, fun s => ?_⟩
  rw [map_smul, hQ, map_smul]
  change s • (e t).2 = 0
  rw [show (e t).2 = ‖x‖ • (e v).2 from by simp [t], hv, smul_zero, smul_zero]

/-- A neighborhood of a point on the interface contains a full short
rotated slab, with room for both closed slabs used for trace comparisons. -/
theorem exists_rotatedSlab_in_closedBall (Q : Point ≃ₗᵢ[ℝ] Point) (y : Point) {ρ : ℝ} (hρ : 0 < ρ)
    (hNormal : ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)) (Q.symm y)).2 0 = 0) :
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)
    let x := (e (Q.symm y)).1
    ∃ δ > (0 : ℝ),
      y ∈ (rotatedCellInterfaceSlab (ballDomain x δ) Q (-δ) δ).val ∧
      ∀ z ∈ cellInterfaceClosedSlab (ballDomain x δ) (-δ) δ, Q z ∈ closedBall y ρ := by
  intro e x
  let M := ‖e.symm.toContinuousLinearMap‖
  let δ := ρ / (2 * (M + 1))
  have hM : 0 ≤ M := norm_nonneg _
  have hM₁ : 0 < M + 1 := by linarith only [hM]
  have hδ : 0 < δ := div_pos hρ (mul_pos (by norm_num) hM₁)
  have hBound : M * δ ≤ ρ := calc
    _ ≤ (M + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
    _ = ρ / 2 := by dsimp only [δ]; field_simp
    _ ≤ ρ := by linarith only [hρ]
  refine ⟨δ, hδ, ?_, ?_⟩
  · change x ∈ ball x δ ∧ (e (Q.symm y)).2 0 ∈ Ioo (-δ) δ
    exact ⟨mem_ball_self hδ, by rw [hNormal]; exact ⟨neg_lt_zero.mpr hδ, hδ⟩⟩
  · intro z hz
    let y₀ := Q.symm y
    have hY : (e y₀).2 = 0 := by
      apply PiLp.ext
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact hNormal
    have hTang : ‖(e z).1 - (e y₀).1‖ ≤ δ := by
      have h := hz.1
      change (e z).1 ∈ ball x δ at h
      exact (by simpa only [mem_ball, dist_eq_norm] using h : ‖(e z).1 - x‖ < δ).le
    have hVert : ‖(e z).2 - (e y₀).2‖ ≤ δ := by
      rw [hY, sub_zero]
      have h := (StratificationTheory.isometry_domainOne_eval.dist_eq (e z).2 (0 : Domain 1)).symm
      have hNorm : ‖(e z).2‖ = |(e z).2 0| := by
        simpa only [dist_zero_right, Real.dist_eq, PiLp.zero_apply, sub_zero, Real.norm_eq_abs] using h
      have hz' : (e z).2 0 ∈ Icc (-δ) δ := hz.2
      rw [hNorm]
      exact abs_le.mpr hz'
    have hZ : ‖e (z - y₀)‖ ≤ δ := by
      rw [map_sub, Prod.norm_def]
      exact max_le hTang hVert
    have hOp : ‖z - y₀‖ ≤ M * ‖e (z - y₀)‖ := by
      have h := e.symm.toContinuousLinearMap.le_opNorm (e (z - y₀))
      change ‖e.symm (e (z - y₀))‖ ≤ _ at h
      rwa [e.symm_apply_apply] at h
    rw [mem_closedBall, ← Q.apply_symm_apply y, Q.isometry.dist_eq, dist_eq_norm]
    exact hOp.trans ((mul_le_mul_of_nonneg_left hZ hM).trans hBound)

/-- A genuine linear interface has zero three-dimensional volume. -/
theorem volume_cellInterface_plane (L : Point →L[ℝ] ℝ) (hL : L ≠ 0) :
    (volume : Measure Point) {z | L z = 0} = 0 := by
  let A := L.toLinearMap.ker.toAffineSubspace
  have hA : A ≠ ⊤ := by
    intro h
    apply hL
    ext z
    have hz : z ∈ A := by rw [h]; simp
    exact hz
  exact Measure.addHaar_affineSubspace volume A hA

end Thesis
