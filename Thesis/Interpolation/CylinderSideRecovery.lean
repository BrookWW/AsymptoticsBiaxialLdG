module

public import Thesis.MeasureGeometry.CylinderCoordinates
public import Thesis.Foundation.VacuumTube
public import Thesis.Foundation.VacuumFreeHomotopy
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Operator.Prod
import Thesis.StressEnergy

/-! The actual radial side interpolation through a regular vacuum band. -/

public section

noncomputable section

open Filter Metric Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace Thesis.MeasureGeometry

local instance cylinderSideFieldNorm : Norm (Point →L[ℝ] S0) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ) (E := Point) (F := S0)

local instance cylinderSideBlendGroup : NormedAddCommGroup ((Point × S0) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ) (E := Point × S0) (F := S0)

local instance cylinderSideBlendNorm : Norm ((Point × S0) →L[ℝ] S0) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ) (E := Point × S0) (F := S0)

local instance cylinderSidePairNorm : Norm (Point →L[ℝ] (Point × S0)) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ) (E := Point) (F := Point × S0)

/-- Transverse and axial coordinates in the same translated orthonormal
frame as the cylindrical energy formulas. -/
@[expose] def axisCoordinates (B : OrthonormalBasis (Fin 3) ℝ Point) (c x : Point) : Plane × ℝ :=
  (planeLineEuclideanIsometry.symm (B.repr (x - c))).ofLp

theorem axisCoordinates_axisChart (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (y : Plane) (z : ℝ) :
    axisCoordinates B c (c + axisChart B (y, z)) = (y, z) := by
  simp only [axisCoordinates, add_sub_cancel_left, axisChart, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.symm_apply_apply, WithLp.ofLp_toLp]

theorem axisChart_axisCoordinates (B : OrthonormalBasis (Fin 3) ℝ Point) (c x : Point) :
    c + axisChart B (axisCoordinates B c x) = x := by
  simp only [axisChart, axisCoordinates, WithLp.toLp_ofLp, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.symm_apply_apply, add_sub_cancel]

/-- Retraction onto one literal lateral slice; the chosen height is
an independent argument. -/
@[expose] def cylinderSidePoint (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (r : ℝ) (x : Point) (z : ℝ) : Point :=
  c + axisChart B (r • NormedSpace.normalize (axisCoordinates B c x).1, z)

theorem cylinderSidePoint_at_original_radius (B : OrthonormalBasis (Fin 3) ℝ Point) (c x : Point)
    {r : ℝ} (hr : ‖(axisCoordinates B c x).1‖ = r) :
    cylinderSidePoint B c r x (axisCoordinates B c x).2 = x := by
  unfold cylinderSidePoint
  rw [← hr, NormedSpace.norm_smul_normalize]
  exact axisChart_axisCoordinates B c x

theorem cylinderSidePoint_eq_native_round_lateral (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (r : ℝ) (x : Point) (z : ℝ) (hAxis : (axisCoordinates B c x).1 ≠ 0) :
    ∃ θ : NativeCircle, cylinderSidePoint B c r x z = c + axisChart B (r • θ.val, z) := by
  let y := (axisCoordinates B c x).1
  let θ : NativeCircle := ⟨NormedSpace.normalize y,
    mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hAxis)⟩
  exact ⟨θ, rfl⟩

private def sideTransition (r s a b : ℝ) : ℝ :=
  Real.smoothTransition ((s / r - a) / (b - a))

private theorem sideTransition_mem (r s a b : ℝ) : sideTransition r s a b ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem sideTransition_zero {r s a b : ℝ} (hr : 0 < r) (hab : a < b) (hs : s ≤ a * r) :
    sideTransition r s a b = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.2 ((div_le_iff₀ hr).2 hs)) (sub_nonneg.2 hab.le))

private theorem sideTransition_one {r s a b : ℝ} (hr : 0 < r) (hab : a < b) (hs : b * r ≤ s) :
    sideTransition r s a b = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (sub_pos.2 hab)).2
  have h := (le_div_iff₀ hr).2 hs
  linarith only [h]

private theorem extend_vacuum_of_mem_tube {a : BulkCoefficients} (p : VacuumTubularProjection a)
    {Q : S0} (hQ : Q ∈ vacuumTube a p.radius) : p.extend Q ∈ vacuum a := by
  rw [p.extend_eq ⟨Q, hQ⟩]
  exact (p.project ⟨Q, hQ⟩).property

private theorem extend_eq_of_mem_vacuum {a : BulkCoefficients} (p : VacuumTubularProjection a)
    {Q : S0} (hQ : Q ∈ vacuum a) : p.extend Q = Q := by
  rw [p.extend_eq ⟨Q, vacuum_subset_vacuumTube a p.radius_pos hQ⟩, p.project_of_mem hQ]

def cylinderSideHeight (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point)
    (r z₀ : ℝ) (x : Point) : ℝ :=
  let yz := axisCoordinates B c x
  z₀ + sideTransition r ‖yz.1‖ (5 / 8) (3 / 4) * (yz.2 - z₀)

theorem cylinderSideHeight_mem_Icc (B : OrthonormalBasis (Fin 3) ℝ Point) (c x : Point)
    (r : ℝ) {z₀ lo hi : ℝ} (h₀ : z₀ ∈ Icc lo hi) (hx : (axisCoordinates B c x).2 ∈ Icc lo hi) :
    cylinderSideHeight B c r z₀ x ∈ Icc lo hi := by
  let t := sideTransition r ‖(axisCoordinates B c x).1‖ (5 / 8) (3 / 4)
  have ht : t ∈ Icc (0 : ℝ) 1 := sideTransition_mem _ _ _ _
  change z₀ + t * ((axisCoordinates B c x).2 - z₀) ∈ Icc lo hi
  constructor
  · nlinarith only [mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 h₀.1),
      mul_nonneg ht.1 (sub_nonneg.2 hx.1)]
  · nlinarith only [mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 h₀.2),
      mul_nonneg ht.1 (sub_nonneg.2 hx.2)]

private def cylinderSideBlend (a : BulkCoefficients) (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (r z₀ : ℝ) (q : Point → S0) (x : Point) (U : S0) : S0 :=
  let ρ := ‖(axisCoordinates B c x).1‖
  let t₂ := sideTransition r ρ (3 / 4) (13 / 16)
  let t₃ := sideTransition r ρ (7 / 8) (15 / 16)
  let q₀ := q (cylinderSidePoint B c r x (cylinderSideHeight B c r z₀ x))
  let P := (vacuumTubularProjection a).extend U
  let v := (vacuumTubularProjection a).extend ((1 - t₂) • q₀ + t₂ • P)
  t₃ • U + (1 - t₃) • v

/-- The side interpolation first changes height in the regular limit,
then connects its trace to the projected approximant, and restores the
original approximant at the outer wall. -/
def cylinderSideRecovery (a : BulkCoefficients) (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (r z₀ : ℝ) (q Q : Point → S0) (x : Point) : S0 :=
  cylinderSideBlend a B c r z₀ q x (Q (cylinderSidePoint B c r x (axisCoordinates B c x).2))

/-- The actual side data give the precise inner and outer values and a
bulk-potential upper bound by that of the original lateral trace. -/
theorem exists_cylinderSideRecovery_bounds (a : BulkCoefficients) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {r lo hi z₀ : ℝ},
        0 < r → z₀ ∈ Icc lo hi → ∀ (q Q : Point → S0) (M : ℝ),
        (∀ (θ : NativeCircle) (z : ℝ), z ∈ Icc lo hi →
          q (c + axisChart B (r • θ.val, z)) ∈ vacuum a) →
        (∀ (θ : NativeCircle) (z : ℝ), z ∈ Icc lo hi →
          let Y := c + axisChart B (r • θ.val, z)
          Q Y ∈ vacuumTube a δ ∧ ‖Q Y‖ ≤ M ∧
            dist ((vacuumTubularProjection a).extend (Q Y)) (q Y) < (vacuumTubularProjection a).radius) →
        ∀ x : Point, (axisCoordinates B c x).1 ≠ 0 → (axisCoordinates B c x).2 ∈ Icc lo hi →
          let w := cylinderSideRecovery a B c r z₀ q Q x
          (‖w‖ ≤ max M (Real.sqrt 2 * vacuumRadius a)) ∧
          bulkPotential a w ≤ C * bulkPotential a (Q (cylinderSidePoint B c r x (axisCoordinates B c x).2)) ∧
          (‖(axisCoordinates B c x).1‖ ≤ (5 / 8 : ℝ) * r → w = q (cylinderSidePoint B c r x z₀)) ∧
          (‖(axisCoordinates B c x).1‖ = r → w = Q x) := by
  obtain ⟨_, C, δ, _, hC, hδ, hδR, hBulk⟩ := bulkPotential_tubular_estimates a
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro B c r lo hi z₀ hr hz₀ q Q M hq hQ x hAxis hz
  let yz := axisCoordinates B c x
  let ρ := ‖yz.1‖
  let t₁ := sideTransition r ρ (5 / 8) (3 / 4)
  let t₂ := sideTransition r ρ (3 / 4) (13 / 16)
  let t₃ := sideTransition r ρ (7 / 8) (15 / 16)
  let z₁ := z₀ + t₁ * (yz.2 - z₀)
  let q₀ := q (cylinderSidePoint B c r x z₁)
  let Q₀ := Q (cylinderSidePoint B c r x yz.2)
  let qP := vacuumTubularProjection a
  let P := qP.extend Q₀
  let X := (1 - t₂) • q₀ + t₂ • P
  let v := qP.extend X
  let w := t₃ • Q₀ + (1 - t₃) • v
  have ht₂ : t₂ ∈ Icc (0 : ℝ) 1 := sideTransition_mem _ _ _ _
  have ht₃ : t₃ ∈ Icc (0 : ℝ) 1 := sideTransition_mem _ _ _ _
  let θ : NativeCircle := ⟨NormedSpace.normalize yz.1,
    mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hAxis)⟩
  have hZ : z₁ ∈ Icc lo hi := cylinderSideHeight_mem_Icc B c x r hz₀ hz
  have hY (z : ℝ) : cylinderSidePoint B c r x z = c + axisChart B (r • θ.val, z) := rfl
  have hq₀ : q₀ ∈ vacuum a := hq θ z₁ hZ
  obtain ⟨hNear, hN, hClose⟩ := hQ θ yz.2 hz
  have hNear' : Q₀ ∈ vacuumTube a qP.radius :=
    (show Metric.infDist Q₀ (vacuum a) < δ from hNear).trans_le hδR
  have hPVac : P ∈ vacuum a := extend_vacuum_of_mem_tube qP hNear'
  have hXV : X ∈ vacuumTube a qP.radius := by
    by_cases ht : t₂ = 0
    · have hEq : X = q₀ := by simp only [X, ht, sub_zero, one_smul, zero_smul, add_zero]
      exact hEq.symm ▸ vacuum_subset_vacuumTube a qP.radius_pos hq₀
    · have hρ : (3 / 4 : ℝ) * r < ρ := lt_of_not_ge fun h =>
        ht (sideTransition_zero hr (by norm_num) h)
      have h1 : t₁ = 1 := sideTransition_one hr (by norm_num) hρ.le
      have hzEq : z₁ = yz.2 := by simp only [z₁, h1, one_mul, add_sub_cancel]
      have hqEq : q₀ = q (cylinderSidePoint B c r x yz.2) := congrArg (q ∘ cylinderSidePoint B c r x) hzEq
      have hD : dist P q₀ < qP.radius := by
        rw [hqEq]
        exact hClose
      apply (Metric.infDist_le_dist_of_mem hq₀).trans_lt
      have hT : (1 - t₂) ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.2 ht₂.2, sub_le_self _ ht₂.1⟩
      have hLip := dist_smul_add_one_sub_smul_le (x := q₀) (y := P) hT
      rw [sub_sub_cancel] at hLip
      exact hLip.trans_lt hD
  have hvVac : v ∈ vacuum a := extend_vacuum_of_mem_tube qP hXV
  have hwB : ‖w‖ ≤ max M (Real.sqrt 2 * vacuumRadius a) := by
    let K := max M (Real.sqrt 2 * vacuumRadius a)
    have hQV : ‖Q₀‖ ≤ K := hN.trans (le_max_left _ _)
    have hVV : ‖v‖ ≤ K := (vacuum_norm hvVac).le.trans (le_max_right _ _)
    calc
      ‖w‖ ≤ ‖t₃ • Q₀‖ + ‖(1 - t₃) • v‖ := norm_add_le _ _
      _ = t₃ * ‖Q₀‖ + (1 - t₃) * ‖v‖ := by
        rw [norm_smul, Real.norm_of_nonneg ht₃.1, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 ht₃.2)]
      _ ≤ t₃ * K + (1 - t₃) * K := add_le_add
        (mul_le_mul_of_nonneg_left hQV ht₃.1) (mul_le_mul_of_nonneg_left hVV (sub_nonneg.2 ht₃.2))
      _ = K := by ring
  have hwBulk : bulkPotential a w ≤ C * bulkPotential a Q₀ := by
    by_cases ht : t₃ = 0
    · have hEq : w = v := by simp only [w, ht, zero_smul, sub_zero, one_smul, zero_add]
      rw [hEq, (bulkPotential_eq_zero_iff a _).2 hvVac]
      exact mul_nonneg hC.le (bulkPotential_nonneg a _)
    · have hρ : (7 / 8 : ℝ) * r < ρ := lt_of_not_ge fun h =>
        ht (sideTransition_zero hr (by norm_num) h)
      have h₂ : t₂ = 1 :=
        sideTransition_one hr (by norm_num) ((mul_le_mul_of_nonneg_right (by norm_num) hr.le).trans hρ.le)
      have hX : X = P := by simp only [X, h₂, sub_self, zero_smul, one_smul, zero_add]
      have hProj : v = P := (congrArg qP.extend hX).trans (extend_eq_of_mem_vacuum qP hPVac)
      let A : vacuumTube a qP.radius := ⟨Q₀, hNear'⟩
      have hBound := (hBulk A hNear).2 t₃ ht₃
      have hEq : P = (qP.project A).val := qP.extend_eq A
      change bulkPotential a (t₃ • Q₀ + (1 - t₃) • v) ≤ _
      rw [hProj, hEq]
      exact hBound.trans (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left
        (pow_le_one₀ ht₃.1 ht₃.2) hC.le).trans_eq (mul_one C)) (bulkPotential_nonneg a _))
  refine ⟨hwB, hwBulk, ?_, ?_⟩
  · intro hh
    have h₁ : t₁ = 0 := sideTransition_zero hr (by norm_num) hh
    have h₂ : t₂ = 0 := sideTransition_zero hr (by norm_num)
      (hh.trans (mul_le_mul_of_nonneg_right (by norm_num) hr.le))
    have h₃ : t₃ = 0 := sideTransition_zero hr (by norm_num)
      (hh.trans (mul_le_mul_of_nonneg_right (by norm_num) hr.le))
    have hX : X = q₀ := by simp only [X, h₂, sub_zero, one_smul, zero_smul, add_zero]
    have hv : v = q₀ := (congrArg qP.extend hX).trans (extend_eq_of_mem_vacuum qP hq₀)
    change w = q (cylinderSidePoint B c r x z₀)
    simp only [w, h₃, zero_smul, sub_zero, one_smul, zero_add, hv, q₀, z₁, h₁, zero_mul, add_zero]
  · intro hh
    have h3 : t₃ = 1 := sideTransition_one hr (by norm_num)
      ((mul_le_mul_of_nonneg_right (by norm_num : (15 / 16 : ℝ) ≤ 1) hr.le).trans_eq (by simpa only [one_mul] using hh.symm))
    change w = Q x
    simp only [w, h3, one_smul, sub_self, zero_smul, add_zero, Q₀]
    exact congrArg Q (cylinderSidePoint_at_original_radius B c x hh)

theorem contDiff_axisCoordinates (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) :
    ContDiff ℝ ∞ (axisCoordinates B c) := by
  unfold axisCoordinates
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ Plane ℝ).contDiff.comp
    (planeLineEuclideanIsometry.symm.contDiff.comp (B.repr.contDiff.comp
      (contDiff_id.sub contDiff_const)))

theorem contDiff_axisChart (B : OrthonormalBasis (Fin 3) ℝ Point) :
    ContDiff ℝ ∞ (axisChart B) := by
  unfold axisChart
  exact B.repr.symm.contDiff.comp (planeLineEuclideanIsometry.contDiff.comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ Plane ℝ).symm.contDiff)

private theorem contDiffAt_transverseNorm {B : OrthonormalBasis (Fin 3) ℝ Point}
    {c x : Point} (hAxis : (axisCoordinates B c x).1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => ‖(axisCoordinates B c y).1‖) x :=
  (contDiffAt_norm ℝ hAxis).comp x ((contDiff_axisCoordinates B c).fst.contDiffAt)

private theorem contDiffAt_sideTransition {B : OrthonormalBasis (Fin 3) ℝ Point}
    {c x : Point} (hAxis : (axisCoordinates B c x).1 ≠ 0) (r a b : ℝ) :
    ContDiffAt ℝ ∞ (fun y => sideTransition r ‖(axisCoordinates B c y).1‖ a b) x := by
  unfold sideTransition
  exact Real.smoothTransition.contDiff.contDiffAt.comp x
    ((((contDiffAt_transverseNorm hAxis).div_const r).sub contDiffAt_const).div_const (b - a))

theorem contDiffAt_cylinderSidePoint {B : OrthonormalBasis (Fin 3) ℝ Point}
    {c x : Point} (hAxis : (axisCoordinates B c x).1 ≠ 0) (r : ℝ) {z : Point → ℝ}
    (hz : ContDiffAt ℝ ∞ z x) : ContDiffAt ℝ ∞ (fun y => cylinderSidePoint B c r y (z y)) x := by
  have hY := (contDiff_axisCoordinates B c).fst.contDiffAt (x := x)
  have hN : ‖(axisCoordinates B c x).1‖ ≠ 0 := norm_ne_zero_iff.2 hAxis
  have hInv := (contDiffAt_transverseNorm hAxis).inv hN
  have hRad : ContDiffAt ℝ ∞ (fun y => r • NormedSpace.normalize (axisCoordinates B c y).1) x :=
    (hInv.smul hY).const_smul r
  exact contDiffAt_const.add ((contDiff_axisChart B).contDiffAt.comp x (hRad.prodMk hz))

theorem contDiffAt_cylinderSideHeight {B : OrthonormalBasis (Fin 3) ℝ Point}
    {c x : Point} (hAxis : (axisCoordinates B c x).1 ≠ 0) (r z₀ : ℝ) :
    ContDiffAt ℝ ∞ (cylinderSideHeight B c r z₀) x := by
  unfold cylinderSideHeight
  exact contDiffAt_const.add ((contDiffAt_sideTransition hAxis r (5 / 8) (3 / 4)).mul
    ((contDiff_axisCoordinates B c).snd.contDiffAt.sub contDiffAt_const))

private theorem contDiffOn_cylinderSideBlend (a : BulkCoefficients) (B : OrthonormalBasis (Fin 3) ℝ Point)
    (c : Point) (r z₀ : ℝ) {q : Point → S0} {U V : Set Point}
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U)
    (hAxis : ∀ x ∈ V, (axisCoordinates B c x).1 ≠ 0)
    (hRef : ∀ x ∈ V, cylinderSidePoint B c r x (cylinderSideHeight B c r z₀ x) ∈ U) :
    ContDiffOn ℝ ∞ (fun p : Point × S0 => cylinderSideBlend a B c r z₀ q p.1 p.2) (V ×ˢ univ) := by
  let V' : Set (Point × S0) := V ×ˢ univ
  let t₂ (p : Point × S0) := sideTransition r ‖(axisCoordinates B c p.1).1‖ (3 / 4) (13 / 16)
  let t₃ (p : Point × S0) := sideTransition r ‖(axisCoordinates B c p.1).1‖ (7 / 8) (15 / 16)
  let Z (x : Point) := cylinderSidePoint B c r x (cylinderSideHeight B c r z₀ x)
  let Q (p : Point × S0) := q (Z p.1)
  let P := vacuumTubularProjection a
  have hP := P.contDiff_extend
  have h₂ : ContDiffOn ℝ ∞ t₂ V' := fun p hp =>
    ((contDiffAt_sideTransition (hAxis p.1 hp.1) r (3 / 4) (13 / 16)).comp p contDiff_fst.contDiffAt).contDiffWithinAt
  have h₃ : ContDiffOn ℝ ∞ t₃ V' := fun p hp =>
    ((contDiffAt_sideTransition (hAxis p.1 hp.1) r (7 / 8) (15 / 16)).comp p contDiff_fst.contDiffAt).contDiffWithinAt
  have hQ : ContDiffOn ℝ ∞ Q V' := by
    intro p hp
    have hZ := contDiffAt_cylinderSidePoint (hAxis p.1 hp.1) r
      (contDiffAt_cylinderSideHeight (hAxis p.1 hp.1) r z₀)
    exact (((hq (Z p.1) (hRef p.1 hp.1)).contDiffAt
      (hU.mem_nhds (hRef p.1 hp.1))).comp p (hZ.comp p contDiff_fst.contDiffAt)).contDiffWithinAt
  have hU' : ContDiffOn ℝ ∞ (fun p : Point × S0 => P.extend p.2) V' :=
    (hP.comp contDiff_snd).contDiffOn
  have hBlend : ContDiffOn ℝ ∞ (fun p : Point × S0 => P.extend ((1 - t₂ p) • Q p + t₂ p • P.extend p.2)) V' :=
    hP.comp_contDiffOn (((contDiffOn_const.sub h₂).smul hQ).add (h₂.smul hU'))
  exact (h₃.smul contDiff_snd.contDiffOn).add ((contDiffOn_const.sub h₃).smul hBlend)

private theorem fderiv_pair_comp_bound (F : Point × S0 → S0) (f : Point → S0)
    (x : Point) (hf : DifferentiableAt ℝ f x) (hF : DifferentiableAt ℝ F (x, f x))
    {M L : ℝ} (hL : 0 ≤ L)
    (h₁ : ‖fderiv ℝ F (x, f x)‖ ≤ M) (h₂ : ‖fderiv ℝ f x‖ ≤ L) :
    ‖fderiv ℝ (fun y => F (y, f y)) x‖ ≤ M * (1 + L) := by
  let A := fderiv ℝ F (x, f x)
  let D := fderiv ℝ f x
  let T := (ContinuousLinearMap.id ℝ Point).prod D
  have hT : HasFDerivAt (fun y => (y, f y)) T x :=
    (hasFDerivAt_id x).prodMk hf.hasFDerivAt
  have hDer : HasFDerivAt (fun y => F (y, f y)) (A.comp T) x :=
    hF.hasFDerivAt.comp x hT
  have hNorm : ‖T‖ ≤ 1 + L := by
    apply ContinuousLinearMap.opNorm_le_bound T (add_nonneg zero_le_one hL)
    intro y
    change ‖(y, D y)‖ ≤ (1 + L) * ‖y‖
    rw [norm_prod_le_iff]
    refine ⟨?_, ?_⟩
    · exact (one_mul _).symm.le.trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hL) (norm_nonneg _))
    · exact (D.le_opNorm y).trans (mul_le_mul_of_nonneg_right
        (h₂.trans (le_add_of_nonneg_left zero_le_one)) (norm_nonneg _))
  rw [hDer.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul h₁ hNorm (norm_nonneg _) ((norm_nonneg A).trans h₁))

private theorem uniform_fderiv_comp_pair_on_compact {ι : Type*}
    {U V K : Set Point} (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    (F : Point × S0 → S0) (S : Point → Point) {Q : ι → Point → S0}
    (hF : ContDiffOn ℝ ∞ F (V ×ˢ univ)) (hS : ContDiffOn ℝ ∞ S V) (hSide : MapsTo S V U)
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) U) {M L : ℝ} (hL : 0 ≤ L)
    (hBound : ∀ n x, x ∈ K → ‖Q n (S x)‖ ≤ M ∧ ‖fderiv ℝ (Q n) (S x)‖ ≤ L) :
    (∀ n, ContDiffOn ℝ ∞ (fun x => F (x, Q n (S x))) V) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K →
      ‖fderiv ℝ (fun y => F (y, Q n (S y))) x‖ ≤ C := by
  let H (n : ι) (x : Point) := (x, Q n (S x))
  have hH (n : ι) : ContDiffOn ℝ ∞ (H n) V :=
    contDiffOn_id.prodMk ((hQ n).comp hS hSide)
  have hMap (n : ι) : MapsTo (H n) V (V ×ˢ univ) := fun _ hx => ⟨hx, mem_univ _⟩
  refine ⟨fun n => hF.comp (hH n) (hMap n), ?_⟩
  have hDF : ContinuousOn (fderiv ℝ F) (V ×ˢ univ) :=
    hF.continuousOn_fderiv_of_isOpen (hV.prod isOpen_univ) (by simp)
  have hDS : ContinuousOn (fderiv ℝ S) V := hS.continuousOn_fderiv_of_isOpen hV (by simp)
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn (hDS.mono hKV)
  have hK' : IsCompact (K ×ˢ closedBall (0 : S0) M) := hK.prod (isCompact_closedBall _ _)
  have hSub : K ×ˢ closedBall (0 : S0) M ⊆ V ×ˢ univ := fun _ hx => ⟨hKV hx.1, mem_univ _⟩
  obtain ⟨C₂, hC₂⟩ := hK'.exists_bound_of_continuousOn (hDF.mono hSub)
  let D₁ := max 0 C₁
  let D₂ := max 0 C₂
  have hD₁ : 0 ≤ D₁ := le_max_left _ _
  have hD₂ : 0 ≤ D₂ := le_max_left _ _
  have hLD : 0 ≤ L * D₁ := mul_nonneg hL hD₁
  refine ⟨D₂ * (1 + L * D₁), mul_nonneg hD₂ (add_nonneg zero_le_one hLD), ?_⟩
  intro n x hx
  have hxV := hKV hx
  have hxU : S x ∈ U := hSide hxV
  have hSx := ((hS x hxV).contDiffAt (hV.mem_nhds hxV)).differentiableAt (by simp)
  have hAx := (((hQ n) (S x) hxU).contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
  have hKx : H n x ∈ K ×ˢ closedBall (0 : S0) M :=
    ⟨hx, mem_closedBall_zero_iff.2 (hBound n x hx).1⟩
  have hVx := hSub hKx
  have hFx := ((hF (H n x) hVx).contDiffAt ((hV.prod isOpen_univ).mem_nhds hVx)).differentiableAt (by simp)
  have hAcT : ‖fderiv ℝ (Q n ∘ S) x‖ ≤ L * D₁ := by
    have hEq : fderiv ℝ (Q n ∘ S) x = (fderiv ℝ (Q n) (S x)).comp (fderiv ℝ S x) :=
      (hAx.hasFDerivAt.comp x hSx.hasFDerivAt).fderiv
    calc
      _ = ‖(fderiv ℝ (Q n) (S x)).comp (fderiv ℝ S x)‖ :=
        congrArg (fun B : Point →L[ℝ] S0 => ‖B‖) hEq
      _ ≤ ‖fderiv ℝ (Q n) (S x)‖ * ‖fderiv ℝ S x‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ _ := mul_le_mul (hBound n x hx).2 ((hC₁ x hx).trans (le_max_right _ _)) (norm_nonneg _) hL
  exact fderiv_pair_comp_bound F (Q n ∘ S) x (hAx.comp x hSx) hFx hLD
    ((hC₂ _ hKx).trans (le_max_right _ _)) hAcT

/-- The side map is smooth near a regular band, and its first derivative
is uniformly bounded on every fixed compact physical collar whenever the
actual lateral values and first derivatives are uniformly bounded there. -/
theorem exists_uniform_cylinderSideRecovery_fderiv {ι : Type*} (a : BulkCoefficients)
    (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) (r z₀ : ℝ)
    {U V K : Set Point} (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    {q : Point → S0} {Q : ι → Point → S0} (hq : ContDiffOn ℝ ∞ q U)
    (hQ : ∀ n, ContDiffOn ℝ ∞ (Q n) U)
    (hAxis : ∀ x ∈ V, (axisCoordinates B c x).1 ≠ 0)
    (hRef : ∀ x ∈ V, cylinderSidePoint B c r x (cylinderSideHeight B c r z₀ x) ∈ U)
    (hSide : ∀ x ∈ V, cylinderSidePoint B c r x (axisCoordinates B c x).2 ∈ U)
    {M L : ℝ} (hL : 0 ≤ L)
    (hBound : ∀ n x, x ∈ K → let y := cylinderSidePoint B c r x (axisCoordinates B c x).2
      ‖Q n y‖ ≤ M ∧ ‖fderiv ℝ (Q n) y‖ ≤ L) :
    (∀ n, ContDiffOn ℝ ∞ (cylinderSideRecovery a B c r z₀ q (Q n)) V) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K →
      ‖fderiv ℝ (cylinderSideRecovery a B c r z₀ q (Q n)) x‖ ≤ C := by
  let S (x : Point) := cylinderSidePoint B c r x (axisCoordinates B c x).2
  let F (p : Point × S0) := cylinderSideBlend a B c r z₀ q p.1 p.2
  have hS : ContDiffOn ℝ ∞ S V := fun x hx =>
    (contDiffAt_cylinderSidePoint (hAxis x hx) r ((contDiff_axisCoordinates B c).snd.contDiffAt)).contDiffWithinAt
  have hF : ContDiffOn ℝ ∞ F (V ×ˢ univ) := contDiffOn_cylinderSideBlend a B c r z₀ hU hq hAxis hRef
  exact uniform_fderiv_comp_pair_on_compact hU hV hK hKV F S hF hS hSide hQ hL hBound

/-- Uniform side energy on the fixed physical regular band. Constants may
depend on that band and its limit map, and do not depend on the elastic scale. -/
theorem exists_uniform_cylinderSideRecovery_on_band (a : BulkCoefficients) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {ι : Type} (ε : ι → ElasticScale)
      (B : OrthonormalBasis (Fin 3) ℝ Point) (c : Point) {r lo hi z₀ : ℝ} (_ : 0 < r)
      (_ : z₀ ∈ Icc lo hi) {U K : Set Point} (_ : IsOpen U) (_ : IsCompact K)
      {q : Point → S0} {Q : ι → Point → S0} (_ : ContDiffOn ℝ ∞ q U)
      (_ : ∀ n, ContDiffOn ℝ ∞ (Q n) U)
      (_ : ∀ x ∈ K, (axisCoordinates B c x).1 ≠ 0)
      (_ : ∀ x ∈ K, (axisCoordinates B c x).2 ∈ Icc lo hi)
      (_ : ∀ (θ : NativeCircle) z, z ∈ Icc lo hi →
        let y := c + axisChart B (r • θ.val, z)
        y ∈ U ∧ q y ∈ vacuum a)
      {M L B₀ : ℝ} (_ : 0 ≤ L) (_ : 0 ≤ B₀)
      (_ : ∀ n (θ : NativeCircle) z, z ∈ Icc lo hi →
        let y := c + axisChart B (r • θ.val, z)
        (Q n y ∈ vacuumTube a δ ∧ ‖Q n y‖ ≤ M ∧
          dist ((vacuumTubularProjection a).extend (Q n y)) (q y) <
            (vacuumTubularProjection a).radius) ∧
        ‖fderiv ℝ (Q n) y‖ ≤ L ∧ (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q n y) ≤ B₀),
      ∃ (V : Set Point) (C : ℝ), IsOpen V ∧ K ⊆ V ∧ 0 ≤ C ∧
        (∀ n, ContDiffOn ℝ ∞ (cylinderSideRecovery a B c r z₀ q (Q n)) V) ∧
        ∀ n x, x ∈ K →
          let w := cylinderSideRecovery a B c r z₀ q (Q n)
          ‖w x‖ ≤ max M (Real.sqrt 2 * vacuumRadius a) ∧
          ‖fderiv ℝ w x‖ ≤ C ∧
          energyDensity a (ε n) (w x) (ClassicalGradient w x) ≤ C ∧
          (‖(axisCoordinates B c x).1‖ ≤ (5 / 8 : ℝ) * r → w x = q (cylinderSidePoint B c r x z₀)) ∧
          (‖(axisCoordinates B c x).1‖ = r → w x = Q n x) := by
  obtain ⟨δ, C, hδ, hC, hPointwise⟩ := exists_cylinderSideRecovery_bounds a
  refine ⟨δ, hδ, ?_⟩
  intro ι ε B c r lo hi z₀ hr hz₀ U K hU hK q Q hq hQ hAxis hHeight hBand M L B₀ hL hB₀ hTrace
  let S (x : Point) := cylinderSidePoint B c r x (axisCoordinates B c x).2
  let T (x : Point) := cylinderSidePoint B c r x (cylinderSideHeight B c r z₀ x)
  let V := {x : Point | (axisCoordinates B c x).1 ≠ 0 ∧ S x ∈ U ∧ T x ∈ U}
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.2
    intro x hx
    have hxAxis : (axisCoordinates B c x).1 ≠ 0 := hx.1
    have hAxisOpen : IsOpen {y : Point | (axisCoordinates B c y).1 ≠ 0} :=
      isOpen_compl_singleton.preimage ((contDiff_axisCoordinates B c).fst.continuous)
    have hs : ContinuousAt S x :=
      (contDiffAt_cylinderSidePoint hxAxis r ((contDiff_axisCoordinates B c).snd.contDiffAt)).continuousAt
    have ht : ContinuousAt T x :=
      (contDiffAt_cylinderSidePoint hxAxis r (contDiffAt_cylinderSideHeight hxAxis r z₀)).continuousAt
    exact Filter.inter_mem (hAxisOpen.mem_nhds hxAxis)
      (Filter.inter_mem (hs (hU.mem_nhds hx.2.1)) (ht (hU.mem_nhds hx.2.2)))
  have hSV (x : Point) (hx : x ∈ K) (z : ℝ) (hz : z ∈ Icc lo hi) :
      cylinderSidePoint B c r x z ∈ U := by
    obtain ⟨θ, hxθ⟩ := cylinderSidePoint_eq_native_round_lateral B c r x z (hAxis x hx)
    rw [hxθ]
    exact (hBand θ z hz).1
  have hKV : K ⊆ V := fun x hx =>
    ⟨hAxis x hx, hSV x hx _ (hHeight x hx),
      hSV x hx _ (cylinderSideHeight_mem_Icc B c x r hz₀ (hHeight x hx))⟩
  have hActual (n : ι) (x : Point) (hx : x ∈ K) :
      ‖Q n (S x)‖ ≤ M ∧ ‖fderiv ℝ (Q n) (S x)‖ ≤ L ∧
        (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q n (S x)) ≤ B₀ := by
    obtain ⟨θ, hxθ⟩ := cylinderSidePoint_eq_native_round_lateral B c r x _ (hAxis x hx)
    have h := hTrace n θ (axisCoordinates B c x).2 (hHeight x hx)
    change S x = _ at hxθ
    rw [hxθ]
    exact ⟨h.1.2.1, h.2.1, h.2.2⟩
  obtain ⟨hSmooth, D, hD, hDbound⟩ := exists_uniform_cylinderSideRecovery_fderiv a B c r z₀
    hU hV hK hKV hq hQ (fun _ hx => hx.1) (fun _ hx => hx.2.2) (fun _ hx => hx.2.1) hL
    (fun n x hx => ⟨(hActual n x hx).1, (hActual n x hx).2.1⟩)
  let C' := D + (1 / 2 : ℝ) * (3 * D ^ 2) + C * B₀
  have hC' : 0 ≤ C' := by dsimp only [C']; positivity
  refine ⟨V, C', hV, hKV, hC', hSmooth, ?_⟩
  intro n x hx
  let w := cylinderSideRecovery a B c r z₀ q (Q n)
  obtain ⟨hW, hP, hIn, hOut⟩ := hPointwise B c hr hz₀ q (Q n) M
    (fun θ z hz => (hBand θ z hz).2) (fun θ z hz => (hTrace n θ z hz).1)
    x (hAxis x hx) (hHeight x hx)
  have hBound : ‖fderiv ℝ w x‖ ≤ D := hDbound n x hx
  have hC₁ : D ≤ C' := by
    dsimp only [C']
    nlinarith only [sq_nonneg D, mul_nonneg hC.le hB₀]
  have hGrad : gradientNormSq (ClassicalGradient w x) ≤ 3 * D ^ 2 := by
    have hj (j : Fin 3) : ‖ClassicalGradient w x j‖ ≤ D := by
      change ‖(fderiv ℝ w x) (axis j)‖ ≤ _
      have hA : ‖axis j‖ = 1 := by rw [axis, PiLp.norm_single, norm_one]
      exact ((fderiv ℝ w x).le_opNorm (axis j)).trans
        (by rw [hA, mul_one]; exact hBound)
    rw [gradientNormSq_eq_sum_norm_sq]
    calc
      _ ≤ ∑ _ : Fin 3, D ^ 2 := Finset.sum_le_sum fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hj j) 2
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  have hBulk : (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (w x) ≤ C * B₀ := by
    calc
      _ ≤ (ε n : ℝ)⁻¹ ^ 2 * (C * bulkPotential a (Q n (S x))) :=
        mul_le_mul_of_nonneg_left hP (sq_nonneg _)
      _ = C * ((ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (Q n (S x))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hActual n x hx).2.2 hC.le
  have hE : energyDensity a (ε n) (w x) (ClassicalGradient w x) ≤ C' := by
    change (1 / 2 : ℝ) * gradientNormSq (ClassicalGradient w x) + (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (w x) ≤ _
    dsimp only [C']
    linarith only [mul_le_mul_of_nonneg_left hGrad (by norm_num : (0 : ℝ) ≤ 1 / 2), hBulk, hD]
  exact ⟨hW, hBound.trans hC₁, hE, hIn, hOut⟩

end Thesis.MeasureGeometry
