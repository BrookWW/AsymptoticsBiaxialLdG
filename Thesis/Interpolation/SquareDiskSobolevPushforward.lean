module

public import Thesis.Interpolation.MeshFaceDisk
public import Thesis.Interpolation.SquareDiskSobolevTransport
import Thesis.Interpolation.NativeDiskTrace
import StratificationTheory.Foundation.RadialTraceCompatibility
import HarmonicMaps.Analysis.EuclideanHausdorffLipschitz
import HarmonicMaps.EnergyLemmas

/-! The inverse square chart transports the full graph and the four original side classes. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ContDiff ENNReal NNReal Topology

namespace Thesis

private theorem inverse_squareDisk_preimage_unit_exact :
    planarSquareBallHomeomorph.symm ⁻¹' (unitCellCube 2).val = ball (0 : Plane) 1 := by
  rw [← squareDisk_preimage_unit]
  ext x
  change planarSquareBallHomeomorph (planarSquareBallHomeomorph.symm x) ∈ ball (0 : Plane) 1 ↔ _
  rw [Homeomorph.apply_symm_apply]

/-- The literal disk representative of a square graph retains the actual
unhalved weak gradient bound for the inverse radial chart. -/
theorem exists_unitDisk_memW12_square_pushforward (u : Plane → Ambient 5)
    (Du : Plane → HarmonicMaps.Gradient 2 5) (hu : MemW12 (unitCellCube 2) u Du) :
    ∃ Dw : Plane → HarmonicMaps.Gradient 2 5,
      MemW12 (ballDomain (0 : Plane) 1) (u ∘ planarSquareBallHomeomorph.symm) Dw ∧
      (∫ x in ball (0 : Plane) 1, hsNormSq (Dw x)) ≤ 1152 * (∫ x in (unitCellCube 2).val, hsNormSq (Du x)) := by
  let e := planarSquareBallHomeomorph.symm
  let D (x : Plane) (i : Fin 2) := ∑ j : Fin 2, (fderiv ℝ e x (EuclideanSpace.single i 1)) j • Du (e x) j
  let Ω : OpenDomain 2 := ⟨e ⁻¹' (unitCellCube 2).val, (unitCellCube 2).property.preimage e.continuous⟩
  have hΩ : Ω = ballDomain (0 : Plane) 1 := Subtype.ext inverse_squareDisk_preimage_unit_exact
  have hW : MemW12 Ω (u ∘ e) D := memW12_lipschitz_homeomorph_preimage e lipschitz_ballToCoordinateCube_plane
    lipschitz_coordinateCubeToBall_plane (unitCellCube 2) u Du hu
  have hMemW : MemW12 (ballDomain (0 : Plane) 1) (u ∘ e) D := hΩ ▸ hW
  refine ⟨D, hMemW, ?_⟩
  have hMap := map_lipschitzHomeomorph_preimage_volume_le e lipschitz_coordinateCubeToBall_plane
    (unitCellCube 2).val
  have hE := dirichletEnergy_lipschitz_pullback_le (e ⁻¹' (unitCellCube 2).val) (unitCellCube 2).val
    e lipschitz_ballToCoordinateCube_plane hMap Du hu.2.2
  change HarmonicMaps.dirichletEnergy D (e ⁻¹' (unitCellCube 2).val) ≤
    ENNReal.ofReal ((2 : ℝ) * ((8 : ℝ≥0) : ℝ) ^ 2) *
      ((((3 : ℝ≥0) : ℝ≥0∞) ^ 2) * HarmonicMaps.dirichletEnergy Du (unitCellCube 2).val) at hE
  have hDInt : IntegrableOn (fun x => hsNormSq (D x)) (ball (0 : Plane) 1) := hMemW.integrable_hsNormSq
  have hL : e ⁻¹' (unitCellCube 2).val = ball (0 : Plane) 1 := inverse_squareDisk_preimage_unit_exact
  rw [hL, HarmonicMaps.dirichletEnergy_eq_ofReal_integral hDInt,
    HarmonicMaps.dirichletEnergy_eq_ofReal_integral hu.integrable_hsNormSq] at hE
  have hR := ENNReal.toReal_mono (by finiteness) hE
  have hD₀ : 0 ≤ ∫ x in ball (0 : Plane) 1, hsNormSq (D x) := integral_nonneg fun _ => hsNormSq_nonneg _
  have hDu₀ : 0 ≤ ∫ x in (unitCellCube 2).val, hsNormSq (Du x) := integral_nonneg fun _ => hsNormSq_nonneg _
  have hC : 0 ≤ (2 : ℝ) * ((8 : ℝ≥0) : ℝ) ^ 2 := by norm_num
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD₀, ENNReal.toReal_ofReal hDu₀,
    ENNReal.toReal_ofReal hC] at hR
  norm_num at hR
  linarith only [hR]

private theorem dist_square_side_parameters (i : Fin 2) (s a b : ℝ) :
    dist (unitCellFaceSlice i (EuclideanSpace.single 0 a) s) (unitCellFaceSlice i (EuclideanSpace.single 0 b) s) =
      dist a b := by
  have hDiff : unitCellFaceSlice i (EuclideanSpace.single 0 a) s -
      unitCellFaceSlice i (EuclideanSpace.single 0 b) s = EuclideanSpace.single (if i = 0 then 1 else 0) (a - b) := by
    apply PiLp.ext
    intro j
    fin_cases i <;> fin_cases j <;> simp [unitCellFaceSlice_coordinates, PiLp.sub_apply]
  rw [dist_eq_norm, dist_eq_norm, hDiff, PiLp.norm_single]

private theorem lipschitz_squareDiskSideAngle (i : Fin 2) (p : Bool) : LipschitzWith 3 (squareDiskSideAngle i p) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let t : ℝ := if p then 1 else -1
  let k (z : Domain 1) := (projIcc (-1 : ℝ) 1 (by norm_num) (z 0)).val
  let S (z : Domain 1) := unitCellFaceSlice i (EuclideanSpace.single 0 (k z)) t
  change dist (coordinateCubeToBall (S x)) (coordinateCubeToBall (S y)) ≤ (3 : ℝ) * dist x y
  have hC := lipschitz_coordinateCubeToBall_plane.dist_le_mul (S x) (S y)
  have hD : dist (S x) (S y) = dist (k x) (k y) := dist_square_side_parameters i t (k x) (k y)
  have hK : dist (k x) (k y) ≤ dist (x 0) (y 0) := by
    have h := (LipschitzWith.projIcc (show (-1 : ℝ) ≤ 1 by norm_num)).dist_le_mul (x 0) (y 0)
    change dist (k x) (k y) ≤ ((1 : ℝ≥0) : ℝ) * dist (x 0) (y 0) at h
    rwa [NNReal.coe_one, one_mul] at h
  have hXY : dist (x 0) (y 0) ≤ dist x y := by
    rw [dist_eq_norm, dist_eq_norm]
    exact PiLp.norm_apply_le (x - y) 0
  apply hC.trans
  rw [hD]
  exact mul_le_mul_of_nonneg_left (hK.trans hXY) (by norm_num)

private theorem squareSide_closed_except_open_null :
    (volume : Measure (Domain 1)) ({x : Domain 1 | x 0 ∈ Icc (-1 : ℝ) 1} \ (unitCellCube 1).val) = 0 := by
  have hSub : ({x : Domain 1 | x 0 ∈ Icc (-1 : ℝ) 1} \ (unitCellCube 1).val) ⊆
      ({EuclideanSpace.single (0 : Fin 1) (-1 : ℝ), EuclideanSpace.single (0 : Fin 1) (1 : ℝ)} : Set (Domain 1)) := by
    intro x hx
    have hxI : x 0 ∈ Icc (-1 : ℝ) 1 := hx.1
    have hNo : x 0 ∉ Ioo (-1 : ℝ) 1 := by
      intro h
      apply hx.2
      apply mem_iInter.mpr
      intro i
      fin_cases i
      exact h
    rcases (not_and_or.mp hNo) with h | h
    · have hEq : x 0 = -1 := le_antisymm (le_of_not_gt h) hxI.1
      apply mem_insert_iff.mpr
      left
      apply PiLp.ext
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simpa only [PiLp.single_apply, ite_true] using hEq
    · have hEq : x 0 = 1 := le_antisymm hxI.2 (le_of_not_gt h)
      apply mem_insert_of_mem
      apply mem_singleton_iff.mpr
      apply PiLp.ext
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simpa only [PiLp.single_apply, ite_true] using hEq
  exact measure_mono_null hSub (((Set.finite_singleton _).insert _).measure_zero _)

private theorem ae_eq_circle_of_square_side_eq {b v : UnitSquareBoundary → Ambient 5}
    (h : ∀ i : Fin 2, ∀ p : Bool,
      (fun x : Domain 1 => b (unitSquareSideParameter i p (x 0))) =ᵐ[volume.restrict (unitCellCube 1).val]
        fun x => v (unitSquareSideParameter i p (x 0))) :
    (fun θ : NativeCircle => b (unitSquareCircleHomeomorph.symm θ)) =ᵐ[unitBoundarySurface 2]
      fun θ => v (unitSquareCircleHomeomorph.symm θ) := by
  let σ := unitBoundarySurface 2
  let Bad (i : Fin 2) (p : Bool) := {x : Domain 1 | x 0 ∈ Icc (-1 : ℝ) 1 ∧
    b (unitSquareSideParameter i p (x 0)) ≠ v (unitSquareSideParameter i p (x 0))}
  have hBad (i : Fin 2) (p : Bool) : (volume : Measure (Domain 1)) (Bad i p) = 0 := by
    have hEq := (ae_restrict_iff' (unitCellCube 1).property.measurableSet).mp (h i p)
    have hA : ∀ᵐ x : Domain 1 ∂volume, x ∉ ({x : Domain 1 | x 0 ∈ Icc (-1 : ℝ) 1} \ (unitCellCube 1).val) :=
      measure_eq_zero_iff_ae_notMem.mp squareSide_closed_except_open_null
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hEq, hA] with x hx hxA hxB
    have hxS : x ∈ (unitCellCube 1).val := not_not.mp (fun hn => hxA ⟨hxB.1, hn⟩)
    exact hxB.2 (hx hxS)
  have hImage (i : Fin 2) (p : Bool) : σ (squareDiskSideAngle i p '' Bad i p) = 0 := by
    have hBound := euclideanHausdorff_lipschitzOn_image_le_volume
      ((lipschitz_squareDiskSideAngle i p).lipschitzOnWith (s := univ)) (subset_univ (Bad i p))
    have hDim : Module.finrank ℝ (Domain 1) = 1 := by simp [Domain]
    rw [hDim, hBad, mul_zero] at hBound
    exact nonpos_iff_eq_zero.mp hBound
  let C := ⋃ i : Fin 2, ⋃ p : Bool, squareDiskSideAngle i p '' Bad i p
  have hC : σ C = 0 := measure_iUnion_null fun i => measure_iUnion_null (hImage i)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hC] with θ hθ
  by_contra he
  obtain ⟨i, p, t, ht⟩ := exists_unitSquareSideParameter (unitSquareCircleHomeomorph.symm θ)
  let x : Domain 1 := EuclideanSpace.single 0 t.val
  have hx : x 0 = t.val := by simp [x]
  have hxB : x ∈ Bad i p := by
    change x 0 ∈ Icc (-1 : ℝ) 1 ∧ _
    rw [hx, ht]
    exact ⟨t.property, he⟩
  have hxi : squareDiskSideAngle i p x = θ := by
    unfold squareDiskSideAngle
    rw [hx, ht, Homeomorph.apply_symm_apply]
  exact hθ (mem_iUnion_of_mem i (mem_iUnion_of_mem p ⟨x, hxB, hxi⟩))

private theorem centeredSquareBoundary_ae_eq_on_sides {u v : Plane → Ambient 5}
    {a b : UnitSquareBoundary → Ambient 5} (h : u = v)
    (A : CenteredSquareTraceData u a) (B : CenteredSquareTraceData v b) :
    ∀ i : Fin 2, ∀ p : Bool,
      (fun x : Domain 1 => a (unitSquareSideParameter i p (x 0))) =ᵐ[volume.restrict (unitCellCube 1).val]
        fun x => b (unitSquareSideParameter i p (x 0)) := by
  subst v
  intro i p
  have hAB : A.curve i = B.curve i := continuous_Lp_representatives_eq_of_ae_slices
    (f := fun q : Domain 1 × ℝ => u (unitCellFaceSlice i q.1 q.2))
    (g := fun q : Domain 1 × ℝ => u (unitCellFaceSlice i q.1 q.2))
    (by norm_num : (-1 : ℝ) < 1) (A.curve i) (B.curve i) (A.slice i) (B.slice i)
    (Eventually.of_forall fun _ _ => EventuallyEq.rfl)
  have hA := A.edge i p
  rw [hAB] at hA
  exact hA.symm.trans (B.edge i p)

/-- The actual square graph pushes forward to the disk with the same
boundary field and one continuous native radial endpoint class. -/
theorem unitSquareDiskSobolevPushforward : External.UnitSquareDiskSobolevPushforward := by
  refine ⟨1152, by norm_num, ?_⟩
  intro u Du hu b Tb w
  obtain ⟨Dw, hw, hEnergy⟩ := exists_unitDisk_memW12_square_pushforward u Du hu
  obtain ⟨H, hH⟩ := exists_native_disk_radial_L2_trace hw
  let h₁ : (1 / 2 : ℝ) < 1 := by norm_num
  let h := H ⟨1, h₁.le, le_rfl⟩
  let g (x : UnitSquareBoundary) := h (unitSquareCircleHomeomorph x)
  have hRaw : (fun θ => g (unitSquareCircleHomeomorph.symm θ)) = (h : NativeCircle → Ambient 5) := by
    funext θ
    change h (unitSquareCircleHomeomorph (unitSquareCircleHomeomorph.symm θ)) = h θ
    rw [Homeomorph.apply_symm_apply]
  have hEnd : ∃ hg : MemLp (fun θ => g (unitSquareCircleHomeomorph.symm θ)) 2 (unitBoundarySurface 2),
      H ⟨1, h₁.le, le_rfl⟩ = hg.toLp _ := by
    rw [hRaw]
    exact ⟨Lp.memLp h, (Lp.toLp_coeFn h (Lp.memLp h)).symm⟩
  obtain ⟨_, _, hPull⟩ := unitSquareDiskSobolevPullback
  obtain ⟨_, _, ⟨Tg⟩, _⟩ := hPull w Dw hw g h₁ H hH hEnd
  have hComp : w ∘ planarSquareBallHomeomorph = u := by
    funext x
    change u (planarSquareBallHomeomorph.symm (planarSquareBallHomeomorph x)) = u x
    rw [Homeomorph.symm_apply_apply]
  have hBoundary := ae_eq_circle_of_square_side_eq (centeredSquareBoundary_ae_eq_on_sides hComp Tg Tb)
  rw [hRaw] at hBoundary
  let hb := (Lp.memLp h).ae_eq hBoundary
  refine ⟨Dw, 1 / 2, h₁, H, by norm_num, hw, hH, ⟨hb, ?_⟩, hEnergy⟩
  exact (Lp.toLp_coeFn h (Lp.memLp h)).symm.trans (MemLp.toLp_congr (Lp.memLp h) hb hBoundary)

end Thesis

end
