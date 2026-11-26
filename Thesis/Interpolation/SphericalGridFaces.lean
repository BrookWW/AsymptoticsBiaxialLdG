module

public import Thesis.Interpolation.SphericalGrid
public import StratificationTheory.Foundation.CoordinateNormalLineGeometry
import StratificationTheory.Foundation.CoordinateACLIntegralIncrements
import StratificationTheory.Foundation.CylinderCoordinateMeasure
import StratificationTheory.Foundation.GridNeighborCoordinates
import StratificationTheory.Foundation.OriginalCoordinateLineChannels
import Mathlib.Data.Finset.Sum

/-! Original face and edge traces of a single translated sphere grid. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Module Set
open scoped BigOperators ENNReal Topology

namespace Thesis

/-- One direction along the edges of a square and one direction across it. -/
abbrev TensorGridFaceAxes := {j : Fin 3 × Fin 3 // j.1 ≠ j.2}

/-- The common index type for oriented edges and oriented square faces. -/
abbrev TensorGridSample := Fin 3 ⊕ TensorGridFaceAxes

@[expose] def tensorGridSampleDimension : TensorGridSample → ℕ
  | .inl _ => 1
  | .inr _ => 2

@[expose] def tensorGridEdgeDirection (i : Fin 3) : Fin 1 ↪ Fin 3 :=
  ⟨fun _ => i, fun _ _ _ => Subsingleton.elim _ _⟩

@[expose] def tensorGridSquareDirections (a : TensorGridFaceAxes) : Fin 2 ↪ Fin 3 := by
  refine ⟨fun i => if i = 0 then a.val.1 else a.val.2, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [a.property, Ne.symm a.property]

@[expose] def tensorGridSampleDirections (j : TensorGridSample) : Fin (tensorGridSampleDimension j) ↪ Fin 3 :=
  match j with
  | .inl i => tensorGridEdgeDirection i
  | .inr a => tensorGridSquareDirections a

/-- Physical parameter domain in the native coordinates of a cube face. -/
@[expose] def tensorGridOpenParameterBox (d : ℕ) (h : ℝ) : OpenDomain d :=
  ⟨⋂ j : Fin d, (EuclideanSpace.proj j) ⁻¹' Ioo 0 h,
    isOpen_iInter_of_finite (fun j => isOpen_Ioo.preimage (EuclideanSpace.proj j).continuous)⟩

/-- The native translated lattice at the positive mesh size. -/
@[expose] noncomputable def tensorScaledLattice (h : ℝ) (hh : 0 < h) : Submodule ℤ (Fin 3 → ℝ) :=
  Submodule.span ℤ (range ((Pi.basisFun ℝ (Fin 3)).isUnitSMul (w := fun _ : Fin 3 => h)
    (fun _ => hh.ne'.isUnit)))

@[expose] def tensorGridLatticePoint {h : ℝ} {hh : 0 < h} (c : Fin 3 → ℝ)
    (z : tensorScaledLattice h hh) : Point :=
  WithLp.toLp 2 ((z : Fin 3 → ℝ) + c)

/-- The point of an oriented square in physical coordinates, including its
edges when one of the parameter values is an endpoint. -/
@[expose] noncomputable def tensorGridSquarePoint (y : Point) (a : TensorGridFaceAxes) (s t : ℝ) : Point :=
  y + s • EuclideanSpace.single a.val.1 (1 : ℝ) + t • EuclideanSpace.single a.val.2 (1 : ℝ)

/-- Reverse which square coordinate is used for its transverse slices. -/
@[expose] def tensorGridFaceAxesSwap (a : TensorGridFaceAxes) : TensorGridFaceAxes :=
  ⟨(a.val.2, a.val.1), Ne.symm a.property⟩

theorem tensorGridSquarePoint_swap (y : Point) (a : TensorGridFaceAxes) (s t : ℝ) :
    tensorGridSquarePoint y (tensorGridFaceAxesSwap a) s t = tensorGridSquarePoint y a t s := by
  unfold tensorGridSquarePoint tensorGridFaceAxesSwap
  exact add_right_comm _ _ _

/-- Point of the original translated lattice in the native parameters of its
edge or square face. -/
@[expose] noncomputable def tensorGridSamplePoint (j : TensorGridSample) (y : Point)
    (s : Domain (tensorGridSampleDimension j)) : Point :=
  y + ∑ i : Fin (tensorGridSampleDimension j), s i • EuclideanSpace.single
    (tensorGridSampleDirections j i) (1 : ℝ)

theorem tensorGridSamplePoint_square (a : TensorGridFaceAxes) (y : Point) (s : Domain 2) :
    tensorGridSamplePoint (.inr a) y s = tensorGridSquarePoint y a (s 0) (s 1) := by
  change y + ∑ i : Fin 2, s i • EuclideanSpace.single (tensorGridSquareDirections a i) (1 : ℝ) = _
  rw [Fin.sum_univ_two]
  simp [tensorGridSquareDirections, tensorGridSquarePoint, add_assoc]

theorem tensorGridSamplePoint_edge (i : Fin 3) (y : Point) (s : Domain 1) :
    tensorGridSamplePoint (.inl i) y s = y + s 0 • EuclideanSpace.single i (1 : ℝ) := by
  change y + ∑ j : Fin 1, s j • EuclideanSpace.single (tensorGridEdgeDirection i j) (1 : ℝ) = _
  rw [Fin.sum_univ_one]
  rfl

private abbrev squareAxisPermutation (a : TensorGridFaceAxes) : Equiv.Perm (Fin 3) :=
  Equiv.swap (Fin.natAdd 2 (0 : Fin 1)) a.val.2

private noncomputable abbrev squareSplit := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)

private noncomputable abbrev squareAxisEquiv (a : TensorGridFaceAxes) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (squareAxisPermutation a)

private theorem squareSplit_head_in_unit_box (a : TensorGridFaceAxes) {y : Point}
    (hy : ∀ j : Fin 3, y j ∈ Ioo (-1 : ℝ) 1) :
    (squareSplit ((squareAxisEquiv a).symm y)).1 ∈
      ⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1 := by
  apply mem_iInter.mpr
  intro j
  change (squareSplit ((squareAxisEquiv a).symm y)).1 j ∈ Ioo (-1 : ℝ) 1
  dsimp only [squareAxisEquiv]
  rw [LinearIsometryEquiv.piLpCongrLeft_symm]
  exact hy (squareAxisPermutation a (j.castAdd 1))

private theorem squareSplit_tail_eq (a : TensorGridFaceAxes) (y : Point) :
    (squareSplit ((squareAxisEquiv a).symm y)).2 0 = y a.val.2 := by
  have h := StratificationTheory.coordinate_split_last_eq (n := 2) (squareAxisPermutation a) y
  simpa only [squareAxisPermutation, Equiv.swap_apply_left] using h

private def axesWithNormalDirection (k : Fin 3) : TensorGridFaceAxes := by
  let j : Fin 3 := if k = 0 then 1 else 0
  refine ⟨(j, k), ?_⟩
  by_cases hk : k = 0
  · subst k
    decide
  · simpa only [j, if_neg hk] using Ne.symm hk

private theorem tensorGridOpenParameterBox_one_eq (h : ℝ) :
    (tensorGridOpenParameterBox 1 h).val = (fun x : Domain 1 => x 0) ⁻¹' Ioo (0 : ℝ) h := by
  ext x
  constructor
  · intro hx
    exact mem_iInter.mp hx (0 : Fin 1)
  · intro hx
    exact mem_iInter.mpr (fun j => (Subsingleton.elim (0 : Fin 1) j) ▸ hx)

private theorem volume_tensorGridOpenParameterBox_one_ne_top (h : ℝ) :
    (volume : Measure (Domain 1)) (tensorGridOpenParameterBox 1 h).val ≠ ⊤ := by
  rw [tensorGridOpenParameterBox_one_eq, StratificationTheory.measurePreserving_domainOne_eval.measure_preimage
    measurableSet_Ioo.nullMeasurableSet]
  exact measure_Ioo_lt_top.ne

/-- Actual Sobolev graphs and compatible edge traces sampled from one
translated cubical lattice of the original radial sphere pair. -/
structure SphereFaceGrid {q : ℕ} (P : Fin 2 → UnitTensorSphere → Ambient q)
    (hP : ∀ l, StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) (P l))
    (h : ℝ) (hh : 0 < h) where
  radialPair : Fin 2 → Point → Ambient q
  gradient : Fin 2 → Point → HarmonicMaps.Gradient 3 q
  ball_memW12 : ∀ l, MemW12 (ballDomain 0 4) (radialPair l) (gradient l)
  radial_eq : ∀ (l : Fin 2) (ρ : PositiveRadius) (θ : UnitTensorSphere),
    radialPair l (ρ.val • θ.val) = P l θ
  radial_gradient_eq : ∀ (l : Fin 2) (ρ : PositiveRadius) (i : Fin 3),
    (fun θ : UnitTensorSphere => ρ.val • gradient l (ρ.val • θ.val) i) =ᵐ[tensorSphereMeasure]
      (fun θ => StratificationTheory.sphereGradient (by decide : 2 ≤ 3) (P l) (hP l) i θ)
  offset : Fin 3 → ℝ
  offset_mem : ∀ i, offset i ∈ Ico (0 : ℝ) h
  gradientChannel : ∀ j : TensorGridSample,
    (∑' z : tensorScaledLattice h hh,
      ∫⁻ s : Domain (tensorGridSampleDimension j)
        in ⋂ i : Fin (tensorGridSampleDimension j), (EuclideanSpace.proj i) ⁻¹' Ico 0 h,
        (ball (0 : Point) 4).indicator (fun x => ENNReal.ofReal
          (hsNormSq (gradient 0 x) + hsNormSq (gradient 1 x)))
          (tensorGridSamplePoint j (tensorGridLatticePoint offset z) s)) ≤
      2 * (ENNReal.ofReal (h ^ 3))⁻¹ *
        ((Fintype.card TensorGridSample : ℝ≥0∞) * ENNReal.ofReal (h ^ tensorGridSampleDimension j)) *
        ENNReal.ofReal (4 * (nativeSphereGradientEnergy (P 0) (hP 0) + nativeSphereGradientEnergy (P 1) (hP 1)))
  discrepancyChannel : ∀ j : TensorGridSample,
    (∑' z : tensorScaledLattice h hh,
      ∫⁻ s : Domain (tensorGridSampleDimension j)
        in ⋂ i : Fin (tensorGridSampleDimension j), (EuclideanSpace.proj i) ⁻¹' Ico 0 h,
        (ball (0 : Point) 4).indicator (fun x => ENNReal.ofReal
          (‖radialPair 0 x - radialPair 1 x‖ ^ 2))
          (tensorGridSamplePoint j (tensorGridLatticePoint offset z) s)) ≤
      2 * (ENNReal.ofReal (h ^ 3))⁻¹ *
        ((Fintype.card TensorGridSample : ℝ≥0∞) * ENNReal.ofReal (h ^ tensorGridSampleDimension j)) *
        ENNReal.ofReal ((64 / 3 : ℝ) * (∫ θ : UnitTensorSphere, ‖P 0 θ - P 1 θ‖ ^ 2 ∂tensorSphereMeasure))
  face_memW12 : ∀ (z : tensorScaledLattice h hh) (a : TensorGridSample)
    (U : OpenDomain (tensorGridSampleDimension a)),
    (∀ s ∈ U.val, tensorGridSamplePoint a (tensorGridLatticePoint offset z) s ∈ ball (0 : Point) 4) →
    ∀ l, MemW12 U (fun s => radialPair l (tensorGridSamplePoint a (tensorGridLatticePoint offset z) s))
      (fun s j => gradient l (tensorGridSamplePoint a (tensorGridLatticePoint offset z) s)
        (tensorGridSampleDirections a j))
  edge_trace : ∀ (z : tensorScaledLattice h hh) (i : Fin 3),
    let x := fun t : ℝ => tensorGridLatticePoint offset z + t • EuclideanSpace.single i (1 : ℝ)
    (∀ t ∈ Icc 0 h, ∀ j : Fin 3, x t j ∈ Ioo (-1 : ℝ) 1) →
    ∀ l, ∃ g : ℝ → Ambient q,
      ContinuousOn g (Icc 0 h) ∧
      g =ᵐ[volume.restrict (Ioo 0 h)] (fun t => radialPair l (x t)) ∧
      g 0 = radialPair l (x 0) ∧ g h = radialPair l (x h) ∧
      ∀ s ∈ Icc 0 h, ∀ t ∈ Icc 0 h, g t - g s = ∫ r in s..t, gradient l (x r) i
  face_trace : ∀ (z : tensorScaledLattice h hh) (a : TensorGridFaceAxes),
    let y := tensorGridLatticePoint offset z
    (∀ s ∈ Icc 0 h, ∀ t ∈ Icc 0 h, ∀ j : Fin 3,
      tensorGridSquarePoint y a s t j ∈ Ioo (-1 : ℝ) 1) →
    ∀ l, ∃ H : C(Icc (0 : ℝ) h, Lp (Ambient q) 2
        (volume.restrict (tensorGridOpenParameterBox 1 h).val)),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) h,
        ∃ hs : MemLp (fun s : Domain 1 => radialPair l (tensorGridSquarePoint y a (s 0) t))
          2 (volume.restrict (tensorGridOpenParameterBox 1 h).val),
          H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp _ ) ∧
      (∃ h₀ : MemLp (fun s : Domain 1 => radialPair l (y + s 0 • EuclideanSpace.single a.val.1 (1 : ℝ)))
        2 (volume.restrict (tensorGridOpenParameterBox 1 h).val), H ⟨0, le_rfl, hh.le⟩ = h₀.toLp _) ∧
      (∃ h₁ : MemLp (fun s : Domain 1 => radialPair l (y + h • EuclideanSpace.single a.val.2 (1 : ℝ) +
          s 0 • EuclideanSpace.single a.val.1 (1 : ℝ))) 2 (volume.restrict (tensorGridOpenParameterBox 1 h).val),
        H ⟨h, hh.le, le_rfl⟩ = h₁.toLp _)

/-- The sphere pair's face and edge data come from one native translated
lattice. Each qualified square has a single continuous transverse L² curve
whose two endpoints are its actual parallel raw edges. -/
theorem exists_sphereFaceGrid {q : ℕ} (P : Fin 2 → UnitTensorSphere → Ambient q)
    (hP : ∀ l, StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) (P l))
    {N : Set (Ambient q)} (hN : IsCompact N)
    (hTarget : ∀ l, ∀ᵐ θ ∂tensorSphereMeasure, P l θ ∈ N) {h : ℝ} (hh : 0 < h) :
    Nonempty (SphereFaceGrid P hP h hh) := by
  classical
  have hAxes (a : TensorGridFaceAxes) (i : Fin 1) :
      tensorGridEdgeDirection a.val.1 i ≠ squareAxisPermutation a (Fin.natAdd 2 (0 : Fin 1)) := by
    simpa only [tensorGridEdgeDirection, Function.Embedding.coeFn_mk, squareAxisPermutation,
      Equiv.swap_apply_left] using a.property
  obtain ⟨w, Dw, hSob, _, hRad, hRadGrad, _, _, c, hc, hFaces, hACL, _, _, hE, hD, hTrace⟩ :=
    StratificationTheory.exists_sphere_pair_original_closed_target_face_grid
      (n := 2) (by decide : 2 ≤ 2) P hP hN hTarget (fun _ : TensorGridFaceAxes => 1)
      squareAxisPermutation (fun a => tensorGridEdgeDirection a.val.1) hAxes
      tensorGridSampleDimension tensorGridSampleDirections hh
  refine ⟨{ radialPair := w
            gradient := Dw
            offset := c
            offset_mem := hc
            radial_eq := hRad
            radial_gradient_eq := hRadGrad
            gradientChannel := ?_
            discrepancyChannel := ?_
            ball_memW12 := ?_
            face_memW12 := ?_
            edge_trace := ?_
            face_trace := ?_ }⟩
  · simpa only [Nat.cast_ofNat, show (2 : ℝ) + 2 = 4 by norm_num] using hSob
  · intro j
    simpa only [tensorGridSamplePoint, tensorGridLatticePoint, tensorScaledLattice, nativeSphereGradientEnergy, Nat.reduceAdd,
      Nat.reduceSub, Nat.cast_ofNat, Nat.cast_one, pow_one, div_one, show (2 : ℝ) + 2 = 4 by norm_num,
      show (2 : ℝ) + 1 - 2 = 1 by norm_num] using hE j
  · intro j
    simpa only [tensorGridSamplePoint, tensorGridLatticePoint, tensorScaledLattice, Nat.reduceAdd, Nat.cast_ofNat,
      show (2 : ℝ) + 2 = 4 by norm_num, show (4 : ℝ) ^ 3 = 64 by norm_num,
      show (2 : ℝ) + 1 = 3 by norm_num] using hD j
  · intro z a U hInside l
    have hw := hFaces z a U (by
      simpa only [tensorGridSamplePoint, tensorGridLatticePoint, Nat.cast_ofNat,
        show (2 : ℝ) + 2 = 4 by norm_num] using hInside)
    fin_cases l
    · exact hw.1
    · exact hw.2
  · intro z i x hIn l
    let a := axesWithNormalDirection i
    let y := tensorGridLatticePoint c z
    let W := StratificationTheory.coordinatePermACLRepresentative (squareAxisPermutation a)
      (-1 : ℝ) 1 (w l) (Dw l)
    let head := (squareSplit ((squareAxisEquiv a).symm y)).1
    let line (r : ℝ) : Point := squareAxisEquiv a (squareSplit.symm (head, EuclideanSpace.single 0 r))
    let g (t : ℝ) := W (line (y i + t))
    have hAxis : squareAxisPermutation a (Fin.natAdd 2 (0 : Fin 1)) = i :=
      Equiv.swap_apply_left _ _
    have hLine (t : ℝ) : line (y i + t) = x t := by
      have hLine := StratificationTheory.coordinate_line_eq_add_normal (n := 2)
        (squareAxisPermutation a) y (y i + t)
      simpa only [hAxis, add_sub_cancel_left] using hLine
    have hBox {v : Point} (hv : ∀ j : Fin 3, v j ∈ Ioo (-1 : ℝ) 1) :
        (squareSplit ((squareAxisEquiv a).symm v)).1 ∈
          ⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1 ∧
        (squareSplit ((squareAxisEquiv a).symm v)).2 0 ∈ Ioo (-1 : ℝ) 1 :=
      ⟨squareSplit_head_in_unit_box a hv, (squareSplit_tail_eq a v) ▸ hv a.val.2⟩
    have hy : x 0 = y := by
      change y + (0 : ℝ) • EuclideanSpace.single i (1 : ℝ) = y
      rw [zero_smul, add_zero]
    have hStart := hIn 0 ⟨le_rfl, hh.le⟩
    rw [hy] at hStart
    have hShift (t : ℝ) (ht : t ∈ Icc 0 h) : y i + t ∈ Ioo (-1 : ℝ) 1 := by
      have heq : x t i = y i + t := by
        change (y + t • EuclideanSpace.single i (1 : ℝ)) i = _
        simp [PiLp.add_apply, PiLp.smul_apply]
      exact heq ▸ hIn t ht i
    obtain ⟨hLower, _, hLineGrad, hAC, hAE, _, _⟩ := hACL z l a (hBox hStart)
    have hInc (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 1) (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
        W (line t) - W (line s) = ∫ r in s..t, Dw l (line r) i := by
      calc
        _ = ∫ r in s..t, Dw l (line r) (squareAxisPermutation a (Fin.natAdd 2 (0 : Fin 1))) :=
          StratificationTheory.coordinatePermACLRepresentative_integral_increments_of_memLp
            (n := 2) (squareAxisPermutation a) (by norm_num) (w l) (Dw l) head hLineGrad s hs t ht
        _ = _ := congrArg (fun j => ∫ r in s..t, Dw l (line r) j) hAxis
    obtain ⟨z', hz'⟩ := StratificationTheory.exists_scaled_grid_neighbor hh c z i
    let y' := tensorGridLatticePoint (hh := hh) c z'
    have hzEnd : y' = x h := hz'
    have hzBox : ∀ j : Fin 3, y' j ∈ Ioo (-1 : ℝ) 1 :=
      hzEnd ▸ hIn h ⟨hh.le, le_rfl⟩
    have hUpper := (hACL z' l a (hBox hzBox)).1
    change W y' = w l y' at hUpper
    rw [hzEnd] at hUpper
    have hCont := hAC.continuousOn
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hCont
    change ContinuousOn (fun r => W (line r)) (Icc (-1 : ℝ) 1) at hCont
    refine ⟨g, hCont.comp (continuous_const.add continuous_id).continuousOn
      (fun t ht => Ioo_subset_Icc_self (hShift t ht)), ?_, ?_, ?_, ?_⟩
    · apply (ae_restrict_iff' measurableSet_Ioo).mpr
      change (fun r => W (line r)) =ᵐ[volume.restrict (Ioo (-1 : ℝ) 1)] (fun r => w l (line r)) at hAE
      have hAE' := (measurePreserving_add_left (volume : Measure ℝ) (y i)).quasiMeasurePreserving.ae
        ((ae_restrict_iff' measurableSet_Ioo).mp hAE)
      filter_upwards [hAE'] with t ht hmem
      simpa only [g, hLine] using ht (hShift t (Ioo_subset_Icc_self hmem))
    · change W (line (y i + 0)) = _
      rw [hLine, hy]
      exact hLower
    · change W (line (y i + h)) = _
      rw [hLine]
      exact hUpper
    · intro s hs t ht
      have hFTC := hInc (y i + s) (Ioo_subset_Icc_self (hShift s hs))
        (y i + t) (Ioo_subset_Icc_self (hShift t ht))
      rw [← intervalIntegral.integral_comp_add_left (fun r => Dw l (line r) i) (y i)] at hFTC
      simpa only [g, hLine] using hFTC
  · intro z a y hInside l
    let U := tensorGridOpenParameterBox 1 h
    let B := fun s : Domain 1 => s 0 • EuclideanSpace.single a.val.1 (1 : ℝ)
    have hY : ∀ i, y i ∈ Ioo (-1 : ℝ) 1 := by
      intro i
      simpa only [tensorGridSquarePoint, zero_smul, add_zero] using
        hInside 0 ⟨le_rfl, hh.le⟩ 0 ⟨le_rfl, hh.le⟩ i
    have hRight : y a.val.2 + h ∈ Ioo (-1 : ℝ) 1 := by
      simpa [tensorGridSquarePoint, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply] using
        hInside 0 ⟨le_rfl, hh.le⟩ h ⟨hh.le, le_rfl⟩ a.val.2
    have hBase (s : Domain 1) (hs : s ∈ U.val) :
        (squareSplit ((squareAxisEquiv a).symm (y + B s))).1 ∈
          ⋂ j : Fin 2, (EuclideanSpace.proj j) ⁻¹' Ioo (-1 : ℝ) 1 := by
      apply squareSplit_head_in_unit_box
      have hs' : s 0 ∈ Ioo (0 : ℝ) h := mem_iInter.mp hs 0
      intro j
      simpa only [B, tensorGridSquarePoint, zero_smul, add_zero] using
        hInside (s 0) (Ioo_subset_Icc_self hs') 0 ⟨le_rfl, hh.le⟩ j
    have hLeftNative : y (squareAxisPermutation a (Fin.natAdd 2 (0 : Fin 1))) ∈ Ioo (-1 : ℝ) 1 := by
      simpa only [squareAxisPermutation, Equiv.swap_apply_left] using hY a.val.2
    have hRightNative : y (squareAxisPermutation a (Fin.natAdd 2 (0 : Fin 1))) + h ∈ Ioo (-1 : ℝ) 1 := by
      simpa only [squareAxisPermutation, Equiv.swap_apply_left] using hRight
    obtain ⟨H, hInsideSlice, hLeftTrace, hRightTrace, _⟩ := hTrace z l a hLeftNative hRightNative U
      (volume_tensorGridOpenParameterBox_one_ne_top h) (by
        simpa only [B, Fin.sum_univ_one, tensorGridEdgeDirection, Function.Embedding.coeFn_mk] using! hBase)
    refine ⟨H, ?_, ?_, ?_⟩
    · simpa only [B, Fin.sum_univ_one, tensorGridEdgeDirection, Function.Embedding.coeFn_mk,
        squareAxisPermutation, Equiv.swap_apply_left, tensorGridSquarePoint] using! hInsideSlice
    · simpa only [B, Fin.sum_univ_one, tensorGridEdgeDirection, Function.Embedding.coeFn_mk] using! hLeftTrace
    · simpa only [B, Fin.sum_univ_one, tensorGridEdgeDirection, Function.Embedding.coeFn_mk,
        squareAxisPermutation, Equiv.swap_apply_left] using! hRightTrace

/-- The integer origin and the ordered coordinate directions of one square. -/
abbrev TensorGridSquare := (Fin 3 → ℤ) × TensorGridFaceAxes

/-- The actual squares of the boundary grid of the integer cube `[-m,m]³`.
Requiring an increasing order of the tangential axes records each physical
square once. -/
@[expose] noncomputable def cubeBoundarySquares (m : ℕ) : Finset TensorGridSquare := by
  classical
  exact (Finset.Icc (fun _ : Fin 3 => -(m : ℤ)) (fun _ => (m : ℤ)) ×ˢ Finset.univ).filter
    (fun f => f.2.val.1 < f.2.val.2 ∧ f.1 f.2.val.1 < (m : ℤ) ∧ f.1 f.2.val.2 < (m : ℤ) ∧
      ∃ j : Fin 3, j ≠ f.2.val.1 ∧ j ≠ f.2.val.2 ∧ |f.1 j| = (m : ℤ))

theorem mem_cubeBoundarySquares_iff {m : ℕ} {f : TensorGridSquare} :
    f ∈ cubeBoundarySquares m ↔
      (∀ i : Fin 3, -(m : ℤ) ≤ f.1 i ∧ f.1 i ≤ (m : ℤ)) ∧
        f.2.val.1 < f.2.val.2 ∧ f.1 f.2.val.1 < (m : ℤ) ∧ f.1 f.2.val.2 < (m : ℤ) ∧
        ∃ j : Fin 3, j ≠ f.2.val.1 ∧ j ≠ f.2.val.2 ∧ |f.1 j| = (m : ℤ) := by
  classical
  rcases f with ⟨z, a⟩
  simp only [cubeBoundarySquares, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
    Finset.mem_Icc, Pi.le_def, ← forall_and]

/-- Boundary squares of distinct integer levels have disjoint index sets. -/
theorem disjoint_cubeBoundarySquares {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (cubeBoundarySquares m) (cubeBoundarySquares n) := by
  apply Finset.disjoint_left.mpr
  intro f hm hn
  obtain ⟨hmb, _, _, _, i, _, _, hi⟩ := mem_cubeBoundarySquares_iff.mp hm
  obtain ⟨hnb, _, _, _, j, _, _, hj⟩ := mem_cubeBoundarySquares_iff.mp hn
  have hij : (m : ℤ) ≤ n := hi ▸ abs_le.mpr (hnb i)
  have hji : (n : ℤ) ≤ m := hj ▸ abs_le.mpr (hmb j)
  exact hmn (by exact_mod_cast le_antisymm hij hji)

/-- The physical vertex of the mesh with offset `c` and mesh size `h`. -/
@[expose] noncomputable def tensorGridVertex (c : Point) (h : ℝ) (z : Fin 3 → ℤ) : Point :=
  WithLp.toLp 2 (fun i : Fin 3 => c i + (z i : ℝ) * h)

theorem tensorGridVertex_add_unit (c : Point) (h : ℝ) (z : Fin 3 → ℤ) (i : Fin 3) :
    tensorGridVertex c h (z + Pi.single i (1 : ℤ)) =
      tensorGridVertex c h z + h • EuclideanSpace.single i (1 : ℝ) := by
  apply PiLp.ext
  intro j
  change c j + ((z + Pi.single i (1 : ℤ) : Fin 3 → ℤ) j : ℝ) * h =
    (tensorGridVertex c h z + h • EuclideanSpace.single i (1 : ℝ)) j
  simp only [tensorGridVertex, Pi.add_apply, Int.cast_add, PiLp.add_apply, PiLp.smul_apply,
    Pi.single_apply, PiLp.single_apply]
  split_ifs <;> push_cast <;> ring

theorem tensorGridSquarePoint_apply (c : Point) (h : ℝ) (f : TensorGridSquare)
    (s t : ℝ) (i : Fin 3) :
    tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 s t i =
      c i + (f.1 i : ℝ) * h + (if i = f.2.val.1 then s else 0) +
        (if i = f.2.val.2 then t else 0) := by
  simp only [tensorGridSquarePoint, tensorGridVertex, PiLp.add_apply, PiLp.smul_apply,
    PiLp.single_apply]
  split_ifs <;> ring

/-- The entire closed parameter square maps into the boundary of the same
shifted physical cube, including all endpoints of its four edges. -/
theorem tensorGridSquarePoint_mem_frontier {c : Point} {h : ℝ} (hh : 0 < h)
    {m : ℕ} {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares m)
    {s t : ℝ} (hs : s ∈ Icc 0 h) (ht : t ∈ Icc 0 h) :
    tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 s t ∈
      frontier (shiftedCoordinateCube c ((m : ℝ) * h)) := by
  obtain ⟨hBox, _, hFirst, hSecond, j, hj₁, hj₂, hSat⟩ := mem_cubeBoundarySquares_iff.mp hf
  let x := tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 s t
  have hMem : x ∈ shiftedCoordinateCube c ((m : ℝ) * h) := by
    apply mem_iInter.mpr
    intro i
    change c i - (m : ℝ) * h ≤ x i ∧ x i ≤ c i + (m : ℝ) * h
    have hlo : -(m : ℝ) ≤ (f.1 i : ℝ) := by exact_mod_cast (hBox i).1
    have hhi : (f.1 i : ℝ) ≤ (m : ℝ) := by exact_mod_cast (hBox i).2
    have hlo' := mul_le_mul_of_nonneg_right hlo hh.le
    have hhi' := mul_le_mul_of_nonneg_right hhi hh.le
    change _ ≤ tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 s t i ∧
      tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 s t i ≤ _
    rw [tensorGridSquarePoint_apply]
    by_cases h₁ : i = f.2.val.1
    · have h₂ : i ≠ f.2.val.2 := h₁.symm ▸ f.2.property
      have hStep : (f.1 i : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast (show f.1 i + 1 ≤ (m : ℤ) by rw [h₁]; omega)
      have hStep' := mul_le_mul_of_nonneg_right hStep hh.le
      rw [if_pos h₁, if_neg h₂, add_zero]
      exact ⟨by linarith only [hlo', hs.1], by linarith only [hStep', hs.2]⟩
    · by_cases h₂ : i = f.2.val.2
      · have hStep : (f.1 i : ℝ) + 1 ≤ (m : ℝ) := by
          exact_mod_cast (show f.1 i + 1 ≤ (m : ℤ) by rw [h₂]; omega)
        have hStep' := mul_le_mul_of_nonneg_right hStep hh.le
        rw [if_neg h₁, if_pos h₂, add_zero]
        exact ⟨by linarith only [hlo', ht.1], by linarith only [hStep', ht.2]⟩
      · rw [if_neg h₁, if_neg h₂, add_zero, add_zero]
        exact ⟨by linarith only [hlo'], by linarith only [hhi']⟩
  refine ⟨subset_closure hMem, ?_⟩
  intro hInterior
  have hjCube : shiftedCoordinateCube c ((m : ℝ) * h) ⊆
      (EuclideanSpace.proj j) ⁻¹' Icc (c j - (m : ℝ) * h) (c j + (m : ℝ) * h) :=
    iInter_subset _ j
  have hOpen : IsOpenMap (EuclideanSpace.proj j : Point → ℝ) :=
    PiLp.isOpenMap_apply 2 (fun _ : Fin 3 => ℝ) j
  have hJ := hOpen.interior_preimage_subset_preimage_interior (interior_mono hjCube hInterior)
  rw [interior_Icc] at hJ
  change tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 s t j ∈
    Ioo (c j - (m : ℝ) * h) (c j + (m : ℝ) * h) at hJ
  rw [tensorGridSquarePoint_apply, if_neg hj₁, if_neg hj₂, add_zero, add_zero] at hJ
  rcases eq_or_eq_neg_of_abs_eq hSat with hUpper | hLower
  · have hu : (f.1 j : ℝ) = m := by exact_mod_cast hUpper
    rw [hu] at hJ
    exact (lt_irrefl _) hJ.2
  · have hl : (f.1 j : ℝ) = -(m : ℝ) := by exact_mod_cast hLower
    rw [hl, neg_mul, ← sub_eq_add_neg] at hJ
    exact (lt_irrefl _) hJ.1

/-- The four actual boundary curves of a physical grid square are physical
grid edges with their common vertex labels. -/
theorem tensorGridSquarePoint_boundary (c : Point) (h : ℝ) (f : TensorGridSquare) (t : ℝ) :
    tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 t 0 =
        tensorGridEdgePoint c h ⟨f.1, f.2.val.1⟩ t ∧
      tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 t h =
        tensorGridEdgePoint c h ⟨f.1 + Pi.single f.2.val.2 (1 : ℤ), f.2.val.1⟩ t ∧
      tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 0 t =
        tensorGridEdgePoint c h ⟨f.1, f.2.val.2⟩ t ∧
      tensorGridSquarePoint (tensorGridVertex c h f.1) f.2 h t =
        tensorGridEdgePoint c h ⟨f.1 + Pi.single f.2.val.1 (1 : ℤ), f.2.val.2⟩ t := by
  have hEdge (z : Fin 3 → ℤ) (j : Fin 3) :
      tensorGridEdgePoint c h ⟨z, j⟩ t = tensorGridVertex c h z + t • EuclideanSpace.single j (1 : ℝ) := rfl
  simp only [hEdge, tensorGridSquarePoint, tensorGridVertex_add_unit, zero_smul, add_zero,
    true_and, and_true]
  exact add_right_comm _ _ _

/-- All four integer edge labels of a selected square are edges of the same
boundary mesh. -/
theorem cubeBoundarySquares_edges_mem {m : ℕ} {f : TensorGridSquare}
    (hf : f ∈ cubeBoundarySquares m) :
    (f.1, f.2.val.1) ∈ cubeBoundaryEdges m ∧
      (f.1 + Pi.single f.2.val.2 (1 : ℤ), f.2.val.1) ∈ cubeBoundaryEdges m ∧
    (f.1, f.2.val.2) ∈ cubeBoundaryEdges m ∧
      (f.1 + Pi.single f.2.val.1 (1 : ℤ), f.2.val.2) ∈ cubeBoundaryEdges m := by
  obtain ⟨hBox, _, hFirst, hSecond, j, hj₁, hj₂, hSat⟩ := mem_cubeBoundarySquares_iff.mp hf
  have hShift {i k : Fin 3} (hki : i ≠ k) (hi : f.1 i < (m : ℤ)) (hk : f.1 k < (m : ℤ))
      (hji : j ≠ i) (hjk : j ≠ k) : (f.1 + Pi.single k (1 : ℤ), i) ∈ cubeBoundaryEdges m := by
    apply mem_cubeBoundaryEdges_iff.mpr
    refine ⟨?_, ?_, ⟨j, hji, ?_⟩⟩
    · intro l
      by_cases hl : l = k
      · subst l
        change -(m : ℤ) ≤ (f.1 + Pi.single k (1 : ℤ) : Fin 3 → ℤ) k ∧
           (f.1 + Pi.single k (1 : ℤ) : Fin 3 → ℤ) k ≤ (m : ℤ)
        simp only [Pi.add_apply, Pi.single_apply]
        have hb := (hBox k).1
        omega
      · simpa [Pi.single_apply, hl] using hBox l
    · simpa [Pi.single_apply, hki] using hi
    · simpa [Pi.single_apply, hjk] using hSat
  exact ⟨mem_cubeBoundaryEdges_iff.mpr ⟨hBox, hFirst, j, hj₁, hSat⟩,
    hShift f.2.property hFirst hSecond hj₁ hj₂,
    mem_cubeBoundaryEdges_iff.mpr ⟨hBox, hSecond, j, hj₂, hSat⟩,
    hShift f.2.property.symm hSecond hFirst hj₂ hj₁⟩

variable {q : ℕ} {P : Fin 2 → UnitTensorSphere → Ambient q}
  {hP : ∀ l, StratificationTheory.MemSphereW12 (by decide : 2 ≤ 3) (P l)}
  {h : ℝ} {hh : 0 < h}

@[expose] def SphereFaceGrid.center (G : SphereFaceGrid P hP h hh) : Point :=
  WithLp.toLp 2 G.offset

/-- One closed cube in the selected native lattice with jointly controlled
physical edge and square sums. The vertex embedding retains the original
native face and edge trace configuration on this cube. -/
structure SphereFaceCube (G : SphereFaceGrid P hP h hh) where
  hsmall : h ≤ 1 / 32
  level : ℕ
  radius_mem : (level : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4)
  vertex : (Fin 3 → ℤ) ↪ tensorScaledLattice h hh
  vertex_eq : ∀ z i, (vertex z : Fin 3 → ℝ) i = (z i : ℝ) * h
  gradient_budget :
    (∑ e ∈ cubeBoundaryEdges level, ∫⁻ t in Ioo (0 : ℝ) h,
      ENNReal.ofReal (hsNormSq (G.gradient 0 (tensorGridEdgePoint G.center h e t)) +
        hsNormSq (G.gradient 1 (tensorGridEdgePoint G.center h e t)))) ≤
      ENNReal.ofReal ((768 * Fintype.card TensorGridSample : ℝ) / h) *
        ENNReal.ofReal (nativeSphereGradientEnergy (P 0) (hP 0) + nativeSphereGradientEnergy (P 1) (hP 1))
  discrepancy_budget :
    (∑ e ∈ cubeBoundaryEdges level, ∫⁻ t in Ioo (0 : ℝ) h,
      ENNReal.ofReal (‖G.radialPair 0 (tensorGridEdgePoint G.center h e t) -
        G.radialPair 1 (tensorGridEdgePoint G.center h e t)‖ ^ 2)) ≤
      ENNReal.ofReal ((4096 * Fintype.card TensorGridSample : ℝ) / h) *
        ENNReal.ofReal (∫ θ : UnitTensorSphere, ‖P 0 θ - P 1 θ‖ ^ 2 ∂tensorSphereMeasure)
  square_gradient_budget :
    (∑ f ∈ cubeBoundarySquares level, ∫⁻ s in (tensorGridOpenParameterBox 2 h).val,
      let x := tensorGridSquarePoint (tensorGridVertex G.center h f.1) f.2 (s 0) (s 1)
      ENNReal.ofReal (hsNormSq (G.gradient 0 x) + hsNormSq (G.gradient 1 x))) ≤
      ENNReal.ofReal (4608 * Fintype.card TensorGridSample : ℝ) *
        ENNReal.ofReal (nativeSphereGradientEnergy (P 0) (hP 0) + nativeSphereGradientEnergy (P 1) (hP 1))
  square_discrepancy_budget :
    (∑ f ∈ cubeBoundarySquares level, ∫⁻ s in (tensorGridOpenParameterBox 2 h).val,
      let x := tensorGridSquarePoint (tensorGridVertex G.center h f.1) f.2 (s 0) (s 1)
      ENNReal.ofReal (‖G.radialPair 0 x - G.radialPair 1 x‖ ^ 2)) ≤
      ENNReal.ofReal (24576 * Fintype.card TensorGridSample : ℝ) *
        ENNReal.ofReal (∫ θ : UnitTensorSphere, ‖P 0 θ - P 1 θ‖ ^ 2 ∂tensorSphereMeasure)

theorem SphereFaceCube.vertex_point_eq {G : SphereFaceGrid P hP h hh} (C : SphereFaceCube G)
    (z : Fin 3 → ℤ) : tensorGridLatticePoint G.offset (C.vertex z) = tensorGridVertex G.center h z := by
  apply PiLp.ext
  intro i
  change (C.vertex z : Fin 3 → ℝ) i + G.offset i = G.offset i + (z i : ℝ) * h
  rw [C.vertex_eq, add_comm]

theorem SphereFaceCube.frontier_coordinates {G : SphereFaceGrid P hP h hh} (C : SphereFaceCube G)
    {x : Point} (hx : x ∈ frontier (shiftedCoordinateCube G.center ((C.level : ℝ) * h))) :
    ∀ i : Fin 3, x i ∈ Ioo (-1 : ℝ) 1 := by
  have hc (i : Fin 3) : G.center i ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(G.offset_mem i).1, (G.offset_mem i).2.le.trans C.hsmall⟩
  obtain ⟨hClosed, _, hBox, _⟩ := shiftedCoordinateCube_geometry hc C.radius_mem
  exact hBox x (hClosed.closure_eq ▸ frontier_subset_closure hx)

private theorem in_ball_four_of_coordinates {x : Point}
    (hx : ∀ i : Fin 3, x i ∈ Ioo (-1 : ℝ) 1) : x ∈ ball (0 : Point) 4 := by
  have hNorm := StratificationTheory.euclidean_norm_le_dim_of_coordinate_bound x
    (fun i => (abs_lt.mpr (hx i)).le)
  exact mem_ball_zero_iff.mpr (hNorm.trans_lt (by norm_num))

private theorem native_grid_channel_coefficient {h : ℝ} (hh : 0 < h) (n : ℕ) (r : ℝ) :
    2 * (ENNReal.ofReal (h ^ 3))⁻¹ * ((n : ℝ≥0∞) * ENNReal.ofReal r) =
      ENNReal.ofReal (2 * (h ^ 3)⁻¹ * ((n : ℝ) * r)) := by
  rw [← ENNReal.ofReal_inv_of_pos (pow_pos hh 3), ← ENNReal.ofReal_natCast n,
    ← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.ofReal_mul (by positivity)]

private theorem native_grid_channel_sum {ι L : Type*} [Fintype ι]
    (ν : (Fin 3 → ℤ) ↪ L) (F : ι → L → ℝ≥0∞) (b : ℝ≥0∞)
    (hF : ∀ i, (∑' z, F i z) ≤ b) :
    (∑' e : (Fin 3 → ℤ) × ι, F e.2 (ν e.1)) ≤ (Fintype.card ι : ℝ≥0∞) * b := by
  calc
    _ = ∑' z : Fin 3 → ℤ, ∑' i : ι, F i (ν z) :=
      ENNReal.tsum_prod (f := fun (z : Fin 3 → ℤ) (i : ι) => F i (ν z))
    _ = ∑ i : ι, ∑' z : Fin 3 → ℤ, F i (ν z) := by rw [ENNReal.tsum_comm, tsum_fintype]
    _ ≤ ∑ _i : ι, b := Finset.sum_le_sum fun i _ =>
      (ENNReal.tsum_comp_le_tsum_of_injective ν.injective (F i)).trans (hF i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem combined_grid_channel_coefficient {h : ℝ} (hh : 0 < h) (n : ℕ) :
    ENNReal.ofReal h * (3 * ENNReal.ofReal ((2 * n : ℝ) / h ^ 2)) +
      ENNReal.ofReal (1 / 6) * (9 * ENNReal.ofReal ((2 * n : ℝ) / h)) =
      ENNReal.ofReal ((9 * n : ℝ) / h) := by
  rw [← ENNReal.ofReal_ofNat (n := 3), ← ENNReal.ofReal_ofNat (n := 9),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ← ENNReal.ofReal_mul hh.le,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 6),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

/-- Two weighted channels choose one level of the already selected lattice.
At each level the edge term is weighted by the mesh size and the square term
by a fixed constant. This gives the inverse mesh-size bound on the edges
and a uniform bound on the square sums. -/
theorem SphereFaceGrid.exists_cube (G : SphereFaceGrid P hP h hh) (hsmall : h ≤ 1 / 32) :
    Nonempty (SphereFaceCube G) := by
  classical
  let c := G.center
  let L := tensorScaledLattice h hh
  obtain ⟨embedding, hEmbedding⟩ := scaled_integer_lattice_embedding hh
  let ν : (Fin 3 → ℤ) ↪ L := embedding
  have hν (z : Fin 3 → ℤ) (i : Fin 3) : (ν z : Fin 3 → ℝ) i = (z i : ℝ) * h := hEmbedding z i
  let origin (z : L) := tensorGridLatticePoint G.offset z
  have hOrigin (z : Fin 3 → ℤ) : tensorGridVertex c h z = origin (ν z) := by
    apply PiLp.ext
    intro i
    change G.offset i + (z i : ℝ) * h = (ν z : Fin 3 → ℝ) i + G.offset i
    rw [hν, add_comm]
  let K := ball (0 : Point) 4
  let Edata (x : Point) := ENNReal.ofReal (hsNormSq (G.gradient 0 x) + hsNormSq (G.gradient 1 x))
  let Ddata (x : Point) := ENNReal.ofReal (‖G.radialPair 0 x - G.radialPair 1 x‖ ^ 2)
  let channel (f : Point → ℝ≥0∞) (j : TensorGridSample) (z : L) :=
    ∫⁻ t : Domain (tensorGridSampleDimension j)
        in ⋂ i : Fin (tensorGridSampleDimension j), (EuclideanSpace.proj i) ⁻¹' Ico (0 : ℝ) h,
      K.indicator f (tensorGridSamplePoint j (origin z) t)
  let A := nativeSphereGradientEnergy (P 0) (hP 0) + nativeSphereGradientEnergy (P 1) (hP 1)
  let D := ∫ θ : UnitTensorSphere, ‖P 0 θ - P 1 θ‖ ^ 2 ∂tensorSphereMeasure
  let n := Fintype.card TensorGridSample
  let coeff (j : TensorGridSample) : ℝ≥0∞ :=
    2 * (ENNReal.ofReal (h ^ 3))⁻¹ * ((n : ℝ≥0∞) * ENNReal.ofReal (h ^ tensorGridSampleDimension j))
  have hCoeffEdge (i : Fin 3) : coeff (.inl i) = ENNReal.ofReal ((2 * n : ℝ) / h ^ 2) := by
    change 2 * (ENNReal.ofReal (h ^ 3))⁻¹ * ((n : ℝ≥0∞) * ENNReal.ofReal (h ^ 1)) = _
    rw [native_grid_channel_coefficient hh n (h ^ 1)]
    congr 1
    field_simp
  have hCoeffSquare (a : TensorGridFaceAxes) : coeff (.inr a) = ENNReal.ofReal ((2 * n : ℝ) / h) := by
    change 2 * (ENNReal.ofReal (h ^ 3))⁻¹ * ((n : ℝ≥0∞) * ENNReal.ofReal (h ^ 2)) = _
    rw [native_grid_channel_coefficient hh n (h ^ 2)]
    congr 1
    field_simp
  let edge (f : Point → ℝ≥0∞) (e : TensorGridEdge) := channel f (.inl e.2) (ν e.1)
  let square (f : Point → ℝ≥0∞) (e : TensorGridSquare) := channel f (.inr e.2) (ν e.1)
  let weight (f : Point → ℝ≥0∞) : TensorGridEdge ⊕ TensorGridSquare → ℝ≥0∞ :=
    Sum.elim (fun e => ENNReal.ofReal h * edge f e) (fun s => ENNReal.ofReal (1 / 6) * square f s)
  have hCard : Fintype.card TensorGridFaceAxes ≤ 9 := by
    have hc := Fintype.card_le_of_injective (fun a : TensorGridFaceAxes => a.val) Subtype.val_injective
    simpa only [Fintype.card_prod, Fintype.card_fin, show 3 * 3 = (9 : ℕ) by norm_num] using hc
  have hTotal (f : Point → ℝ≥0∞) (b : ℝ)
      (hf : ∀ j, (∑' z, channel f j z) ≤ coeff j * ENNReal.ofReal b) :
      (∑' e, weight f e) ≤ ENNReal.ofReal ((9 * n : ℝ) / h) * ENNReal.ofReal b := by
    have hEdge : (∑' e, edge f e) ≤ 3 * (ENNReal.ofReal ((2 * n : ℝ) / h ^ 2) * ENNReal.ofReal b) := by
      simpa only [Fintype.card_fin, Nat.cast_ofNat] using
        native_grid_channel_sum ν (fun i => channel f (.inl i)) _
          (fun i => by simpa only [hCoeffEdge] using hf (.inl i))
    have hSquare : (∑' e, square f e) ≤ 9 * (ENNReal.ofReal ((2 * n : ℝ) / h) * ENNReal.ofReal b) := by
      exact (native_grid_channel_sum ν (fun i => channel f (.inr i)) _
        (fun i => by simpa only [hCoeffSquare] using hf (.inr i))).trans
        (mul_le_mul_left (by exact_mod_cast hCard) _)
    have hSum := (ENNReal.summable (f := weight f ∘ Sum.inl)).tsum_sum
      (ENNReal.summable (f := weight f ∘ Sum.inr))
    rw [hSum]
    simp only [weight, Sum.elim_inl, Sum.elim_inr, ENNReal.tsum_mul_left]
    refine (add_le_add (mul_le_mul_right hEdge _) (mul_le_mul_right hSquare _)).trans_eq ?_
    simp only [← mul_assoc, ← add_mul]
    rw [mul_assoc (ENNReal.ofReal h), mul_assoc (ENNReal.ofReal (1 / 6)), combined_grid_channel_coefficient hh n]
  have hEraw (j : TensorGridSample) : (∑' z, channel Edata j z) ≤ coeff j * ENNReal.ofReal (4 * A) :=
    G.gradientChannel j
  have hDraw (j : TensorGridSample) : (∑' z, channel Ddata j z) ≤ coeff j * ENNReal.ofReal ((64 / 3) * D) :=
    G.discrepancyChannel j
  let B (m : ℕ) := (cubeBoundaryEdges m).disjSum (cubeBoundarySquares m)
  have hDisj : Pairwise (fun m n => Disjoint (B m) (B n)) := by
    intro m n hmn
    apply Finset.disjoint_left.mpr
    intro z hz hw
    rcases z with e | s
    · exact Finset.disjoint_left.mp (disjoint_cubeBoundaryEdges hmn)
        (Finset.inl_mem_disjSum.mp hz) (Finset.inl_mem_disjSum.mp hw)
    · exact Finset.disjoint_left.mp (disjoint_cubeBoundarySquares hmn)
        (Finset.inr_mem_disjSum.mp hz) (Finset.inr_mem_disjSum.mp hw)
  obtain ⟨m, hm, hSelE, hSelD⟩ := exists_meshBoundary_linear_gain hh hsmall B hDisj (weight Edata)
    (weight Ddata)
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hTotal Edata _ hEraw))
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) (hTotal Ddata _ hDraw))
  have hSplit (f : Point → ℝ≥0∞) :
      (∑ z ∈ B m, weight f z) =
        ENNReal.ofReal h * (∑ e ∈ cubeBoundaryEdges m, edge f e) +
          ENNReal.ofReal (1 / 6) * (∑ s ∈ cubeBoundarySquares m, square f s) := by
    unfold B
    rw [← Finset.map_inl_disjUnion_map_inr, Finset.sum_disjUnion, Finset.sum_map, Finset.sum_map]
    simp only [weight, Function.Embedding.inl_apply, Function.Embedding.inr_apply,
      Sum.elim_inl, Sum.elim_inr, Finset.mul_sum]
  have hBudgets (f : Point → ℝ≥0∞) (b : ℝ)
      (hf : ∀ j, (∑' z, channel f j z) ≤ coeff j * ENNReal.ofReal b)
      (hsel : (∑ z ∈ B m, weight f z) ≤ ENNReal.ofReal ((64 / 3) * h) * ∑' z, weight f z) :
      (∑ e ∈ cubeBoundaryEdges m, edge f e) ≤ ENNReal.ofReal ((192 * n : ℝ) / h) * ENNReal.ofReal b ∧
      (∑ s ∈ cubeBoundarySquares m, square f s) ≤ ENNReal.ofReal (1152 * n : ℝ) * ENNReal.ofReal b := by
    have hCombined := hsel.trans (mul_le_mul_right (hTotal f b hf) _)
    have hScale : ((64 / 3) * h) * ((9 * n : ℝ) / h) = (192 * n : ℝ) := by field_simp; ring
    rw [hSplit, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hScale] at hCombined
    have hEd : ENNReal.ofReal h * ENNReal.ofReal ((192 * n : ℝ) / h) = ENNReal.ofReal (192 * n : ℝ) := by
      rw [← ENNReal.ofReal_mul hh.le, mul_comm h, div_mul_cancel₀ _ hh.ne']
    have hSq : ENNReal.ofReal (1 / 6) * ENNReal.ofReal (1152 * n : ℝ) =
        ENNReal.ofReal (192 * n : ℝ) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 6)]
      congr 1
      ring
    constructor
    · apply (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hh).ne' ENNReal.ofReal_ne_top).mp
      rw [← mul_assoc, hEd]
      exact le_self_add.trans hCombined
    · apply (ENNReal.mul_le_mul_iff_right (by norm_num : ENNReal.ofReal (1 / 6) ≠ 0) ENNReal.ofReal_ne_top).mp
      rw [← mul_assoc, hSq]
      exact le_add_self.trans hCombined
  have hc (i : Fin 3) : c i ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(G.offset_mem i).1, (G.offset_mem i).2.le.trans hsmall⟩
  obtain ⟨hClosed, _, hCoordinates, _⟩ := shiftedCoordinateCube_geometry hc hm
  have hImage {x : Point} (hx : x ∈ frontier (shiftedCoordinateCube c ((m : ℝ) * h))) : x ∈ K :=
    in_ball_four_of_coordinates (hCoordinates _ (hClosed.closure_eq ▸ frontier_subset_closure hx))
  have hEdgeSample (f : Point → ℝ≥0∞) (e : TensorGridEdge) (he : e ∈ cubeBoundaryEdges m) :
      (∫⁻ t in Ioo (0 : ℝ) h, f (tensorGridEdgePoint c h e t)) ≤ edge f e := by
    have hPoint (t : ℝ) : tensorGridEdgePoint c h e t =
        origin (ν e.1) + t • EuclideanSpace.single e.2 (1 : ℝ) := by
      change tensorGridVertex c h e.1 + t • EuclideanSpace.single e.2 (1 : ℝ) = _
      rw [hOrigin]
    calc
      _ ≤ ∫⁻ t in Ioo (0 : ℝ) h, K.indicator f (tensorGridEdgePoint c h e t) := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro t ht
        rw [indicator_of_mem (hImage (tensorGridEdgePoint_mem_frontier hh he (Ioo_subset_Icc_self ht)))]
      _ ≤ _ := by
        simp_rw [hPoint]
        dsimp only [edge, channel, tensorGridSampleDimension]
        simp only [tensorGridSamplePoint_edge]
        exact StratificationTheory.lintegral_real_edge_le_native_channel _ _ _ _ (fun _ _ => le_rfl)
  have hSquareSample (f : Point → ℝ≥0∞) (s : TensorGridSquare) (hs : s ∈ cubeBoundarySquares m) :
      (∫⁻ t in (tensorGridOpenParameterBox 2 h).val,
        f (tensorGridSquarePoint (tensorGridVertex c h s.1) s.2 (t 0) (t 1))) ≤ square f s := by
    let V := tensorGridOpenParameterBox 2 h
    let x := fun t : Domain 2 => tensorGridSamplePoint (.inr s.2) (origin (ν s.1)) t
    have hx (t : Domain 2) : x t = tensorGridSquarePoint (tensorGridVertex c h s.1) s.2 (t 0) (t 1) := by
      change tensorGridSamplePoint (.inr s.2) (origin (ν s.1)) t = _
      rw [tensorGridSamplePoint_square, ← hOrigin]
    calc
      _ ≤ ∫⁻ t in V.val, K.indicator f (x t) := by
        apply setLIntegral_mono' V.property.measurableSet
        intro t ht
        have ht₀ : t 0 ∈ Icc 0 h := Ioo_subset_Icc_self (mem_iInter.mp ht 0)
        have ht₁ : t 1 ∈ Icc 0 h := Ioo_subset_Icc_self (mem_iInter.mp ht 1)
        rw [hx, indicator_of_mem (hImage (tensorGridSquarePoint_mem_frontier hh hs ht₀ ht₁))]
      _ ≤ _ := by
        apply lintegral_mono_set
        intro t ht
        exact mem_iInter.mpr (fun i => Ioo_subset_Ico_self (mem_iInter.mp ht i))
  obtain ⟨hEdgeE, hFaceE⟩ := hBudgets Edata _ hEraw hSelE
  obtain ⟨hEdgeD, hFaceD⟩ := hBudgets Ddata _ hDraw hSelD
  refine ⟨{ hsmall := hsmall
            level := m
            radius_mem := hm
            vertex := ν
            vertex_eq := hν
            gradient_budget := ?_
            discrepancy_budget := ?_
            square_gradient_budget := ?_
            square_discrepancy_budget := ?_ }⟩
  · refine (Finset.sum_le_sum (fun e he => hEdgeSample Edata e he)).trans (hEdgeE.trans_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (192 * n : ℝ) / h),
      show ((192 * n : ℝ) / h) * (4 * A) = ((768 * n : ℝ) / h) * A by ring,
      ENNReal.ofReal_mul (by positivity)]
  · refine (Finset.sum_le_sum (fun e he => hEdgeSample Ddata e he)).trans (hEdgeD.trans_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (192 * n : ℝ) / h),
      show ((192 * n : ℝ) / h) * ((64 / 3) * D) = ((4096 * n : ℝ) / h) * D by ring,
      ENNReal.ofReal_mul (by positivity)]
  · refine (Finset.sum_le_sum (fun s hs => hSquareSample Edata s hs)).trans (hFaceE.trans_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (1152 * n : ℝ)),
      show (1152 * n : ℝ) * (4 * A) = (4608 * n : ℝ) * A by ring,
      ENNReal.ofReal_mul (by positivity)]
  · refine (Finset.sum_le_sum (fun s hs => hSquareSample Ddata s hs)).trans (hFaceD.trans_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (1152 * n : ℝ)),
      show (1152 * n : ℝ) * ((64 / 3) * D) = (24576 * n : ℝ) * D by ring,
      ENNReal.ofReal_mul (by positivity)]

theorem SphereFaceCube.edge_memW12 {G : SphereFaceGrid P hP h hh} (C : SphereFaceCube G)
    {e : TensorGridEdge} (he : e ∈ cubeBoundaryEdges C.level) (l : Fin 2) :
    MemW12 (tensorGridOpenParameterBox 1 h)
      (fun t => G.radialPair l (tensorGridEdgePoint G.center h e (t 0)))
      (fun t _ => G.gradient l (tensorGridEdgePoint G.center h e (t 0)) e.2) := by
  have hPoint (t : Domain 1) :
      tensorGridSamplePoint (.inl e.2) (tensorGridLatticePoint G.offset (C.vertex e.1)) t =
        tensorGridEdgePoint G.center h e (t 0) := by
    rw [tensorGridSamplePoint_edge, C.vertex_point_eq]
    rfl
  have hIn (t : Domain 1) (ht : t ∈ (tensorGridOpenParameterBox 1 h).val) :
      tensorGridSamplePoint (.inl e.2) (tensorGridLatticePoint G.offset (C.vertex e.1)) t ∈ ball (0 : Point) 4 := by
    rw [hPoint]
    apply in_ball_four_of_coordinates
    apply C.frontier_coordinates
    exact tensorGridEdgePoint_mem_frontier hh he (Ioo_subset_Icc_self (mem_iInter.mp ht 0))
  have h := G.face_memW12 (C.vertex e.1) (.inl e.2) (tensorGridOpenParameterBox 1 h) hIn l
  simpa only [hPoint, tensorGridSampleDirections, tensorGridEdgeDirection, Function.Embedding.coeFn_mk] using! h

/-- Every selected edge has the original continuous representative, agreed
at both physical vertices of the same chosen cube. -/
theorem SphereFaceCube.edge_trace {G : SphereFaceGrid P hP h hh} (C : SphereFaceCube G)
    {e : TensorGridEdge} (he : e ∈ cubeBoundaryEdges C.level) (l : Fin 2) :
    ∃ g : ℝ → Ambient q, ContinuousOn g (Icc 0 h) ∧
      g =ᵐ[volume.restrict (Ioo 0 h)] (fun t => G.radialPair l (tensorGridEdgePoint G.center h e t)) ∧
      g 0 = G.radialPair l (tensorGridEdgePoint G.center h e 0) ∧
      g h = G.radialPair l (tensorGridEdgePoint G.center h e h) ∧
      ∀ s ∈ Icc 0 h, ∀ t ∈ Icc 0 h, g t - g s =
        ∫ r in s..t, G.gradient l (tensorGridEdgePoint G.center h e r) e.2 := by
  have hPoint (t : ℝ) :
      tensorGridLatticePoint G.offset (C.vertex e.1) + t • EuclideanSpace.single e.2 (1 : ℝ) =
        tensorGridEdgePoint G.center h e t := by
    rw [C.vertex_point_eq]
    rfl
  have hunit (t : ℝ) (ht : t ∈ Icc 0 h) (i : Fin 3) :
      (tensorGridLatticePoint G.offset (C.vertex e.1) + t • EuclideanSpace.single e.2 (1 : ℝ)) i ∈
        Ioo (-1 : ℝ) 1 := by
    rw [hPoint]
    exact C.frontier_coordinates (tensorGridEdgePoint_mem_frontier hh he ht) i
  simpa only [hPoint] using G.edge_trace (C.vertex e.1) e.2 hunit l

/-- The original pair has a displayed weak graph on every selected square. -/
theorem SphereFaceCube.square_memW12 {G : SphereFaceGrid P hP h hh} (C : SphereFaceCube G)
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares C.level) (l : Fin 2) :
    let y := tensorGridVertex G.center h f.1
    MemW12 (tensorGridOpenParameterBox 2 h)
      (fun s => G.radialPair l (tensorGridSquarePoint y f.2 (s 0) (s 1)))
      (fun s i => G.gradient l (tensorGridSquarePoint y f.2 (s 0) (s 1)) (tensorGridSquareDirections f.2 i)) := by
  intro y
  have hPoint (s : Domain 2) :
      tensorGridSamplePoint (.inr f.2) (tensorGridLatticePoint G.offset (C.vertex f.1)) s =
        tensorGridSquarePoint y f.2 (s 0) (s 1) := by
    rw [tensorGridSamplePoint_square, C.vertex_point_eq]
  have hIn (s : Domain 2) (hs : s ∈ (tensorGridOpenParameterBox 2 h).val) :
      tensorGridSamplePoint (.inr f.2) (tensorGridLatticePoint G.offset (C.vertex f.1)) s ∈ ball (0 : Point) 4 := by
    rw [hPoint]
    apply in_ball_four_of_coordinates
    apply C.frontier_coordinates
    exact tensorGridSquarePoint_mem_frontier hh hf
      (Ioo_subset_Icc_self (mem_iInter.mp hs 0)) (Ioo_subset_Icc_self (mem_iInter.mp hs 1))
  have h := G.face_memW12 (C.vertex f.1) (.inr f.2) (tensorGridOpenParameterBox 2 h) hIn l
  simpa only [hPoint, tensorGridSampleDirections] using! h

/-- Each selected square has the actual continuous face-to-edge trace on both
parallel edges, each with its original integer edge index. -/
theorem SphereFaceCube.square_trace {G : SphereFaceGrid P hP h hh} (C : SphereFaceCube G)
    {f : TensorGridSquare} (hf : f ∈ cubeBoundarySquares C.level) (l : Fin 2) :
    let y := tensorGridVertex G.center h f.1
    ∃ H : C(Icc (0 : ℝ) h, Lp (Ambient q) 2 (volume.restrict (tensorGridOpenParameterBox 1 h).val)),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) h,
        ∃ hs : MemLp (fun s : Domain 1 => G.radialPair l (tensorGridSquarePoint y f.2 (s 0) t))
          2 (volume.restrict (tensorGridOpenParameterBox 1 h).val),
          H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp _) ∧
      (∃ h₀ : MemLp (fun s : Domain 1 => G.radialPair l
          (tensorGridEdgePoint G.center h ⟨f.1, f.2.val.1⟩ (s 0)))
          2 (volume.restrict (tensorGridOpenParameterBox 1 h).val), H ⟨0, le_rfl, hh.le⟩ = h₀.toLp _) ∧
      (∃ h₁ : MemLp (fun s : Domain 1 => G.radialPair l
          (tensorGridEdgePoint G.center h ⟨f.1 + Pi.single f.2.val.2 (1 : ℤ), f.2.val.1⟩ (s 0)))
          2 (volume.restrict (tensorGridOpenParameterBox 1 h).val), H ⟨h, hh.le, le_rfl⟩ = h₁.toLp _) := by
  intro y
  have hunit (s : ℝ) (hs : s ∈ Icc 0 h) (t : ℝ) (ht : t ∈ Icc 0 h) (i : Fin 3) :
      tensorGridSquarePoint (tensorGridLatticePoint G.offset (C.vertex f.1)) f.2 s t i ∈ Ioo (-1 : ℝ) 1 := by
    rw [C.vertex_point_eq]
    exact C.frontier_coordinates (tensorGridSquarePoint_mem_frontier hh hf hs ht) i
  obtain ⟨H, hInside, hLeft, hRight⟩ := G.face_trace (C.vertex f.1) f.2 hunit l
  have hEdge (s : ℝ) (z : Fin 3 → ℤ) (i : Fin 3) :
      tensorGridEdgePoint G.center h ⟨z, i⟩ s =
        tensorGridVertex G.center h z + s • EuclideanSpace.single i (1 : ℝ) := rfl
  refine ⟨H, ?_, ?_, ?_⟩
  · simpa only [C.vertex_point_eq] using! hInside
  · simpa only [C.vertex_point_eq, hEdge] using! hLeft
  · simpa only [C.vertex_point_eq, hEdge, tensorGridVertex_add_unit] using! hRight

private theorem ae_eq_tensorGridOpenParameterBox_one {g f : ℝ → Ambient q}
    (hEq : g =ᵐ[volume.restrict (Ioo 0 h)] f) :
    (fun s : Domain 1 => g (s 0)) =ᵐ[volume.restrict (tensorGridOpenParameterBox 1 h).val]
      (fun s : Domain 1 => f (s 0)) := by
  rw [tensorGridOpenParameterBox_one_eq]
  exact (StratificationTheory.measurePreserving_domainOne_eval.restrict_preimage
    (measurableSet_Ioo (a := 0) (b := h))).quasiMeasurePreserving.ae hEq

/-- The face-to-edge trace takes the very same L² values with any chosen
representatives of its two grid edges. In particular the continuous
representatives from `SphereFaceCube.edge_trace` have these endpoint classes. -/
theorem SphereFaceCube.square_trace_of_edge_representatives
    {G : SphereFaceGrid P hP h hh} (C : SphereFaceCube G) {f : TensorGridSquare}
    (hf : f ∈ cubeBoundarySquares C.level) (l : Fin 2)
    {g₀ g₁ : ℝ → Ambient q}
    (h₀ : g₀ =ᵐ[volume.restrict (Ioo 0 h)] fun t =>
      G.radialPair l (tensorGridEdgePoint G.center h ⟨f.1, f.2.val.1⟩ t))
    (h₁ : g₁ =ᵐ[volume.restrict (Ioo 0 h)] fun t =>
      G.radialPair l (tensorGridEdgePoint G.center h ⟨f.1 + Pi.single f.2.val.2 (1 : ℤ), f.2.val.1⟩ t)) :
    let y := tensorGridVertex G.center h f.1
    let μ := volume.restrict (tensorGridOpenParameterBox 1 h).val
    ∃ H : C(Icc (0 : ℝ) h, Lp (Ambient q) 2 μ),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) h,
        ∃ hs : MemLp (fun s : Domain 1 => G.radialPair l (tensorGridSquarePoint y f.2 (s 0) t)) 2 μ,
          H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp _) ∧
      (∃ hg₀ : MemLp (fun s : Domain 1 => g₀ (s 0)) 2 μ, H ⟨0, le_rfl, hh.le⟩ = hg₀.toLp _) ∧
      (∃ hg₁ : MemLp (fun s : Domain 1 => g₁ (s 0)) 2 μ, H ⟨h, hh.le, le_rfl⟩ = hg₁.toLp _) := by
  intro y μ
  obtain ⟨H, hInterior, ⟨hLeft, hLeftEq⟩, ⟨hRight, hRightEq⟩⟩ := C.square_trace hf l
  have h₀' := ae_eq_tensorGridOpenParameterBox_one h₀
  have h₁' := ae_eq_tensorGridOpenParameterBox_one h₁
  have hg₀ := (memLp_congr_ae h₀').mpr hLeft
  have hg₁ := (memLp_congr_ae h₁').mpr hRight
  exact ⟨H, hInterior, ⟨hg₀, hLeftEq.trans (MemLp.toLp_congr hLeft hg₀ h₀'.symm)⟩,
    ⟨hg₁, hRightEq.trans (MemLp.toLp_congr hRight hg₁ h₁'.symm)⟩⟩

/-- Slicing in the other coordinate gives the original continuous trace on
the two remaining boundary edges of the same selected square. -/
theorem SphereFaceCube.square_trace_cross_of_edge_representatives
    {G : SphereFaceGrid P hP h hh} (C : SphereFaceCube G) {f : TensorGridSquare}
    (hf : f ∈ cubeBoundarySquares C.level) (l : Fin 2)
    {g₀ g₁ : ℝ → Ambient q}
    (h₀ : g₀ =ᵐ[volume.restrict (Ioo 0 h)] fun t =>
      G.radialPair l (tensorGridEdgePoint G.center h ⟨f.1, f.2.val.2⟩ t))
    (h₁ : g₁ =ᵐ[volume.restrict (Ioo 0 h)] fun t =>
      G.radialPair l (tensorGridEdgePoint G.center h ⟨f.1 + Pi.single f.2.val.1 (1 : ℤ), f.2.val.2⟩ t)) :
    let y := tensorGridVertex G.center h f.1
    let μ := volume.restrict (tensorGridOpenParameterBox 1 h).val
    ∃ H : C(Icc (0 : ℝ) h, Lp (Ambient q) 2 μ),
      (∀ᵐ t : ℝ ∂volume, ∀ ht : t ∈ Ioo (0 : ℝ) h,
        ∃ hs : MemLp (fun s : Domain 1 => G.radialPair l (tensorGridSquarePoint y f.2 t (s 0))) 2 μ,
          H ⟨t, ht.1.le, ht.2.le⟩ = hs.toLp _) ∧
      (∃ hg₀ : MemLp (fun s : Domain 1 => g₀ (s 0)) 2 μ, H ⟨0, le_rfl, hh.le⟩ = hg₀.toLp _) ∧
      (∃ hg₁ : MemLp (fun s : Domain 1 => g₁ (s 0)) 2 μ, H ⟨h, hh.le, le_rfl⟩ = hg₁.toLp _) := by
  intro y μ
  let a := tensorGridFaceAxesSwap f.2
  have hunit (s : ℝ) (hs : s ∈ Icc 0 h) (t : ℝ) (ht : t ∈ Icc 0 h) (i : Fin 3) :
      tensorGridSquarePoint (tensorGridLatticePoint G.offset (C.vertex f.1)) a s t i ∈ Ioo (-1 : ℝ) 1 := by
    rw [C.vertex_point_eq, tensorGridSquarePoint_swap]
    exact C.frontier_coordinates (tensorGridSquarePoint_mem_frontier hh hf ht hs) i
  obtain ⟨H, hInside, ⟨hLeft, hLe⟩, ⟨hRight, hRe⟩⟩ := G.face_trace (C.vertex f.1) a hunit l
  have hEdge (s : ℝ) (z : Fin 3 → ℤ) (i : Fin 3) :
      tensorGridEdgePoint G.center h ⟨z, i⟩ s = tensorGridVertex G.center h z + s • EuclideanSpace.single i (1 : ℝ) := rfl
  have hEq₀ : (fun s : Domain 1 => g₀ (s 0)) =ᵐ[μ]
      (fun s => G.radialPair l (tensorGridLatticePoint G.offset (C.vertex f.1) +
        s 0 • EuclideanSpace.single a.val.1 (1 : ℝ))) := by
    simpa only [C.vertex_point_eq, hEdge, a, tensorGridFaceAxesSwap] using! ae_eq_tensorGridOpenParameterBox_one h₀
  have hEq₁ : (fun s : Domain 1 => g₁ (s 0)) =ᵐ[μ]
      (fun s => G.radialPair l (tensorGridLatticePoint G.offset (C.vertex f.1) +
        h • EuclideanSpace.single a.val.2 (1 : ℝ) + s 0 • EuclideanSpace.single a.val.1 (1 : ℝ))) := by
    simpa only [C.vertex_point_eq, hEdge, tensorGridVertex_add_unit, a, tensorGridFaceAxesSwap] using!
      ae_eq_tensorGridOpenParameterBox_one h₁
  have hg₀ := (memLp_congr_ae hEq₀).mpr hLeft
  have hg₁ := (memLp_congr_ae hEq₁).mpr hRight
  refine ⟨H, ?_, ⟨hg₀, hLe.trans (MemLp.toLp_congr hLeft hg₀ hEq₀.symm)⟩,
    ⟨hg₁, hRe.trans (MemLp.toLp_congr hRight hg₁ hEq₁.symm)⟩⟩
  simpa only [C.vertex_point_eq, a, tensorGridSquarePoint_swap] using! hInside

end Thesis

end
