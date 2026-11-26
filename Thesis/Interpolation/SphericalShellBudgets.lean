module

public import Thesis.Interpolation.PenalizedShellGluing
import Thesis.Upstream.MinimizingSobolev
import Thesis.Foundation.BulkGeometry
import Thesis.StressEnergy
import StratificationTheory.Foundation.UnitCubeAffineCoordinates

/-! The finite shell energy sum and the actual incidence multiplicity of its radial sides. -/

public section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ENNReal Topology Matrix.Norms.Frobenius

namespace Thesis

private theorem shellSide_eq_of_cell_eq_edge_eq {m : ℕ} {s t : ShellSideIndex m}
    (hCell : s.1 = t.1) (hEdge : s.edge = t.edge) : s = t := by
  obtain ⟨f, i, b⟩ := s
  obtain ⟨g, j, p⟩ := t
  change f = g at hCell
  subst g
  have hData := congrArg Subtype.val hEdge
  have hDir := congrArg (fun e : TensorGridEdge => e.2) hData
  have hOrigin (k : Fin 3) := congrArg (fun e : TensorGridEdge => e.1 k) hData
  have hf := f.val.2.property
  fin_cases i <;> fin_cases j <;> cases b <;> cases p <;>
    simp [ShellSideIndex.edge, tensorSquareCoordinateEdge, tensorSquareLeftEdge, tensorSquareRightEdge,
      tensorSquareLowerEdge, tensorSquareUpperEdge, hf, Ne.symm hf] at hDir ⊢
  all_goals
    have hL := hOrigin f.val.2.val.1
    have hR := hOrigin f.val.2.val.2
    simp [ShellSideIndex.edge, tensorSquareCoordinateEdge, tensorSquareLeftEdge, tensorSquareRightEdge,
      tensorSquareLowerEdge, tensorSquareUpperEdge, Pi.add_apply, Pi.single_apply] at hL hR

private theorem no_three_shellSides {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32)) (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    {s₀ s₁ s₂ : ShellSideIndex m} (h₀₁ : s₀ ≠ s₁) (h₀₂ : s₀ ≠ s₂) (h₁₂ : s₁ ≠ s₂)
    (he₁ : s₀.edge = s₁.edge) (he₂ : s₀.edge = s₂.edge) : False := by
  let t := h / 2
  let r := 1 - h / 2
  let y := sphericalLateralEdge c h s₀.edge.val (t, r)
  have ht : t ∈ Ioo (0 : ℝ) h := ⟨half_pos hh, half_lt_self hh⟩
  have hr : r ∈ Ioo (1 - h) 1 := ⟨by dsimp only [r]; linarith only [hh], by dsimp only [r]; linarith only [hh]⟩
  have hGeom (s : ShellSideIndex m) (he : s₀.edge = s.edge) :
      ∃ (L : Point →L[ℝ] ℝ) (N : Set Point), L ≠ 0 ∧ IsOpen N ∧ y ∈ N ∧ L y = 0 ∧
        ∀ z ∈ N, z ∈ interior (sphericalClosedCell c h s.1.val) ↔ 0 < L z := by
    obtain ⟨L, N, hL, hN, hY, hy₀, _, hI, _⟩ :=
      sphericalClosedCell_halfspace_near_side hh hh' hc hm s.1.property s.2.1 s.2.2 ht hr
    rw [shellSquareSide_point_on_edge] at hY hy₀
    change sphericalLateralEdge c h s.edge.val (t, r) ∈ N at hY
    change L (sphericalLateralEdge c h s.edge.val (t, r)) = 0 at hy₀
    rw [← he] at hY hy₀
    exact ⟨L, N, hL, hN, hY, hy₀, hI⟩
  obtain ⟨L₀, N₀, hL₀, hN₀, hy₀, hY₀, hI₀⟩ := hGeom s₀ rfl
  obtain ⟨L₁, N₁, hL₁, hN₁, hy₁, hY₁, hI₁⟩ := hGeom s₁ he₁
  obtain ⟨L₂, N₂, hL₂, hN₂, hy₂, hY₂, hI₂⟩ := hGeom s₂ he₂
  have hDisj (i j : ShellSideIndex m) (hne : i ≠ j) (he : i.edge = j.edge) :
      Disjoint (interior (sphericalClosedCell c h i.1.val)) (interior (sphericalClosedCell c h j.1.val)) :=
    sphericalClosedCell_disjoint_interiors hh hh' hc hm i.1.property j.1.property
      (fun h => hne (shellSide_eq_of_cell_eq_edge_eq (Subtype.ext h) he))
  obtain ⟨C₁, hC₁, hOpp₁⟩ := opposite_planeForms_of_disjoint_near hL₀ hL₁ (hN₀.inter hN₁) ⟨hy₀, hy₁⟩
    hY₀ hY₁ (fun z hz h => Set.disjoint_left.mp (hDisj s₀ s₁ h₀₁ he₁)
      ((hI₀ z hz.1).mpr h.1) ((hI₁ z hz.2).mpr h.2))
  obtain ⟨C₂, hC₂, hOpp₂⟩ := opposite_planeForms_of_disjoint_near hL₀ hL₂ (hN₀.inter hN₂) ⟨hy₀, hy₂⟩
    hY₀ hY₂ (fun z hz h => Set.disjoint_left.mp (hDisj s₀ s₂ h₀₂ he₂)
      ((hI₀ z hz.1).mpr h.1) ((hI₂ z hz.2).mpr h.2))
  obtain ⟨p, hp⟩ := exists_pos_of_ne_zero_planeForm L₀ hL₀
  obtain ⟨ε, hε, hz⟩ := exists_positive_step_mem_open (hN₁.inter hN₂) ⟨hy₁, hy₂⟩ (-p)
  let z := y + ε • (-p)
  have hZ₀ : L₀ z < 0 := by
    simp only [z, map_add, map_smul, map_neg, hY₀, zero_add, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hε (neg_neg_of_pos hp)
  have hZ₁ : 0 < L₁ z := by rw [hOpp₁]; exact mul_pos_of_neg_of_neg (neg_neg_of_pos hC₁) hZ₀
  have hZ₂ : 0 < L₂ z := by rw [hOpp₂]; exact mul_pos_of_neg_of_neg (neg_neg_of_pos hC₂) hZ₀
  exact Set.disjoint_left.mp (hDisj s₁ s₂ h₁₂ (he₁.symm.trans he₂)) ((hI₁ z hz.1).mpr hZ₁) ((hI₂ z hz.2).mpr hZ₂)

/-- Each actual lateral edge contributes to at most two selected cells. -/
theorem shellSide_fiber_card_le_two {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32)) (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    (e : ↥(cubeBoundaryEdges m)) :
    ((Finset.univ : Finset (ShellSideIndex m)).filter (fun s => s.edge = e)).card ≤ 2 := by
  classical
  let T := (Finset.univ : Finset (ShellSideIndex m)).filter (fun s => s.edge = e)
  change T.card ≤ 2
  rcases T.eq_empty_or_nonempty with hT | ⟨s₀, hs₀⟩
  · simp [hT]
  have hEdge {s : ShellSideIndex m} (hs : s ∈ T) : s.edge = e := (Finset.mem_filter.mp hs).2
  by_cases hs : ∃ s₁ ∈ T, s₀ ≠ s₁
  · obtain ⟨s₁, hs₁, h₀₁⟩ := hs
    refine (Finset.card_le_card (show T ⊆ {s₀, s₁} from ?_)).trans Finset.card_le_two
    intro s₂ hs₂
    by_contra h
    have h₂ : s₂ ≠ s₀ ∧ s₂ ≠ s₁ := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using h
    exact no_three_shellSides hh hh' hc hm h₀₁ h₂.1.symm h₂.2.symm
      ((hEdge hs₀).trans (hEdge hs₁).symm) ((hEdge hs₀).trans (hEdge hs₂).symm)
  · have hSub : T ⊆ {s₀} := by
      intro s hs'
      rw [Finset.mem_singleton]
      by_contra hn
      exact hs ⟨s, hs', fun h => hn h.symm⟩
    exact (Finset.card_le_card hSub).trans (by simp)

/-- Counting each actual radial side once per incident cell costs at most a
factor of two in the edge-indexed energy sum. -/
theorem sum_shellSide_cost_le_two {c : Point} {h : ℝ} (hh : 0 < h) (hh' : h ≤ 1 / 2)
    {m : ℕ} (hc : ∀ i : Fin 3, c i ∈ Icc (0 : ℝ) (1 / 32)) (hm : (m : ℝ) * h ∈ Icc (1 / 8 : ℝ) (1 / 4))
    (E : ↥(cubeBoundaryEdges m) → ℝ≥0∞) :
    (∑ s : ShellSideIndex m, E s.edge) ≤ 2 * ∑ e, E e := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset (ShellSideIndex m)))
    (t := (Finset.univ : Finset ↥(cubeBoundaryEdges m))) (g := ShellSideIndex.edge)
    (fun _ _ => Finset.mem_univ _) E, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_left (by exact_mod_cast shellSide_fiber_card_le_two hh hh' hc hm e) _

/-! ### Penalized energy in the actual physical cell and face coordinates -/

/-- Penalized energy of one actual two-dimensional face in physical coordinates. -/
@[expose] noncomputable def physicalFacePenalizedEnergy (a : BulkCoefficients) (ε : ElasticScale) (h : ℝ)
    (u : Domain 2 → Ambient 5) (D : Domain 2 → HarmonicMaps.Gradient 2 5) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / 2 : ℝ) * HarmonicMaps.dirichletEnergy D (tensorGridOpenParameterBox 2 h).val +
    ∫⁻ x in (tensorGridOpenParameterBox 2 h).val,
      ENNReal.ofReal ((ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm (u x)))

/-- The fixed chart factor in the linear cell energy estimate. -/
@[expose] noncomputable def shellCellEnergyConstant : ℝ := 2 * (9 * 204 ^ 2 * 65 ^ 3)

variable {a : BulkCoefficients} {B h : ℝ} {v : UnitTensorSphere → S0} {hv : MemSphereH1 v}
variable {G : PenalizedSphereFaces a B h v hv}
variable {I : ∀ f : ShellCellIndex G.grid.level, ProjectedCellInnerFace G f}

/-- The genuine shell filling in the tensor coordinates of the thesis. -/
@[expose] noncomputable def PenalizedFilledShell.tensorField (W : PenalizedFilledShell G I) (x : Point) : S0 :=
  frobeniusCoordinateEquiv.symm (sphericalShellPiecewiseField G.grid.center h (fun f => (W.cell f).field) x)

@[expose] noncomputable def PenalizedFilledShell.tensorDerivative (W : PenalizedFilledShell G I) : Point → Thesis.Gradient :=
  fun x i => frobeniusCoordinateEquiv.symm
    (sphericalShellPiecewiseDerivative G.grid.center h (fun f => (W.cell f).derivative) x i)

theorem PenalizedFilledShell.frobenius_tensorField (W : PenalizedFilledShell G I) :
    frobeniusField W.tensorField = sphericalShellPiecewiseField G.grid.center h (fun f => (W.cell f).field) :=
  funext fun _ => frobeniusCoordinateEquiv.apply_symm_apply _

private theorem memH1_decode_native {U : OpenDomain 3} {u : Point → Ambient 5}
    {D : Point → HarmonicMaps.Gradient 3 5} (hu : MemW12 U u D) :
    MemH1 U.val (fun x => frobeniusCoordinateEquiv.symm (u x)) (fun x i => frobeniusCoordinateEquiv.symm (D x i)) := by
  apply (memH1_iff_memW12 U _ _).mpr
  have hU : frobeniusField (fun x => frobeniusCoordinateEquiv.symm (u x)) = u :=
    funext fun x => frobeniusCoordinateEquiv.apply_symm_apply _
  have hD : frobeniusGradient (fun x i => frobeniusCoordinateEquiv.symm (D x i)) = D :=
    funext fun x => funext fun i => frobeniusCoordinateEquiv.apply_symm_apply _
  rw [hU, hD]
  exact hu

theorem PenalizedFilledShell.tensor_memH1 (W : PenalizedFilledShell G I) :
    MemH1 (sphericalShellDomain h).val W.tensorField W.tensorDerivative := memH1_decode_native W.memW12

private theorem penalizedEnergy_decode_native {U : OpenDomain 3} {u : Point → Ambient 5}
    {D : Point → HarmonicMaps.Gradient 3 5} (hu : MemW12 U u D) (a : BulkCoefficients) (ε : ElasticScale) :
    energy a ε U.val (fun x => frobeniusCoordinateEquiv.symm (u x)) (fun x i => frobeniusCoordinateEquiv.symm (D x i)) =
      ENNReal.ofReal (1 / 2 : ℝ) * HarmonicMaps.dirichletEnergy D U.val +
        ∫⁻ x in U.val, ENNReal.ofReal ((ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm (u x))) := by
  rw [energy_eq_dirichlet_add_scaledPotential a ε _ (memH1_decode_native hu).2.1, dirichletEnergy_eq_half_upstream]
  have hD : frobeniusGradient (fun x i => frobeniusCoordinateEquiv.symm (D x i)) = D :=
    funext fun x => funext fun i => frobeniusCoordinateEquiv.apply_symm_apply _
  rw [hD, eLpNorm_one_eq_lintegral_enorm]
  congr 1
  exact lintegral_congr fun x => by rw [← ofReal_norm,
    Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _))]

/-- The native finite partition gives exact penalized energy additivity for
the same global weak graph and the same original cells. -/
theorem PenalizedFilledShell.tensor_energy_eq_sum_cells (W : PenalizedFilledShell G I) (hSmall : h ≤ 1 / 32)
    (ε : ElasticScale) :
    energy a ε (sphericalShellDomain h).val W.tensorField W.tensorDerivative =
      ∑ f, energy a ε (sphericalCellOpenDomain G.grid.center h f.val).val
        (W.cell f).tensorField (W.cell f).tensorDerivative := by
  let c := G.grid.center
  let u (f : ShellCellIndex G.grid.level) := (W.cell f).field
  let D (f : ShellCellIndex G.grid.level) := (W.cell f).derivative
  let w := sphericalShellPiecewiseField c h u
  let E := sphericalShellPiecewiseDerivative c h D
  let b : Ambient 5 → ℝ≥0∞ := fun z => ENNReal.ofReal ((ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm z))
  have hc (i : Fin 3) : c i ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(G.grid.offset_mem i).1, (G.grid.offset_mem i).2.le.trans hSmall⟩
  have hHalf : h ≤ 1 / 2 := hSmall.trans (by norm_num)
  have hg (f : ShellCellIndex G.grid.level) : MemW12 (sphericalCellOpenDomain c h f.val) (u f) (D f) := (W.cell f).memW12
  obtain ⟨_, _, _, hDir, hBulk, _⟩ := sphericalShellPiecewise_data G.ht_pos hHalf hc G.grid.radius_mem u D hg
  have hNatDir : HarmonicMaps.dirichletEnergy E (sphericalShellDomain h).val =
      ∑ f, HarmonicMaps.dirichletEnergy (D f) (sphericalCellOpenDomain c h f.val).val := by
    rw [HarmonicMaps.dirichletEnergy_eq_ofReal_integral W.memW12.integrable_hsNormSq, hDir,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg fun _ => hsNormSq_nonneg _)]
    exact Finset.sum_congr rfl (fun f _ => (HarmonicMaps.dirichletEnergy_eq_ofReal_integral (hg f).integrable_hsNormSq).symm)
  have hGlobal : energy a ε (sphericalShellDomain h).val W.tensorField W.tensorDerivative =
      ENNReal.ofReal (1 / 2 : ℝ) * HarmonicMaps.dirichletEnergy E (sphericalShellDomain h).val +
        ∫⁻ x in (sphericalShellDomain h).val, b (w x) := penalizedEnergy_decode_native W.memW12 a ε
  have hEach (f : ShellCellIndex G.grid.level) :
      energy a ε (sphericalCellOpenDomain c h f.val).val (W.cell f).tensorField (W.cell f).tensorDerivative =
        ENNReal.ofReal (1 / 2 : ℝ) * HarmonicMaps.dirichletEnergy (D f) (sphericalCellOpenDomain c h f.val).val +
          ∫⁻ x in (sphericalCellOpenDomain c h f.val).val, b (u f x) :=
    penalizedEnergy_decode_native (hg f) a ε
  rw [hGlobal, hNatDir, hBulk b, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun f _ => (hEach f).symm)

/-- Summed native cell filling costs at most the fixed chart constant times
the mesh size times the exact physical six-face energy sum. -/
theorem PenalizedFilledShell.tensor_energy_le_sum_physical_faces (W : PenalizedFilledShell G I)
    (hSmall : h ≤ 1 / 32) (ε : ElasticScale) :
    energy a ε (sphericalShellDomain h).val W.tensorField W.tensorDerivative ≤
      ENNReal.ofReal (shellCellEnergyConstant * h) *
        ∑ f, ∑ j : CellFaceIndex,
          physicalFacePenalizedEnergy a ε h (penalizedShellCellFace (I f) j) (penalizedShellCellFaceDerivative (I f) j) := by
  let C := ENNReal.ofReal (shellCellEnergyConstant * h)
  have hDirCoeff : (9 * 204 ^ 2 * 65 ^ 3 : ℝ≥0∞) * ENNReal.ofReal (3 * h / 2) ≤ C := by
    rw [show (9 * 204 ^ 2 * 65 ^ 3 : ℝ≥0∞) = ENNReal.ofReal (9 * 204 ^ 2 * 65 ^ 3) by norm_num,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    dsimp only [shellCellEnergyConstant]
    nlinarith only [G.ht_pos]
  have hBulkCoeff : (65 ^ 3 : ℝ≥0∞) * ENNReal.ofReal (h / 6) ≤ C := by
    rw [show (65 ^ 3 : ℝ≥0∞) = ENNReal.ofReal (65 ^ 3) by norm_num, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    dsimp only [shellCellEnergyConstant]
    nlinarith only [G.ht_pos]
  rw [W.tensor_energy_eq_sum_cells hSmall ε]
  change _ ≤ C * _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  have h := (W.cell f).tensor_energy_bound a ε
  have hData (j : CellFaceIndex) := (W.faceFamily f).physical_eq G.ht_pos j
  simp_rw [(hData _).1, (hData _).2, W.face_eq, W.derivative_eq] at h
  refine h.trans ?_
  simp only [physicalFacePenalizedEnergy, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [mul_add, mul_left_comm C (ENNReal.ofReal (1 / 2 : ℝ))]
  exact add_le_add (mul_le_mul_right (mul_le_mul_left hDirCoeff _) _) (mul_le_mul_left hBulkCoeff _)

private theorem physicalFacePenalizedEnergy_swap (a : BulkCoefficients) (ε : ElasticScale)
    {h : ℝ} (hh : 0 < h) {u : Domain 2 → Ambient 5} {D : Domain 2 → HarmonicMaps.Gradient 2 5}
    (hu : MemW12 (tensorGridOpenParameterBox 2 h) u D) :
    let Δ : Domain 2 → HarmonicMaps.Gradient 2 5 := fun x i =>
      ∑ j : Fin 2, (physicalSquareSwap (EuclideanSpace.single i 1)) j • D (physicalSquareSwap x) j
    physicalFacePenalizedEnergy a ε h (u ∘ physicalSquareSwap) Δ = physicalFacePenalizedEnergy a ε h u D := by
  intro Δ
  let μ := volume.restrict (tensorGridOpenParameterBox 2 h).val
  let b := fun z : Ambient 5 => ENNReal.ofReal ((ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm z))
  have hCont : Continuous (fun z : Ambient 5 => (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm z)) :=
    continuous_const.mul ((contDiff_bulkPotential a).continuous.comp frobeniusCoordinateEquiv.symm.continuous)
  have hb : AEMeasurable (b ∘ u) μ := hCont.measurable.ennreal_ofReal.comp_aemeasurable hu.2.1.aemeasurable
  have hMP := measurePreserving_physicalSquareSwap h
  have hMeas : AEMeasurable (b ∘ u) (Measure.map physicalSquareSwap μ) := by rw [hMP.map_eq]; exact hb
  have hbEq : (∫⁻ x, b (u (physicalSquareSwap x)) ∂μ) = (∫⁻ x, b (u x) ∂μ) := by
    have h := (lintegral_map' hMeas hMP.measurable.aemeasurable).symm
    rwa [hMP.map_eq] at h
  unfold physicalFacePenalizedEnergy
  rw [(memW12_physicalSquareSwap hh hu).2]
  exact congrArg (_ + ·) hbEq

/-- The vacuum inner face contributes exactly its original physical
Dirichlet term and no bulk term. -/
theorem ProjectedCellInnerFace.penalizedEnergy_eq {f : ShellCellIndex G.grid.level} (V : ProjectedCellInnerFace G f)
    (ε : ElasticScale) : physicalFacePenalizedEnergy a ε h V.field V.derivative =
      ENNReal.ofReal (1 / 2 : ℝ) * HarmonicMaps.dirichletEnergy V.derivative (tensorGridOpenParameterBox 2 h).val := by
  unfold physicalFacePenalizedEnergy
  have hZero : (fun x => ENNReal.ofReal ((ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm (V.field x))))
      =ᵐ[volume.restrict (tensorGridOpenParameterBox 2 h).val] fun _ => 0 :=
    V.vacuum_ae.mono (fun x hx => by
      have h0 : bulkPotential a (frobeniusCoordinateEquiv.symm (V.field x)) = 0 := (bulkPotential_eq_zero_iff a _).mpr hx
      change ENNReal.ofReal ((ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm (V.field x))) = 0
      rw [h0, mul_zero, ENNReal.ofReal_zero])
  rw [lintegral_congr_ae hZero, lintegral_zero, add_zero]

/-- The summed actual cell boundary costs split into the original outer
faces, the original vacuum inner-face gradients, and the actual lateral
rectangles with their verified incidence multiplicity. -/
theorem sum_physicalFacePenalizedEnergy_le_boundary_sums
    (hSmall : h ≤ 1 / 32) {C : ℝ} (S : PenalizedCellSides G.grid C) (ε : ElasticScale) :
    (∑ f, ∑ j : CellFaceIndex,
      physicalFacePenalizedEnergy a ε h (penalizedShellCellFace (I f) j) (penalizedShellCellFaceDerivative (I f) j)) ≤
        (∑ f, physicalFacePenalizedEnergy a ε h (fun x => frobeniusCoordinateEquiv (G.face f x))
          (fun x i => frobeniusCoordinateEquiv (G.derivative f x i))) +
         (ENNReal.ofReal (1 / 2 : ℝ) * ∑ f,
           HarmonicMaps.dirichletEnergy (I f).derivative (tensorGridOpenParameterBox 2 h).val) +
         2 * ∑ e, physicalFacePenalizedEnergy a ε h (G.grid.cellSide e) (G.grid.cellSideDerivative e) := by
  let out (f : ShellCellIndex G.grid.level) := physicalFacePenalizedEnergy a ε h
    (fun x => frobeniusCoordinateEquiv (G.face f x)) (fun x i => frobeniusCoordinateEquiv (G.derivative f x i))
  let inn (f : ShellCellIndex G.grid.level) := ENNReal.ofReal (1 / 2 : ℝ) *
    HarmonicMaps.dirichletEnergy (I f).derivative (tensorGridOpenParameterBox 2 h).val
  let side (e : ↥(cubeBoundaryEdges G.grid.level)) := physicalFacePenalizedEnergy a ε h (G.grid.cellSide e) (G.grid.cellSideDerivative e)
  let cost (f : ShellCellIndex G.grid.level) (j : CellFaceIndex) := physicalFacePenalizedEnergy a ε h
    (penalizedShellCellFace (I f) j) (penalizedShellCellFaceDerivative (I f) j)
  have hSide (f : ShellCellIndex G.grid.level) (i : Fin 2) (p : Bool) :
      cost f (i.castSucc, p) = side (tensorSquareCoordinateEdge f i p) := by
    fin_cases i
    · simpa [cost, side, penalizedShellCellFace, penalizedShellCellFaceDerivative, shellCellSideEdge] using
        physicalFacePenalizedEnergy_swap a ε G.ht_pos (S.memW12 (tensorSquareCoordinateEdge f 0 p))
    · simp [cost, side, penalizedShellCellFace, penalizedShellCellFaceDerivative, shellCellSideEdge]
  have hf (f : ShellCellIndex G.grid.level) :
      (∑ j : CellFaceIndex, cost f j) = out f + inn f + ∑ s : Fin 2 × Bool, side (ShellSideIndex.edge (f, s)) := by
    have hOut : cost f (2, true) = out f := by simp [cost, out, penalizedShellCellFace, penalizedShellCellFaceDerivative]
    have hInn : cost f (2, false) = inn f := by
      simpa [cost, inn, penalizedShellCellFace, penalizedShellCellFaceDerivative] using (I f).penalizedEnergy_eq ε
    have h0 (p : Bool) : cost f (0, p) = side (tensorSquareCoordinateEdge f 0 p) := hSide f 0 p
    have h1 (p : Bool) : cost f (1, p) = side (tensorSquareCoordinateEdge f 1 p) := hSide f 1 p
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two]
    simp only [Fintype.sum_bool, ShellSideIndex.edge, hOut, hInn, h0, h1]
    ring
  have hc (i : Fin 3) : G.grid.center i ∈ Icc (0 : ℝ) (1 / 32) :=
    ⟨(G.grid.offset_mem i).1, (G.grid.offset_mem i).2.le.trans hSmall⟩
  have hh' : h ≤ 1 / 2 := hSmall.trans (by norm_num)
  change (∑ f, ∑ j : CellFaceIndex, cost f j) ≤ (∑ f, out f) + _ + 2 * ∑ e, side e
  simp_rw [hf, Finset.sum_add_distrib]
  rw [← (Fintype.sum_prod_type (fun s : ShellSideIndex G.grid.level => side (ShellSideIndex.edge s)))]
  change (∑ f, out f) + (∑ f, inn f) + (∑ s : ShellSideIndex G.grid.level, side (ShellSideIndex.edge s)) ≤
    (∑ f, out f) + (ENNReal.ofReal (1 / 2 : ℝ) * ∑ f,
      HarmonicMaps.dirichletEnergy (I f).derivative (tensorGridOpenParameterBox 2 h).val) + 2 * ∑ e, side e
  rw [Finset.mul_sum (a := ENNReal.ofReal (1 / 2 : ℝ))]
  exact add_le_add_right (sum_shellSide_cost_le_two G.ht_pos hh' hc G.grid.radius_mem side) _

/-- The cell energy uses the outer, inner and lateral face budgets with one
factor of the mesh size. -/
theorem PenalizedFilledShell.tensor_energy_le_h_boundary_sums (W : PenalizedFilledShell G I)
    (hSmall : h ≤ 1 / 32) {C : ℝ} (S : PenalizedCellSides G.grid C) (ε : ElasticScale) :
    energy a ε (sphericalShellDomain h).val W.tensorField W.tensorDerivative ≤
      ENNReal.ofReal (shellCellEnergyConstant * h) *
        ((∑ f, physicalFacePenalizedEnergy a ε h (fun x => frobeniusCoordinateEquiv (G.face f x))
          (fun x i => frobeniusCoordinateEquiv (G.derivative f x i))) +
         (ENNReal.ofReal (1 / 2 : ℝ) * ∑ f,
           HarmonicMaps.dirichletEnergy (I f).derivative (tensorGridOpenParameterBox 2 h).val) +
         2 * ∑ e, physicalFacePenalizedEnergy a ε h (G.grid.cellSide e) (G.grid.cellSideDerivative e)) :=
  (W.tensor_energy_le_sum_physical_faces hSmall ε).trans
    (mul_le_mul_right (sum_physicalFacePenalizedEnergy_le_boundary_sums (I := I) hSmall S ε) _)

private theorem physicalFacePenalizedEnergy_eq_ofReal_integral {h R : ℝ} (hh : 0 < h)
    (a : BulkCoefficients) (ε : ElasticScale) {u : Domain 2 → Ambient 5} {D : Domain 2 → HarmonicMaps.Gradient 2 5}
    (hW : MemW12 (tensorGridOpenParameterBox 2 h) u D)
    (hB : ∀ᵐ x ∂volume.restrict (tensorGridOpenParameterBox 2 h).val, ‖u x‖ ≤ R) :
    physicalFacePenalizedEnergy a ε h u D = ENNReal.ofReal
      (∫ x in (tensorGridOpenParameterBox 2 h).val, (1 / 2 : ℝ) * hsNormSq (D x) +
        (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm (u x))) := by
  let U := (tensorGridOpenParameterBox 2 h).val
  let μ := volume.restrict U
  have hFinite : (volume : Measure (Domain 2)) U ≠ ⊤ :=
    (StratificationTheory.volume_native_positive_cube 2 hh).trans_ne ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hFinite
  let w := frobeniusCoordinateEquiv.symm ∘ u
  have hV : ∀ᵐ x ∂μ, w x ∈ closedBall (0 : S0) R := by
    filter_upwards [hB] with x hx
    exact mem_closedBall_zero_iff.mpr (by simpa only [w, Function.comp_apply, LinearIsometryEquiv.norm_map] using hx)
  have hBCont := (contDiff_bulkPotential a).continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : S0) R).exists_bound_of_continuousOn hBCont.continuousOn
  have hMeas := (hBCont.comp frobeniusCoordinateEquiv.symm.continuous).comp_aestronglyMeasurable hW.2.1.aestronglyMeasurable
  have hBInt : Integrable (fun x => bulkPotential a (w x)) μ :=
    (MemLp.of_bound (p := 1) hMeas M (hV.mono fun _ hx => hM _ hx)).integrable (by norm_num)
  have hDInt := hW.integrable_hsNormSq
  let k : ℝ := (ε : ℝ)⁻¹ ^ 2
  have hk : 0 ≤ k := sq_nonneg _
  have hB₀ (x : Domain 2) : 0 ≤ bulkPotential a (w x) := bulkPotential_nonneg a _
  have hBI : Integrable (fun x => k * bulkPotential a (w x)) μ := hBInt.const_mul _
  have hDN : (∀ᵐ x ∂μ, 0 ≤ hsNormSq (D x)) := Eventually.of_forall fun _ => hsNormSq_nonneg _
  have hBN : (∀ᵐ x ∂μ, 0 ≤ k * bulkPotential a (w x)) := Eventually.of_forall fun x => mul_nonneg hk (hB₀ x)
  unfold physicalFacePenalizedEnergy
  change ENNReal.ofReal (1 / 2 : ℝ) * HarmonicMaps.dirichletEnergy D U +
    (∫⁻ x, ENNReal.ofReal (k * bulkPotential a (w x)) ∂μ) =
      ENNReal.ofReal (∫ x, (1 / 2 : ℝ) * hsNormSq (D x) + k * bulkPotential a (w x) ∂μ)
  rw [HarmonicMaps.dirichletEnergy_eq_ofReal_integral hDInt,
    ← ofReal_integral_eq_lintegral_ofReal hBI hBN, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← integral_const_mul, ← ENNReal.ofReal_add (integral_nonneg_of_ae (hDN.mono fun _ h => mul_nonneg (by norm_num) h))
      (integral_nonneg_of_ae hBN), integral_add (hDInt.const_mul _) hBI]

/-- The actual side rectangles retain both edge channels at the physical
scale. The factor from the trace discrepancy is absorbed when `ε ≤ h`. -/
theorem penalizedCellSides_sum_energy_le {C C₀ : ℝ} (G : PenalizedSphereFaces a B h v hv)
    (S : PenalizedCellSides G.grid C) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (ε : ElasticScale) (hε : (ε : ℝ) ≤ h)
    {G₀ B₀ : ℝ} (hG₀ : 0 ≤ G₀) (hB₀ : 0 ≤ B₀)
    (hGrad : (∑ e, ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative e t‖ ^ 2) ≤ C₀ / h * G₀)
    (hBulk : (∑ e, ∫ t in Ioo (0 : ℝ) h, bulkPotential a (G.grid.trace e t)) ≤ C₀ / h * B₀) :
    (∑ e, physicalFacePenalizedEnergy a ε h (G.grid.cellSide e) (G.grid.cellSideDerivative e)) ≤
      ENNReal.ofReal ((C₀ * (1 + C ^ 2) + 2 * C * C₀) * ((1 / 2 : ℝ) * G₀ + (ε : ℝ)⁻¹ ^ 2 * B₀)) := by
  let J := ↥(cubeBoundaryEdges G.grid.level)
  let U := (tensorGridOpenParameterBox 2 h).val
  let E (e : J) := ∫ x in U, (1 / 2 : ℝ) * hsNormSq (G.grid.cellSideDerivative e x) +
    (ε : ℝ)⁻¹ ^ 2 * bulkPotential a (frobeniusCoordinateEquiv.symm (G.grid.cellSide e x))
  let grad (e : J) := ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative e t‖ ^ 2
  let pot (e : J) := ∫ t in Ioo (0 : ℝ) h, bulkPotential a (G.grid.trace e t)
  let d := h / 4 * (1 + C ^ 2)
  let b := C / 2 * h⁻¹ + (ε : ℝ)⁻¹ ^ 2 * (C * h)
  let K := C₀ * (1 + C ^ 2) + 2 * C * C₀
  have hh := G.ht_pos
  have hD : 0 ≤ d := by dsimp only [d]; positivity
  have hB : 0 ≤ b := by dsimp only [b]; positivity
  have hEach (e : J) : physicalFacePenalizedEnergy a ε h (G.grid.cellSide e) (G.grid.cellSideDerivative e) =
      ENNReal.ofReal (E e) := by
    apply physicalFacePenalizedEnergy_eq_ofReal_integral hh a ε (S.memW12 e)
    filter_upwards [ae_restrict_mem (tensorGridOpenParameterBox 2 h).property.measurableSet] with x hx
    exact S.side_bound e x ⟨Ioo_subset_Icc_self (mem_iInter.mp hx 0), Ioo_subset_Icc_self (mem_iInter.mp hx 1)⟩
  have hE₀ (e : J) : 0 ≤ E e := integral_nonneg (fun _ => add_nonneg
    (mul_nonneg (by norm_num) (hsNormSq_nonneg _)) (mul_nonneg (sq_nonneg _) (bulkPotential_nonneg a _)))
  have hSum : ∑ e, E e ≤ d * (C₀ / h * G₀) + b * (C₀ / h * B₀) := by
    calc
      _ ≤ (∑ e : J, (d * grad e + b * pot e)) := Finset.sum_le_sum fun e _ => S.penalized_bound ε e
      _ = d * (∑ e, grad e) + b * (∑ e, pot e) := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hGrad hD) (mul_le_mul_of_nonneg_left hBulk hB)
  have hInv : h⁻¹ ^ 2 ≤ (ε : ℝ)⁻¹ ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hh.le)
    (inv_anti₀ ε.property.1 hε) 2
  have hdCoeff : d * (C₀ / h) = C₀ / 4 * (1 + C ^ 2) := by dsimp only [d]; field_simp
  have hbCoeff : b * (C₀ / h) = C * C₀ / 2 * h⁻¹ ^ 2 + C * C₀ * (ε : ℝ)⁻¹ ^ 2 := by
    dsimp only [b]
    field_simp
  have hGD : C₀ / 4 * (1 + C ^ 2) ≤ K * (1 / 2 : ℝ) := by
    dsimp only [K]
    nlinarith only [mul_nonneg hC hC₀, mul_nonneg hC₀ (sq_nonneg C), hC₀]
  have hBK : (3 / 2 : ℝ) * (C * C₀) ≤ K := by
    dsimp only [K]
    nlinarith only [mul_nonneg hC hC₀, mul_nonneg hC₀ (sq_nonneg C), hC₀]
  have hbBound : b * (C₀ / h) ≤ K * (ε : ℝ)⁻¹ ^ 2 := by
    rw [hbCoeff]
    calc
      _ ≤ C * C₀ / 2 * (ε : ℝ)⁻¹ ^ 2 + C * C₀ * (ε : ℝ)⁻¹ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hInv (by positivity)) le_rfl
      _ = (3 / 2) * (C * C₀) * (ε : ℝ)⁻¹ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hBK (sq_nonneg _)
  simp_rw [hEach]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => hE₀ e)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ d * (C₀ / h * G₀) + b * (C₀ / h * B₀) := hSum
    _ ≤ (K * (1 / 2 : ℝ)) * G₀ + (K * (ε : ℝ)⁻¹ ^ 2) * B₀ := by
      rw [← mul_assoc, ← mul_assoc, hdCoeff]
      exact add_le_add (mul_le_mul_of_nonneg_right hGD hG₀) (mul_le_mul_of_nonneg_right hbBound hB₀)
    _ = _ := by dsimp only [K]; ring

private theorem outerFace_sum_energy_le {C₀ G₀ B₀ : ℝ} (G : PenalizedSphereFaces a B h v hv)
    (ε : ElasticScale) (hC₀ : 0 ≤ C₀) (hG₀ : 0 ≤ G₀) (hB₀ : 0 ≤ B₀)
    (hGrad : (∑ f, ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (∑ i, ‖G.derivative f x i‖ ^ 2)) ≤
      ENNReal.ofReal (6 * C₀ * G₀))
    (hBulk : (∑ f, ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (bulkPotential a (G.face f x))) ≤
      ENNReal.ofReal (6 * C₀ * B₀)) :
    (∑ f, physicalFacePenalizedEnergy a ε h (fun x => frobeniusCoordinateEquiv (G.face f x))
      (fun x i => frobeniusCoordinateEquiv (G.derivative f x i))) ≤
      ENNReal.ofReal (6 * C₀ * ((1 / 2 : ℝ) * G₀ + (ε : ℝ)⁻¹ ^ 2 * B₀)) := by
  let μ := volume.restrict (tensorGridOpenParameterBox 2 h).val
  let k : ℝ := (ε : ℝ)⁻¹ ^ 2
  have hk : 0 ≤ k := sq_nonneg _
  have hDir (f : ShellCellIndex G.grid.level) :
      HarmonicMaps.dirichletEnergy (fun x i => frobeniusCoordinateEquiv (G.derivative f x i)) (tensorGridOpenParameterBox 2 h).val =
        ∫⁻ x, ENNReal.ofReal (∑ i, ‖G.derivative f x i‖ ^ 2) ∂μ := by
    simp only [HarmonicMaps.dirichletEnergy, hsNormSq, LinearIsometryEquiv.norm_map]
    rfl
  have hPot (f : ShellCellIndex G.grid.level) :
      (∫⁻ x, ENNReal.ofReal (k * bulkPotential a (frobeniusCoordinateEquiv.symm
        (frobeniusCoordinateEquiv (G.face f x)))) ∂μ) = ENNReal.ofReal k * ∫⁻ x, ENNReal.ofReal (bulkPotential a (G.face f x)) ∂μ := by
    simp_rw [LinearIsometryEquiv.symm_apply_apply, ENNReal.ofReal_mul hk]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hEach (f : ShellCellIndex G.grid.level) :
      physicalFacePenalizedEnergy a ε h (fun x => frobeniusCoordinateEquiv (G.face f x))
        (fun x i => frobeniusCoordinateEquiv (G.derivative f x i)) =
      ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x, ENNReal.ofReal (∑ i, ‖G.derivative f x i‖ ^ 2) ∂μ) +
        ENNReal.ofReal k * ∫⁻ x, ENNReal.ofReal (bulkPotential a (G.face f x)) ∂μ := by
    unfold physicalFacePenalizedEnergy
    change _ + (∫⁻ x, ENNReal.ofReal (k * bulkPotential a (frobeniusCoordinateEquiv.symm
      (frobeniusCoordinateEquiv (G.face f x)))) ∂μ) = _
    rw [hDir, hPot]
  simp_rw [hEach, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine (add_le_add (mul_le_mul_right hGrad _) (mul_le_mul_right hBulk _)).trans_eq ?_
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.ofReal_mul hk,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  dsimp only [k]
  ring

/-- All physical face costs are controlled by the simultaneous edge and
outer face budgets and the separate vacuum inner-face Dirichlet cost. -/
theorem sum_physicalFacePenalizedEnergy_le_input_channels
    (hSmall : h ≤ 1 / 32) {C C₀ Cᵢ : ℝ} (S : PenalizedCellSides G.grid C)
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hCᵢ : 0 ≤ Cᵢ) (ε : ElasticScale) (hε : (ε : ℝ) ≤ h)
    {G₀ B₀ : ℝ} (hG₀ : 0 ≤ G₀) (hB₀ : 0 ≤ B₀)
    (hEdgeGrad : (∑ e, ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative e t‖ ^ 2) ≤ C₀ / h * G₀)
    (hEdgeBulk : (∑ e, ∫ t in Ioo (0 : ℝ) h, bulkPotential a (G.grid.trace e t)) ≤ C₀ / h * B₀)
    (hFaceGrad : (∑ f, ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (∑ i, ‖G.derivative f x i‖ ^ 2)) ≤
      ENNReal.ofReal (6 * C₀ * G₀))
    (hFaceBulk : (∑ f, ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (bulkPotential a (G.face f x))) ≤
      ENNReal.ofReal (6 * C₀ * B₀)) :
    let E := (1 / 2 : ℝ) * G₀ + (ε : ℝ)⁻¹ ^ 2 * B₀
    let K := 6 * C₀ + Cᵢ + 2 * (C₀ * (1 + C ^ 2) + 2 * C * C₀)
    (ENNReal.ofReal (1 / 2 : ℝ) * ∑ f,
      HarmonicMaps.dirichletEnergy (I f).derivative (tensorGridOpenParameterBox 2 h).val) ≤ ENNReal.ofReal (Cᵢ * E) →
    (∑ f, ∑ j : CellFaceIndex,
      physicalFacePenalizedEnergy a ε h (penalizedShellCellFace (I f) j) (penalizedShellCellFaceDerivative (I f) j)) ≤
      ENNReal.ofReal (K * E) := by
  intro E K hInner
  have hOuter := outerFace_sum_energy_le G ε hC₀ hG₀ hB₀ hFaceGrad hFaceBulk
  have hSides := penalizedCellSides_sum_energy_le G S hC hC₀ ε hε hG₀ hB₀ hEdgeGrad hEdgeBulk
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hS : 0 ≤ C₀ * (1 + C ^ 2) + 2 * C * C₀ := by positivity
  refine (sum_physicalFacePenalizedEnergy_le_boundary_sums hSmall S ε).trans ?_
  refine (add_le_add (add_le_add hOuter hInner) (mul_le_mul_right hSides _)).trans_eq ?_
  rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  dsimp only [K, E]
  ring

/-- The shell cost is bounded by the original channel budgets with one factor
of the mesh size. -/
theorem PenalizedFilledShell.tensor_energy_le_h_input_channels (W : PenalizedFilledShell G I)
    (hSmall : h ≤ 1 / 32) {C C₀ Cᵢ : ℝ} (S : PenalizedCellSides G.grid C)
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hCᵢ : 0 ≤ Cᵢ) (ε : ElasticScale) (hε : (ε : ℝ) ≤ h)
    {G₀ B₀ : ℝ} (hG₀ : 0 ≤ G₀) (hB₀ : 0 ≤ B₀)
    (hEdgeGrad : (∑ e, ∫ t in Ioo (0 : ℝ) h, ‖G.grid.derivative e t‖ ^ 2) ≤ C₀ / h * G₀)
    (hEdgeBulk : (∑ e, ∫ t in Ioo (0 : ℝ) h, bulkPotential a (G.grid.trace e t)) ≤ C₀ / h * B₀)
    (hFaceGrad : (∑ f, ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (∑ i, ‖G.derivative f x i‖ ^ 2)) ≤
      ENNReal.ofReal (6 * C₀ * G₀))
    (hFaceBulk : (∑ f, ∫⁻ x in (tensorGridOpenParameterBox 2 h).val, ENNReal.ofReal (bulkPotential a (G.face f x))) ≤
      ENNReal.ofReal (6 * C₀ * B₀)) :
    let E := (1 / 2 : ℝ) * G₀ + (ε : ℝ)⁻¹ ^ 2 * B₀
    let K := 6 * C₀ + Cᵢ + 2 * (C₀ * (1 + C ^ 2) + 2 * C * C₀)
    (ENNReal.ofReal (1 / 2 : ℝ) * ∑ f,
      HarmonicMaps.dirichletEnergy (I f).derivative (tensorGridOpenParameterBox 2 h).val) ≤ ENNReal.ofReal (Cᵢ * E) →
    energy a ε (sphericalShellDomain h).val W.tensorField W.tensorDerivative ≤
      ENNReal.ofReal (shellCellEnergyConstant * K * h * E) := by
  intro E K hInner
  have hSum := sum_physicalFacePenalizedEnergy_le_input_channels
    hSmall S hC hC₀ hCᵢ ε hε hG₀ hB₀ hEdgeGrad hEdgeBulk hFaceGrad hFaceBulk hInner
  have hgeom : 0 ≤ shellCellEnergyConstant * h :=
    mul_nonneg (by unfold shellCellEnergyConstant; positivity) G.ht_pos.le
  refine (W.tensor_energy_le_sum_physical_faces hSmall ε).trans
    ((mul_le_mul_right hSum _).trans_eq ?_)
  rw [← ENNReal.ofReal_mul hgeom]
  congr 1
  dsimp only [K, E]
  ring

end Thesis
