module

public import Thesis.Variational.DirichletPoissonInverse
public import Thesis.Variational.CompactSpectralBasis
import Thesis.Variational.FractionalFiniteAverages
import Thesis.Variational.H10StrongApproximation
import Thesis.Foundation.WeakGradient
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Sequences

/-! The compact Dirichlet eigenbasis in the actual gradient Hilbert space. -/

public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal NNReal Matrix Matrix.Norms.Frobenius RealInnerProductSpace

namespace Thesis

local instance dirichletSpectralTensorComplete : CompleteSpace S0 := complete_of_proper

local instance dirichletSpectralGraphComplete (U : Set Point) : CompleteSpace (H10 U) :=
  isClosed_closure.completeSpace_coe

/-- The Euclidean Hilbert coordinates of a tensor-valued (L^2) field. -/
@[expose] def dirichletFrobeniusL2 (U : Set Point) :
    Lp S0 2 (volume.restrict U) →L[ℝ] Lp (EuclideanSpace ℝ (Fin 5)) 2 (volume.restrict U) :=
  frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 (volume.restrict U)

theorem dirichletFrobeniusL2_ae {U : Set Point} (u : Lp S0 2 (volume.restrict U)) :
    (dirichletFrobeniusL2 U u : Point → EuclideanSpace ℝ (Fin 5)) =ᵐ[volume.restrict U]
      fun x => frobeniusCoordinateEquiv (u x) :=
  ContinuousLinearMap.coeFn_compLpL _ u

theorem norm_dirichletFrobeniusL2 {U : Set Point} (u : Lp S0 2 (volume.restrict U)) :
    ‖dirichletFrobeniusL2 U u‖ = ‖u‖ := by
  have heq : ∀ᵐ x ∂volume.restrict U, ‖dirichletFrobeniusL2 U u x‖ = ‖u x‖ := by
    filter_upwards [dirichletFrobeniusL2_ae u] with x hx
    rw [hx,LinearIsometryEquiv.norm_map]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (heq.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (heq.mono fun _ h => h.symm.le))

/-- The original (L^2) value of a zero-trace graph. -/
@[expose] def dirichletValueLp (U : Set Point) : H10 U →L[ℝ] Lp S0 2 (volume.restrict U) :=
  (ContinuousLinearMap.fst ℝ (Lp S0 2 (volume.restrict U)) (Fin 3 → Lp S0 2 (volume.restrict U))).comp
    (h10Submodule U).subtypeL

/-- The actual value coordinates of the Sobolev graph in the (L^2) Hilbert space. -/
@[expose] def dirichletValueCoords (U : Set Point) :
    H10 U →L[ℝ] Lp (EuclideanSpace ℝ (Fin 5)) 2 (volume.restrict U) :=
  (dirichletFrobeniusL2 U).comp (dirichletValueLp U)

theorem dirichletValueCoords_ae {U : Set Point} (u : H10 U) :
    (dirichletValueCoords U u : Point → EuclideanSpace ℝ (Fin 5)) =ᵐ[volume.restrict U]
      fun x => frobeniusCoordinateEquiv (h10Value u x) :=
  dirichletFrobeniusL2_ae u.val.1

theorem norm_dirichletValueCoords {U : Set Point} (u : H10 U) :
    ‖dirichletValueCoords U u‖ = ‖u.val.1‖ := norm_dirichletFrobeniusL2 _

theorem inner_dirichletValueCoords_tensor {U : Set Point}
    (u v : Lp S0 2 (volume.restrict U)) :
    inner ℝ (dirichletFrobeniusL2 U u) (dirichletFrobeniusL2 U v) =
      ∫ x in U, frobeniusS0 (u x) (v x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [dirichletFrobeniusL2_ae u,dirichletFrobeniusL2_ae v] with x hu hv
  rw [hu,hv]
  exact frobeniusCoordinateEquiv_inner _ _

private theorem h10Gradient_ae_zero_of_value_ae_zero {U : Set Point} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)]
    {u : H10 U} (hValue : h10Value u =ᵐ[volume.restrict U] (0 : Point → S0)) :
    h10Gradient u =ᵐ[volume.restrict U] (0 : Point → Gradient) := by
  have hSob := (u.hasZeroTrace hU).1
  have hGradient := hSob.2.2.ae_eq_classicalGradient hU hSob.locallyIntegrableOn_gradient
    (v := fun _ => (0 : S0)) contDiffOn_const hValue
  have hGzero : ClassicalGradient (fun _ : Point => (0 : S0)) = 0 := by
    funext x i
    change (fderiv ℝ (fun _ : Point => (0 : S0)) x) (axis i) = 0
    simp
  rw [hGzero] at hGradient
  exact hGradient

private theorem h10_eq_zero_of_valueLp_zero {U : Set Point} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)] {u : H10 U}
    (huZero : u.val.1 = 0) : u = 0 := by
  have hValue : h10Value u =ᵐ[volume.restrict U] (0 : Point → S0) := by
    change (u.val.1 : Point → S0) =ᵐ[_] _
    rw [huZero]
    exact Lp.coeFn_zero _ _ _
  have hGradient := h10Gradient_ae_zero_of_value_ae_zero hU hValue
  have hCol (j : Fin 3) : u.val.2 j = (0 : Lp S0 2 (volume.restrict U)) := by
    have hAE : (u.val.2 j : Point → S0) =ᵐ[volume.restrict U] (0 : Point → S0) :=
      hGradient.mono fun x hx => congrFun hx j
    exact Lp.ext (hAE.trans (Lp.coeFn_zero S0 2 (volume.restrict U)).symm)
  exact Subtype.ext (Prod.ext huZero (funext hCol))

theorem dirichletValueCoords_injective {U : Set Point} (hU : IsBoundedDomain U) :
    Injective (dirichletValueCoords U) := by
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.2 hU.2.2.measure_lt_top.ne
  rw [injective_iff_map_eq_zero]
  intro u hu
  apply h10_eq_zero_of_valueLp_zero hU.1
  apply norm_eq_zero.mp
  rw [← norm_dirichletValueCoords u,hu,norm_zero]

private theorem dirichletValueLp_isCompactOperator {U : Set Point} (hU : IsSmoothDomain U) :
    IsCompactOperator (dirichletValueLp U) := by
  apply isCompactOperator_of_bounded_image_subsequence
  intro v hv
  obtain ⟨C,hC,hF⟩ := exists_h10FractionalEmbedding_bound hU.1 (1 / 2) (by norm_num) (by norm_num)
  have hAll (n : ℕ) : fractionalEnergy (1 / 2) U (dirichletValueLp U (v n)) ≤ ENNReal.ofReal (C ^ 2) := by
    obtain ⟨hM,hEq⟩ := hF (v n)
    have hR := hEq.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hv n) hC)
    have hSq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hR 2
    rw [Real.sq_sqrt ENNReal.toReal_nonneg] at hSq
    have h := ENNReal.ofReal_le_ofReal hSq
    rw [ENNReal.ofReal_toReal hM.2.ne] at h
    exact h
  exact exists_L2_subsequence_of_bounded_fractionalEnergy
    hU (1/2) (by norm_num) (fun n => dirichletValueLp U (v n)) _ ENNReal.ofReal_lt_top hAll

theorem dirichletValueCoords_isCompactOperator {U : Set Point} (hU : IsSmoothDomain U) :
    IsCompactOperator (dirichletValueCoords U) :=
  (dirichletValueLp_isCompactOperator hU).clm_comp (dirichletFrobeniusL2 U)

/-- A spectral realization of the original Dirichlet gradient pairing.
The mass is the (L^2) norm squared of an energy-normalized eigenvector. -/
structure DirichletSpectralData (U : Set Point) where
  energy : Submodule ℝ (DirichletGradientCoordinates U)
  energy_closed : IsClosed (energy : Set (DirichletGradientCoordinates U))
  energyEquiv : H10 U ≃L[ℝ] energy
  energy_coords : ∀ w, (energyEquiv w).val = h10GradientCoordinates U w
  index : Type
  basis : HilbertBasis index ℝ energy
  mass : index → ℝ
  mass_pos : ∀ i, 0 < mass i
  maxMass : ℝ
  maxMass_pos : 0 < maxMass
  mass_bound : ∀ i, mass i ≤ maxMass
  eigenForm : ∀ i w, inner ℝ (dirichletValueCoords U (energyEquiv.symm (basis i)))
    (dirichletValueCoords U w) = mass i * inner ℝ (basis i) (energyEquiv w)

/-- The compact positive value operator supplies the actual energy basis. -/
theorem exists_dirichletSpectralData {U : Set Point} (hU : IsSmoothDomain U) :
    Nonempty (DirichletSpectralData U) := by
  obtain ⟨G,hG,L,hL⟩ := exists_gradientCoordinateEquiv hU.1.1.measurableSet hU.1.2.2
  letI : CompleteSpace G := hG.completeSpace_coe
  let J := (dirichletValueCoords U).comp L.symm.toContinuousLinearMap
  have hJI : Injective J := (dirichletValueCoords_injective hU.1).comp L.symm.injective
  have hJC : IsCompactOperator J :=
    (dirichletValueCoords_isCompactOperator hU).comp_clm L.symm.toContinuousLinearMap
  obtain ⟨I,b,μ,C,hC,hMass,hForm⟩ := exists_positive_hilbertBasis_of_compact_injective J hJC hJI
  refine ⟨⟨G,hG,L,hL,I,b,μ,fun i => (hMass i).1,C,hC,fun i => (hMass i).2,?_⟩⟩
  intro i w
  have hJ (v : H10 U) : J (L v) = dirichletValueCoords U v := by
    change dirichletValueCoords U (L.symm (L v)) = _
    rw [L.symm_apply_apply]
  change inner ℝ (J (b i)) (dirichletValueCoords U w) = _
  simpa only [hJ] using hForm i (L w)

namespace DirichletSpectralData

variable {U : Set Point}

@[expose] def mode (D : DirichletSpectralData U) (i : D.index) : H10 U :=
  D.energyEquiv.symm (D.basis i)

@[expose] def coefficient (D : DirichletSpectralData U) (w : H10 U) (i : D.index) : ℝ :=
  D.basis.repr (D.energyEquiv w) i

theorem coefficient_eq_inner (D : DirichletSpectralData U) (w : H10 U) (i : D.index) :
    D.coefficient w i = inner ℝ (D.basis i) (D.energyEquiv w) :=
  D.basis.repr_apply_apply (D.energyEquiv w) i

theorem hasSum_modes (D : DirichletSpectralData U) (w : H10 U) :
    HasSum (fun i => D.coefficient w i • D.mode i) w := by
  have h := D.energyEquiv.symm.toContinuousLinearMap.hasSum (D.basis.hasSum_repr (D.energyEquiv w))
  simpa only [mode,coefficient,map_smul,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] using h

theorem energyEquiv_mode (D : DirichletSpectralData U) (i : D.index) :
    D.energyEquiv (D.mode i) = D.basis i := D.energyEquiv.apply_symm_apply _

theorem principalPart_eq_energy_inner (D : DirichletSpectralData U) (v w : H10 U) :
    h10PrincipalPart U v w = -inner ℝ (D.energyEquiv v) (D.energyEquiv w) := by
  rw [h10PrincipalPart_eq_neg_gradientCoordinate_inner]
  change -inner ℝ (h10GradientCoordinates U v) (h10GradientCoordinates U w) =
    -inner ℝ (D.energyEquiv v).val (D.energyEquiv w).val
  rw [D.energy_coords v,D.energy_coords w]

theorem mass_gram (D : DirichletSpectralData U) [DecidableEq D.index] (i j : D.index) :
    inner ℝ (dirichletValueCoords U (D.mode i)) (dirichletValueCoords U (D.mode j)) =
      if i = j then D.mass i else 0 := by
  classical
  rw [show (D.mode i) = D.energyEquiv.symm (D.basis i) from rfl,
    D.eigenForm i (D.mode j),D.energyEquiv_mode,
    (orthonormal_iff_ite.mp D.basis.orthonormal) i j]
  by_cases h : i = j <;> simp [h]

theorem norm_value_combination_sq (D : DirichletSpectralData U) (F : Finset D.index) (c : D.index → ℝ) :
    ‖dirichletValueLp U (∑ i ∈ F, c i • D.mode i)‖ ^ 2 = ∑ i ∈ F, D.mass i * c i ^ 2 := by
  classical
  have h := norm_sum_sq_of_diagonal_gram F
    (fun i => dirichletValueCoords U (D.mode i)) D.mass c D.mass_gram
  change ‖(∑ i ∈ F, c i • D.mode i).val.1‖ ^ 2 = _
  rw [← norm_dirichletValueCoords (∑ i ∈ F, c i • D.mode i)]
  simpa only [map_sum,map_smul,dirichletValueLp] using h

theorem norm_energy_combination_sq (D : DirichletSpectralData U) (F : Finset D.index) (c : D.index → ℝ) :
    ‖D.energyEquiv (∑ i ∈ F, c i • D.mode i)‖ ^ 2 = ∑ i ∈ F, c i ^ 2 := by
  classical
  have h := norm_sum_sq_of_diagonal_gram F (fun i => D.basis i) (fun _ => 1) c
    ((orthonormal_iff_ite.mp D.basis.orthonormal))
  simpa only [map_sum,map_smul,D.energyEquiv_mode,one_mul] using h

end DirichletSpectralData

end Thesis
