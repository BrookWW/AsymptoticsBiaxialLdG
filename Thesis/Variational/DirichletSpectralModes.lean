module

public import Thesis.Variational.DirichletSpectralCoordinates
public import Thesis.Variational.FiniteSpectralInterpolation
import Thesis.Variational.H10StrongApproximation
import HarmonicMaps.Analysis.VariableMollificationL2

/-! Value and derivative interpolation weights for the actual Dirichlet modes. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Matrix.Norms.Frobenius RealInnerProductSpace

namespace Thesis

/-- The displayed original column as a continuous map into its (L^2) space. -/
def dirichletColumnLp (U : Set Point) (j : Fin 3) : H10 U →L[ℝ] Lp S0 2 (volume.restrict U) :=
  (ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.snd ℝ
    (Lp S0 2 (volume.restrict U)) (Fin 3 → Lp S0 2 (volume.restrict U))).comp (h10Submodule U).subtypeL)

namespace DirichletSpectralData

variable {U : Set Point}

theorem norm_dirichletColumnLp_le_energy (D : DirichletSpectralData U) (w : H10 U) (j : Fin 3) :
    ‖dirichletColumnLp U j w‖ ≤ ‖D.energyEquiv w‖ := by
  change ‖w.val.2 j‖ ≤ ‖(D.energyEquiv w).val‖
  rw [D.energy_coords w,← norm_h10FrobeniusColumnL2 j w,← h10GradientCoordinates_apply]
  exact PiLp.norm_apply_le _ _

private theorem norm_graph_of_H10_value {w : H10 U} (h : MemH1 U (h10Value w) (h10Gradient w)) :
    ‖(h.1.toLp (h10Value w),fun j => (h.2.1 j).toLp (fun x => h10Gradient w x j))‖ = ‖w‖ := by
  have hB :
      ((h.1.toLp (h10Value w),fun j => (h.2.1 j).toLp (fun x => h10Gradient w x j)) : H1Graph U) = w.val := by
    apply Prod.ext
    · exact Lp.ext h.1.coeFn_toLp
    · funext j
      exact Lp.ext (h.2.1 j).coeFn_toLp
  rw [hB]
  rfl

/-- The (H^s) norm of a finite value-mode sum is controlled by the masses
at exponent (1-s). -/
theorem exists_fractionalEnergy_value_modes_le (D : DirichletSpectralData U)
    (hU : IsSmoothDomain U) (s : ℝ) (hs : 0 < s) (hs₁ : s < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Finset D.index) (c : D.index → ℝ),
      fractionalEnergy s U (h10Value (∑ i ∈ F,c i • D.mode i)) ≤
        ENNReal.ofReal (C * ∑ i ∈ F, D.mass i^(1-s)*c i^2) := by
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.2 hU.1.2.2.measure_lt_top.ne
  let B := ‖D.energyEquiv.symm.toContinuousLinearMap‖ ^ 2
  let a (i : D.index) := dirichletValueLp U (D.mode i)
  have hLp (F : Finset D.index) (c : D.index → ℝ) :
      (∑ i ∈ F, c i • a i) = dirichletValueLp U (∑ i ∈ F, c i • D.mode i) := by
    simp only [a,map_sum,map_smul]
  have hValue (F : Finset D.index) (c : D.index → ℝ) :
      ‖∑ i ∈ F, c i • a i‖ ^ 2 ≤ ∑ i ∈ F, D.mass i*1*c i^2 := by
    rw [hLp F c,D.norm_value_combination_sq]
    simp only [mul_one,le_refl]
  have hGraph (F : Finset D.index) (c : D.index → ℝ) :
      ∃ (G : Point → Gradient) (h : MemH1 U (⇑(∑ i ∈ F, c i • a i)) G),
        ‖(h.1.toLp (⇑(∑ i ∈ F, c i • a i)),fun j => (h.2.1 j).toLp (fun x => G x j))‖ ^ 2 ≤
          B * ∑ i ∈ F, 1*c i^2 := by
    rw [hLp F c]
    let w := ∑ i ∈ F,c i • D.mode i
    let hwGraph : MemH1 U (h10Value w) (h10Gradient w) := (w.hasZeroTrace hU.1.1).1
    refine ⟨h10Gradient w,hwGraph,?_⟩
    change ‖(hwGraph.1.toLp (h10Value w),fun j => (hwGraph.2.1 j).toLp (fun x => h10Gradient w x j))‖ ^ 2 ≤ _
    rw [norm_graph_of_H10_value hwGraph]
    have h := D.energyEquiv.symm.toContinuousLinearMap.le_opNorm (D.energyEquiv w)
    have hw : D.energyEquiv.symm.toContinuousLinearMap (D.energyEquiv w) = w :=
      D.energyEquiv.symm_apply_apply w
    rw [hw] at h
    have hBound := pow_le_pow_left₀ (norm_nonneg w) h 2
    rw [mul_pow,show ‖D.energyEquiv w‖ ^ 2 = ∑ i ∈ F,c i^2
      from D.norm_energy_combination_sq F c] at hBound
    simpa only [B,one_mul] using hBound
  obtain ⟨C,hC,hModes⟩ := exists_fractionalEnergy_le_finite_modes hU a D.mass (fun _ => 1)
    s hs hs₁ D.maxMass B D.maxMass_pos (sq_nonneg _) (fun i => ⟨D.mass_pos i,D.mass_bound i⟩)
    (fun _ => zero_le_one) hValue hGraph
  refine ⟨C,hC,fun F c => ?_⟩
  have h := hModes F c
  rw [hLp F c] at h
  change fractionalEnergy s U (dirichletValueLp U (∑ i ∈ F,c i • D.mode i)) ≤ _
  simpa only [mul_one] using h

/-- The literal forcing of a finite mode sum is square bounded by the
reciprocal masses. -/
theorem exists_forcing_of_mode_combination (D : DirichletSpectralData U)
    (F : Finset D.index) (c : D.index → ℝ) :
    ∃ g : Lp S0 2 (volume.restrict U),
      ‖g‖ ^ 2 = ∑ i ∈ F, (D.mass i)⁻¹ * c i^2 ∧
      ∀ v : H10 U, h10PrincipalPart U (∑ i ∈ F,c i • D.mode i) v =
        ∫ x in U, frobeniusS0 (g x) (h10Value v x) := by
  let q (i : D.index) := -(c i / D.mass i)
  let g := ∑ i ∈ F,q i • dirichletValueLp U (D.mode i)
  let w := ∑ i ∈ F,c i • D.mode i
  refine ⟨g,?_,?_⟩
  · have h : g = dirichletValueLp U (∑ i ∈ F,q i • D.mode i) := by
      simp only [g,map_sum,map_smul]
    rw [h,D.norm_value_combination_sq]
    apply Finset.sum_congr rfl
    intro i _
    unfold q
    have hn := (D.mass_pos i).ne'
    field_simp
  · intro v
    have hG (i : D.index) :
        inner ℝ (dirichletValueCoords U (D.mode i)) (dirichletValueCoords U v) =
          D.mass i * inner ℝ (D.basis i) (D.energyEquiv v) := D.eigenForm i v
    have h : dirichletFrobeniusL2 U g = ∑ i ∈ F,q i • dirichletValueCoords U (D.mode i) := by
      simp only [g,map_sum,map_smul,dirichletValueCoords,ContinuousLinearMap.comp_apply]
    have hPair : (∫ x in U, frobeniusS0 (g x) (h10Value v x)) =
        inner ℝ (dirichletFrobeniusL2 U g) (dirichletValueCoords U v) :=
      (inner_dirichletValueCoords_tensor g v.val.1).symm
    rw [hPair,h,D.principalPart_eq_energy_inner]
    simp only [map_sum,map_smul,D.energyEquiv_mode,sum_inner,real_inner_smul_left,hG]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    unfold q
    have hn := (D.mass_pos i).ne'
    field_simp
    exact congrArg Neg.neg (real_inner_smul_left (D.basis i) (D.energyEquiv v) (c i))

private theorem norm_second_gradient_graph_le
    (D : DirichletSpectralData U) (F : Finset D.index) (c : D.index → ℝ) (j : Fin 3)
    {H : Point → Gradient}
    (h : MemH1 U (h10Gradient (∑ i ∈ F,c i • D.mode i) · j) H)
    (C : ℝ) (hH : (∑ i : Fin 3, ∫ x in U, ‖H x i‖ ^ 2) ≤
      C^2 * ∑ i ∈ F, (D.mass i)⁻¹*c i^2) :
    ‖(h.1.toLp (h10Gradient (∑ i ∈ F,c i • D.mode i) · j),
      fun i => (h.2.1 i).toLp (fun x => H x i))‖ ^ 2 ≤
      (D.maxMass+C^2) * ∑ i ∈ F, (D.mass i)⁻¹*c i^2 := by
  let S := ∑ i ∈ F, (D.mass i)⁻¹*c i^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (inv_nonneg.mpr (D.mass_pos i).le) (sq_nonneg _)
  let w := ∑ i ∈ F,c i • D.mode i
  let p : H1Graph U := (h.1.toLp (h10Gradient w · j),fun i => (h.2.1 i).toLp (fun x => H x i))
  have hP : p.1 = dirichletColumnLp U j w := Lp.ext h.1.coeFn_toLp
  have hL : ‖p.1‖ ^ 2 ≤ D.maxMass*S := by
    rw [hP]
    have hN := (pow_le_pow_left₀ (norm_nonneg _) (D.norm_dirichletColumnLp_le_energy w j) 2)
    refine hN.trans ?_
    rw [show ‖D.energyEquiv w‖^2 = ∑ i∈F,c i^2 from D.norm_energy_combination_sq F c]
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_right (D.mass_bound i)
      (mul_nonneg (inv_nonneg.mpr (D.mass_pos i).le) (sq_nonneg (c i)))
    exact (by
      have e : D.mass i * ((D.mass i)⁻¹*c i^2) = c i^2 := by
        rw [← mul_assoc,mul_inv_cancel₀ (D.mass_pos i).ne',one_mul]
      rwa [e] at hh)
  have hC : ‖p.2‖ ^ 2 ≤ C^2*S := by
    have hN : 0 ≤ C^2*S := mul_nonneg (sq_nonneg _) hS
    rw [← Real.sq_sqrt hN]
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
    rw [Real.sq_sqrt hN]
    have hEq : ‖p.2 i‖ ^ 2 = ∫ x in U, ‖H x i‖ ^ 2 := by
      rw [Lp.norm_toLp, HarmonicMaps.integral_norm_sq_eq_eLpNorm_two_toReal_sq (h.2.1 i)]
    rw [hEq]
    exact (Finset.single_le_sum (fun k _ => integral_nonneg (fun _ => sq_nonneg _))
      (Finset.mem_univ i)).trans hH
  change ‖p‖ ^ 2 ≤ (D.maxMass+C^2)*S
  rw [Prod.norm_def]
  rcases le_total ‖p.1‖ ‖p.2‖ with h₀|h₁
  · rw [max_eq_right h₀]
    exact hC.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left D.maxMass_pos.le) hS)
  · rw [max_eq_left h₁]
    exact hL.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) hS)

private theorem graph_bound_of_finite_gradient_modes (D : DirichletSpectralData U)
    (F : Finset D.index) (c : D.index → ℝ) (j : Fin 3) (C : ℝ)
    (hH2 : ∀ (w : H10 U) (g : Lp S0 2 (volume.restrict U)),
      (∀ v : H10 U, h10PrincipalPart U w v = ∫ x in U, frobeniusS0 (g x) (h10Value v x)) →
      ∃ H : Point → Fin 3 → Gradient,
        (∀ j, MemH1 U (fun x => h10Gradient w x j) (fun x => H x j)) ∧
          (∑ j : Fin 3, ∑ i : Fin 3, (∫ x in U, ‖H x j i‖ ^ 2)) ≤ C^2 * ‖g‖^2) :
    let w := ∑ i ∈ F,c i • D.mode i
    ∃ (G : Point → Gradient) (h : MemH1 U (h10Gradient w · j) G),
      ‖(h.1.toLp (h10Gradient w · j),fun k => (h.2.1 k).toLp (fun x => G x k))‖^2 ≤
        (D.maxMass+C^2) * ∑ i ∈ F, (D.mass i)⁻¹*c i^2 := by
  dsimp only
  obtain ⟨g,hg,hPair⟩ := D.exists_forcing_of_mode_combination F c
  let w : H10 U := ∑ i ∈ F,c i • D.mode i
  have hData := hH2 w g (fun v => hPair v)
  obtain ⟨H,hGraph,hNorm⟩ := hData
  have hJ : (∑ i : Fin 3, ∫ x in U, ‖H x j i‖^2) ≤ C^2 * ∑ i ∈ F, (D.mass i)⁻¹*c i^2 := by
    rw [← hg]
    exact (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun i _ =>
      integral_nonneg (fun x => sq_nonneg ‖H x k i‖))) (Finset.mem_univ j)).trans hNorm
  refine ⟨fun x => H x j,hGraph j,?_⟩
  exact norm_second_gradient_graph_le D F c j (hGraph j) C hJ

/-- The native (H^2) estimate for the finite Dirichlet modes yields
the required fractional gradient norm with reciprocal mass weights. -/
theorem exists_fractionalEnergy_gradient_modes_le (D : DirichletSpectralData U)
    (hU : IsSmoothDomain U) (s : ℝ) (hs : 0 < s) (hs₁ : s < 1)
    (C : ℝ) (hH2 : ∀ (w : H10 U) (g : Lp S0 2 (volume.restrict U)),
      (∀ v : H10 U, h10PrincipalPart U w v = ∫ x in U, frobeniusS0 (g x) (h10Value v x)) →
      ∃ H : Point → Fin 3 → Gradient,
        (∀ j, MemH1 U (fun x => h10Gradient w x j) (fun x => H x j)) ∧
          (∑ j : Fin 3, ∑ i : Fin 3, (∫ x in U, ‖H x j i‖ ^ 2)) ≤ C^2 * ‖g‖^2)
    (j : Fin 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Finset D.index) (c : D.index → ℝ),
      fractionalEnergy s U (h10Gradient (∑ i ∈ F,c i • D.mode i) · j) ≤
        ENNReal.ofReal (K * ∑ i ∈ F, D.mass i^(-s)*c i^2) := by
  let a (i : D.index) := dirichletColumnLp U j (D.mode i)
  let B := D.maxMass+C^2
  have hB : 0 ≤ B := add_nonneg D.maxMass_pos.le (sq_nonneg _)
  have hLp (F : Finset D.index) (c : D.index → ℝ) :
      (∑ i ∈ F,c i • a i) = dirichletColumnLp U j (∑ i ∈ F,c i • D.mode i) := by
    simp only [a,map_sum,map_smul]
  have hValue (F : Finset D.index) (c : D.index → ℝ) :
      ‖∑ i ∈ F,c i • a i‖^2 ≤ ∑ i ∈ F, D.mass i*(D.mass i)⁻¹*c i^2 := by
    rw [hLp F c]
    refine (pow_le_pow_left₀ (norm_nonneg _) (D.norm_dirichletColumnLp_le_energy _ j) _).trans ?_
    rw [D.norm_energy_combination_sq]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_inv_cancel₀ (D.mass_pos i).ne',one_mul]
  have hGraph (F : Finset D.index) (c : D.index → ℝ) :
      ∃ (G : Point → Gradient) (h : MemH1 U (⇑(∑ i ∈ F,c i • a i)) G),
        ‖(h.1.toLp (⇑(∑ i ∈ F,c i • a i)),fun j => (h.2.1 j).toLp (fun x => G x j))‖^2 ≤
          B * ∑ i ∈ F, (D.mass i)⁻¹*c i^2 := by
    rw [hLp F c]
    exact graph_bound_of_finite_gradient_modes D F c j C hH2
  obtain ⟨K,hK,hModes⟩ := exists_fractionalEnergy_le_finite_modes hU a D.mass
    (fun i => (D.mass i)⁻¹) s hs hs₁ D.maxMass B D.maxMass_pos hB
    (fun i => ⟨D.mass_pos i,D.mass_bound i⟩) (fun i => inv_nonneg.mpr (D.mass_pos i).le) hValue hGraph
  refine ⟨K,hK,fun F c => ?_⟩
  have h := hModes F c
  rw [hLp F c] at h
  have hPow (i : D.index) : D.mass i^(1-s)*(D.mass i)⁻¹ = D.mass i^(-s) := by
    rw [← Real.rpow_neg_one,← Real.rpow_add (D.mass_pos i)]
    congr 1
    ring
  change fractionalEnergy s U (dirichletColumnLp U j (∑ i ∈ F,c i • D.mode i)) ≤ _
  simpa only [hPow] using h

end DirichletSpectralData

end Thesis
