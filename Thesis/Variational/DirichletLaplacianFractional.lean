module

public import Thesis.External.FractionalDirichlet
import Thesis.Variational.DirichletSpectralModes
import Thesis.Variational.DirichletPoissonH2
import Thesis.Variational.H10FractionalEmbedding
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Fractional regularity of the actual weak Dirichlet inverse. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal Matrix Matrix.Norms.Frobenius RealInnerProductSpace

namespace Thesis

private def finiteFractionalCoefficientEnergy {U : Set Point}
    (D : DirichletSpectralData U) (s : ℝ) (w : H10 U) (F : Finset D.index) : ℝ :=
  ∑ i ∈ F, D.mass i^(s-1) * D.coefficient w i ^ 2

private theorem finiteFractionalCoefficientEnergy_nonneg {U : Set Point}
    (D : DirichletSpectralData U) (s : ℝ) (w : H10 U) (F : Finset D.index) :
    0 ≤ finiteFractionalCoefficientEnergy D s w F :=
  Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (D.mass_pos i).le _) (sq_nonneg _)

private theorem square_bound_of_mul_sqrt_bound {X C N : ℝ}
    (hX : 0 ≤ X) (hC : 0 ≤ C) (hBound : X ≤ N * Real.sqrt (C*X)) :
    X ≤ C*N^2 := by
  by_cases h0 : X = 0
  · rw [h0]
    exact mul_nonneg hC (sq_nonneg _)
  have hP : 0 < Real.sqrt X := Real.sqrt_pos.2 (lt_of_le_of_ne hX (fun h => h0 h.symm))
  have hSq : Real.sqrt X * Real.sqrt X ≤ (N * Real.sqrt C) * Real.sqrt X := by
    rw [← pow_two,Real.sq_sqrt hX]
    simpa only [Real.sqrt_mul hC,mul_assoc] using hBound
  have h := le_of_mul_le_mul_right hSq hP
  have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rwa [Real.sq_sqrt hX,mul_pow,Real.sq_sqrt hC,mul_comm] at hh

private theorem finiteCoefficientEnergy_le_fractional_dual
    {U : Set Point} (D : DirichletSpectralData U) (s : ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hModes : ∀ (F : Finset D.index) (c : D.index → ℝ),
      fractionalEnergy s U (h10Value (∑ i ∈ F,c i • D.mode i)) ≤
        ENNReal.ofReal (C * ∑ i ∈ F, D.mass i^(1-s)*c i^2))
    {w : H10 U} {f : Lp S0 2 (volume.restrict U)} {N : ℝ}
    (hDual : FractionalL2DualBound s U f N)
    (hSolve : ∀ v : H10 U, h10PrincipalPart U v w = ∫ x in U, frobeniusS0 (h10Value v x) (f x))
    (F : Finset D.index) : finiteFractionalCoefficientEnergy D s w F ≤ C*N^2 := by
  let c (i : D.index) := D.mass i^(s-1) * D.coefficient w i
  let v := ∑ i ∈ F,c i • D.mode i
  let E := finiteFractionalCoefficientEnergy D s w F
  have hE : 0 ≤ E := finiteFractionalCoefficientEnergy_nonneg D s w F
  have hPow (i : D.index) :
      D.mass i^(1-s)*c i^2 = D.mass i^(s-1)*D.coefficient w i^2 := by
    dsimp only [c]
    rw [mul_pow,← mul_assoc,← Real.rpow_mul_natCast (D.mass_pos i).le,← Real.rpow_add (D.mass_pos i)]
    congr 2
    push_cast
    ring
  have hEnergy : fractionalEnergy s U (h10Value v) ≤ ENNReal.ofReal (C*E) := by
    have h := hModes F c
    simp_rw [hPow] at h
    exact h
  have hv : MemHs s U (h10Value v) :=
    ⟨Lp.aestronglyMeasurable v.val.1,hEnergy.trans_lt ENNReal.ofReal_lt_top⟩
  have hPair : h10PrincipalPart U v w = -E := by
    unfold v E finiteFractionalCoefficientEnergy
    rw [D.principalPart_eq_energy_inner]
    simp only [map_sum,map_smul,D.energyEquiv_mode,sum_inner]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = c i * inner ℝ (D.basis i) (D.energyEquiv w) :=
        real_inner_smul_left (D.basis i) (D.energyEquiv w) (c i)
      _ = _ := by
        rw [← D.coefficient_eq_inner]
        simp only [c, pow_two, mul_assoc]
  have h := hDual.2 (h10Value v) hv
  rw [← hSolve v,hPair,abs_neg,abs_of_nonneg hE] at h
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEnergy
  rw [ENNReal.toReal_ofReal (mul_nonneg hC hE)] at hReal
  apply square_bound_of_mul_sqrt_bound hE hC
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hReal) hDual.1)

private theorem exists_mode_sums_tendsto {U : Set Point} (D : DirichletSpectralData U) (w : H10 U) :
    ∃ F : ℕ → Finset D.index,
      Tendsto (fun n => ∑ i ∈ F n, D.coefficient w i • D.mode i) atTop (𝓝 w) := by
  have ht := D.hasSum_modes w
  have hNear (n : ℕ) : ∃ F : Finset D.index,
      dist (∑ i ∈ F,D.coefficient w i • D.mode i) w < 1 / ((n : ℝ) + 1) := by
    have hδ : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    exact ((Metric.tendsto_nhds.mp ht) _ hδ).exists
  choose F hF using hNear
  refine ⟨F,Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  have ht' : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨n,hn⟩ := eventually_atTop.mp (ht'.eventually_lt_const hε)
  exact ⟨n,fun k hk => (hF k).trans (hn k hk)⟩

private theorem lintegral_sq_value_le_of_Lp_tendsto {U : Set Point}
    {v : ℕ → Lp S0 2 (volume.restrict U)} {w : Lp S0 2 (volume.restrict U)}
    (hConv : Tendsto v atTop (𝓝 w)) {C : ℝ≥0∞}
    (hSq : ∀ n, (∫⁻ x in U, ENNReal.ofReal (‖v n x‖ ^ 2)) ≤ C) :
    (∫⁻ x in U, ENNReal.ofReal (‖w x‖ ^ 2)) ≤ C := by
  have ht : Tendsto (fun n => ENNReal.ofReal (‖v n‖ ^ 2)) atTop (𝓝 (ENNReal.ofReal (‖w‖ ^ 2))) :=
    ENNReal.tendsto_ofReal (hConv.norm.pow 2)
  have h := le_of_tendsto ht (Eventually.of_forall fun n => by
    rw [← lintegral_sq_norm_lp (volume.restrict U) (v n)]
    exact hSq n)
  rw [lintegral_sq_norm_lp]
  exact h

private theorem fractionalEnergy_le_of_Lp_tendsto_uniform {U : Set Point}
    (s : ℝ) {v : ℕ → Lp S0 2 (volume.restrict U)} {w : Lp S0 2 (volume.restrict U)}
    (hConv : Tendsto v atTop (𝓝 w)) {C : ℝ≥0∞}
    (hBound : ∀ n, fractionalEnergy s U (v n) ≤ C) :
    fractionalEnergy s U w ≤ C+C := by
  have hwL := lintegral_sq_value_le_of_Lp_tendsto hConv
    (fun n => (self_le_add_right _ _).trans (hBound n))
  obtain ⟨κ,_,hAe⟩ := (tendstoInMeasure_of_tendsto_Lp hConv).exists_seq_tendsto_ae
  have hN := nonlocal_energy_bounded_of_tendsto_ae s
    (fun n => Lp.aestronglyMeasurable (v (κ n))) (Lp.aestronglyMeasurable w)
    hAe (Eventually.of_forall fun n => hBound (κ n))
  exact add_le_add hwL hN

private theorem value_modes_L2_le {U : Set Point}
    (D : DirichletSpectralData U) (s : ℝ) (hs : s < 2) (w : H10 U) (F : Finset D.index) :
    ‖dirichletValueLp U (∑ i ∈ F,D.coefficient w i • D.mode i)‖ ^ 2 ≤
      D.maxMass^(2-s) * finiteFractionalCoefficientEnergy D s w F := by
  rw [D.norm_value_combination_sq,finiteFractionalCoefficientEnergy,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hExp : D.mass i = D.mass i^(2-s)*D.mass i^(s-1) := by
    rw [← Real.rpow_add (D.mass_pos i), show (2-s)+(s-1)=1 by ring,Real.rpow_one]
  calc
    _ = D.mass i^(2-s)*(D.mass i^(s-1)*D.coefficient w i^2) := by
      conv_lhs => rw [hExp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (D.mass_pos i).le (D.mass_bound i) (sub_nonneg.mpr hs.le))
      (mul_nonneg (Real.rpow_nonneg (D.mass_pos i).le _) (sq_nonneg _))

/-- The native weak (H^2) estimate implies the pure Dirichlet fractional
estimate. The weak graph, right hand side, and boundary trace are the
original ones on the actual smooth domain. -/
theorem dirichletLaplacianFractionalRegularity_of_H2
    (hH2 : ∀ U : Set Point, IsSmoothDomain U →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : H10 U) (g : Lp S0 2 (volume.restrict U)),
        (∀ v : H10 U, h10PrincipalPart U w v = ∫ x in U, frobeniusS0 (g x) (h10Value v x)) →
        ∃ H : Point → Fin 3 → Gradient,
          (∀ j, MemH1 U (fun x => h10Gradient w x j) (fun x => H x j)) ∧
          (∑ j : Fin 3, ∑ i : Fin 3, (∫ x in U, ‖H x j i‖ ^ 2)) ≤ C^2 * ‖g‖^2) :
    External.DirichletLaplacianFractionalRegularity := by
  intro U hU s hs hs₁
  obtain ⟨C,hC,hSecond⟩ := hH2 U hU
  let D := Classical.choice (exists_dirichletSpectralData hU)
  have hs1 : s < 1 := hs₁.trans (by norm_num)
  obtain ⟨A,hA,hValues⟩ := D.exists_fractionalEnergy_value_modes_le hU s hs hs1
  have hGrad (j : Fin 3) := D.exists_fractionalEnergy_gradient_modes_le hU (1-s)
    (sub_pos.mpr hs1) (sub_lt_self _ hs) C hSecond j
  choose B hB hModes using hGrad
  let K := D.maxMass^(2-s) + ∑ j : Fin 3, (2*B j)
  have hK : 0 ≤ K := add_nonneg (Real.rpow_nonneg D.maxMass_pos.le _)
    (Finset.sum_nonneg fun j _ => mul_nonneg (by norm_num) (hB j))
  refine ⟨Real.sqrt (K*A),Real.sqrt_nonneg _,?_⟩
  intro w f N hDual hEq
  have hSolve (v : H10 U) : h10PrincipalPart U v w = ∫ x in U, frobeniusS0 (h10Value v x) (f x) :=
    (h10PrincipalPart_apply v w).trans (hEq v)
  let M := A*N^2
  have hM : 0 ≤ M := mul_nonneg hA (sq_nonneg _)
  have hCoeff (F : Finset D.index) : finiteFractionalCoefficientEnergy D s w F ≤ M :=
    finiteCoefficientEnergy_le_fractional_dual D s A hA hValues hDual hSolve F
  obtain ⟨F,hLim⟩ := exists_mode_sums_tendsto D w
  let v (n : ℕ) := ∑ i ∈ F n,D.coefficient w i • D.mode i
  have hV : Tendsto (fun n => dirichletValueLp U (v n)) atTop (𝓝 (dirichletValueLp U w)) :=
    (dirichletValueLp U).continuous.continuousAt.tendsto.comp hLim
  have hV2 : (∫⁻ x in U, ENNReal.ofReal (‖h10Value w x‖^2)) ≤ ENNReal.ofReal (D.maxMass^(2-s)*M) := by
    apply lintegral_sq_value_le_of_Lp_tendsto hV
    intro n
    rw [lintegral_sq_norm_lp]
    exact ENNReal.ofReal_le_ofReal ((value_modes_L2_le D s (hs1.trans (by norm_num)) w (F n)).trans
      (mul_le_mul_of_nonneg_left (hCoeff (F n)) (Real.rpow_nonneg D.maxMass_pos.le _)))
  have hJ (j : Fin 3) : fractionalEnergy (1-s) U (fun x => h10Gradient w x j) ≤
      ENNReal.ofReal ((2*B j)*M) := by
    have hP : Tendsto (fun n => dirichletColumnLp U j (v n)) atTop (𝓝 (dirichletColumnLp U j w)) :=
      (dirichletColumnLp U j).continuous.continuousAt.tendsto.comp hLim
    have hK (n : ℕ) : fractionalEnergy (1-s) U (dirichletColumnLp U j (v n)) ≤
        ENNReal.ofReal (B j*M) := by
      have h := hModes j (F n) (D.coefficient w)
      simp only [neg_sub] at h
      exact h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hCoeff (F n)) (hB j)))
    have h := fractionalEnergy_le_of_Lp_tendsto_uniform (1-s) hP hK
    rw [← ENNReal.ofReal_add (mul_nonneg (hB j) hM) (mul_nonneg (hB j) hM)] at h
    exact h.trans_eq (congrArg ENNReal.ofReal (by ring))
  have hMain : dirichletFractionalTestEnergy s U w ≤ ENNReal.ofReal (K*M) := by
    unfold dirichletFractionalTestEnergy
    refine (add_le_add hV2 (Finset.sum_le_sum fun j _ => hJ j)).trans_eq ?_
    have hSum : 0 ≤ ∑ j : Fin 3, (2*B j)*M :=
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (by norm_num) (hB j)) hM
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (mul_nonneg (by norm_num) (hB j)) hM),
      ← ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg D.maxMass_pos.le _) hM) hSum]
    congr 1
    unfold K
    rw [add_mul,Finset.sum_mul]
  have hFin := hMain.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hFin,?_⟩
  unfold dirichletFractionalTestNorm
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hMain
  rw [ENNReal.toReal_ofReal (mul_nonneg hK hM)] at h
  apply (Real.sqrt_le_sqrt h).trans_eq
  have hM' : K*M = (K*A)*N^2 := by unfold M; ring
  rw [hM',Real.sqrt_mul (mul_nonneg hK hA),Real.sqrt_sq hDual.1]

/-- The pure fractional Dirichlet estimate on the original smooth domain. -/
theorem dirichletLaplacianFractionalRegularity : External.DirichletLaplacianFractionalRegularity :=
  dirichletLaplacianFractionalRegularity_of_H2 fun _ hU =>
    exists_H10_dirichletPoisson_secondWeakGradient hU

end Thesis
