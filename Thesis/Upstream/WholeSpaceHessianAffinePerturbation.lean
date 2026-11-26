module

public import Thesis.Upstream.WholeSpaceWeakHessianOperator
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-! Bounded coefficient perturbations on the scalar forcing space. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Thesis

abbrev WholeSpaceScalarLp (p : ℝ≥0∞) := Lp ℝ p (volume : Measure Point)

private theorem memLp_scalarLpMultiplier {p : ℝ≥0∞} {a : Point → ℝ}
    (ha : MemLp a ⊤ (volume : Measure Point)) (z : WholeSpaceScalarLp p) :
    MemLp (fun x => a x*z x) p (volume : Measure Point) :=
  (Lp.memLp z).smul (r := p) ha

private def scalarLpMultiplierLinear {p : ℝ≥0∞} {a : Point → ℝ}
    (ha : MemLp a ⊤ (volume : Measure Point)) :
    WholeSpaceScalarLp p →ₗ[ℝ] WholeSpaceScalarLp p where
  toFun z := (memLp_scalarLpMultiplier ha z).toLp (fun x => a x*z x)
  map_add' z w := by
    apply Lp.ext
    filter_upwards [(memLp_scalarLpMultiplier ha (z+w)).coeFn_toLp,
      (memLp_scalarLpMultiplier ha z).coeFn_toLp,(memLp_scalarLpMultiplier ha w).coeFn_toLp,
      Lp.coeFn_add z w,Lp.coeFn_add
        ((memLp_scalarLpMultiplier ha z).toLp (fun x => a x*z x))
        ((memLp_scalarLpMultiplier ha w).toLp (fun x => a x*w x))] with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.add_apply] at h₄ h₅
    rw [h₁,h₅,h₂,h₃,h₄,mul_add]
  map_smul' c z := by
    apply Lp.ext
    filter_upwards [(memLp_scalarLpMultiplier ha (c • z)).coeFn_toLp,
      (memLp_scalarLpMultiplier ha z).coeFn_toLp,Lp.coeFn_smul c z,
      Lp.coeFn_smul c ((memLp_scalarLpMultiplier ha z).toLp (fun x => a x*z x))] with x h₁ h₂ h₃ h₄
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply] at h₃ h₄
    rw [h₁,h₄,h₂,h₃]
    simp only [smul_eq_mul]
    ring

private theorem norm_scalarLpMultiplierLinear_le {p : ℝ≥0∞} [Fact (1 ≤ p)] {a : Point → ℝ}
    (ha : MemLp a ⊤ (volume : Measure Point)) {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ x, |a x| ≤ C) (z : WholeSpaceScalarLp p) :
    ‖scalarLpMultiplierLinear ha z‖ ≤ C*‖z‖ := by
  calc
    _ ≤ ‖C • z‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(memLp_scalarLpMultiplier ha z).coeFn_toLp,Lp.coeFn_smul C z] with x hx hy
      change ‖(memLp_scalarLpMultiplier ha z).toLp (fun x => a x*z x) x‖ ≤ _
      simp only [Pi.smul_apply] at hy
      rw [hx,hy,norm_mul,norm_smul,Real.norm_eq_abs (a x),Real.norm_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hBound x) (norm_nonneg _)
    _ = _ := by rw [norm_smul,Real.norm_of_nonneg hC]

/-- Multiplication by an actual bounded measurable scalar coefficient. -/
def scalarLpMultiplier {p : ℝ≥0∞} [Fact (1 ≤ p)] {a : Point → ℝ}
    (ha : MemLp a ⊤ (volume : Measure Point)) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ x, |a x| ≤ C) : WholeSpaceScalarLp p →L[ℝ] WholeSpaceScalarLp p :=
  (scalarLpMultiplierLinear (p := p) ha).mkContinuous C
    (fun z => norm_scalarLpMultiplierLinear_le ha hC hBound z)

theorem scalarLpMultiplier_ae {p : ℝ≥0∞} [Fact (1 ≤ p)] {a : Point → ℝ}
    (ha : MemLp a ⊤ (volume : Measure Point)) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ x, |a x| ≤ C) (z : WholeSpaceScalarLp p) :
    (scalarLpMultiplier ha C hC hBound z : Point → ℝ) =ᵐ[volume] fun x => a x*z x :=
  (memLp_scalarLpMultiplier ha z).coeFn_toLp

theorem norm_scalarLpMultiplier_le {p : ℝ≥0∞} [Fact (1 ≤ p)] {a : Point → ℝ}
    (ha : MemLp a ⊤ (volume : Measure Point)) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ x, |a x| ≤ C) : ‖scalarLpMultiplier (p := p) ha C hC hBound‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_scalarLpMultiplierLinear_le ha hC hBound)

/-- The perturbation of the trace equation measured on the real forcing space. -/
@[expose] def scalarHessianLpPerturbation {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Fin 3 → Fin 3 → Point → ℝ) (ha : ∀ i j, MemLp (a i j) ⊤ (volume : Measure Point))
    (δ : ℝ) (hδ : 0 ≤ δ) (hBound : ∀ i j x, |a i j x| ≤ δ)
    (T : Fin 3 → Fin 3 → (WholeSpaceScalarLp p →L[ℝ] WholeSpaceScalarLp p)) :
    WholeSpaceScalarLp p →L[ℝ] WholeSpaceScalarLp p :=
  ∑ i : Fin 3, ∑ j : Fin 3, (scalarLpMultiplier (ha i j) δ hδ (hBound i j)).comp (T i j)

theorem scalarHessianLpPerturbation_ae {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Fin 3 → Fin 3 → Point → ℝ) (ha : ∀ i j, MemLp (a i j) ⊤ (volume : Measure Point))
    (δ : ℝ) (hδ : 0 ≤ δ) (hBound : ∀ i j x, |a i j x| ≤ δ)
    (T : Fin 3 → Fin 3 → (WholeSpaceScalarLp p →L[ℝ] WholeSpaceScalarLp p))
    (z : WholeSpaceScalarLp p) :
    (scalarHessianLpPerturbation a ha δ hδ hBound T z : Point → ℝ) =ᵐ[volume]
      fun x => ∑ i : Fin 3, ∑ j : Fin 3, a i j x*T i j z x := by
  let L (i j : Fin 3) := scalarLpMultiplier (ha i j) δ hδ (hBound i j) (T i j z)
  let S (i : Fin 3) := ∑ j : Fin 3, L i j
  have hSum (i : Fin 3) : (S i : Point → ℝ) =ᵐ[volume] fun x => ∑ j : Fin 3, L i j x :=
    Lp.coeFn_finsetSum Finset.univ (L i)
  have hL (i j : Fin 3) : (L i j : Point → ℝ) =ᵐ[volume] fun x => a i j x*T i j z x :=
    scalarLpMultiplier_ae (ha i j) δ hδ (hBound i j) (T i j z)
  simp only [scalarHessianLpPerturbation,sum_apply,ContinuousLinearMap.comp_apply]
  change ((∑ i : Fin 3, S i : WholeSpaceScalarLp p) : Point → ℝ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_finsetSum Finset.univ S,Filter.eventually_all.mpr hSum,
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hL i))] with x h₁ h₂ h₃
  rw [h₁,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [h₂ i]
  exact Finset.sum_congr rfl (fun j _ => h₃ i j)

theorem norm_scalarHessianLpPerturbation_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Fin 3 → Fin 3 → Point → ℝ) (ha : ∀ i j, MemLp (a i j) ⊤ (volume : Measure Point))
    (δ : ℝ) (hδ : 0 ≤ δ) (hBound : ∀ i j x, |a i j x| ≤ δ)
    (T : Fin 3 → Fin 3 → (WholeSpaceScalarLp p →L[ℝ] WholeSpaceScalarLp p))
    {C : ℝ} (hT : ∀ i j, ‖T i j‖ ≤ C) :
    ‖scalarHessianLpPerturbation a ha δ hδ hBound T‖ ≤ 9*δ*C := by
  let B (i j : Fin 3) := (scalarLpMultiplier (ha i j) δ hδ (hBound i j)).comp (T i j)
  have hB (i j : Fin 3) : ‖B i j‖ ≤ δ*C :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (norm_scalarLpMultiplier_le (ha i j) δ hδ (hBound i j)) (hT i j) (norm_nonneg _) hδ)
  calc
    _ = ‖∑ i : Fin 3, ∑ j : Fin 3, B i j‖ := rfl
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖B i j‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, δ*C :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum fun j _ => hB i j)
    _ = _ := by simp only [Fin.sum_univ_three]; ring

theorem scalarHessianAffine_contracting {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (B : WholeSpaceScalarLp p →L[ℝ] WholeSpaceScalarLp p)
    (f : WholeSpaceScalarLp p) (hB : ‖B‖ ≤ (1:ℝ)/2) :
    ContractingWith (1/2 : ℝ≥0) (fun z => f+B z) := by
  refine ⟨by norm_num,?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm,add_sub_add_left_eq_sub,← map_sub]
  exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hB) (norm_nonneg _))

end Thesis
