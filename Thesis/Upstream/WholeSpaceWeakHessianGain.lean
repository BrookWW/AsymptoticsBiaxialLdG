module

public import Thesis.Upstream.WholeSpaceHessianFixedPoints
public import Thesis.Upstream.WholeSpaceWeakHessianIdentification
import Thesis.Upstream.AmbientWeakPartialLpBounds

/-! (L^4) gain for actual weak Hessians under small coefficient perturbations. -/

public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Thesis

local instance wholeSpaceWeakGainTwo : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance wholeSpaceWeakGainFour : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance wholeSpaceWeakGainNatTwo : Fact (1 ≤ ((2 : ℕ) : ℝ≥0∞)) := ⟨by norm_num⟩
local instance wholeSpaceWeakGainNatFour : Fact (1 ≤ ((4 : ℕ) : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem scalarHessianAffine_formula {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : Point → ℝ} (hf : MemLp f p (volume : Measure Point))
    (a : Fin 3 → Fin 3 → Point → ℝ) (ha : ∀ i j, MemLp (a i j) ⊤ (volume : Measure Point))
    (δ : ℝ) (hδ : 0 ≤ δ) (hBound : ∀ i j x, |a i j x| ≤ δ)
    (T : Fin 3 → Fin 3 → (WholeSpaceScalarLp p →L[ℝ] WholeSpaceScalarLp p))
    (z : WholeSpaceScalarLp p) :
    ((hf.toLp f+scalarHessianLpPerturbation a ha δ hδ hBound T z : WholeSpaceScalarLp p) : Point → ℝ) =ᵐ[volume]
      fun x => f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x*T i j z x := by
  filter_upwards [Lp.coeFn_add (hf.toLp f) (scalarHessianLpPerturbation a ha δ hδ hBound T z),
    hf.coeFn_toLp,scalarHessianLpPerturbation_ae a ha δ hδ hBound T z] with x h₁ h₂ h₃
  simp only [Pi.add_apply] at h₁
  rw [h₁,h₂,h₃]

private theorem norm_scalarHessianAffine_fixedPoint_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (B : WholeSpaceScalarLp p →L[ℝ] WholeSpaceScalarLp p)
    (b : WholeSpaceScalarLp p) (hc : ContractingWith (1/2 : ℝ≥0) (fun z => b+B z)) :
    ‖ContractingWith.fixedPoint (fun z => b+B z) hc‖ ≤ 2*‖b‖ := by
  have h := hc.dist_fixedPoint_le (0 : WholeSpaceScalarLp p)
  simp only [map_zero,add_zero,dist_zero_left] at h
  norm_num at h
  linarith only [h]

/-- If a square-integrable weak Hessian satisfies a small bounded
coefficient perturbation of the flat trace equation, its original
columns are fourth-integrable with a uniform bound. -/
theorem exists_wholeSpace_weakHessian_four_gain :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ {u f : Point → ℝ} {H a : Fin 3 → Fin 3 → Point → ℝ},
        MemLp u 2 (volume : Measure Point) →
        IsWeakScalarHessian u H →
        (∀ i j, MemLp (H i j) 2 (volume : Measure Point)) →
        HasCompactSupport f → MemLp f 2 (volume : Measure Point) → MemLp f 4 (volume : Measure Point) →
        (∀ i j, AEStronglyMeasurable (a i j) (volume : Measure Point) ∧ HasCompactSupport (a i j)) →
        (∀ i j x, |a i j x| ≤ δ) →
        (scalarWeakHessianTrace H =ᵐ[volume]
          fun x => f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x*H i j x) →
        ∀ i j, MemLp (H i j) 4 (volume : Measure Point) ∧
          lpNorm (H i j) 4 (volume : Measure Point) ≤ C*lpNorm f 4 (volume : Measure Point) := by
  obtain ⟨C₂,hC₂,hT₂⟩ := exists_wholeSpace_laplacianHessianOperator 2 (by decide)
  obtain ⟨C₄,hC₄,hT₄⟩ := exists_wholeSpace_laplacianHessianOperator 4 (by decide)
  choose T₂ hT₂N hT₂ using hT₂
  choose T₄ hT₄N hT₄ using hT₄
  let M := max C₂ C₄
  have hM : 0 < M := hC₂.trans_le (le_max_left _ _)
  let δ := (18*M)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (mul_pos (by norm_num) hM)
  have hSmall : 9*δ*M = (1:ℝ)/2 := by
    dsimp only [δ]
    field_simp [hM.ne']
    ring
  refine ⟨δ,2*C₄,hδ,by positivity,?_⟩
  intro u f H a hu hWeak hH hfc hf₂ hf₄ ha hBound hEq
  have haLp (i j : Fin 3) : MemLp (a i j) ⊤ (volume : Measure Point) :=
    memLp_top_of_bound (ha i j).1 δ
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hBound i j x)
  let B₂ := scalarHessianLpPerturbation a haLp δ hδ.le hBound T₂
  let B₄ := scalarHessianLpPerturbation a haLp δ hδ.le hBound T₄
  let b₂ := hf₂.toLp f
  let b₄ := hf₄.toLp f
  let P₂ (z : WholeSpaceScalarLp 2) := b₂+B₂ z
  let P₄ (z : WholeSpaceScalarLp 4) := b₄+B₄ z
  have hB₂ : ‖B₂‖ ≤ (1:ℝ)/2 := by
    rw [← hSmall]
    exact norm_scalarHessianLpPerturbation_le a haLp δ hδ.le hBound T₂
      (fun i j => (hT₂N i j).trans (le_max_left _ _))
  have hB₄ : ‖B₄‖ ≤ (1:ℝ)/2 := by
    rw [← hSmall]
    exact norm_scalarHessianLpPerturbation_le a haLp δ hδ.le hBound T₄
      (fun i j => (hT₄N i j).trans (le_max_right _ _))
  have hc₂ : ContractingWith (1/2 : ℝ≥0) P₂ := scalarHessianAffine_contracting B₂ b₂ hB₂
  have hc₄ : ContractingWith (1/2 : ℝ≥0) P₄ := scalarHessianAffine_contracting B₄ b₄ hB₄
  have hP₂ (z : WholeSpaceScalarLp 2) : (P₂ z : Point → ℝ) =ᵐ[volume]
      fun x => f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x*T₂ i j z x :=
    scalarHessianAffine_formula hf₂ a haLp δ hδ.le hBound T₂ z
  have hP₄ (z : WholeSpaceScalarLp 4) : (P₄ z : Point → ℝ) =ᵐ[volume]
      fun x => f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x*T₄ i j z x :=
    scalarHessianAffine_formula hf₄ a haLp δ hδ.le hBound T₄ z
  let g := scalarWeakHessianTrace H
  have hg : MemLp g 2 (volume : Measure Point) :=
    memLp_finsetSum Finset.univ (fun i _ => hH i i)
  let z₂ := hg.toLp g
  let z₄ := ContractingWith.fixedPoint P₄ hc₄
  have hActual (i j : Fin 3) : (T₂ i j z₂ : Point → ℝ) =ᵐ[volume] H i j :=
    wholeSpace_laplacianHessianOperator_ae_eq_of_weak hu hg hWeak hH EventuallyEq.rfl i j _ (hT₂ i j)
  have hFixed : IsFixedPt P₂ z₂ := by
    apply Lp.ext
    filter_upwards [hP₂ z₂,hg.coeFn_toLp,hEq,
      Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hActual i))] with x h₁ h₂ h₃ h₄
    rw [h₁,h₂]
    simpa only [h₄] using h₃.symm
  have hAgree : (z₂ : Point → ℝ) =ᵐ[volume] (z₄ : Point → ℝ) := by
    rw [hc₂.fixedPoint_unique hFixed]
    exact scalarHessianAffine_fixedPoint_ae_eq a (fun i j => (ha i j).2) f hfc
      T₂ T₄ hT₂ hT₄ P₂ P₄ hP₂ hP₄ hc₂ hc₄
  let b (x : Point) := f x+∑ i : Fin 3, ∑ j : Fin 3, a i j x*H i j x
  have hb : HasCompactSupport b := hfc.add
    (hasCompactSupport_real_finsetSum Finset.univ (fun i _ =>
      hasCompactSupport_real_finsetSum Finset.univ (fun j _ => (ha i j).2.mul_right)))
  have hBz : (z₂ : Point → ℝ) =ᵐ[volume] b := hg.coeFn_toLp.trans hEq
  have hz₄ : ‖z₄‖ ≤ 2*‖b₄‖ := norm_scalarHessianAffine_fixedPoint_le B₄ b₄ hc₄
  intro i j
  have he : (T₄ i j z₄ : Point → ℝ) =ᵐ[volume] H i j := by
    have hCo := wholeSpaceHessianPair_agree hb z₂ z₄ hBz (hAgree.symm.trans hBz) i j _ _ (hT₂ i j) (hT₄ i j)
    exact hCo.symm.trans (hActual i j)
  refine ⟨MemLp.ae_eq he (Lp.memLp (T₄ i j z₄)),?_⟩
  have hNorm : lpNorm (fun x => T₄ i j z₄ x) 4 (volume : Measure Point) = ‖T₄ i j z₄‖ := by
    rw [← toReal_eLpNorm (Lp.aestronglyMeasurable _),Lp.norm_def]
    simp only [Nat.cast_ofNat]
  have hForcing : ‖b₄‖ = lpNorm f 4 (volume : Measure Point) := by
    rw [← toReal_eLpNorm hf₄.1,Lp.norm_toLp]
  calc
    _ = ‖T₄ i j z₄‖ := (ambient_lpNorm_congr_ae he).symm.trans hNorm
    _ ≤ C₄*‖z₄‖ := ((T₄ i j).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hT₄N i j) (norm_nonneg _))
    _ ≤ C₄*(2*‖b₄‖) := mul_le_mul_of_nonneg_left hz₄ hC₄.le
    _ = _ := by rw [hForcing]; ring

end Thesis
