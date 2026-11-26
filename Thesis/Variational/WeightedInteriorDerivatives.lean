module

public import Thesis.Variational.InteriorBiaxialBootstrap

/-! Smooth composition preserves the inverse-radius weight at each order. -/

public section

open Metric Set
open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace Thesis

theorem exists_weighted_coordinateDerivatives_comp_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) (hg : ContDiff ℝ ∞ g)
    (j : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    ∃ C > (0 : ℝ), ∀ {U : Set Point}, IsOpen U → ∀ {f : Point → E},
      ContDiffOn ℝ ∞ f U → ∀ x ∈ U, ∀ d : ℝ, 0 < d →
      (∀ k ≤ j, ∀ i : Fin k → Fin 3, ‖iteratedCoordinateDerivative k i f x‖ ≤ M * d⁻¹ ^ k) →
      ∀ k ≤ j, ∀ i : Fin k → Fin 3,
        ‖iteratedCoordinateDerivative k i (g ∘ f) x‖ ≤ C * d⁻¹ ^ k := by
  classical
  have hK (k : Fin (j + 1)) := exists_coordinateDerivative_comp_bound g hg k.val M hM
  choose K hKpos hDer using hK
  let C := 1 + ∑ k : Fin (j + 1), K k * (1 + M)
  have hC : 0 < C := by
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun k _ => mul_nonneg (hKpos k).le (by linarith))
  refine ⟨C, hC, ?_⟩
  intro U hU f hf x hx d hd hF k hk i
  let A (y : Point) := x + d • y
  let V := A ⁻¹' U
  have hA : ContDiff ℝ ∞ A := contDiff_const.add (contDiff_id.const_smul d)
  have hV : IsOpen V := hU.preimage hA.continuous
  have h0 : (0 : Point) ∈ V := by simpa only [V, A, mem_preimage, smul_zero, add_zero]
  have hMap : MapsTo A V U := fun _ hy => hy
  have hfA : ContDiffOn ℝ ∞ (f ∘ A) V := hf.comp hA.contDiffOn hMap
  have hScaled (l : ℕ) (hl : l ≤ j) (w : Fin l → Fin 3) :
      ‖iteratedCoordinateDerivative l w (f ∘ A) (0 : Point)‖ ≤ M := by
    have h := iteratedCoordinateDerivative_affine_dilation hU hV hf x d hMap l w h0
    change iteratedCoordinateDerivative l w (f ∘ A) 0 = d ^ l • iteratedCoordinateDerivative l w f (A 0) at h
    rw [h, show A 0 = x by simp [A], norm_smul, Real.norm_of_nonneg (pow_nonneg hd.le _)]
    calc
      _ ≤ d ^ l * (M * d⁻¹ ^ l) := mul_le_mul_of_nonneg_left (hF l hl w) (pow_nonneg hd.le _)
      _ = M := by
        rw [inv_pow, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero _ hd.ne'), mul_one]
  let k' : Fin (j + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  have hVal : ‖(f ∘ A) 0‖ ≤ M := hScaled 0 (Nat.zero_le j) (fun _ => 0)
  have hBound := hDer k' hV hfA 0 h0 hVal (fun l hl => hScaled l (hl.le.trans hk))
    M (zero_le_one.trans hM) (hScaled k hk) i
  have hCoeff : K k' * (1 + M) ≤ C :=
    (Finset.single_le_sum (f := fun l => K l * (1 + M))
      (fun l _ => mul_nonneg (hKpos l).le (by linarith)) (Finset.mem_univ k')).trans
      (le_add_of_nonneg_left zero_le_one)
  have hScaledComp := iteratedCoordinateDerivative_affine_dilation hU hV
    (hg.comp_contDiffOn hf) x d hMap k i h0
  change iteratedCoordinateDerivative k i (g ∘ (f ∘ A)) 0 =
    d ^ k • iteratedCoordinateDerivative k i (g ∘ f) (A 0) at hScaledComp
  rw [hScaledComp, show A 0 = x by simp [A], norm_smul, Real.norm_of_nonneg (pow_nonneg hd.le _)] at hBound
  apply (le_div_iff₀ (pow_pos hd _)).2 ?_ |>.trans_eq
    (by rw [div_eq_mul_inv, inv_pow])
  exact (mul_comm _ _).le.trans (hBound.trans hCoeff)

end Thesis

end
