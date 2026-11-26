module

public import SupportingAnalysis.Basics
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! A local (L^2) Hessian estimate from weighted integration by parts. -/

public section

open Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff Topology

set_option autoImplicit false

namespace SupportingAnalysis

@[expose] noncomputable def coordinatePartial {m : ℕ} (i : Fin m) (f : E m → ℝ) :
    E m → ℝ := fun x => fderiv ℝ f x (axis i)

theorem coordinatePartial_smooth {m : ℕ} {f : E m → ℝ} (hf : ContDiff ℝ ∞ f)
    (i : Fin m) : ContDiff ℝ ∞ (coordinatePartial i f) :=
  (ContinuousLinearMap.apply ℝ ℝ (axis i)).contDiff.comp (hf.fderiv_right (by simp))

private theorem coordinatePartial_compact {m : ℕ} {f : E m → ℝ} (hf : HasCompactSupport f)
    (i : Fin m) : HasCompactSupport (coordinatePartial i f) :=
  hf.fderiv_apply ℝ (axis i)

private theorem coordinatePartial_mul {m : ℕ} {f g : E m → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (i : Fin m) (x : E m) :
    coordinatePartial i (f * g) x =
      coordinatePartial i f x * g x + f x * coordinatePartial i g x := by
  unfold coordinatePartial
  rw [fderiv_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  simp [mul_comm, add_comm]

private theorem coordinatePartial_comm {m : ℕ} {f : E m → ℝ} (hf : ContDiff ℝ ∞ f)
    (i j : Fin m) : coordinatePartial j (coordinatePartial i f) =
      coordinatePartial i (coordinatePartial j f) := by
  funext x
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have hEval (v w : E m) :
      fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
    change fderiv ℝ ((ContinuousLinearMap.apply ℝ ℝ v) ∘ fderiv ℝ f) x w = _
    rw [((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hD.hasFDerivAt).fderiv]
    rfl
  have hSmooth : minSmoothness ℝ 2 ≤ ∞ := by
    simp only [minSmoothness, if_pos (show IsRCLikeNormedField ℝ from inferInstance)]
    exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  unfold coordinatePartial
  rw [hEval, hEval]
  exact (hf.contDiffAt.isSymmSndFDerivAt hSmooth).eq (axis j) (axis i)

private theorem integral_coordinatePartial_parts {m : ℕ} {f g : E m → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hfc : HasCompactSupport f)
    (i : Fin m) :
    (∫ x, f x * coordinatePartial i g x) = -∫ x, coordinatePartial i f x * g x := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact ((coordinatePartial_smooth hf i).continuous.mul hg.continuous) |>.integrable_of_hasCompactSupport (coordinatePartial_compact hfc i).mul_right
  · exact (hf.continuous.mul (coordinatePartial_smooth hg i).continuous) |>.integrable_of_hasCompactSupport hfc.mul_right
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfc.mul_right
  · intro x _
    exact hf.differentiable (by simp) x
  · intro x _
    exact hg.differentiable (by simp) x

/-- The weighted integral of one mixed second derivative squared, with the two cutoff terms. -/
private theorem weighted_second_derivative_identity {m : ℕ} {f weight : E m → ℝ}
    (hf : ContDiff ℝ ∞ f) (hw : ContDiff ℝ ∞ weight) (hc : HasCompactSupport weight)
    (i j : Fin m) :
    (∫ x, weight x * (scalarHessian f x i j) ^ 2) =
      (∫ x, weight x * scalarHessian f x i i * scalarHessian f x j j) +
      (∫ x, coordinatePartial i weight x * coordinatePartial i f x * scalarHessian f x j j) -
      (∫ x, coordinatePartial j weight x * coordinatePartial i f x * scalarHessian f x i j) := by
  let first := coordinatePartial i f
  let mixed := coordinatePartial j first
  let diagonal := coordinatePartial j (coordinatePartial j f)
  have hFirst : ContDiff ℝ ∞ first := coordinatePartial_smooth hf i
  have hMixed : ContDiff ℝ ∞ mixed := coordinatePartial_smooth hFirst j
  have hDiagonal : ContDiff ℝ ∞ diagonal :=
    coordinatePartial_smooth (coordinatePartial_smooth hf j) j
  have hComm : coordinatePartial j mixed = coordinatePartial i diagonal := by
    dsimp only [mixed, diagonal, first]
    rw [coordinatePartial_comm hf i j, coordinatePartial_comm (coordinatePartial_smooth hf j) i j]
  have hcross₁ : Integrable (fun x => coordinatePartial j weight x * mixed x * first x) :=
    (((coordinatePartial_smooth hw j).continuous.mul hMixed.continuous).mul hFirst.continuous) |>.integrable_of_hasCompactSupport (coordinatePartial_compact hc j).mul_right.mul_right
  have hcross₂ : Integrable (fun x => coordinatePartial i weight x * first x * diagonal x) :=
    (((coordinatePartial_smooth hw i).continuous.mul hFirst.continuous).mul hDiagonal.continuous) |>.integrable_of_hasCompactSupport (coordinatePartial_compact hc i).mul_right.mul_right
  have hthird : Integrable (fun x => weight x * coordinatePartial i diagonal x * first x) :=
    ((hw.continuous.mul (coordinatePartial_smooth hDiagonal i).continuous).mul
      hFirst.continuous).integrable_of_hasCompactSupport hc.mul_right.mul_right
  have hsecond : Integrable (fun x => weight x * coordinatePartial i first x * diagonal x) :=
    ((hw.continuous.mul (coordinatePartial_smooth hFirst i).continuous).mul
      hDiagonal.continuous).integrable_of_hasCompactSupport hc.mul_right.mul_right
  have h₁ := integral_coordinatePartial_parts (hw.mul hMixed) hFirst hc.mul_right j
  have h₁' : (∫ x, weight x * mixed x ^ 2) =
      -(∫ x, coordinatePartial j weight x * mixed x * first x) -
        (∫ x, weight x * coordinatePartial i diagonal x * first x) := by
    change (∫ x, (weight * mixed) x * mixed x) =
      -∫ x, coordinatePartial j (weight * mixed) x * first x at h₁
    have hL : (∫ x, (weight * mixed) x * mixed x) = ∫ x, weight x * mixed x ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      change weight x * mixed x * mixed x = _
      ring
    have hR : (∫ x, coordinatePartial j (weight * mixed) x * first x) =
        (∫ x, coordinatePartial j weight x * mixed x * first x) +
          (∫ x, weight x * coordinatePartial i diagonal x * first x) := by
      rw [← integral_add hcross₁ hthird]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      change coordinatePartial j (weight * mixed) x * first x = _
      rw [coordinatePartial_mul hw hMixed j x, hComm]
      ring
    rw [hL, hR] at h₁
    linarith only [h₁]
  have h₂ := integral_coordinatePartial_parts (hw.mul hFirst) hDiagonal hc.mul_right i
  have h₂' : (∫ x, weight x * coordinatePartial i diagonal x * first x) =
      -(∫ x, coordinatePartial i weight x * first x * diagonal x) -
        (∫ x, weight x * coordinatePartial i first x * diagonal x) := by
    have hL : (∫ x, (weight * first) x * coordinatePartial i diagonal x) =
        ∫ x, weight x * coordinatePartial i diagonal x * first x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      change weight x * first x * _ = _
      ring
    have hR : (∫ x, coordinatePartial i (weight * first) x * diagonal x) =
        (∫ x, coordinatePartial i weight x * first x * diagonal x) +
          (∫ x, weight x * coordinatePartial i first x * diagonal x) := by
      rw [← integral_add hcross₂ hsecond]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      change coordinatePartial i (weight * first) x * diagonal x = _
      rw [coordinatePartial_mul hw hFirst i x]
      ring
    change (∫ x, (weight * first) x * coordinatePartial i diagonal x) =
      -∫ x, coordinatePartial i (weight * first) x * diagonal x at h₂
    rw [hL, hR] at h₂
    linarith only [h₂]
  change (∫ x, weight x * mixed x ^ 2) =
    (∫ x, weight x * coordinatePartial i first x * diagonal x) +
      (∫ x, coordinatePartial i weight x * first x * diagonal x) -
      (∫ x, coordinatePartial j weight x * first x * mixed x)
  rw [h₁', h₂']
  have hSwap : (∫ x, coordinatePartial j weight x * mixed x * first x) =
      ∫ x, coordinatePartial j weight x * first x * mixed x := by
    congr 1
    funext x
    ring
  rw [hSwap]
  ring

private theorem scalarHessian_sq_sum {m : ℕ} (f : E m → ℝ) (x : E m) :
    scalarHessianNorm f x ^ 2 = ∑ i, ∑ j, (scalarHessian f x i j) ^ 2 := by
  unfold scalarHessianNorm
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

private theorem twice_mul_le_weighted_sq {a b ε : ℝ} (hε : 0 < ε) :
    2 * a * b ≤ ε * a ^ 2 + ε⁻¹ * b ^ 2 := by
  have hId : ε * ((ε * a ^ 2 + ε⁻¹ * b ^ 2) - 2 * a * b) = (ε * a - b) ^ 2 := by
    field_simp [hε.ne']
    ring
  exact sub_nonneg.mp ((nonneg_of_mul_nonneg_right (by rw [hId]; positivity) hε) :
    0 ≤ (ε * a ^ 2 + ε⁻¹ * b ^ 2) - 2 * a * b)

private theorem integral_doubleSum {m : ℕ} (f : Fin m → Fin m → E m → ℝ)
    (hf : ∀ i j, Integrable (f i j)) :
    (∫ x, ∑ i, ∑ j, f i j x) = ∑ i, ∑ j, ∫ x, f i j x := by
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hf i j)]
  exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hf i j

private theorem weighted_error_pointwise_le {m : ℕ} {f η : E m → ℝ}
    (hη : ContDiff ℝ ∞ η) {ε : ℝ} (hε : 0 < ε)
    (k i j l : Fin m) (x : E m) :
    |coordinatePartial k (η * η) x * coordinatePartial i f x * scalarHessian f x j l| ≤
      ε * (η x ^ 2 * scalarHessianNorm f x ^ 2) +
      ε⁻¹ * (‖fderiv ℝ η x‖ ^ 2 * ∑ q : Fin m, (coordinatePartial q f x) ^ 2) := by
  let H (x : E m) := η x ^ 2 * scalarHessianNorm f x ^ 2
  let G (x : E m) := ‖fderiv ℝ η x‖ ^ 2 * ∑ q : Fin m, (coordinatePartial q f x) ^ 2
  have hAxis : ‖(axis k : E m)‖ = 1 := by simp [axis, PiLp.norm_single]
  have hAxisBound : |coordinatePartial k η x| ≤ ‖fderiv ℝ η x‖ := by
    simpa only [coordinatePartial, Real.norm_eq_abs, hAxis, mul_one] using
      (fderiv ℝ η x).le_opNorm (axis k)
  have hessianBound : |η x * scalarHessian f x j l| ^ 2 ≤ H x := by
    rw [sq_abs, mul_pow]
    change _ ≤ (η x) ^ 2 * (scalarHessianNorm f x) ^ 2
    rw [scalarHessian_sq_sum]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact (Finset.single_le_sum (f := fun l : Fin m => (scalarHessian f x j l) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun j : Fin m => ∑ l, (scalarHessian f x j l) ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j))
  have gradBound : |coordinatePartial k η x * coordinatePartial i f x| ^ 2 ≤ G x := by
    rw [sq_abs, mul_pow]
    change _ ≤ ‖fderiv ℝ η x‖ ^ 2 * ∑ q : Fin m, (coordinatePartial q f x) ^ 2
    refine mul_le_mul ?_ ?_ (sq_nonneg _) (sq_nonneg _)
    · rw [← sq_abs (coordinatePartial k η x)]
      exact pow_le_pow_left₀ (abs_nonneg _) hAxisBound 2
    · exact Finset.single_le_sum (f := fun q : Fin m => (coordinatePartial q f x) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hSplit : coordinatePartial k (η * η) x * coordinatePartial i f x *
        scalarHessian f x j l =
      2 * (η x * scalarHessian f x j l) *
        (coordinatePartial k η x * coordinatePartial i f x) := by
    rw [coordinatePartial_mul hη hη]
    ring
  rw [hSplit, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact (twice_mul_le_weighted_sq hε).trans
    (add_le_add (mul_le_mul_of_nonneg_left hessianBound hε.le)
      (mul_le_mul_of_nonneg_left gradBound (inv_nonneg.2 hε.le)))

theorem weighted_scalarHessian_integral_le {m : ℕ} {f η : E m → ℝ}
    (hf : ContDiff ℝ ∞ f) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) :
    (∫ x, (η x) ^ 2 * (scalarHessianNorm f x) ^ 2) ≤
      2 * (∫ x, (η x) ^ 2 * (laplacian f x) ^ 2) +
      16 * ((m : ℝ) + 1) ^ 4 *
        (∫ x, ‖fderiv ℝ η x‖ ^ 2 * ∑ i : Fin m, (coordinatePartial i f x) ^ 2) := by
  let weight := η * η
  let H (x : E m) := (η x) ^ 2 * (scalarHessianNorm f x) ^ 2
  let G (x : E m) := ‖fderiv ℝ η x‖ ^ 2 * ∑ i : Fin m, (coordinatePartial i f x) ^ 2
  let N := (m : ℝ) + 1
  let ε := (4 * N ^ 2)⁻¹
  have hN : 0 < N := by dsimp [N]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hw : ContDiff ℝ ∞ weight := hη.mul hη
  have hcw : HasCompactSupport weight := hcη.mul_right
  have hsH (i j : Fin m) : ContDiff ℝ ∞ (fun x => scalarHessian f x i j) :=
    coordinatePartial_smooth (coordinatePartial_smooth hf i) j
  have hwt (x : E m) : weight x = η x ^ 2 := (pow_two _).symm
  let hessTerm (i j : Fin m) (x : E m) := weight x * (scalarHessian f x i j) ^ 2
  let lapTerm (i j : Fin m) (x : E m) := weight x * scalarHessian f x i i * scalarHessian f x j j
  have hhi (i j : Fin m) : Integrable (hessTerm i j) :=
    (hw.continuous.mul ((hsH i j).continuous.pow 2)).integrable_of_hasCompactSupport hcw.mul_right
  have hli (i j : Fin m) : Integrable (lapTerm i j) :=
    ((hw.continuous.mul (hsH i i).continuous).mul (hsH j j).continuous)
      |>.integrable_of_hasCompactSupport hcw.mul_right.mul_right
  have hHEq (x : E m) : H x = ∑ i, ∑ j, hessTerm i j x := by
    simp only [H, hessTerm, hwt, scalarHessian_sq_sum, Finset.mul_sum]
  have hLEq (x : E m) : η x ^ 2 * (laplacian f x) ^ 2 = ∑ i, ∑ j, lapTerm i j x := by
    change η x ^ 2 * (∑ i : Fin m, scalarHessian f x i i) ^ 2 = _
    rw [pow_two (∑ i : Fin m, scalarHessian f x i i)]
    simp_rw [Finset.sum_mul, Finset.mul_sum, lapTerm, hwt, mul_assoc]
  have hHi : Integrable H := (integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => hhi i j).congr (Eventually.of_forall fun x => (hHEq x).symm)
  have hGi : Integrable G := by
    have hGradSq : Continuous (fun x : E m => ∑ i : Fin m, (coordinatePartial i f x) ^ 2) :=
      continuous_finsetSum Finset.univ fun i _ => (coordinatePartial_smooth hf i).continuous.pow 2
    have hEtaSq : Continuous (fun x : E m => ‖fderiv ℝ η x‖ ^ 2) :=
      (hη.continuous_fderiv (by simp)).norm.pow 2
    have hEtaSqC : HasCompactSupport (fun x : E m => ‖fderiv ℝ η x‖ ^ 2) :=
      (hcη.fderiv ℝ).comp_left (g := fun T : E m →L[ℝ] ℝ => ‖T‖ ^ 2) (by simp)
    exact (hEtaSq.mul hGradSq).integrable_of_hasCompactSupport hEtaSqC.mul_right
  have hH0 : 0 ≤ (∫ x, H x) := integral_nonneg fun x => by dsimp [H]; positivity
  have hG0 : 0 ≤ (∫ x, G x) := integral_nonneg fun x => by dsimp [G]; positivity
  let error (k i j l : Fin m) (x : E m) :=
    coordinatePartial k weight x * coordinatePartial i f x * scalarHessian f x j l
  have hErrorInt (k i j l : Fin m) : Integrable (error k i j l) :=
    (((coordinatePartial_smooth hw k).continuous.mul (coordinatePartial_smooth hf i).continuous).mul
      (hsH j l).continuous).integrable_of_hasCompactSupport
        (coordinatePartial_compact hcw k).mul_right.mul_right
  let I := ε * (∫ x, H x) + ε⁻¹ * (∫ x, G x)
  have hErrorUpper (k i j l : Fin m) : (∫ x, error k i j l x) ≤ I := by
    rw [show I = ∫ x, ε * H x + ε⁻¹ * G x by
      rw [integral_add (hHi.const_mul ε) (hGi.const_mul ε⁻¹), integral_const_mul, integral_const_mul]]
    exact integral_mono (hErrorInt k i j l) ((hHi.const_mul _).add (hGi.const_mul _))
      (fun x => (le_abs_self _).trans (weighted_error_pointwise_le hη hε k i j l x))
  have hErrorLower (k i j l : Fin m) : -(∫ x, error k i j l x) ≤ I := by
    rw [← integral_neg, show I = ∫ x, ε * H x + ε⁻¹ * G x by
      rw [integral_add (hHi.const_mul ε) (hGi.const_mul ε⁻¹), integral_const_mul, integral_const_mul]]
    exact integral_mono (hErrorInt k i j l).neg ((hHi.const_mul _).add (hGi.const_mul _))
      (fun x => (neg_le_abs _).trans (weighted_error_pointwise_le hη hε k i j l x))
  have hPair (i j : Fin m) : (∫ x, hessTerm i j x) ≤ (∫ x, lapTerm i j x) + 2 * I := by
    have h := weighted_second_derivative_identity hf hw hcw i j
    change (∫ x, hessTerm i j x) = (∫ x, lapTerm i j x) +
      (∫ x, error i i j j x) - (∫ x, error j i i j x) at h
    linarith only [h, hErrorUpper i i j j, hErrorLower j i i j]
  have hSum : (∫ x, H x) ≤
      (∫ x, (η x) ^ 2 * (laplacian f x) ^ 2) + (m : ℝ) ^ 2 * (2 * I) := by
    rw [(integral_congr_ae (Eventually.of_forall hHEq)),
      (integral_congr_ae (Eventually.of_forall hLEq)),
      integral_doubleSum hessTerm hhi, integral_doubleSum lapTerm hli]
    calc
      _ ≤ ∑ i, ∑ j, ((∫ x, lapTerm i j x) + 2 * I) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hPair i j
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
  have hSize : (m : ℝ) ^ 2 ≤ N ^ 2 := by
    dsimp [N]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 2
  have hCrud : (m : ℝ) ^ 2 * (2 * I) ≤
      (∫ x, H x) / 2 + 8 * N ^ 4 * (∫ x, G x) := by
    calc
      _ ≤ N ^ 2 * (2 * I) := mul_le_mul_of_nonneg_right hSize (by dsimp [I]; positivity)
      _ = _ := by
        dsimp only [I, ε]
        rw [inv_inv]
        field_simp [hN.ne']
        ring
  change (∫ x, H x) ≤ 2 * (∫ x, (η x) ^ 2 * (laplacian f x) ^ 2) +
    16 * N ^ 4 * (∫ x, G x)
  linarith only [hSum, hCrud]

end SupportingAnalysis
