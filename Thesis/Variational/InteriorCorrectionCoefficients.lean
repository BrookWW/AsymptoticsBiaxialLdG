module

public import Thesis.Variational.CorrectionCoefficientBounds
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Compact interior derivative bounds for the actual averaged coefficients. -/

public section

open Filter Set Topology
open scoped BigOperators ContDiff Matrix Matrix.Norms.Frobenius

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance interiorCorrectionCoefficientsOperatorNormed : NormedAddCommGroup ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance interiorCorrectionCoefficientsOperatorSpace : NormedSpace ℝ ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

local instance interiorCorrectionCoefficientsPointOperatorNormed : NormedAddCommGroup (Point →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance interiorCorrectionCoefficientsPointOperatorSpace : NormedSpace ℝ (Point →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

private theorem norm_iteratedFDeriv_prodMk_le_max
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Point → E} {g : Point → F} {x : Point} {k : ℕ}
    (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x) :
    ‖iteratedFDeriv ℝ k (fun y => (f y, g y)) x‖ ≤
      max ‖iteratedFDeriv ℝ k f x‖ ‖iteratedFDeriv ℝ k g x‖ := by
  rw [iteratedFDeriv_prodMk hf hg le_rfl]
  apply ContinuousMultilinearMap.opNorm_le_bound
    ((norm_nonneg (iteratedFDeriv ℝ k f x)).trans (le_max_left _ _))
  intro m
  rw [ContinuousMultilinearMap.prod_apply, Prod.norm_def]
  have hm : 0 ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  exact max_le ((ContinuousMultilinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hm))
    ((ContinuousMultilinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hm))

private theorem norm_iteratedFDeriv_classicalGradient_le
    {U : Set Point} (hU : IsOpen U) {Q : Point → S0}
    (hQ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U) {x : Point} (hx : x ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (ClassicalGradient Q) x‖ ≤ ‖iteratedFDeriv ℝ (k+1) Q x‖ := by
  have hAt := (hQ x hx).contDiffAt (hU.mem_nhds hx)
  have hQd : ContDiffAt ℝ k (fderiv ℝ Q) x :=
    ((hAt.fderiv_right (m := (↑(⊤ : ℕ∞) : ℕ∞ω)) (by simp)).of_le (WithTop.coe_le_coe.mpr le_top))
  have hG : ContDiffAt ℝ k (ClassicalGradient Q) x := by
    apply contDiffAt_pi.2
    intro i
    let E := ContinuousLinearMap.apply ℝ S0 (axis i)
    change ContDiffAt ℝ k (E ∘ fderiv ℝ Q) x
    exact E.contDiff.contDiffAt.comp x hQd
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro m
  have hm : 0 ≤ ‖iteratedFDeriv ℝ (k+1) Q x‖ * ∏ i, ‖m i‖ :=
    mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hm).2
  intro i
  let L : Gradient →L[ℝ] S0 := ContinuousLinearMap.proj i
  let E := ContinuousLinearMap.apply ℝ S0 (axis i)
  have hL : iteratedFDeriv ℝ k (fun y => L (ClassicalGradient Q y)) x m =
      (iteratedFDeriv ℝ k (ClassicalGradient Q) x m) i := by
    exact DFunLike.congr_fun (ContinuousLinearMap.iteratedFDeriv_comp_left L hG le_rfl) m
  have hE : iteratedFDeriv ℝ k (fun y => L (ClassicalGradient Q y)) x m =
      (iteratedFDeriv ℝ k (fderiv ℝ Q) x m) (axis i) := by
    change iteratedFDeriv ℝ k (fun y => E (fderiv ℝ Q y)) x m = _
    exact DFunLike.congr_fun (ContinuousLinearMap.iteratedFDeriv_comp_left E hQd le_rfl) m
  rw [← hL, hE]
  have hN := ContinuousLinearMap.le_opNorm (iteratedFDeriv ℝ k (fderiv ℝ Q) x m) (axis i)
  rw [show ‖axis i‖=1 from by simp [axis], mul_one] at hN
  refine hN.trans ?_
  rw [← norm_iteratedFDeriv_fderiv]
  exact ContinuousMultilinearMap.le_opNorm _ _

private theorem norm_iteratedFDeriv_correctionStateField_le
    {U : Set Point} (hU : IsOpen U) {Q : Point → S0}
    (hQ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Q U) {x : Point} (hx : x ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (correctionStateField Q) x‖ ≤
      max ‖iteratedFDeriv ℝ k Q x‖ ‖iteratedFDeriv ℝ (k+1) Q x‖ := by
  have hA : ContDiffAt ℝ k (correctionStateField Q) x :=
    (((contDiffOn_correctionStateField hU hQ) x hx).contDiffAt (hU.mem_nhds hx)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hG : ContDiffAt ℝ k (ClassicalGradient Q) x := hA.snd
  exact ((norm_iteratedFDeriv_prodMk_le_max
      (((hQ x hx).contDiffAt (hU.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr le_top)) hG).trans
    (max_le_max le_rfl (norm_iteratedFDeriv_classicalGradient_le hU hQ hx k)))

private theorem exists_eventual_derivativeBounds_for_field_and_limit
    {U K : Set Point} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {Q : ℕ → Point → S0} {q : Point → S0} (j : ℕ) (h : ConvergesCjLoc j U Q q) :
    ∃ M : ℝ, 1 ≤ M ∧ (∀ k ≤ j, ∀ x ∈ K, ‖iteratedFDeriv ℝ k q x‖ ≤ M) ∧
      ∀ᶠ n in atTop, ∀ k ≤ j, ∀ x ∈ K, ‖iteratedFDeriv ℝ k (Q n) x‖ ≤ M := by
  classical
  have hQbd (k : Fin (j+1)) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ k.val q x‖ ≤ C :=
    hK.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv h.2.1 hU (by exact_mod_cast Nat.lt_succ_iff.mp k.isLt)).mono hKU)
  choose C hC using hQbd
  let L := ∑ k : Fin (j+1), max (C k) 0
  have hL : 0 ≤ L := Finset.sum_nonneg fun k _ => le_max_right _ _
  have hq (k : Fin (j+1)) (x : Point) (hx : x ∈ K) : ‖iteratedFDeriv ℝ k.val q x‖ ≤ L :=
    ((hC k x hx).trans (le_max_left _ _)).trans
      (Finset.single_le_sum (fun k _ => le_max_right _ _) (Finset.mem_univ k))
  refine ⟨1+L, le_add_of_nonneg_right hL, ?_, ?_⟩
  · intro k hk x hx
    exact (hq ⟨k, Nat.lt_succ_iff.mpr hk⟩ x hx).trans (le_add_of_nonneg_left zero_le_one)
  · have hN (k : Fin (j+1)) :
        ∀ᶠ n in atTop, ∀ x ∈ K, dist (iteratedFDeriv ℝ k.val q x) (iteratedFDeriv ℝ k.val (Q n) x) < 1 :=
      Metric.tendstoUniformlyOn_iff.mp (h.2.2 k.val (Nat.lt_succ_iff.mp k.isLt) K hK hKU) 1 zero_lt_one
    filter_upwards [Filter.eventually_all.2 hN] with n hn
    intro k hk x hx
    let t : Fin (j+1) := ⟨k, Nat.lt_succ_iff.mpr hk⟩
    have ht := dist_triangle (iteratedFDeriv ℝ k (Q n) x) (iteratedFDeriv ℝ k q x) 0
    rw [dist_zero_right, dist_zero_right, dist_comm] at ht
    exact ht.trans (add_le_add (hn t x hx).le (hq t x hx))

/-- Compact interior convergence of the original fields supplies uniform
derivative bounds for the coefficients of their scaled difference. -/
theorem exists_eventual_compact_derivative_bound_averagedCorrectionCoefficient
    (a : BulkCoefficients) {U K : Set Point} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {Q : ℕ → Point → S0} {q : Point → S0}
    (hQ : ∀ n, ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (Q n) U)
    (hq : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) q U)
    (hConv : ∀ k : ℕ, 2 ≤ k → ConvergesCjLoc k U Q q) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ j (averagedCorrectionCoefficient a q (Q n)) x‖ ≤ C := by
  let k := max (j+1) 2
  obtain ⟨M, hM, hqBound, hQBound⟩ :=
    exists_eventual_derivativeBounds_for_field_and_limit hU hK hKU k (hConv k (le_max_right _ _))
  let E := (S0 × Gradient) × (S0 × Gradient)
  let B (x : E) := averagedHarmonicLinearization a x.1 x.2
  have hB : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) B := contDiff_averagedHarmonicLinearization a
  have hBounds (i : Fin (j+1)) : ∃ C, ∀ x ∈ Metric.closedBall (0 : E) M,
      ‖iteratedFDeriv ℝ i.val B x‖ ≤ C := by
    letI : NormedAddCommGroup (E [×i.val]→L[ℝ] ((S0 × Gradient) →L[ℝ] S0)) :=
      ContinuousMultilinearMap.normedAddCommGroup
    have hBi : Continuous (iteratedFDeriv ℝ i.val B) :=
      hB.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
    have hOpNorm : Continuous (fun T : E [×i.val]→L[ℝ] ((S0 × Gradient) →L[ℝ] S0) => ‖T‖) :=
      continuous_norm
    have hNorm : Continuous (fun x : E => ‖iteratedFDeriv ℝ i.val B x‖) := hOpNorm.comp hBi
    obtain ⟨C, hNormC⟩ := (isCompact_closedBall (0 : E) M).exists_bound_of_continuousOn hNorm.continuousOn
    refine ⟨C, ?_⟩
    intro x hx
    have h := hNormC x hx
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h)
  choose C hC using hBounds
  let A := ∑ i : Fin (j+1), max (C i) 0
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => le_max_right _ _
  refine ⟨j.factorial*A*M^j, by positivity, ?_⟩
  filter_upwards [hQBound] with n hn x hx
  have hxu : x ∈ U := hKU hx
  let Z (y : Point) := (correctionStateField q y, correctionStateField (Q n) y)
  have hZ : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) Z U :=
    (contDiffOn_correctionStateField hU hq).prodMk (contDiffOn_correctionStateField hU (hQ n))
  have hZDeriv (i : ℕ) (hi : i ≤ j) : ‖iteratedFDeriv ℝ i Z x‖ ≤ M := by
    have hqAt := ((contDiffOn_correctionStateField hU hq x hxu).contDiffAt (hU.mem_nhds hxu)).of_le
      (m := i) (WithTop.coe_le_coe.mpr le_top)
    have hQAt := ((contDiffOn_correctionStateField hU (hQ n) x hxu).contDiffAt (hU.mem_nhds hxu)).of_le
      (m := i) (WithTop.coe_le_coe.mpr le_top)
    have hi₁ : i+1 ≤ k := (Nat.add_le_add_right hi 1).trans (le_max_left _ _)
    have hi₀ : i ≤ k := (Nat.le_succ i).trans hi₁
    refine (norm_iteratedFDeriv_prodMk_le_max hqAt hQAt).trans (max_le ?_ ?_)
    · exact (norm_iteratedFDeriv_correctionStateField_le hU hq hxu i).trans
        (max_le (hqBound i hi₀ x hx) (hqBound (i+1) hi₁ x hx))
    · exact (norm_iteratedFDeriv_correctionStateField_le hU (hQ n) hxu i).trans
        (max_le (hn i hi₀ x hx) (hn (i+1) hi₁ x hx))
  have hZv : Z x ∈ Metric.closedBall (0 : E) M := by
    apply mem_closedBall_zero_iff.mpr
    have h := hZDeriv 0 (Nat.zero_le j)
    simpa only [norm_iteratedFDeriv_zero] using h
  have hA' (i : ℕ) (hi : i ≤ j) : ‖iteratedFDeriv ℝ i B (Z x)‖ ≤ A := by
    let r : Fin (j+1) := ⟨i,Nat.lt_succ_iff.mpr hi⟩
    exact ((hC r (Z x) hZv).trans (le_max_left _ _)).trans
      (Finset.single_le_sum (fun i _ => le_max_right _ _) (Finset.mem_univ r))
  have hMod := norm_iteratedFDerivWithin_comp_le (s := U) (t := Set.univ)
    hB.contDiffOn hZ (n := j) (by exact WithTop.coe_le_coe.mpr le_top)
    uniqueDiffOn_univ hU.uniqueDiffOn (mapsTo_univ Z U) hxu
    (fun i hi => by rw [iteratedFDerivWithin_univ]; exact hA' i hi)
    (fun i hi hj => by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
        (((hZ x hxu).contDiffAt (hU.mem_nhds hxu)).of_le (WithTop.coe_le_coe.mpr le_top)) hxu]
      exact (hZDeriv i hj).trans (le_self_pow₀ hM (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hi))))
  have hAOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) (B ∘ Z) U := hB.comp_contDiffOn hZ
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    (((hAOn x hxu).contDiffAt (hU.mem_nhds hxu)).of_le (WithTop.coe_le_coe.mpr le_top)) hxu] at hMod
  exact hMod

end Thesis

end
