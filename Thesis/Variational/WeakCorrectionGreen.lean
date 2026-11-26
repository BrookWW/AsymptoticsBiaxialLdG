module

public import Thesis.Variational.WeakCorrectionPairing
public import Thesis.Variational.WeakZeroTraceGraph
import Thesis.Variational.ScaledDefects
import HolderToCK.Analysis.ClassicalPoisson

/-! Green's identity and the actual forward weak correction equation. -/

public section

open Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix Matrix.Norms.Frobenius RealInnerProductSpace

set_option autoImplicit false
noncomputable section

namespace Thesis

/-- The original componentwise Laplacian of a classical field satisfies
Green's identity against a compact smooth tensor test. -/
theorem green_h10_smoothTest
    {U : Set Point} (hU : IsOpen U) {W φ : Point → S0}
    (hW : ContDiffOn ℝ 2 W U) (hφ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) φ)
    (hSupport : HasCompactSupport φ) (hSub : tsupport φ ⊆ U) :
    let D (x : Point) := -(∑ j, frobeniusS0 (ClassicalGradient W x j) (coordDeriv j φ x))
    let F (x : Point) := frobeniusS0 (laplacian W x) (φ x)
    IntegrableOn D U volume ∧ IntegrableOn F U volume ∧
      (∫ x in U, D x) = ∫ x in U, F x := by
  let Ω : HarmonicMaps.OpenDomain 3 := ⟨U, hU⟩
  let e := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let W' (x : Point) := e (W x)
  let ψ (x : Point) := e (φ x)
  have hW' : ContDiffOn ℝ 2 W' U := e.contDiff.comp_contDiffOn hW
  have hψ : ContDiff ℝ (↑(⊤ : ℕ∞) : ℕ∞ω) ψ := e.contDiff.comp hφ
  have hSuppψ : tsupport ψ ⊆ tsupport φ := by
    apply closure_mono
    intro x hx
    by_contra hn
    have hzero : φ x = 0 := Function.notMem_support.mp hn
    exact (Function.mem_support.mp hx) (by change e (φ x) = 0; rw [hzero, map_zero])
  have hψC : HasCompactSupport ψ := hSupport.of_isClosed_subset (isClosed_tsupport ψ) hSuppψ
  have hTest := (HolderToCK.weakPoissonOn_of_contDiffOn_two Ω hW').2 ψ hψ hψC (hSuppψ.trans hSub)
  let ΔW' := Laplacian.laplacian W'
  have hWL (x : Point) (hx : x ∈ U) : ΔW' x = e (laplacian W x) := by
    have hAt := (hW' x hx).contDiffAt (hU.mem_nhds hx)
    exact (HolderToCK.laplacian_eq_coordinateSum_of_contDiffAt_two W' x hAt).trans
      (laplacian_compCLM hU hW hx e)
  have hGrad (x : Point) (hx : x ∈ U) (j : Fin 3) :
      fderiv ℝ W' x (EuclideanSpace.single j 1) = e (ClassicalGradient W x j) :=
    coordDeriv_compCLM e (((hW x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt two_ne_zero) j
  have hφGrad (x : Point) (j : Fin 3) :
      fderiv ℝ ψ x (EuclideanSpace.single j 1) = e (coordDeriv j φ x) :=
    coordDeriv_compCLM e (hφ.differentiable (by simp) x) j
  have hGradAe :
      (fun x => ∑ j : Fin 3, inner ℝ (fderiv ℝ W' x (EuclideanSpace.single j 1))
        (fderiv ℝ ψ x (EuclideanSpace.single j 1))) =ᵐ[volume.restrict U]
      (fun x => ∑ j, frobeniusS0 (ClassicalGradient W x j) (coordDeriv j φ x)) := by
    filter_upwards [ae_restrict_mem (μ := volume) hU.measurableSet] with x hx
    simp only [hGrad x hx, hφGrad]
    exact Finset.sum_congr rfl fun j _ => frobeniusCoordinateEquiv_inner _ _
  have hLapAe : (fun x => inner ℝ (ΔW' x) (ψ x)) =ᵐ[volume.restrict U]
      fun x => frobeniusS0 (laplacian W x) (φ x) := by
    filter_upwards [ae_restrict_mem (μ := volume) hU.measurableSet] with x hx
    rw [hWL x hx]
    exact frobeniusCoordinateEquiv_inner _ _
  refine ⟨(hTest.1.congr hGradAe).neg, hTest.2.1.congr hLapAe, ?_⟩
  have hE := hTest.2.2
  rw [integral_congr_ae hGradAe, integral_congr_ae hLapAe] at hE
  rw [integral_neg, hE, neg_neg]

/-- The classical equation of the actual scaled difference yields its
weak pairing against the entire zero-trace Sobolev graph. -/
theorem h10_weakEquation_of_classical_weakCorrectionPairing
    {U : Set Point} (hU : IsOpen U)
    (A : Point → (S0 × Gradient) →L[ℝ] S0)
    (L : H10 U →L[ℝ] HMinusOne U) (hPair : ∀ v w : H10 U, L v w = weakCorrectionPairing U A v w)
    {W F : Point → S0} (hW : ContDiffOn ℝ 2 W U) (hF : MemLp F 2 (volume.restrict U))
    (v : H10 U) (hVal : h10Value v =ᵐ[volume.restrict U] W)
    (hGrad : h10Gradient v =ᵐ[volume.restrict U] ClassicalGradient W)
    (hPde : ∀ x ∈ U, laplacian W x + A x (W x, ClassicalGradient W x) = F x) :
    ∀ w : H10 U, L v w = ∫ x in U, frobeniusS0 (F x) (h10Value w x) := by
  obtain ⟨R, hR⟩ := exists_H10_forcingFunctional_of_memLp hF
  have hEqR : L v = R := by
    apply H10.continuousLinearMap_eq_of_smooth_tests (L v) R
    intro w φ hφ hφc hφs hφVal hφGrad
    let q (x : Point) := -(∑ j, frobeniusS0 (ClassicalGradient W x j) (coordDeriv j φ x))
    let p (x : Point) := frobeniusS0 (laplacian W x) (φ x)
    let f (x : Point) := frobeniusS0 (F x) (φ x)
    let l (x : Point) := frobeniusS0 (A x (W x, ClassicalGradient W x)) (φ x)
    obtain ⟨hq, hp, hGreen⟩ := green_h10_smoothTest hU hW hφ hφc hφs
    have hFae : (fun x => frobeniusS0 (F x) (h10Value w x)) =ᵐ[volume.restrict U] f :=
      hφVal.mono fun x hx => congrArg (frobeniusS0 (F x)) hx
    have hfi : IntegrableOn f U volume := (hR w).1.congr hFae
    have hLower : l =ᵐ[volume.restrict U] f - p := by
      filter_upwards [ae_restrict_mem (μ := volume) hU.measurableSet] with x hx
      have hEq := congrArg (fun Z : S0 => frobeniusS0 Z (φ x)) (hPde x hx)
      simp only [← frobeniusCoordinateEquiv_inner, map_add, inner_add_left] at hEq
      change l x = f x - p x
      dsimp only [l, f, p]
      rw [← frobeniusCoordinateEquiv_inner, ← frobeniusCoordinateEquiv_inner,
        ← frobeniusCoordinateEquiv_inner]
      linarith only [hEq]
    have hp' : IntegrableOn p U volume := hp
    have hl : IntegrableOn l U volume := (hfi.sub hp').congr hLower.symm
    have hWa :
        (fun x => -(∑ j, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j)) +
          frobeniusS0 (A x (h10Value v x, h10Gradient v x)) (h10Value w x)) =ᵐ[volume.restrict U]
            fun x => q x + l x := by
      filter_upwards [hVal, hGrad, hφVal, eventually_all.mpr hφGrad] with x h₁ h₂ h₃ h₄
      have hφG : ∀ j, h10Gradient w x j = coordDeriv j φ x := h₄
      change -(∑ j, frobeniusS0 (h10Gradient v x j) (h10Gradient w x j)) +
        frobeniusS0 (A x (h10Value v x, h10Gradient v x)) (h10Value w x) = q x + l x
      rw [h₁, h₂, h₃]
      simp only [hφG, q, l]
    rw [hPair, weakCorrectionPairing, integral_congr_ae hWa, (hR w).2, integral_congr_ae hFae]
    rw [integral_add hq hl, hGreen, integral_congr_ae hLower]
    have hSub : (∫ x in U, (f - p) x) = (∫ x in U, f x) - ∫ x in U, p x := integral_sub hfi hp'
    rw [hSub]
    ring
  intro w
  rw [hEqR, (hR w).2]

end Thesis

end
