module

public import Thesis.Variational.WeakCorrectionGreen
import Thesis.Upstream.WeakPoissonCoordinates

/-! The componentwise distributional Poisson equation induces the actual
Dirichlet pairing after subtracting the given smooth lift. -/

public section

noncomputable section

open Filter HarmonicMaps HolderToCK MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis

private theorem weakPoisson_frobenius_smoothTest {U : Set Point} (hU : IsOpen U)
    {u φ : Point → S0} {D : Point → Gradient} {F : Point → Tensor}
    (hu : MemH1 U u D) (hP : IsWeakPoisson U D F)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hSupp : tsupport φ ⊆ U) :
    let L (x : Point) := -(∑ k : Fin 3, frobeniusS0 (D x k) (coordDeriv k φ x))
    let R (x : Point) := frobeniusS0 (traceFreeSymmetricPart (F x)) (φ x)
    IntegrableOn L U volume ∧ IntegrableOn R U volume ∧ (∫ x in U,L x) = ∫ x in U,R x := by
  intro L R
  have huLoc : MemH1Loc U u D := fun W _ hW => hu.mono (subset_closure.trans hW.2)
  let e := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let ψ := e ∘ φ
  have hψ : ContDiff ℝ ∞ ψ := e.contDiff.comp hφ
  have hψc : HasCompactSupport ψ := hc.comp_left (map_zero e)
  have hψU : tsupport ψ ⊆ U := (tsupport_comp_subset (map_zero e) φ).trans hSupp
  have hT := (hP.to_frobenius hU huLoc).2.2 ψ hψ hψc hψU
  have hCol (x : Point) (k : Fin 3) :
      fderiv ℝ ψ x (EuclideanSpace.single k 1) = frobeniusCoordinateEquiv (coordDeriv k φ x) :=
    coordDeriv_compCLM e (hφ.differentiable (by simp) x) k
  have hPair (x : Point) :
      (∑ k : Fin 3, inner ℝ (frobeniusGradient D x k) (fderiv ℝ ψ x (EuclideanSpace.single k 1))) =
        ∑ k, frobeniusS0 (D x k) (coordDeriv k φ x) := by
    exact Finset.sum_congr rfl fun k _ => by rw [hCol]; exact frobeniusCoordinateEquiv_inner _ _
  have hForce (x : Point) :
      inner ℝ (frobeniusCoordinateEquiv (traceFreeSymmetricPart (F x))) (ψ x) = R x :=
    frobeniusCoordinateEquiv_inner _ _
  have hleft := hT.1.congr (Eventually.of_forall hPair)
  have hright := hT.2.1.congr (Eventually.of_forall hForce)
  have hEq := hT.2.2
  simp_rw [hPair,hForce] at hEq
  refine ⟨hleft.neg,hright,?_⟩
  dsimp only [L]
  rw [integral_neg,hEq,neg_neg]

/-- Removing a smooth lift from a componentwise weak Poisson pair gives
the literal H¹₀ Laplacian pairing with the projected forcing and the
Laplacian of the lift. -/
theorem h10PrincipalPart_eq_forcing_of_weakPoisson_lift
    {U : Set Point} (hU : IsOpen U) {u B : Point → S0} {D : Point → Gradient}
    {F : Point → Tensor} (hu : MemH1 U u D) (hW : IsWeakPoisson U D F)
    (hB : ContDiff ℝ ∞ B)
    (hF : MemLp (fun x => traceFreeSymmetricPart (F x) - laplacian B x) 2 (volume.restrict U))
    (w : H10 U)
    (hDw : h10Gradient w =ᵐ[volume.restrict U] fun x j => D x j - ClassicalGradient B x j) :
    ∀ v : H10 U, h10PrincipalPart U w v =
      ∫ x in U, frobeniusS0 (traceFreeSymmetricPart (F x) - laplacian B x) (h10Value v x) := by
  obtain ⟨Q,hQ⟩ := exists_H10_forcingFunctional_of_memLp hF
  have hFun : h10PrincipalPart U w = Q := by
    apply H10.continuousLinearMap_eq_of_smooth_tests _ _
    intro v φ hφ hc hSupp hVal hGrad
    let L₁ (x : Point) := -(∑ k : Fin 3, frobeniusS0 (D x k) (coordDeriv k φ x))
    let R₁ (x : Point) := frobeniusS0 (traceFreeSymmetricPart (F x)) (φ x)
    let L₂ (x : Point) := -(∑ k : Fin 3, frobeniusS0 (ClassicalGradient B x k) (coordDeriv k φ x))
    let R₂ (x : Point) := frobeniusS0 (laplacian B x) (φ x)
    obtain ⟨hLi,hRi,hEq⟩ := weakPoisson_frobenius_smoothTest hU hu hW hφ hc hSupp
    have hB₂ : ContDiffOn ℝ 2 B U := hB.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top)
    obtain ⟨hL₂,hR₂,hEq₂⟩ := green_h10_smoothTest hU hB₂ hφ hc hSupp
    have hLeft :
        (∫ x in U, -(∑ j, frobeniusS0 (h10Gradient w x j) (h10Gradient v x j))) =
          ∫ x in U, (L₁-L₂) x := by
      apply integral_congr_ae
      filter_upwards [hDw,ae_all_iff.2 hGrad] with x hx hJ
      simp only [hx,hJ,L₁,L₂,Pi.sub_apply,← frobeniusCoordinateEquiv_inner,map_sub,inner_sub_left,
        Finset.sum_sub_distrib,neg_sub]
      abel
    have hD₁ : IntegrableOn L₁ U volume := hLi
    have hD₂ : IntegrableOn L₂ U volume := hL₂
    have hE₁ : (∫ x in U,L₁ x) = ∫ x in U,R₁ x := hEq
    have hE₂ : (∫ x in U,L₂ x) = ∫ x in U,R₂ x := hEq₂
    rw [h10PrincipalPart_apply,hLeft]
    simp only [Pi.sub_apply]
    rw [integral_sub hD₁ hD₂,hE₁,hE₂,(hQ v).2]
    have hS₁ : IntegrableOn R₁ U volume := hRi
    have hS₂ : IntegrableOn R₂ U volume := hR₂
    rw [← integral_sub hS₁ hS₂]
    apply integral_congr_ae
    filter_upwards [hVal] with x hx
    change R₁ x - R₂ x = _
    rw [hx]
    simp only [R₁,R₂,← frobeniusCoordinateEquiv_inner,map_sub,inner_sub_left]
  intro v
  rw [hFun,(hQ v).2]

end Thesis
