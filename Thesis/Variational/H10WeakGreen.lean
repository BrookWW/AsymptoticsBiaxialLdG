module

public import Thesis.Variational.H10SobolevEmbedding
public import Thesis.Foundation.FrobeniusInnerProduct
import Thesis.Foundation.WeakGradient
import Thesis.Variational.ScaledDefects
import StratificationTheory.Compactness.L2PairingConvergence

/-! Integration by parts between an actual H¹ graph and a field in the
compact smooth Dirichlet closure. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal Matrix.Norms.Frobenius

namespace Thesis

local instance weakGreenFrobenius : InnerProductSpace ℝ S0 := frobeniusInnerProductSpace

local instance weakGreenContinuousENorm : ContinuousENorm S0 :=
  @SeminormedAddGroup.toContinuousENorm S0 inferInstance

/-- Two square-integrable tensor fields give an integrable Frobenius
pairing on their original measure space. -/
theorem integrable_frobenius_of_memLp {μ : Measure Point} {f g : Point → S0}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) : Integrable (fun x => frobeniusS0 (f x) (g x)) μ := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  rw [hx,hy,frobenius_inner_eq]

private theorem integral_frobenius_smooth_test_weak_col
    {U : Set Point} {w φ : Point → S0} {D : Point → Gradient}
    (hw : MemH1 U w D) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hSupp : tsupport φ ⊆ U)
    (j : Fin 3) :
    (∫ x in U, frobeniusS0 (coordDeriv j φ x) (w x)) =
      -(∫ x in U, frobeniusS0 (φ x) (D x j)) := by
  let e := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let L (i : Fin 5) : S0 →L[ℝ] ℝ := (EuclideanSpace.proj i).comp e
  let ψ (i : Fin 5) : Point → ℝ := L i ∘ φ
  have hψ (i : Fin 5) : SmoothTest U (ψ i) :=
    ⟨(L i).contDiff.comp hφ,hc.comp_left (map_zero (L i)),
      (tsupport_comp_subset (map_zero (L i)) φ).trans hSupp⟩
  have hDer (i : Fin 5) (x : Point) : coordDeriv j (ψ i) x = L i (coordDeriv j φ x) :=
    coordDeriv_compCLM (L i) (hφ.differentiable (by simp) x) j
  have hL (i : Fin 5) : IntegrableOn (fun x => coordDeriv j (ψ i) x • w x) U volume :=
    ((hψ i).coordDeriv j |>.integrable_smul hw.locallyIntegrableOn_map).integrableOn
  have hR (i : Fin 5) : IntegrableOn (fun x => ψ i x • D x j) U volume :=
    ((hψ i).integrable_smul (hw.locallyIntegrableOn_gradient j)).integrableOn
  have hProj (i : Fin 5) :
      (∫ x in U, coordDeriv j (ψ i) x * L i (w x)) =
        -(∫ x in U, ψ i x * L i (D x j)) := by
    have h := congrArg (L i) (hw.2.2 j (ψ i) (hψ i))
    rw [map_neg] at h
    have hLeft : (∫ x in U, coordDeriv j (ψ i) x * L i (w x)) =
        L i (∫ x in U, coordDeriv j (ψ i) x • w x) := by
      calc
        _ = ∫ x in U, L i (coordDeriv j (ψ i) x • w x) :=
          integral_congr_ae (Eventually.of_forall fun x => (map_smul (L i) _ _).symm)
        _ = _ := by with_unfolding_all exact (L i).integral_comp_comm (hL i)
    have hRight : (∫ x in U, ψ i x * L i (D x j)) = L i (∫ x in U, ψ i x • D x j) := by
      calc
        _ = ∫ x in U, L i (ψ i x • D x j) :=
          integral_congr_ae (Eventually.of_forall fun x => (map_smul (L i) _ _).symm)
        _ = _ := by with_unfolding_all exact (L i).integral_comp_comm (hR i)
    exact hLeft.trans (h.trans (congrArg Neg.neg hRight.symm))
  have hExpand (v z : S0) : frobeniusS0 v z = ∑ i : Fin 5, L i v * L i z := by
    rw [← frobeniusCoordinateEquiv_inner,EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  simp_rw [hExpand]
  rw [integral_finsetSum, integral_finsetSum]
  · simp_rw [← hDer, show ∀ i x, L i (φ x) = ψ i x from fun _ _ => rfl, hProj, Finset.sum_neg_distrib]
  · intro i _
    have h := (L i).integrable_comp (hR i)
    apply h.congr
    exact Eventually.of_forall fun x => map_smul (L i) _ _
  · intro i _
    have h := (L i).integrable_comp (hL i)
    apply h.congr
    exact Eventually.of_forall fun x => by
      change L i (coordDeriv j (ψ i) x • w x) = L i (coordDeriv j φ x) * L i (w x)
      rw [map_smul,hDer]
      rfl

/-- Weak integration by parts uses the actual gradient columns on both
sides and the zero trace on the tested field. -/
theorem integral_frobenius_h10_weak_col
    {U : Set Point} (hU : IsOpen U) (v : H10 U) {w : Point → S0} {D : Point → Gradient}
    (hw : MemH1 U w D) (j : Fin 3) :
    (∫ x in U, frobeniusS0 (h10Gradient v x j) (w x)) =
      -(∫ x in U, frobeniusS0 (h10Value v x) (D x j)) := by
  obtain ⟨f,hf,hVal,_,hCol⟩ := v.exists_smooth_approximation_L6 hU
  have hL := StratificationTheory.Compactness.tendsto_integral_inner_of_L2_convergence
    (fun n => (hf n).2.2.2.2.1 j) (Lp.memLp (v.val.2 j)) hw.1 (hCol j)
  have hR := StratificationTheory.Compactness.tendsto_integral_inner_of_L2_convergence
    (fun n => (hf n).2.2.2.1) (Lp.memLp v.val.1) (hw.2.1 j) hVal
  simp only [frobenius_inner_eq] at hL hR
  apply tendsto_nhds_unique hL
  apply hR.neg.congr
  intro n
  exact (integral_frobenius_smooth_test_weak_col hw (hf n).1 (hf n).2.1 (hf n).2.2.1 j).symm

end Thesis
