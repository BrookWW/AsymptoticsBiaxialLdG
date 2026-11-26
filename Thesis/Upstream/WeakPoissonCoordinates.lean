module

public import Thesis.Upstream.MinimizingSobolev
public import Thesis.Variational.EulerLagrange
public import HolderToCK.Foundation.WeakPoisson

/-! The original tensor Poisson equation in the Frobenius coordinates. -/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Matrix.Norms.Frobenius RealInnerProductSpace

namespace Thesis

private def frobeniusEntry (i j : Fin 3) : HarmonicMaps.Ambient 5 →L[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.comp
    (symmetricTraceless.subtypeL.comp
      frobeniusCoordinateEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap)

private theorem frobeniusEntry_apply (i j : Fin 3) (a : HarmonicMaps.Ambient 5) :
    frobeniusEntry i j a = (frobeniusCoordinateEquiv.symm a : S0).val i j :=
  rfl

private theorem smoothTest_frobeniusEntry {Ω : Set Point} {ψ : Point → HarmonicMaps.Ambient 5}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω) (i j : Fin 3) :
    SmoothTest Ω (frobeniusEntry i j ∘ ψ) := by
  let L := frobeniusEntry i j
  have hS : tsupport (L ∘ ψ) ⊆ tsupport ψ := by
    apply closure_mono
    intro x hx
    contrapose! hx
    rw [Function.notMem_support] at hx ⊢
    change L (ψ x) = 0
    rw [hx,map_zero]
  exact ⟨L.contDiff.comp hψ,hψc.of_isClosed_subset isClosed_closure hS,hS.trans hψΩ⟩

private theorem coordDeriv_frobeniusEntry {ψ : Point → HarmonicMaps.Ambient 5}
    (hψ : ContDiff ℝ ∞ ψ) (k i j : Fin 3) (x : Point) :
    coordDeriv k (frobeniusEntry i j ∘ ψ) x =
      frobeniusEntry i j (fderiv ℝ ψ x (EuclideanSpace.single k 1)) := by
  unfold coordDeriv
  rw [fderiv_comp x (frobeniusEntry i j).differentiableAt (hψ.differentiable (by simp) x),
    ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply]
  rfl

private theorem inner_frobeniusEntry (a : S0) (b : HarmonicMaps.Ambient 5) :
    inner ℝ (frobeniusCoordinateEquiv a) b = ∑ i : Fin 3, ∑ j : Fin 3, frobeniusEntry i j b * a.val i j := by
  calc
    _ = inner ℝ (frobeniusCoordinateEquiv a) (frobeniusCoordinateEquiv (frobeniusCoordinateEquiv.symm b)) := by
      rw [LinearIsometryEquiv.apply_symm_apply]
    _ = _ := by
      rw [frobeniusCoordinateEquiv_inner,frobeniusS0,frobenius_eq_sum]
      simp only [frobeniusEntry_apply,mul_comm]

private theorem inner_frobeniusEntry_forcing (a : Tensor) (b : HarmonicMaps.Ambient 5) :
    inner ℝ (frobeniusCoordinateEquiv (traceFreeSymmetricPart a)) b =
      ∑ i : Fin 3, ∑ j : Fin 3, frobeniusEntry i j b * a i j := by
  calc
    _ = inner ℝ (frobeniusCoordinateEquiv (traceFreeSymmetricPart a))
        (frobeniusCoordinateEquiv (frobeniusCoordinateEquiv.symm b)) := by
      rw [LinearIsometryEquiv.apply_symm_apply]
    _ = _ := by
      rw [frobeniusCoordinateEquiv_inner,frobeniusS0,frobenius_traceFreeSymmetricPart,frobenius_eq_sum]
      simp only [frobeniusEntry_apply,mul_comm]

/-- The original tensor equation supplies the native weak Poisson graph.
The Sobolev map and its gradient retain their Frobenius coordinates, and
the forcing takes its actual symmetric trace-free component. -/
theorem IsWeakPoisson.to_frobenius {Ω : Set Point} {u : Point → S0}
    {D : Point → Gradient} {F : Point → Tensor} (hEq : IsWeakPoisson Ω D F)
    (hΩ : IsOpen Ω) (hu : MemH1Loc Ω u D) :
    HarmonicMaps.MemW12Loc ⟨Ω,hΩ⟩ (frobeniusField u) (frobeniusGradient D) ∧
      HolderToCK.WeakPoissonOn ⟨Ω,hΩ⟩ (frobeniusGradient D)
        (fun x => frobeniusCoordinateEquiv (traceFreeSymmetricPart (F x))) := by
  let U : HarmonicMaps.OpenDomain 3 := ⟨Ω,hΩ⟩
  have huW := (memH1Loc_iff_memW12Loc U u D).mp hu
  let S := frobeniusCoordinateEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp traceFreeSymmetricPartCLM
  have hF : LocallyIntegrableOn (fun x => frobeniusCoordinateEquiv (traceFreeSymmetricPart (F x))) Ω volume :=
    S.locallyIntegrableOn_comp hEq.locallyIntegrable
  refine ⟨huW,hF,?_⟩
  intro ψ hψ hψc hψΩ
  let φ (i j : Fin 3) := frobeniusEntry i j ∘ ψ
  have hφ (i j : Fin 3) : SmoothTest Ω (φ i j) := smoothTest_frobeniusEntry hψ hψc hψΩ i j
  let L (i j : Fin 3) := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  have hD (k i j : Fin 3) :
      LocallyIntegrableOn (fun x => (D x k).val i j) Ω volume := by
    have h := (frobeniusEntry i j).locallyIntegrableOn_comp (huW.1.2.1 k)
    have he : ((frobeniusEntry i j : HarmonicMaps.Ambient 5 → ℝ) ∘
        (fun x => frobeniusGradient D x k)) = fun x => (D x k).val i j := by
      funext x
      simp only [Function.comp_apply,frobeniusGradient,frobeniusEntry_apply,
        LinearIsometryEquiv.symm_apply_apply]
    rwa [he] at h
  have hEntry (i j : Fin 3) : LocallyIntegrableOn (fun x => F x i j) Ω volume :=
    (L i j).locallyIntegrableOn_comp hEq.locallyIntegrable
  let G (k i j : Fin 3) (x : Point) := coordDeriv k (φ i j) x * (D x k).val i j
  let P (i j : Fin 3) (x : Point) := φ i j x * F x i j
  have hG (k i j : Fin 3) : Integrable (G k i j) volume := by
    simpa only [G,smul_eq_mul] using ((hφ i j).coordDeriv k).integrable_smul (hD k i j)
  have hP (i j : Fin 3) : Integrable (P i j) volume := by
    simpa only [P,smul_eq_mul] using (hφ i j).integrable_smul (hEntry i j)
  have hLhs (x : Point) :
      (∑ k : Fin 3, inner ℝ (frobeniusGradient D x k) (fderiv ℝ ψ x (EuclideanSpace.single k 1))) =
        ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, G k i j x := by
    simp only [frobeniusGradient,inner_frobeniusEntry,G,φ,coordDeriv_frobeniusEntry hψ]
  have hRhs (x : Point) :
      inner ℝ (frobeniusCoordinateEquiv (traceFreeSymmetricPart (F x))) (ψ x) =
        ∑ i : Fin 3, ∑ j : Fin 3, P i j x :=
    inner_frobeniusEntry_forcing (F x) (ψ x)
  have hGI (k i : Fin 3) : Integrable (fun x => ∑ j : Fin 3, G k i j x) volume :=
    integrable_finsetSum _ (fun j _ => hG k i j)
  have hPI (i : Fin 3) : Integrable (fun x => ∑ j : Fin 3, P i j x) volume :=
    integrable_finsetSum _ (fun j _ => hP i j)
  have hGII (k : Fin 3) : Integrable (fun x => ∑ i : Fin 3, ∑ j : Fin 3, G k i j x) volume :=
    integrable_finsetSum _ (fun i _ => hGI k i)
  have hL :
      IntegrableOn (fun x => ∑ k : Fin 3,
        inner ℝ (frobeniusGradient D x k) (fderiv ℝ ψ x (EuclideanSpace.single k 1))) Ω volume := by
    simp only [hLhs]
    exact (integrable_finsetSum _ (fun k _ => hGII k)).integrableOn
  have hPall : IntegrableOn (fun x => inner ℝ
      (frobeniusCoordinateEquiv (traceFreeSymmetricPart (F x))) (ψ x)) Ω volume := by
    simp only [hRhs]
    exact (integrable_finsetSum _ (fun i _ => hPI i)).integrableOn
  refine ⟨hL,hPall,?_⟩
  have hComponent (i j : Fin 3) :
      (∑ k : Fin 3, ∫ x in Ω, G k i j x) = -(∫ x in Ω, P i j x) := by
    have h := hEq.test i j (φ i j) (hφ i j)
    have hGset (k : Fin 3) : (∫ x in Ω, G k i j x) = ∫ x, G k i j x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        change coordDeriv k (φ i j) x * (D x k).val i j = 0
        rw [(hφ i j).coordDeriv_eq_zero_of_notMem k hx,zero_mul])
    have hPset : (∫ x in Ω, P i j x) = ∫ x, P i j x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        change φ i j x * F x i j = 0
        rw [(hφ i j).eq_zero_of_notMem hx,zero_mul])
    simp_rw [hGset,hPset]
    exact eq_neg_of_add_eq_zero_left h
  have hSum :
      (∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∫ x in Ω, G k i j x) =
        ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ x in Ω, G k i j x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  simp only [hLhs,hRhs]
  simp_rw [integral_finsetSum _ (fun k _ => (hGII k).integrableOn)]
  simp_rw [integral_finsetSum _ (fun i _ => (hGI _ i).integrableOn)]
  simp_rw [integral_finsetSum _ (fun j _ => (hG _ _ j).integrableOn)]
  simp_rw [integral_finsetSum _ (fun i _ => (hPI i).integrableOn)]
  simp_rw [integral_finsetSum _ (fun j _ => (hP _ j).integrableOn)]
  rw [hSum]
  simp_rw [hComponent,Finset.sum_neg_distrib]

end Thesis
