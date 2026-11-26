module

public import Thesis.Interpolation.LipschitzSobolevPullback
import StratificationTheory.Foundation.SobolevLocalAssembly
import HarmonicMaps.Analysis.RadialIntegrability

/-! Quantitative graph pullback by the Lipschitz projections of a cylinder shell. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ENNReal NNReal

namespace Thesis

private theorem memLp_fderiv_lipschitz_coordinate_top {m n : ℕ} {F : Domain m → Domain n} {K : ℝ≥0}
    (hF : LipschitzWith K F) (i : Fin m) (j : Fin n) (μ : Measure (Domain m)) :
    MemLp (fun x => (fderiv ℝ F x (EuclideanSpace.single i 1)) j) ⊤ μ := by
  have hMeas : Measurable (fun x => (fderiv ℝ F x (EuclideanSpace.single i 1)) j) :=
    (EuclideanSpace.proj j).continuous.measurable.comp
      (measurable_fderiv_apply_const ℝ F (EuclideanSpace.single i 1))
  apply memLp_top_of_bound hMeas.aestronglyMeasurable (K : ℝ)
  refine ae_of_all _ fun x => (PiLp.norm_apply_le _ j).trans ?_
  apply ((fderiv ℝ F x).le_opNorm _).trans
  rw [show ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 by simp, mul_one]
  exact norm_fderiv_le_of_lipschitz ℝ hF

private theorem map_restrict_le_smul_on_ball
    {m n : ℕ} {U : OpenDomain m} {V : OpenDomain n} {F : Domain m → Domain n}
    (hF : Measurable F) {c : ℝ≥0∞} (hMap : Measure.map F (volume.restrict U.val) ≤ c • volume.restrict V.val)
    {z : Domain n} {r : ℝ} (hB : ball z r ⊆ V.val)
    {Q : Set (Domain m)} (hQ : Q ⊆ U.val) (hTo : Q ⊆ F ⁻¹' ball z r) :
    Measure.map F (volume.restrict Q) ≤ c • volume.restrict (ball z r) := by
  have hSub : Q ⊆ F ⁻¹' ball z r ∩ U.val := fun _ hx => ⟨hTo hx, hQ hx⟩
  have hRestrict : Measure.map F ((volume.restrict U.val).restrict (F ⁻¹' ball z r)) ≤
      c • volume.restrict (ball z r) := by
    rw [← Measure.restrict_map hF measurableSet_ball]
    have h := Measure.restrict_mono_measure hMap (ball z r)
    rw [Measure.restrict_smul, Measure.restrict_restrict measurableSet_ball, inter_eq_left.2 hB] at h
    exact h
  have hMono := Measure.restrict_mono_set volume hSub
  rw [← Measure.restrict_restrict (hF measurableSet_ball)] at hMono
  exact (Measure.map_mono hMono hF).trans hRestrict

/-- The actual coordinate columns of the Lipschitz pullback hold on arbitrary
open target sets under finite domination of pushed-forward volume. -/
theorem memW12_lipschitz_domain_pullback
    {m n q : ℕ} (U : OpenDomain m) (V : OpenDomain n) (F : Domain m → Domain n)
    {K : ℝ≥0} (hF : LipschitzWith K F) (hInto : MapsTo F U.val V.val)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hMap : Measure.map F (volume.restrict U.val) ≤ c • volume.restrict V.val)
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q} (hu : MemW12 V u D) :
    MemW12 U (u ∘ F)
      (fun x i => ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • D (F x) j) := by
  let μ := volume.restrict U.val
  let ν := volume.restrict V.val
  let G (x : Domain m) (i : Fin m) := ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • D (F x) j
  have hFMeas := hF.continuous.measurable
  have hcomp {f : Domain n → Ambient q} (hf : MemLp f 2 ν) : MemLp (f ∘ F) 2 μ :=
    memLp_comp_of_map_le_smul hFMeas.aemeasurable hc hMap hf
  have hG (i : Fin m) : MemLp (fun x => G x i) 2 μ := by
    have h := memLp_finsetSum Finset.univ (fun j (_ : j ∈ Finset.univ) =>
      (hcomp (hu.2.2 j)).smul (r := 2) (memLp_fderiv_lipschitz_coordinate_top hF i j μ))
    simpa only [G, Finset.sum_apply, Pi.smul_apply', Function.comp_def] using h
  apply memW12_of_local_sobolev_pair (hcomp hu.2.1) hG
  intro x hx
  obtain ⟨r, hr, hRV⟩ := isOpen_iff.1 V.property (F x) (hInto hx)
  let A : OpenDomain m := ⟨U.val ∩ F ⁻¹' ball (F x) r, U.property.inter (isOpen_ball.preimage hF.continuous)⟩
  have hxA : x ∈ A.val := ⟨hx, mem_ball_self hr⟩
  obtain ⟨s, hs, hsA⟩ := isOpen_iff.1 A.property x hxA
  have hsU : ball x s ⊆ U.val := fun _ hy => (hsA hy).1
  have hsB : ball x s ⊆ F ⁻¹' ball (F x) r := fun _ hy => (hsA hy).2
  have hvB : MemW12 (ballDomain (F x) r) u D :=
    ⟨hu.1.mono hRV, hu.2.1.mono_measure (Measure.restrict_mono_set volume hRV),
      fun j => (hu.2.2 j).mono_measure (Measure.restrict_mono_set volume hRV)⟩
  refine ⟨s, hs, hsU, ?_⟩
  exact memW12_lipschitz_domain_pullback_ball hr hvB (ballDomain x s) measure_ball_ne_top F hF
    (fun _ hy => hsB hy) hc (map_restrict_le_smul_on_ball hFMeas hMap hRV hsU hsB)

/-- Dominated volume pullback bounds the Dirichlet integral of the actual
displayed weak columns by the Lipschitz norm and source dimension. -/
theorem dirichletEnergy_lipschitz_domain_pullback_le
    {m n q : ℕ} (U : OpenDomain m) (V : OpenDomain n) (F : Domain m → Domain n)
    {K : ℝ≥0} (hF : LipschitzWith K F)
    {c : ℝ≥0∞} (hMap : Measure.map F (volume.restrict U.val) ≤ c • volume.restrict V.val)
    {u : Domain n → Ambient q} {D : Domain n → HarmonicMaps.Gradient n q} (hu : MemW12 V u D) :
    dirichletEnergy (fun x i => ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • D (F x) j)
      U.val ≤ ENNReal.ofReal ((m : ℝ) * (K : ℝ) ^ 2) * c * dirichletEnergy D V.val := by
  let G (x : Domain m) (i : Fin m) := ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • D (F x) j
  let f (y : Domain n) := ENNReal.ofReal (hsNormSq (D y))
  let A : ℝ≥0∞ := ENNReal.ofReal ((m : ℝ) * (K : ℝ) ^ 2)
  have hBound (x : Domain m) : hsNormSq (G x) ≤ ((m : ℝ) * (K : ℝ) ^ 2) * hsNormSq (D (F x)) := by
    have hCol (i : Fin m) : ‖G x i‖ ^ 2 ≤ (K : ℝ) ^ 2 * hsNormSq (D (F x)) := by
      let e := EuclideanSpace.single i (1 : ℝ)
      let v := fderiv ℝ F x e
      have hN : ‖v‖ ≤ K := by
        apply ((fderiv ℝ F x).le_opNorm _).trans
        rw [show ‖e‖ = 1 by simp [e], mul_one]
        exact norm_fderiv_le_of_lipschitz ℝ hF
      calc
        _ ≤ ‖v‖ ^ 2 * hsNormSq (D (F x)) := norm_sq_sum_gradient_le _ v
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hN 2) (hsNormSq_nonneg _)
    exact (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hCol i).trans_eq (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc])
  have hDom : (∫⁻ x in U.val, f (F x)) ≤ c * ∫⁻ y in V.val, f y := by
    have hf := (integrable_hsNormSq_of_memLp_columns hu.2.2).aemeasurable.ennreal_ofReal
    have hFMeas := hF.continuous.measurable.aemeasurable (μ := volume.restrict U.val)
    have h := lintegral_mono' hMap (f := f) (g := f) (fun _ => le_rfl)
    rw [lintegral_smul_measure, smul_eq_mul, lintegral_map'
      (hf.mono_ac (Measure.absolutelyContinuous_of_le_smul hMap)) hFMeas] at h
    exact h
  change (∫⁻ x in U.val, ENNReal.ofReal (hsNormSq (G x))) ≤ A * c * ∫⁻ y in V.val, f y
  calc
    _ ≤ ∫⁻ x in U.val, A * f (F x) := by
      apply lintegral_mono
      intro x
      dsimp only [f, A]
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hBound x)
    _ = A * ∫⁻ x in U.val, f (F x) :=
      lintegral_const_mul' A _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_right hDom A

end Thesis

end
