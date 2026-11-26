module

public import Thesis.Interpolation.LipschitzSobolevPullback
import HarmonicMaps.Analysis.SobolevAECongruence

/-! One smooth ball sequence and its strong Sobolev pullback to the original domain. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set StratificationTheory
open scoped BigOperators ContDiff ENNReal NNReal Topology

namespace Thesis

private theorem smooth_closedBall_agreement_graph {n q : ℕ} {R : ℝ} {f g : Domain n → Ambient q}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hfg : EqOn f g (closedBall (0 : Domain n) R)) :
    let μ := (volume : Measure (Domain n)).restrict (ball (0 : Domain n) R)
    f =ᵐ[μ] g ∧
      (fun x i => coordinateDerivative f hf i x) =ᵐ[μ] (fun x i => coordinateDerivative g hg i x) := by
  intro μ
  have hU : EqOn f g (ball (0 : Domain n) R) := hfg.mono ball_subset_closedBall
  constructor
  · exact (ae_restrict_mem measurableSet_ball).mono fun _ hx => hU hx
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hEq : f =ᶠ[𝓝 x] g := Filter.mem_of_superset (isOpen_ball.mem_nhds hx) hU
    funext i
    unfold coordinateDerivative
    rw [hEq.fderiv_eq]

/-- A single smooth Lipschitz sequence converges in both the ball graph and
its original weak graph pulled back by the same bi-Lipschitz homeomorphism. -/
theorem exists_smooth_chart_graph_approximation {n q : ℕ} (F : Domain n ≃ₜ Domain n)
    {K L : ℝ≥0} (hF : LipschitzWith K (F : Domain n → Domain n)) (hInv : LipschitzWith L (F.symm : Domain n → Domain n))
    (U : OpenDomain n) {R : ℝ} (hR : 0 < R) (hU : U.val = F ⁻¹' ball (0 : Domain n) R)
    (u : Domain n → Ambient q) (D : Domain n → Gradient n q) (hu : MemW12 U u D) :
    let v := u ∘ F.symm
    let μ := (volume : Measure (Domain n)).restrict U.val
    let ν := (volume : Measure (Domain n)).restrict (ball (0 : Domain n) R)
    ∃ J : Domain n → Gradient n q, MemW12 (ballDomain (0 : Domain n) R) v J ∧
    ∃ p : ℕ → Domain n → Ambient q, ∃ hp : ∀ k, ContDiff ℝ ∞ (p k),
      (∀ k, ∃ C : ℝ≥0, LipschitzWith C (p k)) ∧
      (∀ k, MemW12 (ballDomain (0 : Domain n) R) (p k) (fun x i => coordinateDerivative (p k) (hp k) i x)) ∧
      Tendsto (fun k => eLpNorm (p k - v) 2 ν) atTop (𝓝 0) ∧
      (∀ i, Tendsto (fun k => eLpNorm (fun x => coordinateDerivative (p k) (hp k) i x - J x i) 2 ν) atTop (𝓝 0)) ∧
    ∃ G : ℕ → Domain n → Gradient n q,
      (∀ k, MemW12 U (p k ∘ F) (G k)) ∧
      Tendsto (fun k => eLpNorm (p k ∘ F - u) 2 μ) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun k => eLpNorm (fun x => G k x i - D x i) 2 μ) atTop (𝓝 0) := by
  intro v μ ν
  let Ball := ballDomain (0 : Domain n) R
  let V : OpenDomain n := ⟨F.symm ⁻¹' U.val, U.property.preimage F.symm.continuous⟩
  have hVB : V = Ball := by
    apply Subtype.ext
    ext x
    change F.symm x ∈ U.val ↔ x ∈ ball (0 : Domain n) R
    rw [hU]
    change F (F.symm x) ∈ ball (0 : Domain n) R ↔ _
    rw [F.apply_symm_apply]
  let J (x : Domain n) (i : Fin n) := ∑ j : Fin n, (fderiv ℝ F.symm x (EuclideanSpace.single i 1)) j • D (F.symm x) j
  have hV : MemW12 Ball v J := by
    rw [← hVB]
    exact memW12_lipschitz_homeomorph_preimage F.symm hInv hF U u D hu
  obtain ⟨f, hf, hfW, hfv, hfj⟩ := hV.smoothDensity_memW12_ball hR
  choose p hp hpComp hpEq hLip using fun k : ℕ =>
    exists_smooth_lipschitz_agreeOn_closedBall (0 : Domain n) hR (f k) (hf k)
  have hpAE (k : ℕ) := smooth_closedBall_agreement_graph (hp k) (hf k) (hpEq k)
  let δ (k : ℕ) (x : Domain n) (i : Fin n) := coordinateDerivative (p k) (hp k) i x
  have hpW (k : ℕ) : MemW12 Ball (p k) (δ k) := (hfW k).congr_ae (hpAE k).1.symm (hpAE k).2.symm
  have hpv : Tendsto (fun k => eLpNorm (p k - v) 2 ν) atTop (𝓝 0) := by
    apply hfv.congr'
    exact Eventually.of_forall fun k => eLpNorm_congr_ae ((hpAE k).1.symm.sub EventuallyEq.rfl)
  have hpj (i : Fin n) : Tendsto (fun k => eLpNorm (fun x => δ k x i - J x i) 2 ν) atTop (𝓝 0) := by
    apply (hfj i).congr'
    refine Eventually.of_forall fun k => eLpNorm_congr_ae ?_
    have hEq : (fun x => coordinateDerivative (f k) (hf k) i x) =ᵐ[ν] fun x => δ k x i :=
      (hpAE k).2.symm.mono fun _ hx => congrFun hx i
    exact hEq.sub EventuallyEq.rfl
  refine ⟨J, hV, p, hp, hLip, hpW, hpv, hpj, ?_⟩
  let G (k : ℕ) (x : Domain n) (i : Fin n) := ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • δ k (F x) j
  let A (x : Domain n) (i : Fin n) := ∑ j : Fin n, (fderiv ℝ F x (EuclideanSpace.single i 1)) j • J (F x) j
  let W : OpenDomain n := ⟨F ⁻¹' Ball.val, Ball.property.preimage F.continuous⟩
  have hWU : W = U := Subtype.ext hU.symm
  have hA : MemW12 U (v ∘ F) A := hWU ▸ memW12_lipschitz_homeomorph_preimage F hF hInv Ball v J hV
  have hPoint : v ∘ F = u := by
    funext x
    change u (F.symm (F x)) = u x
    rw [F.symm_apply_apply]
  have hAD : A =ᵐ[μ] D := hA.1.ae_eq_of_ae_eq_map hu.1 (Eventually.of_forall (congrFun hPoint))
  have hc : ((L : ℝ≥0∞) ^ n) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hMap : Measure.map F μ ≤ (L : ℝ≥0∞) ^ n • ν := by
    have h := map_lipschitzHomeomorph_preimage_volume_le F hInv (ball (0 : Domain n) R)
    rwa [← hU] at h
  refine ⟨G, fun k => hWU ▸ memW12_lipschitz_homeomorph_preimage F hF hInv Ball (p k) (δ k) (hpW k), ?_, ?_⟩
  · have hC := tendsto_eLpNorm_comp_zero_of_map_le_smul F.continuous.measurable.aemeasurable hc hMap
      (p := 2) (f := fun k => p k - v) (fun k => ((hpW k).2.1.sub hV.2.1).aestronglyMeasurable) hpv
    have hFn (k : ℕ) : ((p k - v) ∘ F) = p k ∘ F - u := by
      funext x
      change p k (F x) - v (F x) = p k (F x) - u x
      exact congrArg (fun y : Ambient q => p k (F x) - y) (congrFun hPoint x)
    simpa only [hFn] using hC
  · intro i
    have h := tendsto_eLpNorm_lipschitz_pullback_columns (F : Domain n → Domain n) hF hc hMap δ J
      (fun k => (hpW k).2.2) hV.2.2 hpj i
    apply h.congr'
    refine Eventually.of_forall fun k => eLpNorm_congr_ae ?_
    exact EventuallyEq.rfl.sub (hAD.mono fun _ hx => congrFun hx i)

end Thesis

end
