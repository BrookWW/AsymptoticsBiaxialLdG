module

public import Thesis.Variational.BoundaryPoissonL4Gradient
import Thesis.Variational.BoundaryCaccioppoli
import Thesis.Variational.BoundaryL4Cutoff
import Thesis.Variational.BoundaryPoissonEstimate
import Thesis.Variational.LipschitzGaussGreen
import Thesis.Upstream.PoissonL4Interior
import Thesis.Upstream.WholeSpaceGradientInterpolation
import HarmonicMaps.Analysis.VariableMollificationL2
import Mathlib.Algebra.Order.Chebyshev

/-! A domain-uniform first-derivative bound for bounded classical Dirichlet data. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped BigOperators ContDiff ENNReal Topology

namespace Thesis

private theorem scalar_zeroTrace_energy_eq {U : Set Point} (hU : IsSmoothDomain U)
    {u : Point → ℝ} (hu : ContDiffOn ℝ 2 u (closure U)) (hz : EqOn u (fun _ => 0) (frontier U))
    (hG : MemLp (fderiv ℝ u) 2 (volume.restrict U))
    (hProd : IntegrableOn (fun x => u x*laplacian u x) U) :
    (∫ x in U, ∑ j : Fin 3, (coordDeriv j u x)^2) = -(∫ x in U, u x*laplacian u x) := by
  let g := u*u
  have hg : ContDiffOn ℝ 2 g (closure U) := hu.mul hu
  have hg₀ : EqOn g (fun _ => 0) (frontier U) := fun x hx => by
    change u x*u x=0
    rw [hz hx,mul_zero]
  have hgD₀ : EqOn (fderivWithin ℝ g (closure U)) (fun _ => 0) (frontier U) := by
    intro x hx
    have hxC : x ∈ closure U := frontier_subset_closure hx
    have ha := (hu x hxC).differentiableWithinAt two_ne_zero
    change fderivWithin ℝ (u*u) (closure U) x = 0
    rw [fderivWithin_mul (hU.uniqueDiffOn_closure x hxC) ha ha,hz hx,zero_smul,zero_add]
  have hc : ContDiff ℝ 2 (fun _ : Point => (1:ℝ)) := contDiff_const
  have hL (x : Point) : laplacian (fun _ : Point => (1:ℝ)) x = 0 := by
    have hd (a : ℝ) (j : Fin 3) : coordDeriv j (fun _ : Point => a) = fun _ => 0 := by
      funext y
      exact DFunLike.congr_fun (hasFDerivAt_const a y).fderiv (axis j)
    simp only [laplacian,hd,Finset.sum_const_zero]
  have hzI := (integral_cutoff_laplacian_difference_eq_zero lipschitzGaussGreen hU hg hc hg₀ hgD₀).2
  simp only [hL,mul_zero,one_mul,sub_zero] at hzI
  let W (x : Point) := ∑ j : Fin 3, (coordDeriv j u x)^2
  have hWI : IntegrableOn W U := by
    apply integrable_finsetSum Finset.univ
    intro j _
    have hj : MemLp (coordDeriv j u) 2 (volume.restrict U) :=
      (ContinuousLinearMap.apply ℝ ℝ (axis j)).comp_memLp' hG
    simpa only [Real.norm_eq_abs,sq_abs] using (memLp_two_iff_integrable_sq_norm hj.1).mp hj
  have hID : laplacian g =ᵐ[volume.restrict U] fun x => 2*(W x+u x*laplacian u x) := by
    filter_upwards [ae_restrict_mem hU.1.1.measurableSet] with x hx
    change laplacian (u*u) x = _
    rw [laplacian_mul_scalar hU.1.1 (hu.mono subset_closure) (hu.mono subset_closure) hx]
    dsimp only [W]
    simp only [← pow_two]
    ring
  rw [integral_congr_ae hID,integral_const_mul,integral_add hWI hProd] at hzI
  change (∫ x in U, W x) = _
  linarith only [hzI]

private theorem exists_scalar_dirichlet_grad_force_norms {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ J K : ℝ, 0 ≤ J ∧ 0 ≤ K ∧ ∀ {u : Point → ℝ}, ContDiffOn ℝ 2 u (closure U) →
      EqOn u (fun _ => 0) (frontier U) → ∀ {M F : ℝ}, 0 ≤ M → 0 ≤ F →
      (∀ x ∈ U, ‖u x‖ ≤ M) → (∀ x ∈ U, ‖laplacian u x‖ ≤ F) →
      MemLp (fderiv ℝ u) 2 (volume.restrict U) ∧ MemLp (laplacian u) 4 (volume.restrict U) ∧
      (eLpNorm (fderiv ℝ u) 2 (volume.restrict U)).toReal ≤ J*(M+F) ∧
      (eLpNorm (laplacian u) 4 (volume.restrict U)).toReal ≤ K*F := by
  let μ := (volume : Measure Point).restrict U
  have hC : IsCompact (closure U) := hU.1.2.2.isCompact_closure
  have hVol : (volume : Measure Point) U < ⊤ := (measure_mono subset_closure).trans_lt hC.measure_lt_top
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hVol.ne
  let J := Real.sqrt (3*(volume U).toReal)
  let K := (eLpNorm (fun _ : Point => (1:ℝ)) 4 μ).toReal
  have hJ : 0 ≤ J := Real.sqrt_nonneg _
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  refine ⟨J,K,hJ,hK,?_⟩
  intro u hu hz M F hM hF hv hf
  have huO : ContDiffOn ℝ 2 u U := hu.mono subset_closure
  have hGC := hu.continuousOn_fderivWithin hU.uniqueDiffOn_closure (by norm_num)
  obtain ⟨B,hB⟩ := hC.exists_bound_of_continuousOn hGC
  have hGa : AEStronglyMeasurable (fderiv ℝ u) μ :=
    (huO.continuousOn_fderiv_of_isOpen hU.1.1 (by norm_num)).aestronglyMeasurable hU.1.1.measurableSet
  have hD : MemLp (fderiv ℝ u) 2 μ := by
    apply MemLp.of_bound hGa B
    filter_upwards [ae_restrict_mem hU.1.1.measurableSet] with x hx
    have hNear : closure U ∈ 𝓝 x := mem_of_superset (hU.1.1.mem_nhds hx) subset_closure
    rw [← fderivWithin_of_mem_nhds hNear]
    exact hB x (subset_closure hx)
  have hFC : AEStronglyMeasurable (laplacian u) μ :=
    (continuousOn_laplacian_of_contDiffOn_two hU.1.1 huO).aestronglyMeasurable hU.1.1.measurableSet
  have hFae : ∀ᵐ x ∂μ, ‖laplacian u x‖ ≤ F :=
    (ae_restrict_mem hU.1.1.measurableSet).mono fun _ hx => hf _ hx
  have hFL : MemLp (laplacian u) 4 μ := MemLp.of_bound hFC F hFae
  have hP : Integrable (fun x => u x*laplacian u x) μ := by
    refine Integrable.of_bound (huO.continuousOn.aestronglyMeasurable hU.1.1.measurableSet |>.mul hFC) (M*F) ?_
    filter_upwards [ae_restrict_mem hU.1.1.measurableSet] with x hx
    rw [norm_mul]
    exact mul_le_mul (hv x hx) (hf x hx) (norm_nonneg _) hM
  refine ⟨hD,hFL,?_,?_⟩
  · have hW := scalar_zeroTrace_energy_eq hU hu hz hD hP
    have hJvol : 0 ≤ (volume U).toReal := ENNReal.toReal_nonneg
    have hWP : -(∫ x in U, u x*laplacian u x) ≤ (volume U).toReal*(M*F) := by
      rw [← integral_neg]
      refine (integral_mono_ae hP.neg (integrable_const (M*F)) ?_).trans_eq ?_
      · filter_upwards [ae_restrict_mem hU.1.1.measurableSet] with x hx
        exact (neg_le_abs _).trans (by
          rw [abs_mul,← Real.norm_eq_abs,← Real.norm_eq_abs]
          exact mul_le_mul (hv x hx) (hf x hx) (norm_nonneg _) hM)
      · rw [integral_const,measureReal_def]
        dsimp only [μ]
        rw [Measure.restrict_apply_univ,smul_eq_mul]
    have hI : Integrable (fun x => ‖fderiv ℝ u x‖^2) μ := (memLp_two_iff_integrable_sq_norm hD.1).mp hD
    have hKOrd (j : Fin 3) : Integrable (fun x => (coordDeriv j u x)^2) μ := by
      have h : MemLp (coordDeriv j u) 2 μ := (ContinuousLinearMap.apply ℝ ℝ (axis j)).comp_memLp' hD
      simpa only [Real.norm_eq_abs,sq_abs] using (memLp_two_iff_integrable_sq_norm h.1).mp h
    have hEst : (∫ x in U, ‖fderiv ℝ u x‖^2) ≤ 3*(volume U).toReal*(M*F) := by
      calc
        _ ≤ ∫ x in U, 3*(∑ j : Fin 3, (coordDeriv j u x)^2) := by
          apply integral_mono hI ((integrable_finsetSum Finset.univ (fun j _ => hKOrd j)).const_mul 3)
          intro x
          have h₁ := pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_sum_axisDerivative u x) 2
          have h₂ := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3)))
            (f := fun j => |coordDeriv j u x|)
          simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat,sq_abs] at h₂
          exact h₁.trans h₂
        _ ≤ _ := by
          rw [integral_const_mul,hW,mul_assoc]
          exact mul_le_mul_of_nonneg_left hWP (by norm_num)
    rw [integral_norm_sq_eq_eLpNorm_two_toReal_sq hD] at hEst
    apply le_of_sq_le_sq _ (mul_nonneg hJ (add_nonneg hM hF))
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (by norm_num) hJvol)]
    refine hEst.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hJvol))
    nlinarith only [sq_nonneg M,sq_nonneg F,mul_nonneg hM hF]
  · have hCst : MemLp (fun _ : Point => F) 4 μ := memLp_const _
    have hN := ENNReal.toReal_mono hCst.eLpNorm_ne_top (eLpNorm_mono_ae_real (p := 4) hFae)
    have hFn : (fun _ : Point => F) = F • (fun _ : Point => (1:ℝ)) := by funext x; simp
    rw [hFn,eLpNorm_const_smul,ENNReal.toReal_mul,← ofReal_norm,Real.norm_of_nonneg hF,
      ENNReal.toReal_ofReal hF,mul_comm] at hN
    exact hN

private theorem eLpNorm_toReal_restrict_mono {E : Type*} [NormedAddCommGroup E]
    {U V : Set Point} (hVU : V ⊆ U) {p : ℝ≥0∞} {f : Point → E} (hf : MemLp f p (volume.restrict U)) :
    (eLpNorm f p (volume.restrict V)).toReal ≤ (eLpNorm f p (volume.restrict U)).toReal :=
  ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hVU))

/-- The global scalar classical Dirichlet gradient bound on the actual closure. -/
theorem exists_global_zeroTrace_gradient_sup_bound {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : Point → ℝ}, ContDiffOn ℝ 2 u (closure U) →
      EqOn u (fun _ => 0) (frontier U) → ∀ {M F : ℝ}, 0 ≤ M → 0 ≤ F →
      (∀ x ∈ U, ‖u x‖ ≤ M) → (∀ x ∈ U, ‖laplacian u x‖ ≤ F) →
      ∀ x ∈ closure U, ‖fderivWithin ℝ u (closure U) x‖ ≤ C*(M+F) := by
  obtain ⟨J,K,hJ,hK,hNorms⟩ := exists_scalar_dirichlet_grad_force_norms hU
  obtain ⟨R,CB,hR,hCB,hWall⟩ := zeroTraceBoundaryPoissonL4GradientEstimate U hU
  obtain ⟨CI,hCI,hInt⟩ := exists_scalar_interiorPoissonL4_gradient_bounds
  let s := R/2
  let ρ := s/4
  have hs : 0 < s := half_pos hR
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  let A := CB*(s^(-3/2:ℝ)*J+s^(1/4:ℝ)*K)
  let B := CI*(ρ⁻¹+ρ^(1/4:ℝ)*K)
  let C := 1+A+B
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hNC : (Uᶜ : Set Point).Nonempty := Set.nonempty_compl.2 fun he =>
    NormedSpace.unbounded_univ ℝ Point (he ▸ hU.1.2.2)
  refine ⟨C,hC,?_⟩
  intro u hu hz M F hM hF hv hf
  obtain ⟨hD,hL,hDN,hLN⟩ := hNorms hu hz hM hF hv hf
  have hMF : 0 ≤ M+F := add_nonneg hM hF
  have hF' : F ≤ M+F := le_add_of_nonneg_left hM
  have hM' : M ≤ M+F := le_add_of_nonneg_right hF
  have hLC : ContinuousOn (fun x => ‖fderivWithin ℝ u (closure U) x‖) (closure U) :=
    (hu.continuousOn_fderivWithin hU.uniqueDiffOn_closure (by norm_num)).norm
  have hIn (x : Point) (hx : x ∈ U) : ‖fderivWithin ℝ u (closure U) x‖ ≤ C*(M+F) := by
    have hNear : closure U ∈ 𝓝 x := mem_of_superset (hU.1.1.mem_nhds hx) subset_closure
    rw [fderivWithin_of_mem_nhds hNear]
    obtain ⟨p,hp,hDist,hBall⟩ := exists_interior_ball_nearest_wall hU.1.1 hNC hx
    by_cases hSmall : x ∈ ball p (s/2)
    · let V := U ∩ ball p s
      let W := closure U ∩ ball p s
      have hV : V ⊆ U := inter_subset_left
      have hWV : V ⊆ W := inter_subset_inter subset_closure Subset.rfl
      have hWM : W ∈ 𝓝 x := mem_of_superset ((hU.1.1.inter isOpen_ball).mem_nhds
        ⟨hx,ball_subset_ball (half_le_self hs.le) hSmall⟩) hWV
      have hμ : volume.restrict V ≤ volume.restrict U := Measure.restrict_mono_set volume hV
      have h := hWall p hp s ⟨hs,half_lt_self hR⟩ u (laplacian u)
        (hu.mono inter_subset_left) (hz.mono inter_subset_left) (fun _ _ => rfl)
        (hD.mono_measure hμ) (hL.mono_measure hμ) x ⟨subset_closure hx,hSmall⟩
      change ‖fderivWithin ℝ u W x‖ ≤ _ at h
      rw [fderivWithin_of_mem_nhds hWM] at h
      have hD' := (eLpNorm_toReal_restrict_mono hV hD).trans hDN
      have hL' := (eLpNorm_toReal_restrict_mono hV hL).trans (hLN.trans (mul_le_mul_of_nonneg_left hF' hK))
      calc
        _ ≤ CB*(s^(-3/2:ℝ)*(J*(M+F))+s^(1/4:ℝ)*(K*(M+F))) := h.trans
          (mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul_of_nonneg_left hD' (Real.rpow_nonneg hs.le _))
            (mul_le_mul_of_nonneg_left hL' (Real.rpow_nonneg hs.le _))) hCB.le)
        _ = A*(M+F) := by unfold A; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith only [hB]) hMF
    · have hρd : ρ ≤ dist x p := by
        have h := le_of_not_gt (fun h => hSmall (mem_ball.2 h))
        dsimp only [ρ]
        linarith only [h,hs]
      have hSub : ball x ρ ⊆ U := (ball_subset_ball hρd).trans hBall
      have hμ : volume.restrict (ball x ρ) ≤ volume.restrict U := Measure.restrict_mono_set volume hSub
      have h := (hInt x hρ u (laplacian u) (hu.mono (hSub.trans subset_closure)) (fun _ _ => rfl)
        (hL.mono_measure hμ) (hD.mono_measure hμ)).2 M hM (fun y hy => hv y (hSub hy))
      have hL' := (eLpNorm_toReal_restrict_mono hSub hL).trans (hLN.trans (mul_le_mul_of_nonneg_left hF' hK))
      calc
        _ ≤ CI*(ρ⁻¹*(M+F)+ρ^(1/4:ℝ)*(K*(M+F))) := h.trans
          (mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul_of_nonneg_left hM' (inv_nonneg.mpr hρ.le))
            (mul_le_mul_of_nonneg_left hL' (Real.rpow_nonneg hρ.le _))) hCI.le)
        _ = B*(M+F) := by unfold B; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith only [hA]) hMF
  intro x hx
  exact le_on_closure hIn hLC continuousOn_const hx

end Thesis

end
