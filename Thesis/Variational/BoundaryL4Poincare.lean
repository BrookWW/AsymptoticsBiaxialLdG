module

public import Thesis.Variational.SmoothDomainEpigraphBoxes
public import Thesis.Upstream.PoissonL4Kernel
import Thesis.Variational.SmoothWallGeometry
import HarmonicMaps.Analysis.VariableMollificationL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-! The exact local zero-wall Poincaré inequality in the physical epigraph coordinates. -/

public section

noncomputable section

open Filter HarmonicMaps MeasureTheory Metric Set
open scoped ContDiff ENNReal Topology

namespace Thesis

private theorem exists_uniform_epigraph_box_neighborhoods {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧ ∀ p ∈ frontier U,
      ∃ B : SmoothDomainEpigraphBox U, (B.lip : ℝ) ≤ L ∧ (B.inverseLip : ℝ) ≤ L ∧
        ‖B.chart.symm p‖ ≤ B.radius/4 ∧ L*δ < B.radius/4 ∧
        closedBall p δ ⊆ B.chart '' closedBall (0 : EpigraphCoordinates) B.radius := by
  classical
  let K := frontier U
  have hK : IsCompact K := hU.1.2.2.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  choose B hAt using fun x : K => hU.exists_epigraph_box x.property
  let U₁ (x : K) := (B x).chart '' ball (0 : EpigraphCoordinates) ((B x).radius/4)
  have hO (x : K) : IsOpen (U₁ x) := (B x).chart.isOpenMap _ isOpen_ball
  have hSub : K ⊆ ⋃ x : K, U₁ x := fun x hx =>
    mem_iUnion.2 ⟨⟨x,hx⟩,⟨0,mem_ball_self (div_pos (B ⟨x,hx⟩).radius_pos (by norm_num)),hAt ⟨x,hx⟩⟩⟩
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover U₁ hO hSub
  let L := 1 + (∑ i ∈ I, ((B i).lip : ℝ)) + (∑ i ∈ I, ((B i).inverseLip : ℝ))
  have hL : 0 < L := by dsimp only [L]; positivity
  have hB₁ (i : K) (hi : i ∈ I) : ((B i).lip : ℝ) ≤ L := by
    have h := Finset.single_le_sum (f := fun j : K => ((B j).lip : ℝ)) (fun j _ => (B j).lip.coe_nonneg) hi
    dsimp only [L]
    linarith only [h, Finset.sum_nonneg (fun j (_ : j ∈ I) => (B j).inverseLip.coe_nonneg)]
  have hB₂ (i : K) (hi : i ∈ I) : ((B i).inverseLip : ℝ) ≤ L := by
    have h := Finset.single_le_sum (f := fun j : K => ((B j).inverseLip : ℝ)) (fun j _ => (B j).inverseLip.coe_nonneg) hi
    dsimp only [L]
    linarith only [h, Finset.sum_nonneg (fun j (_ : j ∈ I) => (B j).lip.coe_nonneg)]
  let C (x : K) := (B x).chart '' closedBall (0 : EpigraphCoordinates) ((B x).radius/4)
  let O (x : K) := (B x).chart '' ball (0 : EpigraphCoordinates) ((B x).radius/2)
  have hCO (x : K) : C x ⊆ O x := image_mono (closedBall_subset_ball (by linarith only [(B x).radius_pos]))
  have hOC (x : K) : IsOpen (O x) := (B x).chart.isOpenMap _ isOpen_ball
  have hCC (x : K) : IsCompact (C x) := (isCompact_closedBall _ _).image (B x).chart.continuous
  choose ρ hρ hρC using fun x : K => (hCC x).exists_thickening_subset_open (hOC x) (hCO x)
  have hSmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ i ∈ I, s < min (ρ i) ((B i).radius/(4*L)) :=
    (eventually_all_finset I).2 fun i _ => nhdsWithin_le_nhds
      (Iio_mem_nhds (lt_min (hρ i) (div_pos (B i).radius_pos (by positivity))))
  have hPos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  obtain ⟨δ,hδ,hS⟩ := (hPos.and hSmall).exists
  refine ⟨δ,L,hδ,hL,?_⟩
  intro p hp
  obtain ⟨i,hi,hpB⟩ := mem_iUnion₂.1 (hI hp)
  obtain ⟨z,hz,hpz⟩ := hpB
  have hpC : p ∈ C i := ⟨z,ball_subset_closedBall hz,hpz⟩
  refine ⟨B i,hB₁ i hi,hB₂ i hi,?_,?_,?_⟩
  · rw [← hpz,(B i).chart.symm_apply_apply]
    exact (mem_ball_zero_iff.1 hz).le
  · have hD := (lt_min_iff.1 (hS i hi)).2
    have h := (lt_div_iff₀ (by positivity : 0 < 4*L)).1 hD
    nlinarith only [h]
  · intro x hx
    have hxC : x ∈ thickening (ρ i) (C i) :=
      mem_thickening_iff.2 ⟨p,hpC,(mem_closedBall.1 hx).trans_lt (lt_min_iff.1 (hS i hi)).1⟩
    exact image_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall
      (half_le_self (B i).radius_pos.le))) (hρC i hxC)

private theorem image_setIntegral_epigraph {U : Set Point} (B : SmoothDomainEpigraphBox U)
    (P : Set EpigraphCoordinates) (f : Point → ℝ) :
    (∫ x in B.chart '' P, f x) = ∫ t in P, f (B.chart t) := by
  have hEmb : MeasurableEmbedding (B.chart : EpigraphCoordinates → Point) :=
    B.chart.toMeasurableEquiv.measurableEmbedding
  rw [← B.chart_volume.map_eq, hEmb.setIntegral_map, B.chart.injective.preimage_image]

private theorem zero_line_integral_sq_le {U : Set Point} (hU : IsSmoothDomain U)
    {p : Point} {R : ℝ} {u : Point → ℝ}
    (hu : ContDiffOn ℝ 1 u (closure U ∩ ball p R))
    (hTrace : EqOn u (fun _ => 0) (frontier U ∩ ball p R))
    (B : SmoothDomainEpigraphBox U) (y : ℝ×ℝ) {T : ℝ} (hT : 0 < T)
    (hWall : B.chart (y,0) ∈ frontier U ∩ ball p R)
    (hTube : ∀ t ∈ Ioc 0 T, B.chart (y,t) ∈ U ∩ ball p R) :
    (∫ t in Ioc 0 T, ‖u (B.chart (y,t))‖^2) ≤
      T^2 * ∫ t in Ioc 0 T, ‖fderiv ℝ u (B.chart (y,t))‖^2 := by
  let K := closure U ∩ ball p R
  let γ (t : ℝ) := B.chart (y,t)
  let w := u ∘ γ
  let D (t : ℝ) := fderivWithin ℝ u K (γ t)
  let g (t : ℝ) := D t B.direction
  let J := Ioc (0 : ℝ) T
  let μ := (volume : Measure ℝ).restrict J
  have hγ : Continuous γ := B.chart.continuous.comp (continuous_const.prodMk continuous_id)
  have hMap : MapsTo γ (Icc 0 T) K := by
    intro t ht
    by_cases ht₀ : t=0
    · subst t
      exact ⟨frontier_subset_closure hWall.1,hWall.2⟩
    · have h := hTube t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht₀),ht.2⟩
      exact ⟨subset_closure h.1,h.2⟩
  have hK : UniqueDiffOn ℝ K := by
    intro x hx
    exact (uniqueDiffWithinAt_inter (isOpen_ball.mem_nhds hx.2)).2 (hU.uniqueDiffOn_closure x hx.1)
  have hWC : ContinuousOn w (Icc 0 T) := hu.continuousOn.comp hγ.continuousOn hMap
  have hDC : ContinuousOn D (Icc 0 T) := (hu.continuousOn_fderivWithin hK le_rfl).comp hγ.continuousOn hMap
  have hGC : ContinuousOn g (Icc 0 T) := hDC.clm_apply continuousOn_const
  have hw₀ : w 0 = 0 := hTrace hWall
  have hDerEq (t : ℝ) (ht : t ∈ J) : D t = fderiv ℝ u (γ t) := by
    exact fderivWithin_of_mem_nhds (mem_of_superset ((hU.1.1.inter isOpen_ball).mem_nhds (hTube t ht))
      (fun _ hx => ⟨subset_closure hx.1,hx.2⟩))
  have hDer (t : ℝ) (ht : t ∈ J) : HasDerivAt w (g t) t := by
    have hγD : HasDerivAt γ B.direction t := by
      rw [show γ = fun t => B.chart (y,0)+t • B.direction from funext (B.affineNormal y)]
      simpa only [id_eq, one_smul] using (((hasDerivAt_id t).smul_const B.direction).const_add (B.chart (y,0)))
    have hN : K ∈ 𝓝 (γ t) := mem_of_superset ((hU.1.1.inter isOpen_ball).mem_nhds (hTube t ht))
      (fun _ hx => ⟨subset_closure hx.1,hx.2⟩)
    have hU' := (hu.contDiffAt hN).differentiableAt one_ne_zero
    change HasDerivAt w (D t B.direction) t
    rw [hDerEq t ht]
    exact hU'.hasFDerivAt.comp_hasDerivAt t hγD
  have hWint : Integrable (fun t => ‖w t‖^2) μ :=
    (hWC.norm.pow 2).integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  have hGint : Integrable (fun t => ‖g t‖) μ :=
    hGC.norm.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  have hGSq : Integrable (fun t => ‖g t‖^2) μ :=
    (hGC.norm.pow 2).integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  have hGL : MemLp g 2 μ := (memLp_two_iff_integrable_sq_norm
    (hGC.aestronglyMeasurable measurableSet_Icc |>.mono_measure
      (Measure.restrict_mono_set volume Ioc_subset_Icc_self))).2 hGSq
  have hMass : μ.real univ = T := by
    rw [measureReal_def, show μ univ = volume J from Measure.restrict_apply_univ J,
      Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hT.le]
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hCS₂ : (∫ t, ‖g t‖ ∂μ) ^ 2 ≤ T * ∫ t, ‖g t‖^2 ∂μ := by
    have hc : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.2 (by norm_num)
    have h := integral_norm_mul_le_realLp_mul hc
      (show MemLp g (ENNReal.ofReal 2) μ from by simpa only [ENNReal.ofReal_ofNat] using hGL)
      (show MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ from memLp_const _)
    simp only [norm_one, mul_one, ENNReal.ofReal_ofNat] at h
    have hC₁ : (eLpNorm (fun _ : ℝ => (1 : ℝ)) 2 μ).toReal = Real.sqrt T := by
      rw [eLpNorm_const' _ (by norm_num) (by norm_num), ENNReal.toReal_mul,
        ← ENNReal.toReal_rpow, show ‖(1 : ℝ)‖ₑ = 1 by simp,
        ENNReal.toReal_one, one_mul, ENNReal.toReal_ofNat, ← Real.sqrt_eq_rpow]
      exact congrArg Real.sqrt hMass
    rw [hC₁] at h
    have h' := pow_le_pow_left₀ (integral_nonneg fun _ => norm_nonneg _) h 2
    rw [mul_pow,Real.sq_sqrt hT.le,← integral_norm_sq_eq_eLpNorm_two_toReal_sq hGL, mul_comm] at h'
    exact h'
  have hPoint (t : ℝ) (ht : t ∈ J) : ‖w t‖^2 ≤ T * ∫ s, ‖g s‖^2 ∂μ := by
    have ht₀ := ht.1
    have htT := ht.2
    have hCut : Icc (0:ℝ) t ⊆ Icc 0 T := fun _ h => ⟨h.1,h.2.trans htT⟩
    have hI : IntervalIntegrable g volume 0 t := ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le ht₀.le]
      exact hGC.mono hCut)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht₀.le
      (hWC.mono hCut) (fun a ha => hDer a ⟨ha.1,ha.2.le.trans htT⟩) hI
    rw [intervalIntegral.integral_of_le ht₀.le, hw₀, sub_zero] at hFTC
    have hAbs : ‖w t‖ ≤ ∫ a, ‖g a‖ ∂μ := by
      rw [← hFTC]
      exact (norm_integral_le_integral_norm _).trans
        (setIntegral_mono_set hGint (Eventually.of_forall fun _ => norm_nonneg _)
          (Eventually.of_forall (Ioc_subset_Ioc_right htT)))
    exact (pow_le_pow_left₀ (norm_nonneg _) hAbs 2).trans hCS₂
  have hSqEq : (∫ t, ‖g t‖^2 ∂μ) ≤ ∫ t, ‖fderiv ℝ u (γ t)‖^2 ∂μ := by
    have hI : Integrable (fun t => ‖D t‖^2) μ :=
      (hDC.norm.pow 2).integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
    have hEq : (fun t => ‖D t‖^2) =ᵐ[μ] fun t => ‖fderiv ℝ u (γ t)‖^2 :=
      (ae_restrict_mem measurableSet_Ioc).mono fun t ht => by
        change ‖D t‖^2 = ‖fderiv ℝ u (γ t)‖^2
        rw [hDerEq t ht]
    rw [← integral_congr_ae hEq]
    apply integral_mono hGSq hI
    intro t
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact ((D t).le_opNorm B.direction).trans_eq (by rw [B.direction_norm,mul_one])
  calc
    _ ≤ ∫ t, (T * ∫ s, ‖g s‖^2 ∂μ) ∂μ := by
      apply integral_mono_ae hWint (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hPoint t ht
    _ = T^2 * ∫ s, ‖g s‖^2 ∂μ := by
      rw [integral_const, hMass, smul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hSqEq (sq_nonneg T)

/-- A local zero-wall value on a physical boundary cap has its (L^2) norm
controlled by the original local gradient. The larger patch has a fixed
dilation factor depending only on the smooth domain. -/
theorem IsSmoothDomain.exists_local_zero_wall_poincare {U : Set Point} (hU : IsSmoothDomain U) :
    ∃ δ A C : ℝ, 0 < δ ∧ 1 < A ∧ 0 < C ∧ ∀ p ∈ frontier U, ∀ s ∈ Ioo 0 δ,
      ∀ u : Point → ℝ,
      ContDiffOn ℝ 1 u (closure U ∩ ball p (A*s)) →
      EqOn u (fun _ => 0) (frontier U ∩ ball p (A*s)) →
      MemLp (fderiv ℝ u) 2 (volume.restrict (U ∩ ball p (A*s))) →
      MemLp u 2 (volume.restrict (U ∩ ball p s)) ∧
        (eLpNorm u 2 (volume.restrict (U ∩ ball p s))).toReal ≤
          C * s * (eLpNorm (fderiv ℝ u) 2 (volume.restrict (U ∩ ball p (A*s)))).toReal := by
  obtain ⟨δ,L,hδ,hL,hBoxes⟩ := exists_uniform_epigraph_box_neighborhoods hU
  let A := L^2+1
  refine ⟨δ,A,L,hδ,by dsimp only [A]; nlinarith only [pow_pos hL 2], hL,?_⟩
  intro p hp s hs u hu huTrace huLp
  obtain ⟨B,hBL,hBI,hB0,hR,hBEnv⟩ := hBoxes p hp
  let z := B.chart.symm p
  let T := L*s
  let Q := ball z.1 T
  let J := Ioc (0:ℝ) T
  let P := Q ×ˢ J
  let S := U∩ball p s
  let E := U∩ball p (A*s)
  have hT : 0 < T := mul_pos hL hs.1
  have hTR : T < B.radius/4 := (mul_lt_mul_of_pos_left hs.2 hL).trans hR
  have hzR : z ∈ closedBall (0 : EpigraphCoordinates) B.radius :=
    mem_closedBall_zero_iff.2 (hB0.trans (by linarith only [B.radius_pos]))
  have hz₂ : z.2 = 0 := (B.frontier_iff z hzR).1 (B.chart.apply_symm_apply p ▸ hp)
  have hpE : p ∈ B.chart '' closedBall (0 : EpigraphCoordinates) B.radius :=
    ⟨z,hzR,B.chart.apply_symm_apply p⟩
  have hInc : S ⊆ B.chart '' P := by
    intro x hx
    have hxB : x ∈ B.chart '' closedBall (0 : EpigraphCoordinates) B.radius :=
      hBEnv (mem_closedBall.2 ((mem_ball.1 hx.2).le.trans hs.2.le))
    obtain ⟨w,hw,hwx⟩ := hxB
    have hwz : dist w z < T := by
      have h := B.chart_inverse_lipschitz.dist_le_mul x ⟨w,hw,hwx⟩ p hpE
      rw [← hwx, B.chart.symm_apply_apply] at h
      have h' : dist w z ≤ (B.inverseLip : ℝ) * dist x p := by rwa [hwx] at h
      exact (h'.trans (mul_le_mul_of_nonneg_right hBI dist_nonneg)).trans_lt
        (mul_lt_mul_of_pos_left (mem_ball.1 hx.2) hL)
    have hWall₀ : 0 < w.2 := (B.mem_domain w hw).1 (hwx ▸ hx.1)
    have hQ : w.1 ∈ Q := by
      apply mem_ball.2
      rw [Prod.dist_eq] at hwz
      exact (le_max_left _ _).trans_lt hwz
    have hJ : w.2 ∈ J := by
      rw [Prod.dist_eq, hz₂, Real.dist_eq, sub_zero, abs_of_nonneg hWall₀.le] at hwz
      exact ⟨hWall₀,((le_max_right _ _).trans_lt hwz).le⟩
    exact ⟨w,⟨hQ,hJ⟩,hwx⟩
  have hInR (y : ℝ×ℝ) (hy : y ∈ closedBall z.1 T) (t : ℝ) (ht : t ∈ Icc 0 T) :
      (y,t) ∈ closedBall (0 : EpigraphCoordinates) B.radius := by
    have hN : dist ((y,t) : EpigraphCoordinates) z ≤ T := by
      rw [Prod.dist_eq, hz₂, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact max_le (mem_closedBall.1 hy) ht.2
    apply mem_closedBall_zero_iff.2
    rw [← dist_zero_right]
    exact (dist_triangle _ z 0).trans (by
      rw [dist_zero_right]
      linarith only [hN,hB0,hTR,B.radius_pos])
  have hInBall (y : ℝ×ℝ) (hy : y ∈ closedBall z.1 T) (t : ℝ) (ht : t ∈ Icc 0 T) :
      B.chart (y,t) ∈ ball p (A*s) := by
    have hD := B.chart_lipschitz.dist_le_mul (y,t) (hInR y hy t ht) z hzR
    rw [B.chart.apply_symm_apply p] at hD
    have hN : dist ((y,t) : EpigraphCoordinates) z ≤ T := by
      rw [Prod.dist_eq, hz₂, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact max_le (mem_closedBall.1 hy) ht.2
    apply mem_ball.2
    have hD' := hD.trans (mul_le_mul hBL hN dist_nonneg hL.le)
    dsimp only [A,T]
    nlinarith only [hD',hs.1]
  have hWall (y : ℝ×ℝ) (hy : y ∈ Q) : B.chart (y,0) ∈ frontier U ∩ ball p (A*s) := by
    have hP := hInR y (ball_subset_closedBall hy) 0 ⟨le_rfl,hT.le⟩
    exact ⟨B.wall y ((norm_fst_le _).trans (mem_closedBall_zero_iff.1 hP)),
      hInBall y (ball_subset_closedBall hy) 0 ⟨le_rfl,hT.le⟩⟩
  have hTube (y : ℝ×ℝ) (hy : y ∈ Q) (t : ℝ) (ht : t ∈ J) : B.chart (y,t) ∈ E := by
    have ht' : t ∈ Icc 0 T := ⟨ht.1.le,ht.2⟩
    exact ⟨(B.mem_domain (y,t) (hInR y (ball_subset_closedBall hy) t ht')).2 ht.1,
      hInBall y (ball_subset_closedBall hy) t ht'⟩
  have hPSub : B.chart '' P ⊆ E := by
    rintro x ⟨⟨y,t⟩,⟨hy,ht⟩,rfl⟩
    exact hTube y hy t ht
  have hPmeas : MeasurableSet P := measurableSet_ball.prod measurableSet_Ioc
  have hPImage : MeasurableSet (B.chart '' P) := B.chart.toMeasurableEquiv.measurableSet_image.2 hPmeas
  have hPS : B.chart ⁻¹' (B.chart '' P) = P := B.chart.injective.preimage_image P
  have hMP : MeasurePreserving B.chart ((volume : Measure EpigraphCoordinates).restrict P)
      (volume.restrict (B.chart '' P)) := by
    simpa only [hPS] using B.chart_volume.restrict_preimage hPImage
  have hIG : IntegrableOn (fun x => ‖fderiv ℝ u x‖^2) E :=
    huLp.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hI₂ : IntegrableOn (fun x => ‖fderiv ℝ u x‖^2) (B.chart '' P) := hIG.mono_set hPSub
  have hG₂ : IntegrableOn (fun t => ‖fderiv ℝ u (B.chart t)‖^2) P :=
    hMP.integrable_comp_of_integrable hI₂
  let K := closure U ∩ ball p (A*s)
  let P₀ := closedBall z.1 T ×ˢ Icc (0 : ℝ) T
  have hP₀ : IsCompact P₀ := (isCompact_closedBall _ _).prod isCompact_Icc
  have hMap : MapsTo B.chart P₀ K := by
    rintro ⟨y,t⟩ ⟨hy,ht⟩
    have hD := hInR y hy t ht
    have hD' := hInBall y hy t ht
    refine ⟨?_,hD'⟩
    rcases lt_or_eq_of_le ht.1 with h | h
    · exact subset_closure ((B.mem_domain _ hD).2 h)
    · have hT₂ : t=0 := h.symm
      subst t
      exact frontier_subset_closure (B.wall y ((norm_fst_le _).trans (mem_closedBall_zero_iff.1 hD)))
  have hP₁ : P ⊆ P₀ := prod_mono ball_subset_closedBall Ioc_subset_Icc_self
  have hU₀ : IntegrableOn (fun t => ‖u (B.chart t)‖^2) P :=
    ((hu.continuousOn.comp B.chart.continuous.continuousOn hMap).norm.pow 2).integrableOn_compact hP₀ |>.mono_set hP₁
  have hU₂ : IntegrableOn (fun x => ‖u x‖^2) (B.chart '' P) :=
    (hMP.integrable_comp_emb B.chart.toMeasurableEquiv.measurableEmbedding).1 hU₀
  have hBnd : (∫ t in P, ‖u (B.chart t)‖^2) ≤ T^2 * ∫ t in P, ‖fderiv ℝ u (B.chart t)‖^2 := by
    change (∫ t in Q ×ˢ J, ‖u (B.chart t)‖^2 ∂((volume : Measure (ℝ×ℝ)).prod volume)) ≤
      T^2 * ∫ t in Q ×ˢ J, ‖fderiv ℝ u (B.chart t)‖^2 ∂((volume : Measure (ℝ×ℝ)).prod volume)
    rw [setIntegral_prod _ hU₀, setIntegral_prod _ hG₂, ← integral_const_mul]
    have hUP : Integrable (fun t : EpigraphCoordinates => ‖u (B.chart t)‖^2)
        ((volume.restrict Q).prod (volume.restrict J)) := by rw [Measure.prod_restrict]; exact hU₀
    have hGP : Integrable (fun t : EpigraphCoordinates => ‖fderiv ℝ u (B.chart t)‖^2)
        ((volume.restrict Q).prod (volume.restrict J)) := by rw [Measure.prod_restrict]; exact hG₂
    apply integral_mono_ae hUP.integral_prod_left (hGP.integral_prod_left.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact zero_line_integral_sq_le hU hu huTrace B y hT (hWall y hy) (hTube y hy)
  have hSK : S ⊆ K := fun x hx => by
    obtain ⟨t,ht,rfl⟩ := hInc hx
    exact hMap (hP₁ ht)
  have huM : MemLp u 2 (volume.restrict S) :=
    (memLp_two_iff_integrable_sq_norm ((hu.continuousOn.mono hSK).aestronglyMeasurable
      (hU.1.1.measurableSet.inter measurableSet_ball))).2 (hU₂.mono_set hInc)
  refine ⟨huM, ?_⟩
  apply le_of_sq_le_sq _ (mul_nonneg (mul_nonneg hL.le hs.1.le) ENNReal.toReal_nonneg)
  rw [mul_pow (L*s), ← integral_norm_sq_eq_eLpNorm_two_toReal_sq huM,
    ← integral_norm_sq_eq_eLpNorm_two_toReal_sq huLp]
  calc
    _ ≤ ∫ x in B.chart '' P, ‖u x‖^2 :=
      setIntegral_mono_set hU₂ (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hInc)
    _ = ∫ t in P, ‖u (B.chart t)‖^2 := image_setIntegral_epigraph B P _
    _ ≤ T^2 * ∫ t in P, ‖fderiv ℝ u (B.chart t)‖^2 := hBnd
    _ ≤ T^2 * ∫ x in E, ‖fderiv ℝ u x‖^2 := by
      rw [← image_setIntegral_epigraph B P (fun x => ‖fderiv ℝ u x‖^2)]
      exact mul_le_mul_of_nonneg_left
        (setIntegral_mono_set hIG
          (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hPSub)) (sq_nonneg T)

end Thesis

end
