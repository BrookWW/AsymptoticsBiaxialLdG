module

public import Thesis.MeasureGeometry.CylinderCoordinates
public import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Compactness.Lindelof

/-! Euclidean Hausdorff area of a (C^1) graph over the transverse plane. -/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal NNReal RealInnerProductSpace

namespace Thesis

open MeasureGeometry

/-- The volume-preserving placement of transverse and vertical coordinates. -/
def planeLinePlacement : (Plane × ℝ) ≃L[ℝ] Point :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ Plane ℝ).symm.trans
    planeLineEuclideanIsometry.toContinuousLinearEquiv

theorem planeLinePlacement_volume :
    MeasurePreserving planeLinePlacement (volume : Measure (Plane × ℝ)) volume :=
  planeLineEuclideanIsometry.measurePreserving.comp (WithLp.volume_preserving_toLp Plane ℝ)

/-- The literal graph of a height function in the three ambient coordinates. -/
def wallGraph (g : Plane → ℝ) (y : Plane) : Point :=
  planeLinePlacement (y, g y)

/-- The graph of a linear height derivative. -/
def wallGraphLinear (G : Plane →L[ℝ] ℝ) : Plane →L[ℝ] Point :=
  planeLinePlacement.toContinuousLinearMap.comp ((ContinuousLinearMap.id ℝ Plane).prod G)

/-- Euclidean surface area per unit horizontal area. -/
def wallGraphAreaDensity (g : Plane → ℝ) (y : Plane) : ℝ :=
  Real.sqrt (1 + ((fderiv ℝ g y) (EuclideanSpace.single 0 1)) ^ 2 +
    ((fderiv ℝ g y) (EuclideanSpace.single 1 1)) ^ 2)

theorem planeLinePlacement_coordinate (y : Plane) (t : ℝ) :
    planeLinePlacement (y,t) 0 = y 0 ∧
    planeLinePlacement (y,t) 1 = y 1 ∧ planeLinePlacement (y,t) 2 = t := by
  simp [planeLinePlacement, planeLineEuclideanIsometry, planeLinePack]

private theorem planeLinePlacement_norm_sq (y : Plane) (z : ℝ) :
    ‖planeLinePlacement (y,z)‖ ^ 2 = ‖y‖ ^ 2 + z ^ 2 := by
  have h := planeLinePlacement_coordinate y z
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, h.1, h.2.1, h.2.2,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

private theorem wallGraphLinear_norm_ge (G : Plane →L[ℝ] ℝ) (v : Plane) :
    ‖v‖ ≤ ‖wallGraphLinear G v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  change ‖v‖ ^ 2 ≤ ‖planeLinePlacement (v, G v)‖ ^ 2
  rw [planeLinePlacement_norm_sq]
  exact le_add_of_nonneg_right (sq_nonneg _)

private theorem wallGraphLinear_normDet (G : Plane →L[ℝ] ℝ) :
    (wallGraphLinear G).toLinearMap.normDet =
      Real.sqrt (1 + (G (EuclideanSpace.single 0 1)) ^ 2 + (G (EuclideanSpace.single 1 1)) ^ 2) := by
  let L := wallGraphLinear G
  let u := G (EuclideanSpace.single 0 1)
  let v := G (EuclideanSpace.single 1 1)
  let B := EuclideanSpace.basisFun (Fin 2) ℝ
  have hB (i : Fin 2) : B i = EuclideanSpace.single i (1 : ℝ) := EuclideanSpace.basisFun_apply (Fin 2) ℝ i
  have hC (y : Plane) : L y 0 = y 0 ∧ L y 1 = y 1 ∧ L y 2 = G y :=
    planeLinePlacement_coordinate y (G y)
  have hGram : Matrix.gram ℝ (fun i : Fin 2 => L (B i)) =
      !![1 + u ^ 2, u * v; u * v, 1 + v ^ 2] := by
    ext i j
    simp_rw [Matrix.gram_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three,
      star_trivial, hC, hB]
    fin_cases i <;> fin_cases j <;> simp [u,v,pow_two,mul_comm]
  have hDet := L.toLinearMap.normDet_sq_eq_det_gram B
  change L.toLinearMap.normDet ^ 2 = (Matrix.gram ℝ (fun i : Fin 2 => L (B i))).det at hDet
  rw [hGram, Matrix.det_fin_two] at hDet
  have hP : 0 ≤ 1 + u^2 + v^2 := by positivity
  apply (sq_eq_sq₀ L.toLinearMap.normDet_nonneg (Real.sqrt_nonneg _)).1
  rw [Real.sq_sqrt hP, hDet]
  change (1 + u ^ 2) * (1 + v ^ 2) - (u * v) * (u * v) = 1 + u ^ 2 + v ^ 2
  ring

theorem wallGraph_areaDensity_pos (g : Plane → ℝ) (y : Plane) : 0 < wallGraphAreaDensity g y := by
  unfold wallGraphAreaDensity
  positivity

private theorem wallGraph_areaDensity_continuousOn {V : Set Plane} (hV : IsOpen V)
    {g : Plane → ℝ} (hg : ContDiffOn ℝ 1 g V) : ContinuousOn (wallGraphAreaDensity g) V := by
  have hf := hg.continuousOn_fderiv_of_isOpen hV le_rfl
  unfold wallGraphAreaDensity
  exact ((continuousOn_const.add (((ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.single 0 1)).continuous.comp_continuousOn hf).pow 2)).add
      (((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single 1 1)).continuous.comp_continuousOn hf).pow 2)).sqrt

private theorem hasFDerivAt_wallGraph {g : Plane → ℝ} {y : Plane} (hy : DifferentiableAt ℝ g y) :
    HasFDerivAt (wallGraph g) (wallGraphLinear (fderiv ℝ g y)) y :=
  planeLinePlacement.toContinuousLinearMap.hasFDerivAt.comp y ((hasFDerivAt_id y).prodMk hy.hasFDerivAt)

private theorem wallGraph_injective (g : Plane → ℝ) : Injective (wallGraph g) := by
  intro x y h
  exact congrArg Prod.fst (planeLinePlacement.injective h)

/-- Measurable pieces of a continuous graph are measurable in the ambient space. -/
theorem wallGraph_image_measurable {V S : Set Plane} (hV : IsOpen V)
    (hS : MeasurableSet S) (hSV : S ⊆ V) {g : Plane → ℝ} (hg : ContinuousOn g V) :
    MeasurableSet (wallGraph g '' S) := by
  let Γ (x : V) := wallGraph g x
  have hG : ContinuousOn (wallGraph g) V :=
    planeLinePlacement.continuous.comp_continuousOn (continuousOn_id.prodMk hg)
  letI : PolishSpace V := hV.polishSpace
  have hMe := (continuousOn_iff_continuous_restrict.mp hG).measurableEmbedding
    (f := Γ) ((wallGraph_injective g).comp Subtype.val_injective)
  have hImage : Γ '' (Subtype.val ⁻¹' S : Set V) = wallGraph g '' S := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.val,hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨⟨z,hSV hz⟩,hz,rfl⟩
  rw [← hImage]
  exact hMe.measurableSet_image.2 (hS.preimage measurable_subtype_coe)

private theorem surface_measure_image_le {f : Point → Point} {S : Set Point} {L : ℝ≥0}
    (h : LipschitzOnWith L f S) :
    Measure.euclideanHausdorffMeasure 2 (f '' S) ≤
      (L : ℝ≥0∞) ^ (2 : ℕ) * Measure.euclideanHausdorffMeasure 2 S := by
  have h' := h.hausdorffMeasure_image_le (d := (2 : ℝ)) (by norm_num)
  simp only [ENNReal.rpow_two] at h'
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply,
    Measure.nnreal_smul_coe_apply, Measure.nnreal_smul_coe_apply, mul_left_comm ((L : ℝ≥0∞) ^ 2)]
  exact mul_le_mul_right h' _

private theorem surface_measure_image_compare (F G : Plane → Point) (S : Set Plane) (hG : InjOn G S)
    {K : ℝ} (hK : 0 ≤ K)
    (hDist : ∀ x ∈ S, ∀ y ∈ S, dist (F x) (F y) ≤ K * dist (G x) (G y)) :
    Measure.euclideanHausdorffMeasure 2 (F '' S) ≤
      ENNReal.ofReal K ^ (2 : ℕ) * Measure.euclideanHausdorffMeasure 2 (G '' S) := by
  classical
  let I := F ∘ invFunOn G S
  have hApply (x : Plane) (hx : x ∈ S) : I (G x) = F x :=
    congrArg F (hG.leftInvOn_invFunOn hx)
  have hI : LipschitzOnWith ⟨K,hK⟩ I (G '' S) := LipschitzOnWith.of_dist_le_mul (by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    rw [hApply x hx, hApply y hy]
    exact hDist x hx y hy)
  have hImage : I '' (G '' S) = F '' S := by
    ext z
    constructor
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨x,hx,(hApply x hx).symm⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨G x,⟨x,hx,rfl⟩,hApply x hx⟩
  rw [← hImage, ENNReal.ofReal_eq_coe_nnreal hK]
  with_unfolding_all exact surface_measure_image_le hI

private theorem wallGraph_local_comparison {V : Set Plane} (hV : IsOpen V)
    {g : Plane → ℝ} (hg : ContDiffOn ℝ 1 g V) {η : ℝ} (hη : 0 < η)
    {x : Plane} (hx : x ∈ V) :
    ∃ r > 0, ball x r ⊆ V ∧
      (∀ y ∈ ball x r, (1 - η) * wallGraphAreaDensity g x ≤ wallGraphAreaDensity g y ∧
        wallGraphAreaDensity g y ≤ (1 + η) * wallGraphAreaDensity g x) ∧
      ∀ y ∈ ball x r, ∀ z ∈ ball x r,
        let L := wallGraphLinear (fderiv ℝ g x)
        (1 - η) * dist (L y) (L z) ≤ dist (wallGraph g y) (wallGraph g z) ∧
          dist (wallGraph g y) (wallGraph g z) ≤ (1 + η) * dist (L y) (L z) := by
  let Γ := wallGraph g
  let J := wallGraphAreaDensity g
  let A := fun y => wallGraphLinear (fderiv ℝ g y)
  let L := A x
  have hΓ : ContDiffOn ℝ 1 Γ V := planeLinePlacement.contDiff.comp_contDiffOn (contDiffOn_id.prodMk hg)
  have hD (y : Plane) (hy : y ∈ V) : HasFDerivAt Γ (A y) y :=
    hasFDerivAt_wallGraph ((hg.differentiableOn one_ne_zero y hy).differentiableAt (hV.mem_nhds hy))
  have hContA : ContinuousAt A x := by
    have hEq : A =ᶠ[𝓝 x] fderiv ℝ Γ :=
      Filter.mem_of_superset (hV.mem_nhds hx) (fun y hy => (hD y hy).fderiv.symm)
    exact (((hΓ.continuousOn_fderiv_of_isOpen hV le_rfl) x hx).continuousAt (hV.mem_nhds hx)).congr hEq.symm
  have hContJ := ((wallGraph_areaDensity_continuousOn hV hg) x hx).continuousAt (hV.mem_nhds hx)
  have hBall₁ : ∀ᶠ y in 𝓝 x, ‖A y - L‖ < η := by
    apply ((hContA.sub continuousAt_const).norm.eventually_lt continuousAt_const)
    simpa only [Pi.sub_apply, L, A, sub_self, norm_zero] using hη
  have hBall₂ : ∀ᶠ y in 𝓝 x, |J y - J x| < η * J x := by
    apply ((hContJ.sub continuousAt_const).abs.eventually_lt continuousAt_const)
    simpa only [Pi.sub_apply, sub_self, abs_zero] using mul_pos hη (wallGraph_areaDensity_pos g x)
  have hIn : ∀ᶠ y in 𝓝 x, y ∈ V := hV.mem_nhds hx
  obtain ⟨r,hr,hR⟩ := Metric.mem_nhds_iff.mp (hIn.and (hBall₁.and hBall₂))
  have hSub : ball x r ⊆ V := fun _ hy => (hR hy).1
  refine ⟨r,hr,hSub,?_,?_⟩
  · intro y hy
    have h := abs_lt.mp (hR hy).2.2
    change (1 - η) * J x ≤ J y ∧ J y ≤ (1 + η) * J x
    constructor <;> nlinarith only [h.1,h.2]
  · intro y hy z hz
    let R (u : Plane) := Γ u - L u
    have hDR (u : Plane) (hu : u ∈ ball x r) : HasFDerivAt R (A u - L) u :=
      (hD u (hSub hu)).sub L.hasFDerivAt
    have hFR : ‖R y - R z‖ ≤ η * ‖y-z‖ :=
      (convex_ball x r).norm_image_sub_le_of_norm_fderiv_le
        (fun u hu => (hDR u hu).differentiableAt)
        (fun u hu => (hDR u hu).fderiv ▸ (hR hu).2.1.le) hz hy
    have hFR' : ‖R y - R z‖ ≤ η * ‖L y - L z‖ := hFR.trans
      (mul_le_mul_of_nonneg_left (by rw [← map_sub]; exact wallGraphLinear_norm_ge _ _) hη.le)
    have hEq : Γ y - Γ z = (L y - L z) + (R y - R z) := by dsimp only [R]; abel
    have hEq' : L y - L z = (Γ y - Γ z) - (R y - R z) := by dsimp only [R]; abel
    have hHi : ‖Γ y - Γ z‖ ≤ ‖L y - L z‖ + ‖R y - R z‖ := hEq ▸ norm_add_le _ _
    have hLo : ‖L y - L z‖ ≤ ‖Γ y - Γ z‖ + ‖R y - R z‖ := hEq' ▸ norm_sub_le _ _
    simp only [dist_eq_norm]
    change (1 - η) * ‖L y - L z‖ ≤ ‖Γ y - Γ z‖ ∧
      ‖Γ y - Γ z‖ ≤ (1 + η) * ‖L y - L z‖
    constructor <;> nlinarith only [hHi,hLo,hFR']

private theorem le_of_surfaceMeasure_approximations {A B : ℝ≥0∞}
    (h : ∀ δ : ℝ, 0 < δ → A ≤ ENNReal.ofReal (1+δ)*B) : A ≤ B := by
  by_cases hB : B = ⊤
  · rw [hB]; exact le_top
  let δ (n : ℕ) := (1:ℝ)/((n:ℝ)+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp only [δ]; positivity
  have hLim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hOne : Tendsto (fun n => ENNReal.ofReal (1+δ n)) atTop (𝓝 1) := by
    simpa only [add_zero, ENNReal.ofReal_one] using ENNReal.tendsto_ofReal (hLim.const_add 1)
  have hM : Tendsto (fun n => ENNReal.ofReal (1+δ n)*B) atTop (𝓝 B) := by
    simpa only [Function.comp_def, one_mul] using
      (ENNReal.continuous_mul_const hB).continuousAt.tendsto.comp hOne
  exact le_of_tendsto_of_tendsto' (f := fun _ : ℕ => A) tendsto_const_nhds hM
    (fun n => h (δ n) (hδ n))

private theorem wallGraph_area_comparison {V S : Set Plane} (hV : IsOpen V)
    {g : Plane → ℝ} (hg : ContDiffOn ℝ 1 g V) (hS : MeasurableSet S) (hSV : S ⊆ V)
    {δ : ℝ} (hδ : 0 < δ) :
    Measure.euclideanHausdorffMeasure 2 (wallGraph g '' S) ≤
      ENNReal.ofReal (1 + δ) * (∫⁻ x in S, ENNReal.ofReal (wallGraphAreaDensity g x)) ∧
    (∫⁻ x in S, ENNReal.ofReal (wallGraphAreaDensity g x)) ≤
      ENNReal.ofReal (1 + δ) * Measure.euclideanHausdorffMeasure 2 (wallGraph g '' S) := by
  classical
  rcases V.eq_empty_or_nonempty with rfl | hV₀
  · have h : S = ∅ := subset_empty_iff.mp hSV
    simp [h]
  letI : Nonempty ↥V := hV₀.to_subtype
  let η := min (δ / 16) (1 / 4)
  have hη : 0 < η := lt_min (div_pos hδ (by norm_num)) (by norm_num)
  let lo := 1 - η
  let hi := 1 + η
  have hlo : 0 < lo := sub_pos.mpr ((min_le_right _ _).trans_lt (by norm_num))
  have hh₁ : 1 ≤ hi := le_add_of_nonneg_right hη.le
  have hlo₁ : lo ≤ 1 := sub_le_self _ hη.le
  have hhi : 0 ≤ hi := zero_le_one.trans hh₁
  have hFact : hi ^ 2 ≤ (1 + δ) * lo ^ 2 := by
    have h1 : η ≤ 1 / 4 := min_le_right _ _
    have h2 : 1 / 2 ≤ lo ^ 2 := by
      dsimp only [lo]
      nlinarith only [h1,sq_nonneg η]
    have hδbound := mul_le_mul_of_nonneg_left h2 hδ.le
    have hηbound : η ≤ δ / 16 := min_le_left _ _
    dsimp only [lo,hi] at hδbound ⊢
    nlinarith only [hδ.le,hηbound,hδbound]
  have hFactor₁ : hi ^ 2 * lo⁻¹ ≤ 1 + δ := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hlo).2
    exact hFact.trans (mul_le_mul_of_nonneg_left
      (by rw [pow_two]; exact mul_le_of_le_one_right hlo.le hlo₁) (by linarith))
  have hFactor₂ : hi * (lo⁻¹) ^ 2 ≤ 1 + δ := by
    rw [inv_pow, ← div_eq_mul_inv]
    apply (div_le_iff₀ (pow_pos hlo _)).2
    exact (by rw [pow_two]; exact le_mul_of_one_le_right hhi hh₁ : hi ≤ hi ^ 2).trans hFact
  have hLoc (x : V) := wallGraph_local_comparison hV hg hη x.property
  choose r hr hBall hJ hL using hLoc
  let W (x : V) := ball (x : Plane) (r x)
  have hCover : V ⊆ ⋃ x : V, W x := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (hr _)⟩
  obtain ⟨σ,hσ⟩ := (HereditarilyLindelofSpace.isLindelof V).indexed_countable_subcover
    W (fun _ => isOpen_ball) hCover
  let W' (i : ℕ) := W (σ i)
  let E (i : ℕ) := disjointed W' i ∩ S
  have hEW (i : ℕ) : E i ⊆ W (σ i) := inter_subset_left.trans (disjointed_subset _ _)
  have hE (i : ℕ) : MeasurableSet (E i) :=
    (MeasurableSet.disjointed (fun _ => measurableSet_ball) i).inter hS
  have hEV (i : ℕ) : E i ⊆ V := (hEW i).trans (hBall (σ i))
  have hPair : Pairwise (Disjoint on E) :=
    pairwise_disjoint_mono (disjoint_disjointed W') (fun _ => inter_subset_left)
  have hUnion : (⋃ i, E i) = S := by
    change (⋃ i, disjointed W' i ∩ S) = S
    rw [← iUnion_inter, iUnion_disjointed, inter_eq_right.mpr (hSV.trans hσ)]
  let Γ := wallGraph g
  let J := wallGraphAreaDensity g
  let I (F : Set Plane) := ∫⁻ x in F, ENNReal.ofReal (J x)
  let H (F : Set Plane) := Measure.euclideanHausdorffMeasure 2 (Γ '' F)
  let C := ENNReal.ofReal (1 + δ)
  have hArea (i : ℕ) :
      H (E i) ≤ C * I (E i) ∧ I (E i) ≤ C * H (E i) := by
    let x := σ i
    let L := wallGraphLinear (fderiv ℝ g x)
    let M := ENNReal.ofReal (J x) * volume (E i)
    have hLin : Measure.euclideanHausdorffMeasure 2 (L '' E i) = M := by
      have h := L.toLinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume (E i)
      simpa only [finrank_euclideanSpace_fin, L, wallGraphLinear_normDet, M, J, wallGraphAreaDensity] using! h
    have hLI : Injective L := by
      refine (injective_iff_map_eq_zero L).2 fun y hy => ?_
      have h := wallGraphLinear_norm_ge (fderiv ℝ g x) y
      exact norm_eq_zero.mp (le_antisymm (by simpa only [show wallGraphLinear (fderiv ℝ g x) y = 0 from hy, norm_zero] using h)
        (norm_nonneg _))
    have hHi : H (E i) ≤ ENNReal.ofReal hi ^ (2 : ℕ) * M := by
      rw [← hLin]
      exact surface_measure_image_compare Γ L (E i) hLI.injOn hhi
        (fun y hy z hz => (hL x y (hEW i hy) z (hEW i hz)).2)
    have hLo : M ≤ ENNReal.ofReal lo⁻¹ ^ (2 : ℕ) * H (E i) := by
      rw [← hLin]
      apply surface_measure_image_compare L Γ (E i) (wallGraph_injective g).injOn (inv_nonneg.mpr hlo.le)
      intro y hy z hz
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hlo).2
        (by simpa only [mul_comm] using (hL x y (hEW i hy) z (hEW i hz)).1)
    have hIlo : ENNReal.ofReal lo * M ≤ I (E i) := by
      dsimp only [M, I]
      rw [← mul_assoc, ← ENNReal.ofReal_mul hlo.le, ← setLIntegral_const]
      exact setLIntegral_mono' (hE i) fun y hy => ENNReal.ofReal_le_ofReal (hJ x y (hEW i hy)).1
    have hIhi : I (E i) ≤ ENNReal.ofReal hi * M := by
      dsimp only [M, I]
      rw [← mul_assoc, ← ENNReal.ofReal_mul hhi, ← setLIntegral_const]
      exact setLIntegral_mono' (hE i) fun y hy => ENNReal.ofReal_le_ofReal (hJ x y (hEW i hy)).2
    have hM : M ≤ ENNReal.ofReal lo⁻¹ * I (E i) := by
      calc
        _ = ENNReal.ofReal lo⁻¹ * (ENNReal.ofReal lo * M) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hlo.le), inv_mul_cancel₀ hlo.ne',
            ENNReal.ofReal_one, one_mul]
        _ ≤ _ := mul_le_mul_right hIlo _
    have hQ₁ : ENNReal.ofReal hi ^ (2 : ℕ) * ENNReal.ofReal lo⁻¹ ≤ C := by
      rw [← ENNReal.ofReal_pow hhi, ← ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hFactor₁
    have hQ₂ : ENNReal.ofReal hi * ENNReal.ofReal lo⁻¹ ^ (2 : ℕ) ≤ C := by
      rw [← ENNReal.ofReal_pow (inv_nonneg.mpr hlo.le), ← ENNReal.ofReal_mul hhi]
      exact ENNReal.ofReal_le_ofReal hFactor₂
    exact ⟨hHi.trans ((mul_le_mul_right hM _).trans
      (by rw [← mul_assoc]; exact mul_le_mul_left hQ₁ _)),
      hIhi.trans ((mul_le_mul_right hLo _).trans
        (by rw [← mul_assoc]; exact mul_le_mul_left hQ₂ _))⟩
  have hImPair : Pairwise (Disjoint on fun i => Γ '' E i) := by
    intro i j hij
    rw [Function.onFun,Set.disjoint_left]
    rintro _ ⟨y,hyi,rfl⟩ ⟨z,hzj,hyz⟩
    exact Set.disjoint_left.mp (hPair hij) hyi (((wallGraph_injective g) hyz) ▸ hzj)
  have hH : H S = ∑' i, H (E i) := by
    dsimp only [H]
    rw [← hUnion, image_iUnion, measure_iUnion hImPair
      (fun i => wallGraph_image_measurable hV (hE i) (hEV i) hg.continuousOn)]
  have hI : I S = ∑' i, I (E i) := by
    dsimp only [I]
    rw [← hUnion, lintegral_iUnion hE hPair]
  change H S ≤ C * I S ∧ I S ≤ C * H S
  rw [hH,hI,← ENNReal.tsum_mul_left,← ENNReal.tsum_mul_left]
  exact ⟨ENNReal.tsum_le_tsum fun i => (hArea i).1, ENNReal.tsum_le_tsum fun i => (hArea i).2⟩

/-- Exact normalized geometric surface measure of a measurable piece of a
(C^1) wall, expressed using its horizontal coordinates. -/
theorem euclideanHausdorffMeasure_wallGraph {V S : Set Plane} (hV : IsOpen V)
    {g : Plane → ℝ} (hg : ContDiffOn ℝ 1 g V) (hS : MeasurableSet S) (hSV : S ⊆ V) :
    Measure.euclideanHausdorffMeasure 2 (wallGraph g '' S) =
      ∫⁻ x in S, ENNReal.ofReal (wallGraphAreaDensity g x) := by
  exact le_antisymm
    (le_of_surfaceMeasure_approximations fun _ hδ => (wallGraph_area_comparison hV hg hS hSV hδ).1)
    (le_of_surfaceMeasure_approximations fun _ hδ => (wallGraph_area_comparison hV hg hS hSV hδ).2)

private theorem map_weighted_measure_wallGraph {V : Set Plane} (hV : IsOpen V)
    {g : Plane → ℝ} (hg : ContDiffOn ℝ 1 g V) (hgm : Measurable g) :
    Measure.map (wallGraph g) ((volume.restrict V).withDensity
      (fun y => ENNReal.ofReal (wallGraphAreaDensity g y))) =
        (Measure.euclideanHausdorffMeasure 2).restrict (wallGraph g '' V) := by
  have hΓ : Measurable (wallGraph g) := planeLinePlacement.continuous.measurable.comp (measurable_id.prodMk hgm)
  ext S hS
  have hT := hS.preimage hΓ
  rw [Measure.map_apply hΓ hS, withDensity_apply _ hT, Measure.restrict_apply hS]
  change (∫⁻ y, ENNReal.ofReal (wallGraphAreaDensity g y) ∂(volume.restrict V).restrict (wallGraph g ⁻¹' S)) = _
  rw [Measure.restrict_restrict hT, ← euclideanHausdorffMeasure_wallGraph hV hg (hT.inter hV.measurableSet)
    inter_subset_right, image_preimage_inter]

/-- Integrating the actual wall trace multiplies horizontal volume by the
usual graph area density. -/
theorem integral_wallGraph {V : Set Plane} (hV : IsOpen V)
    {g : Plane → ℝ} (hg : ContDiffOn ℝ 1 g V) (hgm : Measurable g)
    {f : Point → ℝ} (hf : AEStronglyMeasurable f
      ((Measure.euclideanHausdorffMeasure 2).restrict (wallGraph g '' V))) :
    (∫ x in wallGraph g '' V, f x ∂(Measure.euclideanHausdorffMeasure 2)) =
      ∫ y in V, wallGraphAreaDensity g y * f (wallGraph g y) := by
  have hΓ : Measurable (wallGraph g) := planeLinePlacement.continuous.measurable.comp (measurable_id.prodMk hgm)
  have hρ : Measurable (fun y => ENNReal.ofReal (wallGraphAreaDensity g y)) := by
    apply ENNReal.continuous_ofReal.measurable.comp
    unfold wallGraphAreaDensity
    exact (measurable_const.add ((measurable_fderiv_apply_const ℝ g _).pow_const 2) |>.add
      ((measurable_fderiv_apply_const ℝ g _).pow_const 2)).sqrt
  rw [← map_weighted_measure_wallGraph hV hg hgm, integral_map hΓ.aemeasurable
    (map_weighted_measure_wallGraph hV hg hgm ▸ hf),
    integral_withDensity_eq_integral_toReal_smul hρ (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (wallGraph_areaDensity_pos g _).le, smul_eq_mul]

end Thesis
