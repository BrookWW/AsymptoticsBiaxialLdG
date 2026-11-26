module

public import Thesis.Variational.FractionalWallGradientMass
public import Thesis.Variational.HardyFromQuadraticCollar
public import Thesis.Variational.SmoothDomainEpigraphBoxes
public import Thesis.Variational.BoundaryRemainder

/-! The atlas estimates the fractional test on the actual distance collar. -/

public section

open Filter Function MeasureTheory Metric Set Topology
open scoped BigOperators ContDiff ENNReal Matrix Matrix.Norms.Frobenius NNReal

set_option autoImplicit false
noncomputable section

namespace Thesis

local instance dirichletFractionalHardyContinuousENorm : ContinuousENorm S0 :=
  SeminormedAddGroup.toContinuousENorm

private theorem norm_h10Value_integral_le_testNorm
    {U : Set Point} (hU : IsBoundedDomain U) (v : H10 U) (s : ℝ)
    (hFin : dirichletFractionalTestEnergy s U v < ⊤) :
    (∫ x in U, ‖h10Value v x‖) ≤
      Real.sqrt (volume.real U) * dirichletFractionalTestNorm s U v := by
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.2.2.measure_lt_top.ne
  let g (x : Point) := ‖h10Value v x‖
  have hg : MemLp g 2 μ := (Lp.memLp v.val.1).norm
  let E := dirichletFractionalTestEnergy s U v
  have hI : ENNReal.ofReal (∫ x, (g x)^2 ∂μ) ≤ E := by
    rw [ofReal_integral_eq_lintegral_ofReal hg.integrable_sq (.of_forall fun _ => sq_nonneg _)]
    exact self_le_add_right _ _
  have hEq := ENNReal.toReal_mono hFin.ne hI
  rw [ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)] at hEq
  have hC := square_integral_le_measure_mul_integral_square hg
  have hB := Real.le_sqrt_of_sq_le (hC.trans (mul_le_mul_of_nonneg_left hEq measureReal_nonneg))
  rw [Real.sqrt_mul measureReal_nonneg,show μ.real univ=volume.real U by simp [μ,Measure.real]] at hB
  exact hB

private theorem epigraph_box_h10_slab_mass
    {U : Set Point} (hU : IsBoundedDomain U) (B : SmoothDomainEpigraphBox U)
    {s : ℝ} (hs : s < 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : H10 U), dirichletFractionalTestEnergy s U v < ⊤ →
      ∀ t : ℝ, 0 < t → t ≤ B.radius →
        (∫ x in B.chart '' wallChartSlab B.radius t, ‖h10Value v x‖ ∂volume.restrict U) ≤
          C*t^2*dirichletFractionalTestNorm s U v := by
  let b := B.radius
  let K : ℝ≥0 := B.lip+1
  have hK : 0 < (K:ℝ) := by dsimp only [K]; positivity
  have hLip : LipschitzOnWith K B.chart (wallChartClosedBox b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    exact (B.chart_lipschitz.dist_le_mul p (epigraphCoordinates_mem_closedBall_iff.2 hp)
        q (epigraphCoordinates_mem_closedBall_iff.2 hq)).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [K]; norm_num) dist_nonneg)
  have hIn : B.chart '' wallChartSlab b b ⊆ U := by
    rintro x ⟨p,hp,rfl⟩
    have hBox := wallChartSlab_subset_box B.radius_pos le_rfl hp
    exact (B.mem_domain p (epigraphCoordinates_mem_closedBall_iff.2 hBox)).2 hp.2.1
  have hWall (y : ℝ×ℝ) (hy : y ∈ wallChartHorizontal b) : B.chart (y,0) ∈ frontier U := by
    have hBox : ((y,0) : WallChartPoint) ∈ wallChartClosedBox b :=
      ⟨⟨⟨hy.1.1.le,hy.1.2⟩,⟨hy.2.1.le,hy.2.2⟩⟩,⟨neg_nonpos.mpr B.radius_pos.le,B.radius_pos.le⟩⟩
    have hN := mem_closedBall_zero_iff.mp (epigraphCoordinates_mem_closedBall_iff.2 hBox)
    exact B.wall y ((norm_fst_le ((y,0):WallChartPoint)).trans hN)
  exact exists_wallChartSlab_h10Value_mass_le hU B.radius_pos hs B.chart B.chart_volume hIn hK hLip
    B.direction B.direction_norm B.affineNormal hWall

private theorem setIntegral_le_sum_of_nonnegative_cover
    {X ι : Type*} [MeasurableSpace X] (μ : Measure X) (g : X → ℝ) (hg : Integrable g μ)
    (hg₀ : ∀ x, 0 ≤ g x) (S : Set X) (I : Finset ι) (V : ι → Set X)
    (hCover : S ⊆ ⋃ i ∈ I, V i) :
    (∫ x in S, g x ∂μ) ≤ ∑ i ∈ I, ∫ x in V i, g x ∂μ := by
  classical
  have hCover' : S ⊆ ⋃ i : ↥I, V i := by
    intro x hx
    obtain ⟨i,hi,hxV⟩ := mem_iUnion₂.mp (hCover hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hxV⟩
  have h₀ (T : Set X) : 0 ≤ ∫ x in T, g x ∂μ := integral_nonneg hg₀
  apply (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ => h₀ (V i))).1
  rw [ofReal_integral_eq_lintegral_ofReal hg.integrableOn (.of_forall hg₀),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => h₀ (V i))]
  calc
    _ ≤ ∫⁻ x in ⋃ i : ↥I, V i, ENNReal.ofReal (g x) ∂μ := lintegral_mono_set hCover'
    _ ≤ ∑' i : ↥I, ∫⁻ x in V i, ENNReal.ofReal (g x) ∂μ := lintegral_iUnion_le _ _
    _ = _ := by
      simp_rw [tsum_fintype,← ofReal_integral_eq_lintegral_ofReal hg.integrableOn (.of_forall hg₀)]
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach I (fun i => ENNReal.ofReal (∫ x in V i, g x ∂μ)))

private theorem wallChartHorizontal_mem_of_ball
    {b : ℝ} {p : WallChartPoint} (hp : p ∈ ball (0 : WallChartPoint) b) :
    p.1 ∈ wallChartHorizontal b := by
  have hn := mem_ball_zero_iff.mp hp
  simp only [Prod.norm_def,max_lt_iff,Real.norm_eq_abs,abs_lt] at hn
  exact ⟨⟨hn.1.1.1,hn.1.1.2.le⟩,⟨hn.1.2.1,hn.1.2.2.le⟩⟩

/-- The original distance collar and the actual zero-trace value have
quadratic mass in the unchanged fractional test norm. -/
theorem exists_dirichlet_quadratic_collar_mass_bound
    {U : Set Point} (hU : IsSmoothDomain U) {s : ℝ} (hs : s < 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : H10 U), dirichletFractionalTestEnergy s U v < ⊤ →
      ∀ t : ℝ, 0 < t →
        (∫ x in {x | infDist x (frontier U) < t}, ‖h10Value v x‖ ∂volume.restrict U) ≤
          C*t^2*dirichletFractionalTestNorm s U v := by
  classical
  obtain ⟨B,I,δ,hδ,hAtlas⟩ := hU.exists_finite_epigraph_boxes
  have hBoxes (i : frontier U) := epigraph_box_h10_slab_mass hU.1 (B i) hs
  choose C hC hChart using hBoxes
  let L := Real.sqrt (volume.real U)
  let A := ∑ i ∈ I, C i/(B i).distanceFactor^2
  let M := A+L/δ^2
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => div_nonneg (hC i) (sq_nonneg _)
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hM : 0 ≤ M := add_nonneg hA (div_nonneg hL (sq_nonneg _))
  refine ⟨M,hM,?_⟩
  intro v hFin t ht
  let N := dirichletFractionalTestNorm s U v
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  let G (x : Point) := ‖h10Value v x‖
  let F := {x : Point | infDist x (frontier U) < t}
  have hG : Integrable G μ := ((Lp.memLp v.val.1).integrable (by norm_num)).norm
  have hG₀ (x : Point) : 0 ≤ G x := norm_nonneg _
  have hF : MeasurableSet F := measurableSet_lt (continuous_infDist_pt (frontier U)).measurable measurable_const
  change (∫ x in F, G x ∂μ) ≤ M*t^2*N
  by_cases hsmall : t ≤ δ
  · let q (i : frontier U) := min (B i).radius (t/(B i).distanceFactor)
    let J (i : frontier U) := (B i).chart '' wallChartSlab (B i).radius (q i)
    have hq (i : frontier U) : 0 < q i :=
      lt_min (B i).radius_pos (div_pos ht (B i).distanceFactor_pos)
    have hqR (i : frontier U) : q i ≤ (B i).radius := min_le_left _ _
    have hCover : U ∩ F ⊆ ⋃ i ∈ I, J i := by
      intro x hx
      have hd : infDist x (frontier U) < t := hx.2
      obtain ⟨i,hi,p,hp,hpT,hpx⟩ := hAtlas x hx.1 (hd.trans_le hsmall)
      have hClosed := ball_subset_closedBall hp
      have hD := (B i).distance_ge p hClosed hpT
      rw [hpx] at hD
      have hAbs : p.2 ≤ ‖p.2‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
      have hb : p.2 ≤ (B i).radius := hAbs.trans ((norm_snd_le p).trans (mem_closedBall_zero_iff.mp hClosed))
      have hpT' : p.2 ≤ t/(B i).distanceFactor :=
        (le_div_iff₀ (B i).distanceFactor_pos).2 (by rw [mul_comm]; exact hD.trans hd.le)
      exact mem_iUnion₂.mpr ⟨i,hi,p,⟨wallChartHorizontal_mem_of_ball hp,hpT,le_min hb hpT'⟩,hpx⟩
    have hInt : (∫ x in F,G x ∂μ) = ∫ x in U ∩ F,G x ∂μ := by
      have hM' : μ.restrict F = μ.restrict (U ∩ F) := by
        dsimp only [μ]
        rw [Measure.restrict_restrict hF, Measure.restrict_restrict (hU.1.1.measurableSet.inter hF)]
        congr 1
        ext x
        simp only [mem_inter_iff]
        tauto
      rw [hM']
    rw [hInt]
    calc
      _ ≤ ∑ i ∈ I, ∫ x in J i,G x ∂μ :=
        setIntegral_le_sum_of_nonnegative_cover μ G hG hG₀ _ I J hCover
      _ ≤ ∑ i ∈ I, C i/(B i).distanceFactor^2*t^2*N := by
        apply Finset.sum_le_sum
        intro i _
        have hh := hChart i v hFin (q i) (hq i) (hqR i)
        have hqT : q i ≤ t/(B i).distanceFactor := min_le_right _ _
        refine hh.trans ?_
        calc
          _ ≤ C i*(t/(B i).distanceFactor)^2*N :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hq i).le hqT 2) (hC i)) hN
          _ = _ := by rw [div_pow]; ring
      _ = A*t^2*N := by dsimp only [A]; rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (div_nonneg hL (sq_nonneg _))) (sq_nonneg t)) hN
  · have htδ : δ ≤ t := le_of_lt (lt_of_not_ge hsmall)
    have hFull : (∫ x,G x ∂μ) ≤ L*N := norm_h10Value_integral_le_testNorm hU.1 v s hFin
    calc
      _ ≤ ∫ x,G x ∂μ := integral_mono_measure Measure.restrict_le_self (.of_forall hG₀) hG
      _ ≤ L*N := hFull
      _ = (L/δ^2)*δ^2*N := by rw [div_mul_cancel₀ _ (pow_ne_zero _ hδ.ne')]
      _ ≤ (L/δ^2)*t^2*N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ.le htδ 2)
          (div_nonneg hL (sq_nonneg _))) hN
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (sq_nonneg t)) hN

/-- The native fractional Dirichlet Hardy and collar inequalities use the
original graph, boundary distance and volume. -/
theorem dirichletFractionalHardyAndCollar : External.DirichletFractionalHardyAndCollar := by
  intro U hU s _ hs
  obtain ⟨D,hD,hBound⟩ := exists_dirichlet_quadratic_collar_mass_bound hU hs
  let L := Real.sqrt (volume.real U)
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  let C := max D (L+4*D)
  have hC : 0 ≤ C := hD.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro v hFin
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.1.2.2.measure_lt_top.ne
  let d (x : Point) := infDist x (frontier U)
  let g (x : Point) := ‖h10Value v x‖
  let N := dirichletFractionalTestNorm s U v
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hg : Integrable g μ := ((Lp.memLp v.val.1).integrable (by norm_num)).norm
  have hg₀ (x : Point) : 0 ≤ g x := norm_nonneg _
  have hdf : Measurable d := (continuous_infDist_pt (frontier U)).measurable
  have hd : ∀ᵐ x ∂μ, 0 < d x :=
    (ae_restrict_mem hU.1.1.measurableSet).mono fun _ hx => infDist_frontier_pos_of_mem_domain hU.1 hx
  have hLayer (t : ℝ) (ht : 0 < t) : (∫ x in {x | d x < t}, g x ∂μ) ≤ (D*N)*t^2 :=
    (hBound v hFin t ht).trans_eq (by ring)
  obtain ⟨hHard, hI⟩ := inverseDistance_integrable_and_integral_le_of_quadratic_collar
    μ d g hdf hd hg hg₀ (D*N) (mul_nonneg hD hN) hLayer
  refine ⟨⟨hHard,?_⟩,?_⟩
  · exact hI.trans ((add_le_add (norm_h10Value_integral_le_testNorm hU.1 v s hFin) le_rfl).trans
      ((show L*N+4*(D*N)=(L+4*D)*N by ring).le.trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hN)))
  · intro t ht
    have hF : MeasurableSet {x | d x < t} := measurableSet_lt hdf measurable_const
    change (∫ x in U ∩ {x | d x < t}, g x) ≤ C*t^2*N
    rw [inter_comm U, ← Measure.restrict_restrict hF]
    exact (hBound v hFin t ht).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg t)) hN)

end Thesis

end
