module

public import Thesis.Variational.FlatWallLpTransport
public import Thesis.Variational.ChartPoissonCoefficients
public import Thesis.Variational.ClosedConvexNormalRecovery

/-! Closed regularity transported through the actual smooth wall charts. -/

public section

noncomputable section

open Filter Function Metric Set Topology
open scoped ContDiff

namespace Thesis

namespace RegularWallGraphPatch

variable {U : Set Point}
variable (P : RegularWallGraphPatch U)

theorem flatPositiveBox_preimage (P : RegularWallGraphPatch U) :
    P.flatPositiveBox = planeLinePlacement.symm ⁻¹' (P.base ×ˢ Ioo 0 P.halfHeight) := by
  ext z
  let y := planeLinePlacement.symm z
  have hY : y.2 = z 2 := congrArg Prod.snd (planeLinePlacement_symm_eq_horizontal_height z)
  change ((y.1 ∈ P.base ∧ y.2 ∈ Ioo (-P.halfHeight) P.halfHeight) ∧ 0 < z 2) ↔
      y.1 ∈ P.base ∧ y.2 ∈ Ioo 0 P.halfHeight
  rw [← hY]
  constructor
  · rintro ⟨⟨h₁,h₂⟩,h₃⟩
    exact ⟨h₁,h₃,h₂.2⟩
  · rintro ⟨h₁,h₂,h₃⟩
    exact ⟨⟨h₁,(neg_lt_zero.mpr P.halfHeight_pos).trans h₂,h₃⟩,h₂⟩

theorem flatPositiveBox_convex : Convex ℝ P.flatPositiveBox := by
  rw [P.flatPositiveBox_preimage]
  exact ((convex_ball (0 : Plane) P.baseRadius).prod (convex_Ioo 0 P.halfHeight)).linear_preimage
    planeLinePlacement.symm.toContinuousLinearMap.toLinearMap

theorem flatPositiveBox_nonempty : P.flatPositiveBox.Nonempty := by
  rw [P.flatPositiveBox_preimage]
  refine ⟨planeLinePlacement (0,P.halfHeight/2),?_⟩
  change planeLinePlacement.symm (planeLinePlacement (0,P.halfHeight/2)) ∈
    P.base ×ˢ Ioo 0 P.halfHeight
  rw [planeLinePlacement.symm_apply_apply]
  exact ⟨mem_ball_self P.baseRadius_pos,half_pos P.halfHeight_pos,half_lt_self P.halfHeight_pos⟩

theorem flatChart_mapsTo_closure_domain : MapsTo P.flatChart (closure P.flatPositiveBox) (closure U) :=
  closure_minimal (fun _ hx => subset_closure ((P.flatChart_mem_domain hx.1).2 hx.2))
    (isClosed_closure.preimage P.flatChart.continuous)

theorem flatChart_symm_mapsTo_closure_flatPositiveBox :
    MapsTo P.flatChart.symm (closure U ∩ P.neighborhood) (closure P.flatPositiveBox) := by
  intro x hx
  have hp : P.flatChart.symm x ∈ closure (P.flatChart ⁻¹' U) := by
    rw [← P.flatChart.preimage_closure]
    change P.flatChart (P.flatChart.symm x) ∈ closure U
    rw [P.flatChart.apply_symm_apply]
    exact hx.1
  have hn : P.flatChart.symm x ∈ P.flatBox := by
    rw [← P.flatChart_image_flatBox] at hx
    obtain ⟨z,hz,he⟩ := hx.2
    rw [← he,P.flatChart.symm_apply_apply]
    exact hz
  have hEq : P.flatPositiveBox = P.flatChart ⁻¹' U ∩ P.flatBox := by
    rw [← P.preimage_domain_neighborhood,preimage_inter,← P.flatChart_image_flatBox,
      preimage_image_eq _ P.flatChart.injective]
  rw [hEq]
  exact P.flatBox_isOpen.closure_inter ⟨hp,hn⟩

/-- Regularity on the closed flat side gives the corresponding local regularity
on the closed physical domain at the center of the wall chart. -/
theorem contDiffWithinAt_of_flatPositiveBox_closure
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ∞ω} (hP : ContDiff ℝ k P.height) {u : Point → F}
    (h0 : P.center ∈ closure U)
    (hu : ContDiffOn ℝ k (u ∘ P.flatChart) (closure P.flatPositiveBox)) :
    ContDiffWithinAt ℝ k u (closure U) P.center := by
  have hLoc := hu.comp (P.flatChart_symm_contDiff hP).contDiffOn
    P.flatChart_symm_mapsTo_closure_flatPositiveBox
  have hEq : (u ∘ P.flatChart) ∘ P.flatChart.symm = u :=
    funext fun x => congrArg u (P.flatChart.apply_symm_apply x)
  rw [hEq] at hLoc
  exact (contDiffWithinAt_inter (P.isOpen_neighborhood.mem_nhds P.center_mem_neighborhood)).1
    (hLoc _ ⟨h0,P.center_mem_neighborhood⟩)

theorem flatChart_zero : P.flatChart 0 = P.center := by
  rw [P.flatChart_apply]
  simp [P.height_zero]

/-- A smaller flat cap still gives the original within-domain regularity
at the center of the physical chart. -/
theorem contDiffWithinAt_of_flat_wall_cap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ∞ω} (hP : ContDiff ℝ k P.height) {u : Point → F}
    (h0 : P.center ∈ closure U) {V : Set Point}
    (hV : IsOpen V) (hV0 : (0 : Point) ∈ V) (hSub : V ⊆ P.flatBox)
    (hu : ContDiffOn ℝ k (u ∘ P.flatChart) (closure (positiveWallHalf ∩ V))) :
    ContDiffWithinAt ℝ k u (closure U) P.center := by
  let E := P.flatChart
  let A := E '' V
  have hA : IsOpen A := E.isOpenMap _ hV
  have hCenter : P.center ∈ A := ⟨0,hV0,P.flatChart_zero⟩
  have hEq : positiveWallHalf ∩ V = E ⁻¹' U ∩ V := by
    ext z
    constructor
    · rintro ⟨hz,hzV⟩
      exact ⟨(P.flatChart_mem_domain (hSub hzV)).2 hz,hzV⟩
    · rintro ⟨hz,hzV⟩
      exact ⟨(P.flatChart_mem_domain (hSub hzV)).1 hz,hzV⟩
  have hInto : MapsTo E.symm (closure U ∩ A) (closure (positiveWallHalf ∩ V)) := by
    intro x hx
    have hxU : E.symm x ∈ closure (E ⁻¹' U) := by
      rw [← E.preimage_closure]
      change E (E.symm x) ∈ closure U
      rw [E.apply_symm_apply]
      exact hx.1
    have hxV : E.symm x ∈ V := by
      obtain ⟨z,hz,he⟩ := hx.2
      rwa [← he,E.symm_apply_apply]
    rw [hEq]
    exact hV.closure_inter ⟨hxU,hxV⟩
  have hLoc := hu.comp (P.flatChart_symm_contDiff hP).contDiffOn hInto
  have he : (u ∘ E) ∘ E.symm = u := funext fun x => congrArg u (E.apply_symm_apply x)
  rw [he] at hLoc
  exact (contDiffWithinAt_inter (hA.mem_nhds hCenter)).1 (hLoc _ ⟨h0,hCenter⟩)

/-- The actual flattened Poisson equation recovers the pure normal second
derivatives from higher tangential regularity on the closed wall patch. -/
theorem contDiffOn_closure_of_flat_cap_tangential_regular
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hP : ContDiff ℝ ∞ P.height) (hU : IsOpen U)
    {S : Set Point} (hS : IsOpen S) (hConv : Convex ℝ S) (hNe : S.Nonempty)
    (hSub : S ⊆ P.flatPositiveBox) (k : ℕ)
    {u f : Point → F} (hu : ContDiffOn ℝ (↑(k+1) : ℕ∞ω) u (closure U))
    (huI : ContDiffOn ℝ 2 u U) (hf : ContDiffOn ℝ (k : ℕ∞ω) f (closure U))
    (hEq : EqOn (laplacian u) f U)
    (T : Fin 3 → Point → F)
    (hT : ∀ j ≠ 2, ContDiffOn ℝ (↑(k+1) : ℕ∞ω) (T j) (closure S) ∧
      EqOn (T j) (coordDeriv j (u ∘ P.flatChart)) S) :
    ContDiffOn ℝ (↑(k+2) : ℕ∞ω) (u ∘ P.flatChart) (closure S) := by
  let E := P.flatChart
  have hE : ContDiff ℝ ∞ (E : Point → Point) := P.flatChart_contDiff hP
  have hI : ContDiff ℝ ∞ (E.symm : Point → Point) := P.flatChart_symm_contDiff hP
  have hMap : MapsTo E S U :=
    fun _ hz => (P.flatChart_mem_domain (hSub hz).1).2 (hSub hz).2
  have hMapCl : MapsTo E (closure S) (closure U) :=
    fun _ hz => P.flatChart_mapsTo_closure_domain (closure_mono hSub hz)
  have hTwo : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hK (j : ℕ) : (j : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hC := hu.comp (hE.of_le (hK (k+1))).contDiffOn hMapCl
  have hCI := huI.comp (hE.of_le hTwo).contDiffOn hMap
  have hF := hf.comp (hE.of_le (hK k)).contDiffOn hMapCl
  have hA (i j : Fin 3) : ContDiffOn ℝ (k : ℕ∞ω) (chartPoissonPrincipal E i j)
      (closure S) :=
    (chartPoissonPrincipal_contDiff E k (hE.of_le (hK (k+2))) (hI.of_le (hK (k+2))) i j).contDiffOn
  have hB (i : Fin 3) : ContDiffOn ℝ (k : ℕ∞ω) (chartPoissonDrift E i) (closure S) :=
    (chartPoissonDrift_contDiff E k (hE.of_le (hK (k+2))) (hI.of_le (hK (k+2))) i).contDiffOn
  refine contDiffOn_of_tangential_regular_nondivergence hS hConv hNe k hC hCI T hT _ _ hA hB hF ?_ ?_
  · intro z _
    exact (chartPoissonPrincipal_diagonal_pos E (hE.differentiable (by simp)) (hI.differentiable (by simp)) 2 z).ne'
  · intro z hz
    have hAt : ContDiffAt ℝ 2 u (E z) := (huI _ (hMap hz)).contDiffAt (hU.mem_nhds (hMap hz))
    exact (laplacian_flattened_eq_chartPoisson E (hE.of_le hTwo) (hI.of_le hTwo) hAt).symm.trans
      (hEq (hMap hz))

theorem contDiffOn_flatPositiveBox_closure_of_tangential_regular
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hP : ContDiff ℝ ∞ P.height) (hU : IsOpen U) (k : ℕ)
    {u f : Point → F} (hu : ContDiffOn ℝ (↑(k+1) : ℕ∞ω) u (closure U))
    (huI : ContDiffOn ℝ 2 u U) (hf : ContDiffOn ℝ (k : ℕ∞ω) f (closure U))
    (hEq : EqOn (laplacian u) f U)
    (T : Fin 3 → Point → F)
    (hT : ∀ j ≠ 2, ContDiffOn ℝ (↑(k+1) : ℕ∞ω) (T j) (closure P.flatPositiveBox) ∧
      EqOn (T j) (coordDeriv j (u ∘ P.flatChart)) P.flatPositiveBox) :
    ContDiffOn ℝ (↑(k+2) : ℕ∞ω) (u ∘ P.flatChart) (closure P.flatPositiveBox) :=
  P.contDiffOn_closure_of_flat_cap_tangential_regular hP hU P.flatPositiveBox_isOpen
    P.flatPositiveBox_convex P.flatPositiveBox_nonempty Subset.rfl k hu huI hf hEq T hT

end RegularWallGraphPatch

/-- Interior smoothness and true local chart regularity at every wall point
give regularity of the original function on the whole closure. -/
theorem IsSmoothDomain.contDiffOn_closure_of_regular_wall_charts
    {U : Set Point} (hU : IsSmoothDomain U)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ∞ω} {u : Point → F} (hu : ContDiffOn ℝ k u U)
    (hWall : ∀ a ∈ frontier U, ∃ P : RegularWallGraphPatch U, P.center = a ∧ ContDiff ℝ k P.height ∧
      ContDiffOn ℝ k (u ∘ P.flatChart) (closure P.flatPositiveBox)) :
    ContDiffOn ℝ k u (closure U) := by
  intro a ha
  by_cases hMem : a ∈ U
  · exact ((hu a hMem).contDiffAt (hU.1.1.mem_nhds hMem)).contDiffWithinAt
  · have hf : a ∈ frontier U := by
      rw [frontier,hU.1.1.interior_eq]
      exact ⟨ha,hMem⟩
    obtain ⟨P,hP,hS,hBox⟩ := hWall a hf
    rw [← hP] at ha ⊢
    exact P.contDiffWithinAt_of_flatPositiveBox_closure hS ha hBox

end Thesis
