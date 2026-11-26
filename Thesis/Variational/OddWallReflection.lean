module

public import Thesis.Variational.FlatWallCoordinates
public import Thesis.Variational.MorreyDomainCharts
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! Odd reflection of a zero-trace classical field and its actual derivatives. -/

@[expose] public section

noncomputable section

open Filter Function Metric Set Topology
open scoped ContDiff NNReal

namespace Thesis

def negativeWallHalf : Set Point := {z | z 2 < 0}

def lowerClosedWallHalf : Set Point := {z | z 2 ≤ 0}

def flatWall : Set Point := {z | z 2 = 0}

theorem normalReflection_height (x : Point) : normalReflection x 2 = -(x 2) := rfl

theorem normalReflection_wall (x : Point) (hx : x ∈ flatWall) : normalReflection x = x := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [normalReflection,show x 2 = 0 from hx]

theorem normalReflection_involutive : Involutive normalReflection := by
  intro x
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [normalReflection]

theorem closedWallHalf_isClosed : IsClosed closedWallHalf :=
  isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 2).continuous

private theorem lowerClosedWallHalf_isClosed : IsClosed lowerClosedWallHalf :=
  isClosed_le (EuclideanSpace.proj (𝕜 := ℝ) 2).continuous continuous_const

private theorem convex_closedWallHalf : Convex ℝ closedWallHalf :=
  convex_halfSpace_ge (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).toLinearMap.isLinear 0

private theorem convex_lowerClosedWallHalf : Convex ℝ lowerClosedWallHalf :=
  convex_halfSpace_le (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).toLinearMap.isLinear 0

private theorem closedWallHalf_interior_nonempty : (interior closedWallHalf).Nonempty := by
  refine ⟨axis 2,mem_interior_iff_mem_nhds.mpr ?_⟩
  apply mem_of_superset (isOpen_positiveWallHalf.mem_nhds ?_)
  · exact fun y hy => (show 0 < y 2 from hy).le
  · change 0 < (axis 2) 2
    simp [axis]

theorem closedWallHalf_uniqueDiffOn : UniqueDiffOn ℝ closedWallHalf :=
  uniqueDiffOn_convex convex_closedWallHalf closedWallHalf_interior_nonempty

theorem isOpen_negativeWallHalf : IsOpen negativeWallHalf :=
  isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) 2).continuous continuous_const

private theorem lowerClosedWallHalf_interior_nonempty : (interior lowerClosedWallHalf).Nonempty := by
  refine ⟨-(axis 2),mem_interior_iff_mem_nhds.mpr ?_⟩
  apply mem_of_superset (isOpen_negativeWallHalf.mem_nhds ?_)
  · exact fun y hy => (show y 2 < 0 from hy).le
  · change (-(axis 2)) 2 < 0
    simp [axis]

private theorem normalReflection_mapsTo_closed :
    MapsTo normalReflection lowerClosedWallHalf closedWallHalf := by
  intro x hx
  change 0 ≤ normalReflection x 2
  rw [normalReflection_height]
  exact neg_nonneg.mpr hx

private theorem hasDerivAt_tangential_line (x v : Point) :
    HasDerivAt (fun t : ℝ => x+t•v) v 0 := by
  simpa only [id_eq,one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x

private theorem fderivWithin_wall_tangential_zero
    {f : Point → ℝ} (hf : ContDiffOn ℝ 1 f closedWallHalf) (h0 : EqOn f 0 flatWall)
    {x v : Point} (hx : x ∈ flatWall) (hv : v ∈ flatWall) :
    fderivWithin ℝ f closedWallHalf x v = 0 := by
  let γ (t : ℝ) := x+t•v
  have hγ0 : γ 0 = x := by simp [γ]
  have hγ (t : ℝ) : γ t ∈ flatWall := by
    change (x+t•v) 2 = 0
    have hⱼ : (x+t•v) 2 = x 2 + t*v 2 := rfl
    rw [hⱼ,show x 2 = 0 from hx,show v 2 = 0 from hv]
    ring
  have hxH : x ∈ closedWallHalf := (show x 2 = 0 from hx).ge
  have hDF := ((hf.differentiableOn one_ne_zero) x hxH).hasFDerivWithinAt
  have hDF' : HasFDerivWithinAt f (fderivWithin ℝ f closedWallHalf x) closedWallHalf (γ 0) :=
    hγ0.symm ▸ hDF
  have hh := hDF'.comp_hasDerivAt 0 (hasDerivAt_tangential_line x v)
    (Eventually.of_forall fun t => (show (γ t) 2 = 0 from hγ t).ge)
  have hEq : f ∘ γ = fun _ : ℝ => 0 := funext fun t => h0 (hγ t)
  rw [hEq] at hh
  exact hh.unique (hasDerivAt_const 0 0)

private theorem fderivWithin_odd_match_on_wall {f : Point → ℝ}
    (hf : ContDiffOn ℝ 1 f closedWallHalf) (h0 : EqOn f 0 flatWall)
    {x : Point} (hx : x ∈ flatWall) :
    -((fderivWithin ℝ f closedWallHalf x).comp normalReflection.toContinuousLinearMap) =
      fderivWithin ℝ f closedWallHalf x := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : v + normalReflection v ∈ flatWall := by
    change v 2 + normalReflection v 2 = 0
    rw [normalReflection_height,add_neg_cancel]
  have hh := fderivWithin_wall_tangential_zero hf h0 hx hv
  rw [map_add] at hh
  change -(fderivWithin ℝ f closedWallHalf x (normalReflection v)) =
    fderivWithin ℝ f closedWallHalf x v
  linarith only [hh]

/-- Odd extension of the positive-side field across the flat wall. -/
def oddWallReflection (f : Point → ℝ) (x : Point) : ℝ :=
  if 0 ≤ x 2 then f x else -(f (normalReflection x))

theorem oddWallReflection_eqOn_closed {f : Point → ℝ} :
    EqOn (oddWallReflection f) f closedWallHalf := by
  intro x hx
  exact if_pos hx

theorem oddWallReflection_eqOn_lower {f : Point → ℝ} (h0 : EqOn f 0 flatWall) :
    EqOn (oddWallReflection f) (fun x => -(f (normalReflection x))) lowerClosedWallHalf := by
  intro x hx
  by_cases h : x ∈ closedWallHalf
  · have hx0 : x ∈ flatWall := le_antisymm hx h
    change oddWallReflection f x = -f (normalReflection x)
    rw [oddWallReflection,if_pos (show 0 ≤ x 2 from h),normalReflection_wall x hx0,show f x = 0 from h0 hx0,neg_zero]
  · exact if_neg (show ¬ 0 ≤ x 2 from h)

private theorem hasFDerivWithinAt_odd_closed {f : Point → ℝ}
    (hf : ContDiffOn ℝ 1 f closedWallHalf) {x : Point} (hx : x ∈ closedWallHalf) :
    HasFDerivWithinAt (oddWallReflection f) (fderivWithin ℝ f closedWallHalf x) closedWallHalf x :=
  ((hf.differentiableOn one_ne_zero x hx).hasFDerivWithinAt).congr
    (fun _ hy => oddWallReflection_eqOn_closed hy) (oddWallReflection_eqOn_closed hx)

private theorem hasFDerivWithinAt_odd_lower {f : Point → ℝ}
    (hf : ContDiffOn ℝ 1 f closedWallHalf) (h0 : EqOn f 0 flatWall)
    {x : Point} (hx : x ∈ lowerClosedWallHalf) :
    HasFDerivWithinAt (oddWallReflection f)
      (-((fderivWithin ℝ f closedWallHalf (normalReflection x)).comp normalReflection.toContinuousLinearMap))
      lowerClosedWallHalf x := by
  have hRx := normalReflection_mapsTo_closed hx
  have hDF := ((hf.differentiableOn one_ne_zero (normalReflection x) hRx).hasFDerivWithinAt).comp x
    normalReflection.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt normalReflection_mapsTo_closed
  exact hDF.neg.congr (fun y hy => oddWallReflection_eqOn_lower h0 hy) (oddWallReflection_eqOn_lower h0 hx)

private theorem hasFDerivAt_odd_on_wall {f : Point → ℝ}
    (hf : ContDiffOn ℝ 1 f closedWallHalf) (h0 : EqOn f 0 flatWall) {x : Point} (hx : x ∈ flatWall) :
    HasFDerivAt (oddWallReflection f) (fderivWithin ℝ f closedWallHalf x) x := by
  have hH : x ∈ closedWallHalf := (show x 2 = 0 from hx).ge
  have hL : x ∈ lowerClosedWallHalf := (show x 2 = 0 from hx).le
  have hA := hasFDerivWithinAt_odd_closed hf hH
  have hB := hasFDerivWithinAt_odd_lower hf h0 hL
  rw [normalReflection_wall x hx,fderivWithin_odd_match_on_wall hf h0 hx] at hB
  have hu : closedWallHalf ∪ lowerClosedWallHalf = univ := by
    ext y
    change (0 ≤ y 2 ∨ y 2 ≤ 0) ↔ True
    exact ⟨fun _ => trivial,fun _ => le_total _ _⟩
  exact hasFDerivWithinAt_univ.mp (hu ▸ hA.union hB)

theorem oddWallReflection_differentiable {f : Point → ℝ}
    (hf : ContDiffOn ℝ 1 f closedWallHalf) (h0 : EqOn f 0 flatWall) :
    Differentiable ℝ (oddWallReflection f) := by
  intro x
  rcases lt_trichotomy 0 (x 2) with hx|hx|hx
  · have h := hasFDerivWithinAt_odd_closed hf (show x ∈ closedWallHalf from hx.le)
    exact (h.hasFDerivAt (mem_of_superset (isOpen_positiveWallHalf.mem_nhds hx) fun y h => (show 0 < y 2 from h).le)).differentiableAt
  · exact (hasFDerivAt_odd_on_wall hf h0 hx.symm).differentiableAt
  · have h := hasFDerivWithinAt_odd_lower hf h0 (show x ∈ lowerClosedWallHalf from hx.le)
    exact (h.hasFDerivAt (mem_of_superset (isOpen_negativeWallHalf.mem_nhds hx) fun y h => (show y 2 < 0 from h).le)).differentiableAt

theorem fderiv_oddWallReflection_eqOn_closed {f : Point → ℝ}
    (hf : ContDiffOn ℝ 1 f closedWallHalf) (h0 : EqOn f 0 flatWall) :
    EqOn (fderiv ℝ (oddWallReflection f)) (fderivWithin ℝ f closedWallHalf) closedWallHalf := by
  intro x hx
  rcases (show 0 ≤ x 2 from hx).eq_or_lt with hh|hh
  · exact (hasFDerivAt_odd_on_wall hf h0 hh.symm).fderiv
  · exact ((hasFDerivWithinAt_odd_closed hf hx).hasFDerivAt
      (mem_of_superset (isOpen_positiveWallHalf.mem_nhds hh) fun y h => (show 0 < y 2 from h).le)).fderiv

theorem fderiv_oddWallReflection_eqOn_lower {f : Point → ℝ}
    (hf : ContDiffOn ℝ 1 f closedWallHalf) (h0 : EqOn f 0 flatWall) :
    EqOn (fderiv ℝ (oddWallReflection f)) (fun x =>
      -((fderivWithin ℝ f closedWallHalf (normalReflection x)).comp normalReflection.toContinuousLinearMap))
      lowerClosedWallHalf := by
  intro x hx
  rcases (show x 2 ≤ 0 from hx).eq_or_lt with hh|hh
  · have h := (hasFDerivAt_odd_on_wall hf h0 hh).fderiv
    change fderiv ℝ (oddWallReflection f) x =
      -((fderivWithin ℝ f closedWallHalf (normalReflection x)).comp normalReflection.toContinuousLinearMap)
    rwa [normalReflection_wall x hh, fderivWithin_odd_match_on_wall hf h0 hh]
  · exact ((hasFDerivWithinAt_odd_lower hf h0 hx).hasFDerivAt
      (mem_of_superset (isOpen_negativeWallHalf.mem_nhds hh) fun y h => (show y 2 < 0 from h).le)).fderiv

theorem oddWallReflection_contDiffAt_two_off_wall {f : Point → ℝ}
    (hf : ContDiffOn ℝ 2 f closedWallHalf) (h0 : EqOn f 0 flatWall) {x : Point}
    (hx : x ∉ flatWall) : ContDiffAt ℝ 2 (oddWallReflection f) x := by
  rcases lt_or_gt_of_ne (show x 2 ≠ 0 from hx) with hNeg|hPos
  · have hr : 0 < normalReflection x 2 := by rw [normalReflection_height]; exact neg_pos.mpr hNeg
    have hR : closedWallHalf ∈ 𝓝 (normalReflection x) :=
      mem_of_superset (isOpen_positiveWallHalf.mem_nhds hr) fun y h => (show 0 < y 2 from h).le
    have hC := ((hf _ hr.le).contDiffAt hR).comp x normalReflection.contDiff.contDiffAt
    exact hC.neg.congr_of_eventuallyEq (mem_of_superset (isOpen_negativeWallHalf.mem_nhds hNeg)
      fun y hy => oddWallReflection_eqOn_lower h0 (show y ∈ lowerClosedWallHalf from (show y 2 < 0 from hy).le))
  · have hH : closedWallHalf ∈ 𝓝 x :=
      mem_of_superset (isOpen_positiveWallHalf.mem_nhds hPos) fun y h => (show 0 < y 2 from h).le
    exact ((hf _ hPos.le).contDiffAt hH).congr_of_eventuallyEq
      (mem_of_superset hH fun _ hy => oddWallReflection_eqOn_closed hy)

theorem oddWallReflection_hasCompactSupport {f : Point → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (oddWallReflection f) := by
  let K := tsupport f ∪ normalReflection ⁻¹' tsupport f
  have hK : IsCompact K := hf.union (normalReflection.toHomeomorph.isCompact_preimage.mpr hf)
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_cases h : x ∈ closedWallHalf
  · apply subset_union_left
    apply subset_closure
    change f x ≠ 0
    exact fun he => hx ((oddWallReflection_eqOn_closed (f := f) h).trans he)
  · apply subset_union_right
    change normalReflection x ∈ tsupport f
    apply subset_closure
    intro hzero
    apply hx
    rw [oddWallReflection,if_neg (show ¬ 0 ≤ x 2 from h),hzero,neg_zero]

private theorem exists_lipschitzOnWith_of_C1_compactSupport
    {f : Point → ℝ} {S : Set Point} (hS : IsClosed S) (hConv : Convex ℝ S)
    (hIn : (interior S).Nonempty) (hf : ContDiffOn ℝ 1 f S)
    (hc : HasCompactSupport f) : ∃ L : ℝ≥0, LipschitzOnWith L f S := by
  have hUD := uniqueDiffOn_convex hConv hIn
  have hK : IsCompact (tsupport f ∩ S) := hc.inter_right hS
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    ((hf.continuousOn_fderivWithin hUD le_rfl).mono inter_subset_right)
  let L := Real.toNNReal (max D 0)
  have hL : (L : ℝ) = max D 0 := Real.coe_toNNReal _ (le_max_right _ _)
  refine ⟨L,hConv.lipschitzOnWith_of_nnnorm_fderivWithin_le
    (hf.differentiableOn one_ne_zero) ?_⟩
  intro x hx
  change ‖fderivWithin ℝ f S x‖ ≤ (L : ℝ)
  by_cases ht : x ∈ tsupport f
  · rw [hL]
    exact (hD x ⟨ht,hx⟩).trans (le_max_left _ _)
  · have hE : f =ᶠ[𝓝[S] x] (0 : Point → ℝ) :=
      (notMem_tsupport_iff_eventuallyEq.1 ht).filter_mono nhdsWithin_le_nhds
    have hAt : HasFDerivWithinAt f 0 S x :=
      (hasFDerivAt_zero (𝕜 := ℝ) (F := ℝ) x).hasFDerivWithinAt.congr_of_eventuallyEq hE
        (image_eq_zero_of_notMem_tsupport ht)
    rw [hAt.fderivWithin (hUD x hx),norm_zero]
    exact L.coe_nonneg

private theorem lipschitzWith_of_lipschitzOnWith_wall_halves {f : Point → ℝ} {K : ℝ≥0}
    (h1 : LipschitzOnWith K f closedWallHalf) (h2 : LipschitzOnWith K f lowerClosedWallHalf) :
    LipschitzWith K f := by
  have hCross (x y : Point) (hx : x ∈ closedWallHalf) (hy : y ∈ lowerClosedWallHalf) :
      dist (f x) (f y) ≤ (K : ℝ)*dist x y := by
    by_cases hy' : y ∈ closedWallHalf
    · exact h1.dist_le_mul x hx y hy'
    have hyNeg : y 2 < 0 := lt_of_not_ge hy'
    let t := (x 2)/(x 2-y 2)
    have hx0 : 0 ≤ x 2 := hx
    have hPos : 0 < x 2-y 2 := by linarith only [hx0,hyNeg]
    have ht0 : 0 ≤ t := div_nonneg hx0 hPos.le
    have ht1 : t ≤ 1 := (div_le_one hPos).2 (by linarith only [hyNeg])
    let z := AffineMap.lineMap x y t
    have hz : z ∈ flatWall := by
      unfold z flatWall
      rw [mem_setOf_eq,AffineMap.lineMap_apply_module]
      change (1-t)*x 2 + t*y 2 = 0
      dsimp only [t]
      field_simp [hPos.ne']
      ring
    have hd1 := dist_left_lineMap x y t
    have hd2 := dist_lineMap_right x y t
    change dist x z = ‖t‖ * dist x y at hd1
    change dist z y = ‖1-t‖ * dist x y at hd2
    rw [Real.norm_of_nonneg ht0] at hd1
    rw [Real.norm_of_nonneg (sub_nonneg.mpr ht1)] at hd2
    have hxz := h1.dist_le_mul x hx z (show 0 ≤ z 2 from hz.ge)
    have hzy := h2.dist_le_mul z (show z 2 ≤ 0 from hz.le) y hy
    exact (dist_triangle _ _ _).trans
      ((add_le_add hxz hzy).trans_eq (by rw [hd1,hd2]; ring))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ∈ closedWallHalf
  · by_cases hy : y ∈ closedWallHalf
    · exact h1.dist_le_mul x hx y hy
    · exact hCross x y hx (not_le.mp (show ¬ 0 ≤ y 2 from hy)).le
  · by_cases hy : y ∈ closedWallHalf
    · rw [dist_comm (f x),dist_comm x]
      exact hCross y x hy (not_le.mp (show ¬ 0 ≤ x 2 from hx)).le
    · exact h2.dist_le_mul x (not_le.mp (show ¬ 0 ≤ x 2 from hx)).le y (not_le.mp (show ¬ 0 ≤ y 2 from hy)).le

theorem exists_lipschitzWith_oddWallReflection {f : Point → ℝ}
    (hf : ContDiffOn ℝ 1 f closedWallHalf) (h0 : EqOn f 0 flatWall) (hc : HasCompactSupport f) :
    ∃ L : ℝ≥0, LipschitzWith L (oddWallReflection f) := by
  have hcap := oddWallReflection_hasCompactSupport hc
  have hUp : ContDiffOn ℝ 1 (oddWallReflection f) closedWallHalf :=
    hf.congr oddWallReflection_eqOn_closed
  have hDown : ContDiffOn ℝ 1 (oddWallReflection f) lowerClosedWallHalf :=
    ((hf.comp normalReflection.contDiff.contDiffOn normalReflection_mapsTo_closed).neg).congr
      (oddWallReflection_eqOn_lower h0)
  obtain ⟨A,hA⟩ := exists_lipschitzOnWith_of_C1_compactSupport
    closedWallHalf_isClosed convex_closedWallHalf closedWallHalf_interior_nonempty hUp hcap
  obtain ⟨B,hB⟩ := exists_lipschitzOnWith_of_C1_compactSupport
    lowerClosedWallHalf_isClosed convex_lowerClosedWallHalf lowerClosedWallHalf_interior_nonempty hDown hcap
  exact ⟨max A B,lipschitzWith_of_lipschitzOnWith_wall_halves
    (hA.weaken (le_max_left _ _)) (hB.weaken (le_max_right _ _))⟩

/-- Each displayed first column of the odd extension is globally Lipschitz
for a compactly supported (C^2) zero wall field. -/
theorem exists_lipschitzWith_oddWallReflection_column {f : Point → ℝ}
    (hf : ContDiffOn ℝ 2 f closedWallHalf) (h0 : EqOn f 0 flatWall)
    (hc : HasCompactSupport f) (j : Fin 3) :
    ∃ L : ℝ≥0, LipschitzWith L (coordDeriv j (oddWallReflection f)) := by
  let G := coordDeriv j (oddWallReflection f)
  let K := fderivWithin ℝ f closedWallHalf
  have hUD := uniqueDiffOn_convex convex_closedWallHalf closedWallHalf_interior_nonempty
  have hKC : ContDiffOn ℝ 1 K closedWallHalf := hf.fderivWithin hUD (by norm_num)
  have hG1 : ContDiffOn ℝ 1 G closedWallHalf := by
    apply ((ContinuousLinearMap.apply ℝ ℝ (axis j)).contDiff.comp_contDiffOn hKC).congr
    intro x hx
    exact DFunLike.congr_fun (fderiv_oddWallReflection_eqOn_closed (hf.of_le (by norm_num)) h0 hx) (axis j)
  have hG2 : ContDiffOn ℝ 1 G lowerClosedWallHalf := by
    have hComp := hKC.comp normalReflection.contDiff.contDiffOn normalReflection_mapsTo_closed
    apply ((ContinuousLinearMap.apply ℝ ℝ (normalReflection (axis j))).contDiff.comp_contDiffOn hComp).neg.congr
    intro x hx
    exact DFunLike.congr_fun (fderiv_oddWallReflection_eqOn_lower (hf.of_le (by norm_num)) h0 hx) (axis j)
  have hcap : HasCompactSupport G := (oddWallReflection_hasCompactSupport hc).fderiv_apply ℝ (axis j)
  obtain ⟨A,hA⟩ := exists_lipschitzOnWith_of_C1_compactSupport
    closedWallHalf_isClosed convex_closedWallHalf closedWallHalf_interior_nonempty hG1 hcap
  obtain ⟨B,hB⟩ := exists_lipschitzOnWith_of_C1_compactSupport
    lowerClosedWallHalf_isClosed convex_lowerClosedWallHalf lowerClosedWallHalf_interior_nonempty hG2 hcap
  exact ⟨max A B,lipschitzWith_of_lipschitzOnWith_wall_halves
    (hA.weaken (le_max_left _ _)) (hB.weaken (le_max_right _ _))⟩

end Thesis
