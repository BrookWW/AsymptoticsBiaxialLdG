module

public import Thesis.Variational.CollarSlabTransfer
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-! Product rectangles give the physical equal-volume cells for the
dyadic collar comparison. -/

public section

open Filter Function MeasureTheory Metric Set Topology
open scoped BigOperators ENNReal NNReal

set_option autoImplicit false
noncomputable section

namespace Thesis

abbrev WallChartPoint := (ℝ × ℝ) × ℝ

@[expose] def wallChartHorizontal (b : ℝ) : Set (ℝ × ℝ) := Ioc (-b) b ×ˢ Ioc (-b) b

@[expose] def wallChartSlab (b t : ℝ) : Set WallChartPoint := wallChartHorizontal b ×ˢ Ioc 0 t

@[expose] def wallChartClosedBox (b : ℝ) : Set WallChartPoint :=
  (Icc (-b) b ×ˢ Icc (-b) b) ×ˢ Icc (-b) b

private def intervalCell (a d : ℝ) {N : ℕ} (i : Fin N) : Set ℝ :=
  Ioc (a + (i : ℝ) * d) (a + ((i : ℝ) + 1) * d)

private theorem iUnion_intervalCell (a d : ℝ) (hd : 0 < d) (N : ℕ) :
    (⋃ i : Fin N, intervalCell a d i) = Ioc a (a + (N : ℝ) * d) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    have h : (i : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt i.isLt
    exact ⟨(le_add_of_nonneg_right (mul_nonneg (by positivity) hd.le)).trans_lt hi.1,
      hi.2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right h hd.le))⟩
  · intro hx
    have hx₀ : a < x := hx.1
    have hx₁ : x ≤ a + (N : ℝ)*d := hx.2
    let p (j : ℕ) := x ≤ a + (j : ℝ)*d
    have hEx : ∃ j, p j := ⟨N,hx₁⟩
    let n := Nat.find hEx
    have hn : p n := Nat.find_spec hEx
    have hnN : n ≤ N := Nat.find_min' hEx hx₁
    have hn₀ : 0 < n := by
      by_contra! h
      have he : n = 0 := Nat.le_zero.mp h
      change x ≤ a+(n : ℝ)*d at hn
      simp only [he,Nat.cast_zero,zero_mul,add_zero] at hn
      exact (not_le_of_gt hx₀) hn
    let i : Fin N := ⟨n-1, by omega⟩
    have hi : (i : ℕ)+1=n := Nat.sub_add_cancel hn₀
    have hLo : a + (i : ℝ)*d < x :=
      lt_of_not_ge (Nat.find_min hEx (show i.val < n by omega))
    have hHi : x ≤ a + ((i : ℝ)+1)*d := by
      rw [show (i : ℝ)+1=(n:ℝ) by exact_mod_cast hi]
      exact hn
    exact mem_iUnion.mpr ⟨i,hLo,hHi⟩

private theorem pairwise_intervalCell (a d : ℝ) (hd : 0 < d) (N : ℕ) :
    Pairwise (Disjoint on fun i : Fin N => intervalCell a d i) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro x hx hy
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have h : (i : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    exact (not_lt_of_ge (hx.2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right h hd.le)))) hy.1
  · have h : (j : ℝ)+1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    exact (not_lt_of_ge (hy.2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right h hd.le)))) hx.1

private theorem dist_le_of_mem_intervalCell {a d : ℝ} {N : ℕ} {i : Fin N} {x y : ℝ}
    (hx : x ∈ intervalCell a d i) (hy : y ∈ intervalCell a d i) : dist x y ≤ d := by
  rw [Real.dist_eq,abs_le]
  exact ⟨by linarith only [hx.1,hy.2],by linarith only [hx.2,hy.1]⟩

private theorem volume_intervalCell (a d : ℝ) {N : ℕ} (i : Fin N) :
    volume (intervalCell a d i) = ENNReal.ofReal d := by
  unfold intervalCell
  rw [Real.volume_Ioc,show a+((i:ℝ)+1)*d-(a+(i:ℝ)*d)=d by ring]

theorem wallChartSlab_subset_box {b t : ℝ} (hb : 0 < b) (ht : t ≤ b) :
    wallChartSlab b t ⊆ wallChartClosedBox b := by
  rintro ⟨⟨x,y⟩,u⟩ h
  exact ⟨⟨⟨h.1.1.1.le,h.1.1.2⟩,⟨h.1.2.1.le,h.1.2.2⟩⟩,
    ⟨(neg_nonpos.mpr hb.le).trans h.2.1.le,h.2.2.trans ht⟩⟩

private theorem volume_image_of_wallChart {Φ : WallChartPoint ≃ₜ Point}
    (hΦ : MeasurePreserving Φ) {D : Set WallChartPoint} (hD : MeasurableSet D) :
    volume (Φ '' D) = volume D := by
  have hMeas : MeasurableSet (Φ '' D) := Φ.toMeasurableEquiv.measurableSet_image.mpr hD
  have h := hΦ.measure_preimage hMeas.nullMeasurableSet
  rw [preimage_image_eq _ Φ.injective] at h
  exact h.symm

/-- Dyadic-size horizontal cells give the adjacent slab comparison on
the physical wall chart. -/
theorem squared_wallChartSlabAverage_difference_le
    {U : Set Point} (hU : IsBoundedDomain U) {b : ℝ} (hb : 0 < b)
    (Φ : WallChartPoint ≃ₜ Point) (hΦ : MeasurePreserving Φ)
    (hInside : Φ '' wallChartSlab b b ⊆ U)
    {K : ℝ≥0} (hK : 0 < (K : ℝ)) (hLip : LipschitzOnWith K Φ (wallChartClosedBox b))
    {d : ℝ} (hd : 0 < d) (hdB : d ≤ b) (N : ℕ) (hNd : (N : ℝ)*d = 2*b)
    {r : ℝ} (hr : 0 < r) (g : Point → ℝ)
    (hg : MemLp g 2 (volume.restrict U)) (hE : scalarFractionalPairEnergy r (volume.restrict U) g < ⊤) :
    ((∫ x in Φ '' wallChartSlab b (d/2), g x ∂volume.restrict U)/(d/2) -
      (∫ x in Φ '' wallChartSlab b d, g x ∂volume.restrict U)/d)^2 ≤
      2 * (2*b)^2 * (K:ℝ)^(3+2*r) * d^(2*r-1) * (scalarFractionalPairEnergy r (volume.restrict U) g).toReal := by
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.2.2.measure_lt_top.ne
  let I : Fin N → Set ℝ := intervalCell (-b) d
  have hIu : (⋃ i, I i) = Ioc (-b) b := by
    rw [show (⋃ i, I i) = Ioc (-b) (-b + (N:ℝ)*d) from iUnion_intervalCell _ _ hd N,hNd]
    congr 1
    ring
  let W (ij : Fin N × Fin N) (t : ℝ) : Set WallChartPoint := (I ij.1 ×ˢ I ij.2) ×ˢ Ioc 0 t
  let V (t : ℝ) (ij : Fin N × Fin N) : Set Point := Φ '' W ij t
  have hWMeas (ij : Fin N × Fin N) (t : ℝ) : MeasurableSet (W ij t) :=
    (measurableSet_Ioc.prod measurableSet_Ioc).prod measurableSet_Ioc
  have hVMeas (t : ℝ) (ij : Fin N × Fin N) : MeasurableSet (V t ij) :=
    Φ.toMeasurableEquiv.measurableSet_image.mpr (hWMeas ij t)
  have hWi (ij : Fin N × Fin N) (t : ℝ) : W ij t ⊆ wallChartSlab b t := by
    intro x hx
    refine ⟨⟨?_,?_⟩,hx.2⟩
    · rw [← hIu]; exact mem_iUnion.mpr ⟨ij.1,hx.1.1⟩
    · rw [← hIu]; exact mem_iUnion.mpr ⟨ij.2,hx.1.2⟩
  have hDisj (t : ℝ) : Pairwise (Disjoint on V t) := by
    intro ij kl hNe
    apply Set.disjoint_left.2
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,hxy⟩
    have hE : y = x := Φ.injective hxy
    subst y
    by_cases hFirst : ij.1=kl.1
    · have hSecond : ij.2 ≠ kl.2 := fun h => hNe (Prod.ext hFirst h)
      exact Set.disjoint_left.mp (pairwise_intervalCell (-b) d hd N hSecond) hx.1.2 hy.1.2
    · exact Set.disjoint_left.mp (pairwise_intervalCell (-b) d hd N hFirst) hx.1.1 hy.1.1
  have hUnion (t : ℝ) : (⋃ ij, V t ij) = Φ '' wallChartSlab b t := by
    rw [← image_iUnion]
    congr 1
    ext x
    constructor
    · rintro hx
      obtain ⟨ij,h⟩ := mem_iUnion.mp hx
      exact hWi ij t h
    · intro hx
      have hx₁ : x.1.1∈⋃ i, I i := hIu.symm ▸ hx.1.1
      have hx₂ : x.1.2∈⋃ i, I i := hIu.symm ▸ hx.1.2
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx₁
      obtain ⟨j,hj⟩ := mem_iUnion.mp hx₂
      exact mem_iUnion.mpr ⟨(i,j),⟨⟨hi,hj⟩,hx.2⟩⟩
  have hVol (t : ℝ) (_hT : 0 ≤ t) (htB : t ≤ b) (ij : Fin N × Fin N) :
      μ (V t ij) = ENNReal.ofReal (d^2*t) := by
    have hSub : wallChartSlab b t ⊆ wallChartSlab b b := by
      intro x hx
      exact ⟨hx.1,hx.2.1,hx.2.2.trans htB⟩
    have hVS : V t ij ⊆ U :=
      (image_mono ((hWi ij t).trans hSub)).trans hInside
    rw [show μ (V t ij) = volume (V t ij) from by dsimp only [μ]; rw [Measure.restrict_apply (hVMeas t ij),inter_eq_left.mpr hVS],
      volume_image_of_wallChart hΦ (hWMeas ij t)]
    change volume ((I ij.1 ×ˢ I ij.2) ×ˢ Ioc 0 t) = _
    rw [Measure.volume_eq_prod,Measure.prod_prod,Measure.volume_eq_prod,Measure.prod_prod,
      volume_intervalCell _ _,volume_intervalCell _ _,Real.volume_Ioc,sub_zero]
    rw [← ENNReal.ofReal_mul hd.le,← ENNReal.ofReal_mul (mul_nonneg hd.le hd.le)]
    congr 1
    ring
  have hAd (ij : Fin N × Fin N) : μ (V d ij) = ENNReal.ofReal (d^3) := (hVol d hd.le hdB ij)
  have hBd (ij : Fin N × Fin N) : μ (V (d/2) ij) = ENNReal.ofReal (d^3/2) :=
    (hVol (d/2) (half_pos hd).le (half_le_self hd.le |>.trans hdB) ij).trans (by congr 1; ring)
  have hDist (ij : Fin N × Fin N) (x : Point) (hx : x ∈ V (d/2) ij) (y : Point) (hy : y ∈ V d ij) :
      dist x y ≤ (K:ℝ)*d := by
    obtain ⟨u,hu,rfl⟩ := hx
    obtain ⟨v,hv,rfl⟩ := hy
    have huB := wallChartSlab_subset_box hb ((half_le_self hd.le).trans hdB) (hWi ij (d/2) hu)
    have hvB := wallChartSlab_subset_box hb hdB (hWi ij d hv)
    refine (hLip.dist_le_mul _ huB _ hvB).trans (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
    rw [Prod.dist_eq,Prod.dist_eq]
    apply max_le_iff.2
    refine ⟨max_le_iff.2 ⟨dist_le_of_mem_intervalCell hu.1.1 hv.1.1,
      dist_le_of_mem_intervalCell hu.1.2 hv.1.2⟩,?_⟩
    have h₁ : u.2 ∈ Ioc (0:ℝ) d := ⟨hu.2.1,hu.2.2.trans (half_le_self hd.le)⟩
    rw [Real.dist_eq,abs_le]
    exact ⟨by linarith only [h₁.1,hv.2.2],by linarith only [h₁.2,hv.2.1]⟩
  have hCard : (Fintype.card (Fin N × Fin N) : ℝ)*d^2=(2*b)^2 := by
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    calc
      _ = ((N:ℝ)*d)^2 := by ring
      _ = _ := by rw [hNd]
  have hBound := squared_slabAverage_difference_le hr hK hd hCard (V d) (V (d/2))
    (hVMeas d) (hVMeas (d/2)) (hDisj d) (hDisj (d/2)) hAd hBd hDist g hg hE
  rw [hUnion d,hUnion (d/2)] at hBound
  exact hBound

end Thesis

end
