module

public import Thesis.MeasureGeometry.CompactifiedPlanarPerimeter
import Mathlib.Data.Finset.Sort

/-! Separating the projected punctures by ordered strips. -/

public section

noncomputable section

open Filter Function OnePoint Set
open scoped BigOperators Topology NNReal

namespace Thesis.MeasureGeometry

/-- A linear shear preserves each second coordinate. -/
@[expose] def planarShear (s : ℝ) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun z := (z.1+s*z.2,z.2)
  invFun z := (z.1-s*z.2,z.2)
  left_inv z := Prod.ext (add_sub_cancel_right _ _) rfl
  right_inv z := Prod.ext (sub_add_cancel _ _) rfl
  map_add' z w := by
    apply Prod.ext
    · change z.1+w.1+s*(z.2+w.2) = z.1+s*z.2+(w.1+s*w.2)
      ring
    · rfl
  map_smul' r z := by
    apply Prod.ext
    · change r*z.1 + s*(r*z.2) = r*(z.1+s*z.2)
      ring
    · rfl
  continuous_toFun := (continuous_fst.add (continuous_const.mul continuous_snd)).prodMk continuous_snd
  continuous_invFun := (continuous_fst.sub (continuous_const.mul continuous_snd)).prodMk continuous_snd

/-- There is a shear after which all the points have distinct first coordinates. -/
theorem exists_planarShear_fst_injective {n : ℕ} {p : Fin n → ℝ × ℝ} (hp : Injective p) :
    ∃ s : ℝ, Injective (fun i => (planarShear s (p i)).1) := by
  classical
  let ℓ (i j : Fin n) := ((p j).1-(p i).1)/((p i).2-(p j).2)
  obtain ⟨s,hs⟩ := (Set.finite_range (fun ij : Fin n × Fin n => ℓ ij.1 ij.2)).exists_notMem
  refine ⟨s,fun i j he => ?_⟩
  change (p i).1+s*(p i).2 = (p j).1+s*(p j).2 at he
  by_cases h : (p i).2 = (p j).2
  · apply hp
    exact Prod.ext (by linarith only [he,congrArg (fun t : ℝ => s*t) h]) h
  · exfalso
    apply hs
    refine ⟨(i,j),?_⟩
    change ((p j).1-(p i).1)/((p i).2-(p j).2) = s
    apply (div_eq_iff (sub_ne_zero.mpr h)).2
    linarith only [he, mul_sub s (p i).2 (p j).2]

/-- Order the point family by its distinct first coordinates. -/
theorem exists_order_by_firstCoordinate {n : ℕ} (p : Fin n → ℝ × ℝ)
    (h : Injective (fun i => (p i).1)) :
    ∃ e : Equiv.Perm (Fin n), StrictMono (fun i => (p (e i)).1) := by
  classical
  let X := (Finset.univ : Finset (Fin n)).image (fun i => (p i).1)
  have hCard : X.card = n := by
    change (Finset.univ.image (fun i => (p i).1)).card = n
    rw [Finset.card_image_of_injective _ h,Finset.card_fin]
  let g (i : Fin n) : X := ⟨(p i).1,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hgI : Injective g := fun i j he => h (congrArg Subtype.val he)
  have hgS : Surjective g := by
    intro x
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp x.property
    exact ⟨i,Subtype.ext hi⟩
  let E := Equiv.ofBijective g ⟨hgI,hgS⟩
  let e := (X.orderIsoOfFin hCard).toEquiv.trans E.symm
  have hEq (i : Fin n) : (p (e i)).1 = ((X.orderIsoOfFin hCard) i).val :=
    congrArg Subtype.val (E.apply_symm_apply (X.orderIsoOfFin hCard i))
  refine ⟨e,fun i j hij => ?_⟩
  change (p (e i)).1 < (p (e j)).1
  rw [hEq,hEq]
  exact (X.orderIsoOfFin hCard).strictMono hij

/-- Consecutive vertical cuts around an ordered finite set of points, with
the left and right endpoints of one encompassing square. -/
theorem exists_ordered_planar_strips {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ × ℝ)
    (hp : StrictMono (fun i => (p i).1)) :
    ∃ (A : ℝ) (x : ℕ → ℝ), 0 < A ∧ x 0 = -A ∧ x n = A ∧ Monotone x ∧
      (∀ i, ‖p i‖ < A) ∧ ∀ i : Fin n, x i.val < (p i).1 ∧ (p i).1 < x (i.val+1) := by
  obtain ⟨C,hC⟩ := (Set.finite_range p).isCompact.isBounded.exists_norm_le
  let A := max C 0 + 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left (le_max_right _ _))
  have hBound (i : Fin n) : ‖p i‖ < A :=
    (hC _ (mem_range_self i)).trans_lt ((le_max_left _ _).trans_lt (lt_add_one _))
  have hX (i : Fin n) : -A < (p i).1 ∧ (p i).1 < A := by
    rw [← abs_lt]
    exact ((show ‖(p i).1‖ ≤ ‖p i‖ from norm_fst_le _).trans_lt (hBound i))
  let x (i : ℕ) : ℝ :=
    if hi : i = 0 then -A else if hIn : i < n then
      ((p ⟨i-1,by omega⟩).1 + (p ⟨i,hIn⟩).1)/2 else A
  have hLeft (i : Fin n) : x i.val < (p i).1 := by
    by_cases h0 : i.val = 0
    · change (if _ : i.val = 0 then -A else _) < _
      rw [dif_pos h0]
      exact (hX i).1
    · change (if _ : i.val = 0 then -A else _) < _
      rw [dif_neg h0,dif_pos i.isLt]
      have h := hp (show (⟨i.val-1,by omega⟩ : Fin n) < i from by simp only [Fin.lt_def]; omega)
      change ((p ⟨i.val-1,by omega⟩).1 + (p i).1)/2 < (p i).1
      linarith only [h]
  have hRight (i : Fin n) : (p i).1 < x (i.val+1) := by
    change (p i).1 < (if _ : i.val+1 = 0 then -A else _)
    rw [dif_neg (Nat.succ_ne_zero i.val)]
    by_cases hI : i.val+1 < n
    · rw [dif_pos hI]
      have hEq : (⟨i.val+1-1,by omega⟩ : Fin n) = i := Fin.ext (Nat.add_sub_cancel _ _)
      rw [hEq]
      have h := hp (show i < (⟨i.val+1,hI⟩ : Fin n) from Nat.lt_succ_self _)
      change (p i).1 < ((p i).1+(p ⟨i.val+1,hI⟩).1)/2
      linarith only [h]
    · rw [dif_neg hI]
      exact (hX i).2
  have hMono : Monotone x := monotone_nat_of_le_succ fun i => by
    by_cases hI : i < n
    · exact ((hLeft ⟨i,hI⟩).trans (hRight ⟨i,hI⟩)).le
    · have hNI : i ≠ 0 := fun h => hI (h ▸ hn)
      have hNS : ¬ i+1 < n := by omega
      change (if _ : i = 0 then -A else _) ≤ (if _ : i+1 = 0 then -A else _)
      rw [dif_neg hNI,dif_neg (Nat.succ_ne_zero _),dif_neg hI,dif_neg hNS]
  refine ⟨A,x,hA,?_,?_,hMono,hBound,fun i => ⟨hLeft i,hRight i⟩⟩
  · change (if _ : 0 = 0 then -A else _) = -A
    rw [dif_pos rfl]
  · change (if _ : n = 0 then -A else _) = A
    rw [dif_neg hn.ne',dif_neg (lt_irrefl n)]

/-- In the strip enclosing one point the closed rectangle contains none of
the other points. All cut lines avoid every point of the finite family. -/
theorem ordered_planar_strips_separate {n : ℕ} (p : Fin n → ℝ × ℝ) (x : ℕ → ℝ)
    (hx : Monotone x) (h : ∀ i : Fin n, x i.val < (p i).1 ∧ (p i).1 < x (i.val+1)) :
    (∀ j : ℕ, ∀ i : Fin n, x j ≠ (p i).1) ∧
    ∀ i j : Fin n, (p j).1 ∈ Icc (x i.val) (x (i.val+1)) → i = j := by
  constructor
  · intro j i
    by_cases hJI : j ≤ i.val
    · exact ((hx hJI).trans_lt (h i).1).ne
    · exact ((h i).2.trans_le (hx (by omega : i.val+1 ≤ j))).ne'
  · intro i j hj
    rcases lt_trichotomy i j with hIJ | hEq | hJI
    · have hjV : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hIJ
      exact False.elim (not_lt_of_ge hj.2 ((hx hjV).trans_lt (h j).1))
    · exact hEq
    · have hjV : j.val+1 ≤ i.val := Nat.succ_le_of_lt hJI
      exact False.elim (not_lt_of_ge hj.1 ((h j).2.trans_le (hx hjV)))

end Thesis.MeasureGeometry
