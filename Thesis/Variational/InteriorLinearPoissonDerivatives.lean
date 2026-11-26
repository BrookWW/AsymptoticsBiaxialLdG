module

public import Thesis.Variational.InteriorLinearPoissonLowOrder
public import Thesis.Variational.InteriorDerivativeAlgebra

/-! Exact coordinate differentiation and all interior orders of the linear system. -/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

local instance linearPoissonDerivativeCoefficientNormed :
    NormedAddCommGroup ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)

local instance linearPoissonDerivativeCoefficientSpace :
    NormedSpace ℝ ((S0 × Gradient) →L[ℝ] S0) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)

private abbrev coordinateWordDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : List (Fin 3)) (f : Point → E) : Point → E :=
  iteratedCoordinateDerivative l.length l.get f

private theorem coordinateWordDerivative_cons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (l : List (Fin 3)) (f : Point → E) :
    coordinateWordDerivative (i::l) f = coordDeriv i (coordinateWordDerivative l f) := by
  rfl

private abbrev CoordinateSplit := List (Fin 3) × List (Fin 3)

private def differentiateSplits (i : Fin 3) : List CoordinateSplit → List CoordinateSplit
  | [] => []
  | p::rest => (i::p.1,p.2)::(p.1,i::p.2)::differentiateSplits i rest

private def coefficientDerivativeSplits : List (Fin 3) → List CoordinateSplit
  | [] => []
  | i::l => ([i],l)::differentiateSplits i (coefficientDerivativeSplits l)

private theorem length_differentiateSplits (i : Fin 3) (S : List CoordinateSplit) :
    (differentiateSplits i S).length = 2*S.length := by
  induction S with
  | nil => rfl
  | cons p S ih =>
    simp only [differentiateSplits,List.length_cons,ih]
    omega

private theorem length_coefficientDerivativeSplits (l : List (Fin 3)) :
    (coefficientDerivativeSplits l).length+1 = 2^l.length := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [coefficientDerivativeSplits,List.length_cons,length_differentiateSplits,pow_succ]
    omega

private theorem differentiateSplits_mem (i : Fin 3) {S : List CoordinateSplit}
    {p : CoordinateSplit} (hp : p ∈ differentiateSplits i S) :
    ∃ q ∈ S, p = (i::q.1,q.2) ∨ p = (q.1,i::q.2) := by
  induction S with
  | nil => simp [differentiateSplits] at hp
  | cons q S ih =>
    simp only [differentiateSplits,List.mem_cons] at hp
    rcases hp with h | h | h
    · exact ⟨q,List.mem_cons_self ..,Or.inl h⟩
    · exact ⟨q,List.mem_cons_self ..,Or.inr h⟩
    · obtain ⟨q',hq',he⟩ := ih h
      exact ⟨q',List.mem_cons_of_mem _ hq',he⟩

private theorem coefficientDerivativeSplits_orders {l : List (Fin 3)} {p : CoordinateSplit}
    (hp : p ∈ coefficientDerivativeSplits l) :
    p.1 ≠ [] ∧ p.1.length+p.2.length=l.length := by
  induction l generalizing p with
  | nil => simp [coefficientDerivativeSplits] at hp
  | cons i l ih =>
    simp only [coefficientDerivativeSplits,List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp
      omega
    obtain ⟨q,hq,rfl | rfl⟩ := differentiateSplits_mem i hp
    · exact ⟨List.cons_ne_nil _ _,by
        simp only [List.length_cons]
        have h := (ih hq).2
        omega⟩
    · exact ⟨(ih hq).1,by
        simp only [List.length_cons]
        have h := (ih hq).2
        omega⟩

private theorem sum_differentiateSplits {E : Type*} [AddCommMonoid E]
    (i : Fin 3) (S : List CoordinateSplit) (f : CoordinateSplit → E) :
    ((differentiateSplits i S).map f).sum =
      (S.map (fun p => f (i::p.1,p.2)+f (p.1,i::p.2))).sum := by
  induction S with
  | nil => rfl
  | cons p S ih =>
    simp only [differentiateSplits,List.map_cons,List.sum_cons,ih,add_assoc]

private theorem contDiffOn_coordinateWordDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Point} (hU : IsOpen U) {f : Point → E} (hf : ContDiffOn ℝ ∞ f U)
    (l : List (Fin 3)) : ContDiffOn ℝ ∞ (coordinateWordDerivative l f) U :=
  contDiffOn_iteratedCoordinateDerivative hU hf l.length l.get

private theorem coordDeriv_list_sum {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Point} (hU : IsOpen U) (L : List A) (f : A → Point → E)
    (hf : ∀ a ∈ L, ContDiffOn ℝ ∞ (f a) U) :
    ContDiffOn ℝ ∞ (fun x => (L.map fun a => f a x).sum) U ∧
      ∀ x ∈ U, ∀ i : Fin 3,
        coordDeriv i (fun y => (L.map fun a => f a y).sum) x =
          (L.map fun a => coordDeriv i (f a) x).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil,List.sum_nil]
    exact ⟨contDiffOn_const,fun x _ i => by unfold coordDeriv; rw [fderiv_const_apply,zero_apply]⟩
  | cons a L ih =>
    have hA := hf a (List.mem_cons_self ..)
    obtain ⟨hL,hD⟩ := ih (fun a ha => hf a (List.mem_cons_of_mem _ ha))
    simp only [List.map_cons,List.sum_cons]
    refine ⟨hA.add hL,fun x hx i => ?_⟩
    let H (y : Point) := (L.map fun b => f b y).sum
    have hA' := (hA.differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx)
    have hH' : DifferentiableAt ℝ H x := (hL.differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx)
    have h := (hA'.hasFDerivAt.add hH'.hasFDerivAt).fderiv
    have he : coordDeriv i (fun y => f a y+H y) x = coordDeriv i (f a) x+coordDeriv i H x :=
      DFunLike.congr_fun h (axis i)
    exact he.trans (congrArg (fun z => coordDeriv i (f a) x+z) (hD x hx i))

private theorem coordDeriv_apply_coefficient
    {U : Set Point} (hU : IsOpen U) {B : Point → (S0 × Gradient) →L[ℝ] S0}
    {Z : Point → S0 × Gradient} (hB : ContDiffOn ℝ ∞ B U) (hZ : ContDiffOn ℝ ∞ Z U)
    {x : Point} (hx : x ∈ U) (i : Fin 3) :
    coordDeriv i (fun y => B y (Z y)) x = B x (coordDeriv i Z x)+coordDeriv i B x (Z x) := by
  have hB' := (hB.differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx)
  have hZ' := (hZ.differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx)
  exact DFunLike.congr_fun (fderiv_clm_apply hB' hZ') (axis i)

private theorem coordinateWordDerivative_apply_coefficient
    {U : Set Point} (hU : IsOpen U) {B : Point → (S0 × Gradient) →L[ℝ] S0}
    {Z : Point → S0 × Gradient} (hB : ContDiffOn ℝ ∞ B U) (hZ : ContDiffOn ℝ ∞ Z U)
    (l : List (Fin 3)) {x : Point} (hx : x ∈ U) :
    coordinateWordDerivative l (fun y => B y (Z y)) x =
      B x (coordinateWordDerivative l Z x) +
        ((coefficientDerivativeSplits l).map (fun p =>
          coordinateWordDerivative p.1 B x (coordinateWordDerivative p.2 Z x))).sum := by
  induction l generalizing x with
  | nil =>
    change B x (Z x) = B x (Z x)+0
    rw [add_zero]
  | cons i l ih =>
    let S := coefficientDerivativeSplits l
    let t (p : CoordinateSplit) (y : Point) :=
      coordinateWordDerivative p.1 B y (coordinateWordDerivative p.2 Z y)
    let F (y : Point) := B y (coordinateWordDerivative l Z y)
    let T (y : Point) := (S.map fun p => t p y).sum
    have hF : ContDiffOn ℝ ∞ F U := hB.clm_apply (contDiffOn_coordinateWordDerivative hU hZ l)
    have ht (p : CoordinateSplit) : ContDiffOn ℝ ∞ (t p) U :=
      (contDiffOn_coordinateWordDerivative hU hB p.1).clm_apply
        (contDiffOn_coordinateWordDerivative hU hZ p.2)
    obtain ⟨hT,hDT⟩ := coordDeriv_list_sum hU S t (fun p _ => ht p)
    have he : coordinateWordDerivative l (fun y => B y (Z y)) =ᶠ[𝓝 x] (F+T) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih hy
    have hChange : coordDeriv i (coordinateWordDerivative l (fun y => B y (Z y))) x =
        coordDeriv i (F+T) x := DFunLike.congr_fun he.fderiv_eq (axis i)
    have hAdd : coordDeriv i (F+T) x = coordDeriv i F x+coordDeriv i T x := by
      have hF' := (hF.differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx)
      have hT' := (hT.differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx)
      exact DFunLike.congr_fun (hF'.hasFDerivAt.add hT'.hasFDerivAt).fderiv (axis i)
    have hDF : coordDeriv i F x =
        B x (coordinateWordDerivative (i::l) Z x)+coordinateWordDerivative [i] B x (coordinateWordDerivative l Z x) :=
      coordDeriv_apply_coefficient hU hB (contDiffOn_coordinateWordDerivative hU hZ l) hx i
    have hd (p : CoordinateSplit) : coordDeriv i (t p) x = t (i::p.1,p.2) x+t (p.1,i::p.2) x := by
      apply Eq.trans (coordDeriv_apply_coefficient hU
        (contDiffOn_coordinateWordDerivative hU hB p.1)
        (contDiffOn_coordinateWordDerivative hU hZ p.2) hx i)
      exact add_comm _ _
    rw [coordinateWordDerivative_cons i l (fun y => B y (Z y)),hChange,hAdd,hDF,hDT x hx i]
    change _ = B x (coordinateWordDerivative (i::l) Z x)+
      ((coefficientDerivativeSplits (i::l)).map (fun p => t p x)).sum
    simp only [coefficientDerivativeSplits,List.map_cons,List.sum_cons,sum_differentiateSplits]
    change _ = B x (coordinateWordDerivative (i::l) Z x)+
      (t ([i],l) x + (S.map fun p => t (i::p.1,p.2) x+t (p.1,i::p.2) x).sum)
    simp only [hd,add_assoc,t]

private theorem coordinateWordDerivative_coordDeriv
    {U : Set Point} (hU : IsOpen U) {v : Point → S0} (hv : ContDiffOn ℝ ∞ v U)
    (l : List (Fin 3)) (j : Fin 3) {x : Point} (hx : x ∈ U) :
    coordinateWordDerivative l (coordDeriv j v) x =
      coordDeriv j (coordinateWordDerivative l v) x := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    have he : coordinateWordDerivative l (coordDeriv j v) =ᶠ[𝓝 x]
        coordDeriv j (coordinateWordDerivative l v) := by
      filter_upwards [hU.mem_nhds hx] with y hy using ih hy
    exact (DFunLike.congr_fun he.fderiv_eq (axis i)).trans
      (coordDeriv_comm (((contDiffOn_coordinateWordDerivative hU hv l).contDiffAt (hU.mem_nhds hx)).of_le (by decide)) i j)

private theorem coordinateWordDerivative_gradient_pair
    {U : Set Point} (hU : IsOpen U) {v : Point → S0} (hv : ContDiffOn ℝ ∞ v U)
    (l : List (Fin 3)) {x : Point} (hx : x ∈ U) :
    coordinateWordDerivative l (fun y => (v y,ClassicalGradient v y)) x =
      (coordinateWordDerivative l v x,ClassicalGradient (coordinateWordDerivative l v) x) := by
  have hC : ContDiffOn ℝ ∞ (ClassicalGradient v) U := by
    apply contDiffOn_pi.mpr
    intro j
    exact contDiffOn_coordDeriv_infty hU hv j
  change iteratedCoordinateDerivative l.length l.get (fun y => (v y,ClassicalGradient v y)) x = _
  rw [iteratedCoordinateDerivative_prod_mk hU hv hC l.length l.get hx]
  congr 1
  funext j
  exact (iteratedCoordinateDerivative_pi_apply hU hC l.length l.get hx j).trans
    (coordinateWordDerivative_coordDeriv hU hv l j hx)

private def differentiatedPoissonForcing
    (l : List (Fin 3)) (B : Point → (S0 × Gradient) →L[ℝ] S0) (v F : Point → S0) (x : Point) : S0 :=
  coordinateWordDerivative l F x -
    ((coefficientDerivativeSplits l).map (fun p => coordinateWordDerivative p.1 B x
      (coordinateWordDerivative p.2 (fun y => (v y,ClassicalGradient v y)) x))).sum

private theorem coordinateWordDerivative_linearPoisson
    {U : Set Point} (hU : IsOpen U) {B : Point → (S0 × Gradient) →L[ℝ] S0}
    {v F : Point → S0} (hB : ContDiffOn ℝ ∞ B U) (hv : ContDiffOn ℝ ∞ v U)
    (hEq : ∀ x ∈ U, laplacian v x + B x (v x,ClassicalGradient v x) = F x)
    (l : List (Fin 3)) {x : Point} (hx : x ∈ U) :
    let w := coordinateWordDerivative l v
    laplacian w x+B x (w x,ClassicalGradient w x) = differentiatedPoissonForcing l B v F x := by
  let Z (y : Point) := (v y,ClassicalGradient v y)
  let Q (y : Point) := B y (Z y)
  have hGrad : ContDiffOn ℝ ∞ (ClassicalGradient v) U :=
    contDiffOn_pi.mpr fun i => contDiffOn_coordDeriv_infty hU hv i
  have hZ : ContDiffOn ℝ ∞ Z U := hv.prodMk hGrad
  have hQ : ContDiffOn ℝ ∞ Q U := hB.clm_apply hZ
  have he : EqOn (fun y => laplacian v y+Q y) F U := hEq
  have h := iteratedCoordinateDerivative_congr_open hU he l.length l.get hx
  rw [iteratedCoordinateDerivative_add hU (contDiffOn_classical_laplacian_infty hU hv) hQ l.length l.get hx,
    ← laplacian_iteratedCoordinateDerivative_tensor hU hv l.length l.get hx] at h
  change laplacian (coordinateWordDerivative l v) x+coordinateWordDerivative l Q x =
    coordinateWordDerivative l F x at h
  have hb := coordinateWordDerivative_apply_coefficient hU hB hZ l hx
  change coordinateWordDerivative l Q x = _ at hb
  rw [hb,show coordinateWordDerivative l Z x =
      (coordinateWordDerivative l v x,ClassicalGradient (coordinateWordDerivative l v) x) from
        coordinateWordDerivative_gradient_pair hU hv l hx,← add_assoc] at h
  exact eq_sub_of_add_eq h

private theorem norm_list_map_sum_le_length
    {A E : Type*} [NormedAddCommGroup E] (L : List A) (f : A → E) (M : ℝ)
    (h : ∀ x ∈ L, ‖f x‖ ≤ M) :
    ‖(L.map f).sum‖ ≤ (L.length : ℝ)*M := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_succ,add_mul,one_mul]
    exact (norm_add_le _ _).trans (by
      have h₁ := h a (List.mem_cons_self ..)
      have h₂ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
      linarith only [h₁,h₂])

private theorem norm_differentiatedPoissonForcing_le
    {U : Set Point} (hU : IsOpen U) {B : Point → (S0 × Gradient) →L[ℝ] S0}
    {v F : Point → S0} (hv : ContDiffOn ℝ ∞ v U) (l : List (Fin 3))
    {x : Point} (hx : x ∈ U) {M A D : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : ∀ p : List (Fin 3), p.length ≤ l.length → ‖coordinateWordDerivative p B x‖ ≤ M)
    (hV : ∀ p : List (Fin 3), p.length ≤ l.length → ‖coordinateWordDerivative p v x‖ ≤ A)
    (hF : ‖coordinateWordDerivative l F x‖ ≤ D) :
    ‖differentiatedPoissonForcing l B v F x‖ ≤ D+(2 : ℝ)^l.length*M*A := by
  let Z (y : Point) := (v y,ClassicalGradient v y)
  let L := coefficientDerivativeSplits l
  let f (p : CoordinateSplit) := coordinateWordDerivative p.1 B x (coordinateWordDerivative p.2 Z x)
  have hTerm (p : CoordinateSplit) (hp : p ∈ L) : ‖f p‖ ≤ M*A := by
    obtain ⟨hne,hLen⟩ := coefficientDerivativeSplits_orders hp
    have hPos : 0 < p.1.length := List.length_pos_iff.mpr hne
    have hBB := hB p.1 (by omega)
    have hZ : ‖coordinateWordDerivative p.2 Z x‖ ≤ A := by
      change ‖coordinateWordDerivative p.2 (fun y => (v y,ClassicalGradient v y)) x‖ ≤ A
      rw [coordinateWordDerivative_gradient_pair hU hv p.2 hx,Prod.norm_def]
      apply max_le (hV p.2 (by omega))
      apply (pi_norm_le_iff_of_nonneg hA).mpr
      intro i
      have hi := hV (i::p.2) (by simpa only [List.length_cons] using (show p.2.length+1 ≤ l.length by omega))
      rwa [coordinateWordDerivative_cons] at hi
    exact ((coordinateWordDerivative p.1 B x).le_opNorm _).trans
      (mul_le_mul hBB hZ (norm_nonneg _) hM)
  have hSum := norm_list_map_sum_le_length L f (M*A) hTerm
  have hLen : (L.length : ℝ) ≤ (2 : ℝ)^l.length := by
    have h := length_coefficientDerivativeSplits l
    have h' : L.length ≤ 2^l.length := by dsimp only [L]; omega
    exact_mod_cast h'
  change ‖coordinateWordDerivative l F x-(L.map f).sum‖ ≤ D+(2 : ℝ)^l.length*M*A
  refine (norm_sub_le _ _).trans (add_le_add hF (hSum.trans ?_))
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right hLen (mul_nonneg hM hA)

private theorem exists_interior_linearPoisson_coordinate_bounds
    (c : Point) {r s : ℝ} (hs : 0 < s) (hsr : s < r) (j : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C > (0 : ℝ), ∀ (B : Point → (S0 × Gradient) →L[ℝ] S0) (v F : Point → S0) (E D : ℝ),
      ContDiffOn ℝ ∞ B (ball c r) → ContDiffOn ℝ ∞ v (ball c r) → ContDiffOn ℝ ∞ F (ball c r) →
      0 ≤ E → 0 ≤ D → MemLp v 2 (volume.restrict (ball c r)) →
        eLpNorm v 2 (volume.restrict (ball c r)) ≤ ENNReal.ofReal E →
      (∀ y ∈ ball c r, laplacian v y+B y (v y,ClassicalGradient v y)=F y) →
      (∀ k ≤ j, ∀ y ∈ ball c r, ‖iteratedFDeriv ℝ k B y‖ ≤ M) →
      (∀ k ≤ j, ∀ y ∈ ball c r, ‖iteratedFDeriv ℝ k F y‖ ≤ D) →
      ∀ l : List (Fin 3), l.length ≤ j → ∀ y ∈ ball c s,
        ‖coordinateWordDerivative l v y‖ ≤ C*(E+D) := by
  induction j generalizing s with
  | zero =>
    obtain ⟨C,hC,hVal⟩ := exists_interior_linearPoisson_value_bound c hs hsr M hM
    refine ⟨C,hC,?_⟩
    intro B v F E D hBC hv hFC hE hD hV hVE hEq hB hF l hl y hy
    have he : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    subst l
    exact hVal B v F E D hv hE hD hV hVE hEq
      (fun z hz => by simpa only [norm_iteratedFDeriv_zero] using hB 0 le_rfl z hz)
      (fun z hz => by simpa only [norm_iteratedFDeriv_zero] using hF 0 le_rfl z hz) y hy
  | succ j ih =>
    let t := (s+r)/2
    have hst : s < t := by dsimp only [t]; linarith only [hsr]
    have htr : t < r := by dsimp only [t]; linarith only [hsr]
    obtain ⟨C₀,hC₀,hVal⟩ := ih (hs.trans hst) htr
    obtain ⟨C₁,hC₁,hGrad⟩ := exists_interior_linearPoisson_gradient_bound c hs hst M hM
    let C := C₀+C₁*((1+(2 : ℝ)^j*M)*C₀+1)
    have hCtail : 0 ≤ C₁*((1+(2 : ℝ)^j*M)*C₀+1) := by positivity
    have hC : 0 < C := add_pos_of_pos_of_nonneg hC₀ hCtail
    refine ⟨C,hC,?_⟩
    intro B v F E D hBC hv hFC hE hD hV hVE hEq hB hF l hl y hy
    have hS : ball c s ⊆ ball c t := ball_subset_ball hst.le
    have hT : ball c t ⊆ ball c r := ball_subset_ball htr.le
    let A := C₀*(E+D)
    have hA : 0 ≤ A := mul_nonneg hC₀.le (add_nonneg hE hD)
    have hPrev : ∀ l' : List (Fin 3), l'.length ≤ j → ∀ z ∈ ball c t,
        ‖coordinateWordDerivative l' v z‖ ≤ A :=
      hVal B v F E D hBC hv hFC hE hD hV hVE hEq
        (fun k hk => hB k (hk.trans (Nat.le_succ j)))
        (fun k hk => hF k (hk.trans (Nat.le_succ j)))
    by_cases hl' : l.length ≤ j
    · exact (hPrev l hl' y (hS hy)).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCtail) (add_nonneg hE hD))
    rcases l with _ | ⟨i,l⟩
    · exact (hl' (Nat.zero_le _)).elim
    have hLength : l.length = j := by simp only [List.length_cons] at hl hl'; omega
    let w := coordinateWordDerivative l v
    let R := differentiatedPoissonForcing l B v F
    let D' := D+(2 : ℝ)^j*M*A
    have hD' : 0 ≤ D' := by dsimp only [D']; positivity
    have hwC : ContDiffOn ℝ ∞ w (ball c t) :=
      (contDiffOn_coordinateWordDerivative isOpen_ball hv l).mono hT
    have hWA (z : Point) (hz : z ∈ ball c t) : ‖w z‖ ≤ A :=
      hPrev l hLength.le z hz
    have hWEq (z : Point) (hz : z ∈ ball c t) :
        laplacian w z+B z (w z,ClassicalGradient w z) = R z :=
      coordinateWordDerivative_linearPoisson isOpen_ball hBC hv hEq l (hT hz)
    have hBn (z : Point) (hz : z ∈ ball c t) : ‖B z‖ ≤ M := by
      simpa only [norm_iteratedFDeriv_zero] using hB 0 (Nat.zero_le _) z (hT hz)
    have hRn (z : Point) (hz : z ∈ ball c t) : ‖R z‖ ≤ D' := by
      have hz' := hT hz
      have h := norm_differentiatedPoissonForcing_le isOpen_ball hv l hz' hM hA
        (fun p hp => (norm_coordinateDerivative_le_norm_iteratedFDeriv isOpen_ball hBC
          p.length p.get hz').trans (hB p.length (hp.trans (hLength.le.trans (Nat.le_succ j))) z hz'))
        (fun p hp => hPrev p (hp.trans hLength.le) z hz)
        ((norm_coordinateDerivative_le_norm_iteratedFDeriv isOpen_ball hFC l.length l.get hz').trans
          (hF l.length (hLength.le.trans (Nat.le_succ j)) z hz'))
      simpa only [D',R,hLength] using h
    have hGr := hGrad B w R A D' hwC hA hD' hWA hWEq hBn hRn y hy
    have hJ : ‖coordDeriv i w y‖ ≤ ‖ClassicalGradient w y‖ := by
      have h : ‖ClassicalGradient w y‖ ≤ ‖ClassicalGradient w y‖ := le_rfl
      exact (pi_norm_le_iff_of_nonneg (norm_nonneg (ClassicalGradient w y))).mp h i
    rw [coordinateWordDerivative_cons]
    apply (hJ.trans ((norm_classicalGradient_le_sqrt_energy w y).trans hGr)).trans
    have hErr : D ≤ E+D := le_add_of_nonneg_left hE
    have hA' : A+D' ≤ ((1+(2 : ℝ)^j*M)*C₀+1)*(E+D) := by
      dsimp only [A,D']
      linarith only [hErr]
    have hBase : 0 ≤ C₀*(E+D) := hA
    have h := mul_le_mul_of_nonneg_left hA' hC₁.le
    dsimp only [C]
    nlinarith only [h,hBase]

private theorem coordinateWordDerivative_ofFn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {j : ℕ} (i : Fin j → Fin 3) (f : Point → E) :
    coordinateWordDerivative (List.ofFn i) f = iteratedCoordinateDerivative j i f := by
  induction j with
  | zero => rw [List.ofFn_zero]; rfl
  | succ j ih =>
    rw [List.ofFn_succ,coordinateWordDerivative_cons,ih]
    rfl

/-- The full interior derivative estimate for the original finite
linear Poisson system, at every order and with the original L² input. -/
theorem interiorLinearPoissonSystemDerivativeEstimate :
    External.InteriorLinearPoissonSystemDerivativeEstimate := by
  intro c r hr j M hM
  obtain ⟨C,hC,hBound⟩ := exists_interior_linearPoisson_coordinate_bounds c (half_pos hr) (half_lt_self hr) j M hM
  refine ⟨(3 : ℝ)^j*C,by positivity,?_⟩
  intro B v F E D hB hv hF hE hD hV hVE hEq hBD hFD y hy
  have hyr : y ∈ ball c r := ball_subset_ball (half_lt_self hr).le hy
  have hCoord (i : Fin j → Fin 3) : ‖iteratedCoordinateDerivative j i v y‖ ≤ C*(E+D) := by
    have h := hBound B v F E D hB hv hF hE hD hV hVE hEq
      (fun k hk => hBD k (hk.trans (Nat.le_add_right j 2)))
      (fun k hk => hFD k (hk.trans (Nat.le_add_right j 2)))
      (List.ofFn i) (by simp) y hy
    simpa only [coordinateWordDerivative_ofFn] using h
  have h := norm_iteratedFDeriv_le_of_coordinateBounds isOpen_ball hv j hyr
    (mul_nonneg hC.le (add_nonneg hE hD)) hCoord
  exact h.trans_eq (mul_assoc _ _ _).symm

end Thesis
