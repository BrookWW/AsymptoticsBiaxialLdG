module

public import Thesis.Variational.InteriorDerivativeEstimate
import Thesis.Variational.EnergyEstimate
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Coordinate and multilinear derivative estimates used in the interior
bootstrap for the biaxial equation. -/

public section

open Filter Metric Set Topology
open scoped ContDiff Matrix.Norms.Frobenius

noncomputable section

namespace Thesis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An ordered string of coordinate derivatives in the fixed Euclidean frame. -/
@[expose] def iteratedCoordinateDerivative :
    (n : ℕ) → (Fin n → Fin 3) → (Point → E) → Point → E
  | 0, _, f => f
  | n + 1, i, f => coordDeriv (i 0) (iteratedCoordinateDerivative n (Fin.tail i) f)

theorem contDiffOn_coordDeriv_infty {U : Set Point} (hU : IsOpen U) {f : Point → E}
    (hf : ContDiffOn ℝ ∞ f U) (i : Fin 3) : ContDiffOn ℝ ∞ (coordDeriv i f) U :=
  (ContinuousLinearMap.apply ℝ E (axis i)).contDiff.comp_contDiffOn
    (hf.fderiv_of_isOpen hU (le_of_eq (by simp)))

theorem contDiffOn_iteratedCoordinateDerivative {U : Set Point} (hU : IsOpen U) {f : Point → E}
    (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) (i : Fin n → Fin 3) :
    ContDiffOn ℝ ∞ (iteratedCoordinateDerivative n i f) U := by
  induction n with
  | zero => exact hf
  | succ n ih => exact contDiffOn_coordDeriv_infty hU (ih (Fin.tail i)) _

theorem contDiffOn_classical_laplacian_infty {U : Set Point} (hU : IsOpen U) {f : Point → E}
    (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (laplacian f) U :=
  ContDiffOn.sum (fun i _ => contDiffOn_coordDeriv_infty hU (contDiffOn_coordDeriv_infty hU hf i) i)

/-- Ordered coordinate derivatives are the evaluations of the actual
iterated Fréchet derivative on the corresponding Euclidean axes. -/
theorem iteratedCoordinateDerivative_eq_iteratedFDeriv {U : Set Point} (hU : IsOpen U)
    {f : Point → E} (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ U) :
    iteratedCoordinateDerivative n i f x = iteratedFDeriv ℝ n f x (axis ∘ i) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have hEq : iteratedCoordinateDerivative n (Fin.tail i) f =ᶠ[𝓝 x]
          fun y => iteratedFDeriv ℝ n f y (axis ∘ Fin.tail i) := by
        filter_upwards [hU.mem_nhds hx] with y hy using ih (Fin.tail i) hy
      have hD : DifferentiableOn ℝ (iteratedFDeriv ℝ n f) U :=
        (hf.differentiableOn_iteratedFDerivWithin (by exact_mod_cast ENat.coe_lt_top n) hU.uniqueDiffOn).congr
          (fun y hy => (iteratedFDerivWithin_of_isOpen n hU hy).symm)
      change coordDeriv (i 0) (iteratedCoordinateDerivative n (Fin.tail i) f) x = _
      exact (DFunLike.congr_fun hEq.fderiv_eq (axis (i 0))).trans
        (((hD x hx).differentiableAt (hU.mem_nhds hx)).iteratedFDeriv_succ_apply_left' (m := axis ∘ i)).symm

theorem norm_coordinateDerivative_le_norm_iteratedFDeriv {Ω : Set Point}
    (hΩ : IsOpen Ω) {f : Point → E} (hf : ContDiffOn ℝ ∞ f Ω)
    (k : ℕ) (i : Fin k → Fin 3) {x : Point} (hx : x ∈ Ω) :
    ‖iteratedCoordinateDerivative k i f x‖ ≤ ‖iteratedFDeriv ℝ k f x‖ := by
  rw [iteratedCoordinateDerivative_eq_iteratedFDeriv hΩ hf k i hx]
  refine ((iteratedFDeriv ℝ k f x).le_opNorm (axis ∘ i)).trans_eq ?_
  have h : (∏ s, ‖axis (i s)‖) = 1 := Finset.prod_eq_one fun _ _ => by simp [axis]
  rw [show (axis ∘ i) = fun j => axis (i j) from rfl, h, mul_one]

theorem iteratedCoordinateDerivative_congr_open
    {U : Set Point} (hU : IsOpen U) {f g : Point → E} (h : EqOn f g U)
    (n : ℕ) (i : Fin n → Fin 3) :
    EqOn (iteratedCoordinateDerivative n i f) (iteratedCoordinateDerivative n i g) U := by
  induction n with
  | zero => exact h
  | succ n ih =>
      intro x hx
      have he : iteratedCoordinateDerivative n (Fin.tail i) f =ᶠ[𝓝 x]
        iteratedCoordinateDerivative n (Fin.tail i) g := by
        filter_upwards [hU.mem_nhds hx] with y hy using ih (Fin.tail i) hy
      exact DFunLike.congr_fun he.fderiv_eq (axis (i 0))

theorem iteratedCoordinateDerivative_snoc (n : ℕ) (i : Fin n → Fin 3) (j : Fin 3) (f : Point → E) :
    iteratedCoordinateDerivative (n + 1) (Fin.snoc i j) f =
      iteratedCoordinateDerivative n i (coordDeriv j f) := by
  induction n with
  | zero =>
      rw [Fin.snoc_zero]
      rfl
  | succ n ih =>
      have h0 : (Fin.snoc i j : Fin (n + 2) → Fin 3) 0 = i 0 := by simp
      have hTail : Fin.tail (Fin.snoc i j : Fin (n + 2) → Fin 3) =
          (Fin.snoc (Fin.tail i) j : Fin (n + 1) → Fin 3) := by
        funext k
        refine Fin.lastCases ?_ (fun l => ?_) k
        · simp [Fin.tail]
        · simp only [Fin.tail, Fin.succ_castSucc, Fin.snoc_castSucc]
      let p : Fin (n + 2) → Fin 3 := Fin.snoc i j
      change coordDeriv (p 0) (iteratedCoordinateDerivative (n + 1) (Fin.tail p) f) =
        coordDeriv (i 0) (iteratedCoordinateDerivative n (Fin.tail i) (coordDeriv j f))
      dsimp only [p]
      rw [h0, hTail, ih]

theorem iteratedCoordinateDerivative_compCLM {U : Set Point} (hU : IsOpen U) {f : Point → E}
    (hf : ContDiffOn ℝ ∞ f U) (L : E →L[ℝ] F) (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ U) :
    iteratedCoordinateDerivative n i (L ∘ f) x = L (iteratedCoordinateDerivative n i f x) := by
  rw [iteratedCoordinateDerivative_eq_iteratedFDeriv hU (L.contDiff.comp_contDiffOn hf) n i hx,
    iteratedCoordinateDerivative_eq_iteratedFDeriv hU hf n i hx]
  have h := L.iteratedFDeriv_comp_left (((contDiffOn_infty.mp hf) n x hx).contDiffAt (hU.mem_nhds hx))
    (i := n) le_rfl
  exact DFunLike.congr_fun h (axis ∘ i)

theorem iteratedCoordinateDerivative_const_smul {U : Set Point} (hU : IsOpen U) {f : Point → E}
    (hf : ContDiffOn ℝ ∞ f U) (a : ℝ) (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ U) :
    iteratedCoordinateDerivative n i (fun y => a • f y) x = a • iteratedCoordinateDerivative n i f x :=
  iteratedCoordinateDerivative_compCLM hU hf (a • ContinuousLinearMap.id ℝ E) n i hx

theorem iteratedCoordinateDerivative_const (n : ℕ) (hn : n ≠ 0) (i : Fin n → Fin 3) (c : E) (x : Point) :
    iteratedCoordinateDerivative n i (fun _ : Point => c) x = 0 := by
  rw [iteratedCoordinateDerivative_eq_iteratedFDeriv isOpen_univ contDiffOn_const n i (mem_univ x),
    iteratedFDeriv_const_of_ne hn, Pi.zero_apply, zero_apply]

theorem iteratedCoordinateDerivative_add {U : Set Point} (hU : IsOpen U) {f g : Point → E}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ U) :
    iteratedCoordinateDerivative n i (fun y => f y + g y) x =
      iteratedCoordinateDerivative n i f x + iteratedCoordinateDerivative n i g x := by
  have h := fun_iteratedFDeriv_add_apply (((contDiffOn_infty.mp hf) n x hx).contDiffAt (hU.mem_nhds hx))
    (((contDiffOn_infty.mp hg) n x hx).contDiffAt (hU.mem_nhds hx))
  rw [iteratedCoordinateDerivative_eq_iteratedFDeriv hU (hf.add hg) n i hx,
    iteratedCoordinateDerivative_eq_iteratedFDeriv hU hf n i hx,
    iteratedCoordinateDerivative_eq_iteratedFDeriv hU hg n i hx]
  exact DFunLike.congr_fun h (axis ∘ i)

theorem iteratedCoordinateDerivative_sub {U : Set Point} (hU : IsOpen U) {f g : Point → E}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ U) :
    iteratedCoordinateDerivative n i (fun y => f y - g y) x =
      iteratedCoordinateDerivative n i f x - iteratedCoordinateDerivative n i g x := by
  rw [show (fun y => f y - g y) = fun y => f y + -g y from funext fun y => sub_eq_add_neg (f y) (g y)]
  rw [iteratedCoordinateDerivative_add hU hf hg.neg n i hx]
  have he : (fun y => -g y) = fun y => (-1 : ℝ) • g y :=
    funext fun y => (neg_one_smul ℝ (g y)).symm
  rw [he, iteratedCoordinateDerivative_const_smul hU hg _ n i hx, neg_one_smul, sub_eq_add_neg]

theorem iteratedCoordinateDerivative_prod_mk {U : Set Point} (hU : IsOpen U)
    {f : Point → E} {g : Point → F} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ U) :
    iteratedCoordinateDerivative n i (fun y => (f y, g y)) x =
      (iteratedCoordinateDerivative n i f x, iteratedCoordinateDerivative n i g x) := by
  exact Prod.ext
    (iteratedCoordinateDerivative_compCLM hU (hf.prodMk hg) (ContinuousLinearMap.fst ℝ E F) n i hx).symm
    (iteratedCoordinateDerivative_compCLM hU (hf.prodMk hg) (ContinuousLinearMap.snd ℝ E F) n i hx).symm

theorem iteratedCoordinateDerivative_pi_apply {ι : Type*} [Fintype ι]
    {U : Set Point} (hU : IsOpen U) {f : Point → ι → E} (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ U) (j : ι) :
    iteratedCoordinateDerivative n i f x j = iteratedCoordinateDerivative n i (fun y => f y j) x :=
  (iteratedCoordinateDerivative_compCLM hU hf (ContinuousLinearMap.proj (R := ℝ) j) n i hx).symm

private theorem laplacian_iteratedCoordinateDerivative_aux
    (hSingle : ∀ {U : Set Point}, IsOpen U → ∀ {f : Point → E}, ContDiffOn ℝ ∞ f U →
      ∀ {x : Point}, x ∈ U → ∀ i : Fin 3, laplacian (coordDeriv i f) x = coordDeriv i (laplacian f) x)
    {U : Set Point} (hU : IsOpen U) {f : Point → E} (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ U) :
    laplacian (iteratedCoordinateDerivative n i f) x = iteratedCoordinateDerivative n i (laplacian f) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      have he : laplacian (iteratedCoordinateDerivative n (Fin.tail i) f) =ᶠ[𝓝 x]
          iteratedCoordinateDerivative n (Fin.tail i) (laplacian f) := by
        filter_upwards [hU.mem_nhds hx] with y hy using ih (Fin.tail i) hy
      exact (hSingle hU (contDiffOn_iteratedCoordinateDerivative hU hf n (Fin.tail i)) hx (i 0)).trans
        (DFunLike.congr_fun he.fderiv_eq (axis (i 0)))

private theorem scalar_laplacian_coordDeriv_comm {U : Set Point} (hU : IsOpen U)
    {f : Point → ℝ} (hf : ContDiffOn ℝ ∞ f U) {x : Point} (hx : x ∈ U) (i : Fin 3) :
    laplacian (coordDeriv i f) x = coordDeriv i (laplacian f) x := by
  let N : S0 := frobeniusCoordinateEquiv.symm (EuclideanSpace.single (0 : Fin 5) (1 : ℝ))
  have hNorm : ‖N‖ = 1 := by
    rw [show N = frobeniusCoordinateEquiv.symm (EuclideanSpace.single (0 : Fin 5) (1 : ℝ)) from rfl,
      LinearIsometryEquiv.norm_map]
    change ‖PiLp.single 2 (β := fun _ : Fin 5 => ℝ) (0 : Fin 5) (1 : ℝ)‖ = 1
    rw [PiLp.norm_single, norm_one]
  have hN : N ≠ 0 := norm_pos_iff.mp (hNorm ▸ zero_lt_one)
  let L : ℝ →L[ℝ] S0 := (ContinuousLinearMap.id ℝ ℝ).smulRight N
  have hL : Function.Injective L := fun a b hab => by
    have h : a • N = b • N := hab
    have hZ : (a - b) • N = 0 := (sub_smul a b N).trans (sub_eq_zero.mpr h)
    exact sub_eq_zero.mp ((smul_eq_zero.mp hZ).resolve_right hN)
  let F₀ (y : Point) := L (f y)
  have hF : ContDiffOn ℝ ∞ F₀ U := L.contDiff.comp_contDiffOn hf
  have h₂ : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hD (g : Point → ℝ) (hg : ContDiffOn ℝ ∞ g U) :
      EqOn (coordDeriv i (fun y => L (g y))) (fun y => L (coordDeriv i g y)) U := by
    intro y hy
    have hG := (hg.differentiableOn (by simp) y hy).differentiableAt (hU.mem_nhds hy)
    exact DFunLike.congr_fun (L.hasFDerivAt.comp y hG.hasFDerivAt).fderiv (axis i)
  have hLapl (g : Point → ℝ) (hg : ContDiffOn ℝ ∞ g U) :
      EqOn (laplacian (fun y => L (g y))) (fun y => L (laplacian g y)) U :=
    fun _ hy => laplacian_compCLM hU (hg.of_le h₂) hy L
  have hEq : coordDeriv i F₀ =ᶠ[𝓝 x] (fun y => L (coordDeriv i f y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy using hD f hf hy
  have hLapEq : laplacian (coordDeriv i F₀) x = laplacian (fun y => L (coordDeriv i f y)) x := by
    have hd := eventually_eventually_nhds.mpr hEq
    unfold laplacian
    apply Finset.sum_congr rfl
    intro j _
    have hD' : coordDeriv j (coordDeriv i F₀) =ᶠ[𝓝 x] coordDeriv j (fun y => L (coordDeriv i f y)) :=
      hd.mono fun y hy => DFunLike.congr_fun (Filter.EventuallyEq.fderiv_eq hy) (axis j)
    exact DFunLike.congr_fun hD'.fderiv_eq (axis j)
  have hR : laplacian F₀ =ᶠ[𝓝 x] (fun y => L (laplacian f y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy using hLapl f hf hy
  apply hL
  calc
    _ = laplacian (fun y => L (coordDeriv i f y)) x := (hLapl _ (contDiffOn_coordDeriv_infty hU hf i) hx).symm
    _ = laplacian (coordDeriv i F₀) x := hLapEq.symm
    _ = coordDeriv i (laplacian F₀) x := laplacian_coordDeriv_comm hU hF hx i
    _ = coordDeriv i (fun y => L (laplacian f y)) x := DFunLike.congr_fun hR.fderiv_eq (axis i)
    _ = _ := hD _ (contDiffOn_classical_laplacian_infty hU hf) hx

theorem laplacian_iteratedCoordinateDerivative_tensor {U : Set Point} (hU : IsOpen U)
    {f : Point → S0} (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ U) :
    laplacian (iteratedCoordinateDerivative n i f) x = iteratedCoordinateDerivative n i (laplacian f) x :=
  laplacian_iteratedCoordinateDerivative_aux (fun {_} hV {_} hG {_} hy j => laplacian_coordDeriv_comm hV hG hy j)
    hU hf n i hx

theorem laplacian_iteratedCoordinateDerivative_scalar {U : Set Point} (hU : IsOpen U)
    {f : Point → ℝ} (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ U) :
    laplacian (iteratedCoordinateDerivative n i f) x = iteratedCoordinateDerivative n i (laplacian f) x :=
  laplacian_iteratedCoordinateDerivative_aux (fun {_} hV {_} hG {_} hy j => scalar_laplacian_coordDeriv_comm hV hG hy j)
    hU hf n i hx

/-- Coordinate bounds control the operator norm of an actual derivative,
with a finite factor depending only on the order. -/
theorem norm_iteratedFDeriv_le_of_coordinateBounds {U : Set Point} (hU : IsOpen U)
    {f : Point → E} (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) {x : Point} (hx : x ∈ U)
    {B : ℝ} (hB : 0 ≤ B) (h : ∀ i : Fin n → Fin 3, ‖iteratedCoordinateDerivative n i f x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ (3 : ℝ) ^ n * B := by
  classical
  let T := iteratedFDeriv ℝ n f x
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) hB)
  intro v
  have hExp (j : Fin n) : (∑ k : Fin 3, v j k • axis k) = v j := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, axis] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (v j)
  have hSum : T v = ∑ i : Fin n → Fin 3, (∏ j, v j (i j)) • T (axis ∘ i) := by
    calc
      _ = T (fun j => ∑ k : Fin 3, v j k • axis k) := congrArg T (funext hExp).symm
      _ = _ := by
        change T.toMultilinearMap (fun j => ∑ k : Fin 3, v j k • axis k) = _
        rw [MultilinearMap.map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact T.toMultilinearMap.map_smul_univ (fun j => v j (i j)) (axis ∘ i)
  rw [hSum]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin n → Fin 3, B * ∏ j, ‖v j‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, norm_prod]
      calc
        _ ≤ (∏ j, ‖v j‖) * B := by
          apply mul_le_mul (Finset.prod_le_prod (fun _ _ => norm_nonneg _) _) _ (norm_nonneg _) (by positivity)
          · exact fun j _ => PiLp.norm_apply_le (v j) (i j)
          · rw [← iteratedCoordinateDerivative_eq_iteratedFDeriv hU hf n i hx]
            exact h i
        _ = _ := mul_comm _ _
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      ring

private theorem partSize_lt_of_one_lt_length {n : ℕ} (c : OrderedFinpartition n)
    (hc : 1 < c.length) (i : Fin c.length) : c.partSize i < n := by
  letI : Nontrivial (Fin c.length) := Fin.nontrivial_iff_two_le.mpr hc
  obtain ⟨j, hji⟩ := exists_ne i
  let k : Fin (c.partSize j) := ⟨0, c.partSize_pos j⟩
  have hNot : ¬ Function.Surjective (c.emb i) := by
    intro h
    obtain ⟨l, hl⟩ := h (c.emb j k)
    have hD := c.disjoint (Set.mem_univ j) (Set.mem_univ i) hji
    exact Set.disjoint_left.mp hD ⟨k, rfl⟩ ⟨l, hl⟩
  simpa only [Fintype.card_fin] using
    Fintype.card_lt_of_injective_not_surjective (c.emb i) (c.emb_strictMono i).injective hNot

/-- In composition, the term with highest inner derivative occurs linearly.
All other terms are bounded using the lower inner derivatives. -/
theorem norm_iteratedFDeriv_comp_le_linear_top {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} {x : E} {n : ℕ} (hn : 0 < n)
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g (f x)) {C M : ℝ}
    (hC : 0 ≤ C) (hM : 1 ≤ M)
    (hG : ∀ j ≤ n, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ C)
    (hF : ∀ j < n, ‖iteratedFDeriv ℝ j f x‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤
      (Fintype.card (OrderedFinpartition n) : ℝ) * (C * M ^ n) * (1 + ‖iteratedFDeriv ℝ n f x‖) := by
  classical
  rw [iteratedFDeriv_comp hg hf le_rfl]
  let X := ‖iteratedFDeriv ℝ n f x‖
  have hX : 0 ≤ X := norm_nonneg _
  have hMx : 1 ≤ M * (1 + X) := by nlinarith only [hM, hX, mul_nonneg (sub_nonneg.mpr hM) hX]
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  have hProd (c : OrderedFinpartition n) :
      ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) f x‖ ≤ M ^ n * (1 + X) := by
    by_cases hc : 1 < c.length
    · calc
        _ ≤ ∏ _i : Fin c.length, M := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun i _ => hF _ (partSize_lt_of_one_lt_length c hc i))
        _ = M ^ c.length := by simp
        _ ≤ M ^ n := pow_le_pow_right₀ hM c.length_le
        _ ≤ _ := le_mul_of_one_le_right (pow_nonneg hM₀ n) (by linarith)
    · have hL : c.length ≤ 1 := le_of_not_gt hc
      calc
        _ ≤ ∏ _i : Fin c.length, M * (1 + X) := by
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro i _
          rcases (c.partSize_le i).lt_or_eq with hlt | heq
          · exact (hF _ hlt).trans (le_mul_of_one_le_right hM₀ (by linarith))
          · rw [heq]
            exact (le_add_of_nonneg_left (zero_le_one : 0 ≤ (1 : ℝ))).trans
              (le_mul_of_one_le_left (by linarith) hM)
        _ = (M * (1 + X)) ^ c.length := by simp
        _ ≤ (M * (1 + X)) ^ 1 := pow_le_pow_right₀ hMx hL
        _ ≤ _ := by
          rw [pow_one]
          have hMn : M ≤ M ^ n := by
            simpa only [pow_one] using pow_le_pow_right₀ hM (Nat.one_le_iff_ne_zero.mpr hn.ne')
          exact mul_le_mul_of_nonneg_right hMn (by linarith)
  unfold FormalMultilinearSeries.taylorComp
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _c : OrderedFinpartition n, C * M ^ n * (1 + X) := by
      apply Finset.sum_le_sum
      intro c _
      refine (c.norm_compAlongOrderedFinpartition_le _ _).trans ?_
      rw [mul_assoc]
      apply mul_le_mul (hG _ c.length_le) (hProd c) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hC
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, X]; ring

/-- Smooth composition on a bounded range has a uniform bound affine in the
largest derivative, when all lower coordinate derivatives are bounded. -/
theorem exists_coordinateDerivative_comp_bound [ProperSpace F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (g : F → G) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    ∃ C > (0 : ℝ), ∀ {U : Set Point}, IsOpen U → ∀ {f : Point → F},
      ContDiffOn ℝ ∞ f U → ∀ x ∈ U, ‖f x‖ ≤ M →
      (∀ k < n, ∀ i : Fin k → Fin 3, ‖iteratedCoordinateDerivative k i f x‖ ≤ M) →
      ∀ X : ℝ, 0 ≤ X → (∀ i : Fin n → Fin 3, ‖iteratedCoordinateDerivative n i f x‖ ≤ X) →
        ∀ i : Fin n → Fin 3, ‖iteratedCoordinateDerivative n i (g ∘ f) x‖ ≤ C * (1 + X) := by
  classical
  have hUniform (k : Fin (n + 1)) : ∃ C : ℝ, ∀ y ∈ closedBall (0 : F) M, ‖iteratedFDeriv ℝ k.val g y‖ ≤ C :=
    (isCompact_closedBall _ _).exists_bound_of_continuousOn
      ((hg.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).continuousOn)
  choose C hC using hUniform
  let K := 1 + ∑ k : Fin (n + 1), max (C k) 0
  have hK : 0 < K := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun k _ => le_max_right (C k) 0)
  have hUni (k : ℕ) (hk : k ≤ n) (y : F) (hy : ‖y‖ ≤ M) : ‖iteratedFDeriv ℝ k g y‖ ≤ K := by
    let j : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    exact (hC j y (mem_closedBall_zero_iff.mpr hy)).trans
      ((le_max_left _ _).trans ((Finset.single_le_sum (fun p _ => le_max_right (C p) 0) (Finset.mem_univ j)).trans
        (le_add_of_nonneg_left zero_le_one)))
  let A := (3 : ℝ) ^ n
  have hA : 1 ≤ A := by
    dsimp only [A]
    simpa only [pow_zero] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.zero_le n)
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  let B := (Fintype.card (OrderedFinpartition n) : ℝ) * (K * (A * M) ^ n) * A
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨K + B, by positivity, ?_⟩
  intro U hU f hf x hx hFx hLow X hX hTop i
  have hGc := hg.comp_contDiffOn hf
  rcases eq_zero_or_pos n with hn | hn
  · subst n
    have h₀ : ‖g (f x)‖ ≤ K := by simpa only [norm_iteratedFDeriv_zero] using hUni 0 le_rfl (f x) hFx
    exact h₀.trans ((le_add_of_nonneg_right hB).trans (le_mul_of_one_le_right (by positivity) (by linarith)))
  have hL (k : ℕ) (hk : k < n) : ‖iteratedFDeriv ℝ k f x‖ ≤ A * M :=
    (norm_iteratedFDeriv_le_of_coordinateBounds hU hf k hx hM₀ (hLow k hk)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk.le) hM₀)
  have hT := norm_iteratedFDeriv_le_of_coordinateBounds hU hf n hx hX hTop
  have hM' : 1 ≤ A * M := le_mul_of_one_le_right (zero_le_one.trans hA) hM |>.trans' hA
  have hComp := norm_iteratedFDeriv_comp_le_linear_top hn
    (((contDiffOn_infty.mp hf) n x hx).contDiffAt (hU.mem_nhds hx))
    ((contDiff_infty.mp hg) n |>.contDiffAt) hK.le hM'
    (fun k hk => hUni k hk (f x) hFx) hL
  rw [iteratedCoordinateDerivative_eq_iteratedFDeriv hU hGc n i hx]
  have hAxes : (∏ j, ‖axis (i j)‖) = 1 := Finset.prod_eq_one fun _ _ => by simp [axis]
  refine ((iteratedFDeriv ℝ n (g ∘ f) x).le_opNorm (axis ∘ i)).trans ?_
  change ‖iteratedFDeriv ℝ n (g ∘ f) x‖ * (∏ j, ‖axis (i j)‖) ≤ _
  rw [hAxes, mul_one]
  have hC₀ : 0 ≤ (Fintype.card (OrderedFinpartition n) : ℝ) * (K * (A * M) ^ n) := by positivity
  have hAdd : 1 + ‖iteratedFDeriv ℝ n f x‖ ≤ A * (1 + X) := by
    rw [mul_add, mul_one]
    exact add_le_add hA hT
  exact (hComp.trans ((mul_le_mul_of_nonneg_left hAdd hC₀).trans_eq (by dsimp only [B]; ring))).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK.le) (by linarith))

end Thesis

end
