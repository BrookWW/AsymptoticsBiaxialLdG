module

public import Thesis.Variational.ClosedConvexDerivativeColumns
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Recovery of the pure normal columns from the flattened equation. -/

public section

noncomputable section

open Filter Function Set Topology
open scoped ContDiff

namespace Thesis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {S : Set Point}

private def closedDerivativeColumn (S : Set Point) (i : Fin 3) (v : Point → F) : Point → F :=
  fun x => fderivWithin ℝ v (closure S) x (axis i)

private theorem contDiffOn_closedDerivativeColumn (k : ℕ) {v : Point → F}
    (hUd : UniqueDiffOn ℝ (closure S)) (hv : ContDiffOn ℝ (↑(k+1) : ℕ∞ω) v (closure S))
    (i : Fin 3) :
    ContDiffOn ℝ (k : ℕ∞ω) (closedDerivativeColumn S i v) (closure S) :=
  ((ContinuousLinearMap.apply ℝ F (axis i)).contDiff.comp_contDiffOn
    (hv.fderivWithin hUd (by exact_mod_cast (Nat.le_refl (k+1)))))

private theorem closedDerivativeColumn_eqOn (hS : IsOpen S) (i : Fin 3) (v : Point → F) :
    EqOn (closedDerivativeColumn S i v) (coordDeriv i v) S := by
  intro x hx
  change fderivWithin ℝ v (closure S) x (axis i) = fderiv ℝ v x (axis i)
  rw [fderivWithin_of_mem_nhds (mem_of_superset (hS.mem_nhds hx) subset_closure)]

private theorem coordDeriv_eq_of_eqOn_open {v w : Point → F} (hS : IsOpen S)
    (he : EqOn v w S) (i : Fin 3) : EqOn (coordDeriv i v) (coordDeriv i w) S := by
  intro x hx
  have hNear : v =ᶠ[𝓝 x] w := mem_of_superset (hS.mem_nhds hx) he
  exact DFunLike.congr_fun (hNear.fderiv_eq (𝕜 := ℝ)) (axis i)

private theorem closedDerivativeColumn_eqOn_actual_of_extension {v w : Point → F}
    (hS : IsOpen S) (h : EqOn v w S) (i : Fin 3) :
    EqOn (closedDerivativeColumn S i v) (coordDeriv i w) S :=
  (closedDerivativeColumn_eqOn hS i v).trans (coordDeriv_eq_of_eqOn_open hS h i)

/-- Tangential derivative extensions and a pure normal second derivative
extension reconstruct the next full derivative at the wall. -/
theorem contDiffOn_of_tangential_regular_normal_entry
    (hS : IsOpen S) (hConv : Convex ℝ S) (hNe : S.Nonempty) (k : ℕ)
    {u : Point → F} (hu : ContDiffOn ℝ 1 u (closure S)) (huI : ContDiffOn ℝ 2 u S)
    (T : Fin 3 → Point → F)
    (hT : ∀ j ≠ 2, ContDiffOn ℝ (↑(k+1) : ℕ∞ω) (T j) (closure S) ∧
      EqOn (T j) (coordDeriv j u) S)
    {N : Point → F} (hN : ContDiffOn ℝ (k : ℕ∞ω) N (closure S))
    (hNeq : EqOn N (coordDeriv 2 (coordDeriv 2 u)) S) :
    ContDiffOn ℝ (↑(k+2) : ℕ∞ω) u (closure S) := by
  let L := closedDerivativeColumn S 2 u
  have hUd := uniqueDiffOn_closure_of_open_convex hS hConv hNe
  have hLc : ContinuousOn L (closure S) :=
    ((ContinuousLinearMap.apply ℝ F (axis 2)).continuous.comp_continuousOn
      (hu.continuousOn_fderivWithin hUd le_rfl))
  have hLe : EqOn L (coordDeriv 2 u) S := closedDerivativeColumn_eqOn hS 2 u
  have hDeriv (j : Fin 3) : ContDiffOn ℝ 1 (coordDeriv j u) S :=
    ((ContinuousLinearMap.apply ℝ F (axis j)).contDiff.comp_contDiffOn
      (huI.fderiv_of_isOpen hS (by norm_num)))
  have hLI : DifferentiableOn ℝ L S := ((hDeriv 2).congr hLe).differentiableOn one_ne_zero
  let G (j : Fin 3) : Point → F := if j = 2 then N else closedDerivativeColumn S 2 (T j)
  have hG (j : Fin 3) : ContDiffOn ℝ (k : ℕ∞ω) (G j) (closure S) := by
    by_cases he : j = 2
    · simpa only [G,if_pos he] using hN
    · simpa only [G,if_neg he] using contDiffOn_closedDerivativeColumn k hUd (hT j he).1 2
  have heG (j : Fin 3) : EqOn (G j) (coordDeriv j L) S := by
    have he := coordDeriv_eq_of_eqOn_open hS hLe j
    by_cases hj : j = 2
    · subst j
      simpa only [G,if_pos rfl] using hNeq.trans he.symm
    · intro x hx
      have hTwice := (closedDerivativeColumn_eqOn_actual_of_extension hS (hT j hj).2 2) hx
      have hm := coordDeriv_mixed_commute_of_contDiffAt_two ((huI x hx).contDiffAt (hS.mem_nhds hx)) 2 j
      exact (show G j x = closedDerivativeColumn S 2 (T j) x by simp only [G,if_neg hj]).trans
        (hTwice.trans (hm.trans (he hx).symm))
  have hLC := (contDiffOn_succ_of_closed_convex_derivative_columns hS hConv hNe k hLc hLI G hG heG).1
  let J (j : Fin 3) := if j = 2 then L else T j
  have hJ (j : Fin 3) : ContDiffOn ℝ (↑(k+1) : ℕ∞ω) (J j) (closure S) := by
    by_cases hj : j = 2
    · simpa only [J,if_pos hj] using hLC
    · simpa only [J,if_neg hj] using (hT j hj).1
  have heJ (j : Fin 3) : EqOn (J j) (coordDeriv j u) S := by
    by_cases hj : j = 2
    · subst j
      simpa only [J,if_pos rfl] using hLe
    · simpa only [J,if_neg hj] using (hT j hj).2
  exact (contDiffOn_succ_of_closed_convex_derivative_columns hS hConv hNe (k+1) hu.continuousOn
    (huI.differentiableOn two_ne_zero) J hJ heJ).1

private theorem sum_normal_entry (A : Fin 3 → Fin 3 → ℝ) (M : F) :
    (∑ i : Fin 3, ∑ j : Fin 3, A i j • (if i = 2 ∧ j = 2 then M else 0)) = A 2 2 • M := by
  simp [Fin.sum_univ_three]

/-- A nonzero pure normal coefficient in the flattened equation determines the
missing normal entry and recovers one classical derivative at the wall. -/
theorem contDiffOn_of_tangential_regular_nondivergence
    (hS : IsOpen S) (hConv : Convex ℝ S) (hNe : S.Nonempty) (k : ℕ)
    {u : Point → F} (hu : ContDiffOn ℝ (↑(k+1) : ℕ∞ω) u (closure S))
    (huI : ContDiffOn ℝ 2 u S)
    (T : Fin 3 → Point → F)
    (hT : ∀ j ≠ 2, ContDiffOn ℝ (↑(k+1) : ℕ∞ω) (T j) (closure S) ∧
      EqOn (T j) (coordDeriv j u) S)
    (A : Fin 3 → Fin 3 → Point → ℝ) (B : Fin 3 → Point → ℝ) {f : Point → F}
    (hA : ∀ i j, ContDiffOn ℝ (k : ℕ∞ω) (A i j) (closure S))
    (hB : ∀ i, ContDiffOn ℝ (k : ℕ∞ω) (B i) (closure S))
    (hf : ContDiffOn ℝ (k : ℕ∞ω) f (closure S))
    (hA22 : ∀ x ∈ closure S, A 2 2 x ≠ 0)
    (hEq : ∀ x ∈ S,
      (∑ i : Fin 3, ∑ j : Fin 3, A i j x • coordDeriv i (coordDeriv j u) x) +
        ∑ i : Fin 3, B i x • coordDeriv i u x = f x) :
    ContDiffOn ℝ (↑(k+2) : ℕ∞ω) u (closure S) := by
  have hUd := uniqueDiffOn_closure_of_open_convex hS hConv hNe
  let H (i j : Fin 3) : Point → F :=
    if j = 2 then
      if i = 2 then 0 else closedDerivativeColumn S 2 (T i)
    else closedDerivativeColumn S i (T j)
  have hH (i j : Fin 3) : ContDiffOn ℝ (k : ℕ∞ω) (H i j) (closure S) := by
    by_cases hj : j = 2
    · by_cases hi : i = 2
      · simp only [H,if_pos hj,if_pos hi]
        exact contDiffOn_const
      · simpa only [H,if_pos hj,if_neg hi] using contDiffOn_closedDerivativeColumn k hUd (hT i hi).1 2
    · simpa only [H,if_neg hj] using contDiffOn_closedDerivativeColumn k hUd (hT j hj).1 i
  let P (x : Point) := ∑ i : Fin 3, ∑ j : Fin 3, A i j x • H i j x
  let Q (x : Point) := ∑ i : Fin 3, B i x • closedDerivativeColumn S i u x
  let N (x : Point) := (A 2 2 x)⁻¹ • (f x - P x - Q x)
  have hP : ContDiffOn ℝ (k : ℕ∞ω) P (closure S) :=
    ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hA i j).smul (hH i j)
  have hQ : ContDiffOn ℝ (k : ℕ∞ω) Q (closure S) :=
    ContDiffOn.sum fun i _ => (hB i).smul (contDiffOn_closedDerivativeColumn k hUd hu i)
  have hN : ContDiffOn ℝ (k : ℕ∞ω) N (closure S) :=
    ((hA 2 2).inv hA22).smul ((hf.sub hP).sub hQ)
  have heN : EqOn N (coordDeriv 2 (coordDeriv 2 u)) S := by
    intro x hx
    let M := coordDeriv 2 (coordDeriv 2 u) x
    have hEntry (i j : Fin 3) : coordDeriv i (coordDeriv j u) x =
        H i j x + if i = 2 ∧ j = 2 then M else 0 := by
      by_cases hj : j = 2
      · by_cases hi : i = 2
        · subst i; subst j
          simp [H,M]
        · subst j
          have he := (closedDerivativeColumn_eqOn_actual_of_extension hS (hT i hi).2 2) hx
          have hEq := coordDeriv_mixed_commute_of_contDiffAt_two ((huI x hx).contDiffAt (hS.mem_nhds hx)) i 2
          simpa [H,hi] using hEq.trans he.symm
      · have he := (closedDerivativeColumn_eqOn_actual_of_extension hS (hT j hj).2 i) hx
        simpa [H,hj] using he.symm
    have hPrincipal : (∑ i : Fin 3, ∑ j : Fin 3, A i j x • coordDeriv i (coordDeriv j u) x) =
        P x + A 2 2 x • M := by
      simp_rw [hEntry,smul_add,Finset.sum_add_distrib]
      exact congrArg (P x + ·) (sum_normal_entry (fun i j => A i j x) M)
    have hLower : (∑ i : Fin 3, B i x • coordDeriv i u x) = Q x := by
      exact Finset.sum_congr rfl fun i _ => congrArg (B i x • ·) ((closedDerivativeColumn_eqOn hS i u) hx).symm
    have hData := hEq x hx
    rw [hPrincipal,hLower] at hData
    have hR : f x - P x - Q x = A 2 2 x • M := by rw [← hData]; abel
    change (A 2 2 x)⁻¹ • (f x - P x - Q x) = M
    rw [hR,smul_smul,inv_mul_cancel₀ (hA22 x (subset_closure hx)),one_smul]
  have hu1 : ContDiffOn ℝ 1 u (closure S) := hu.of_le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k)))
  exact contDiffOn_of_tangential_regular_normal_entry hS hConv hNe k hu1 huI T hT hN heN

end Thesis
