module

public import SupportingAnalysis.Euclidean

/-! The Euclidean Laplacian of the exponential lift with one auxiliary variable. -/

@[expose] public section

open Filter Set
open scoped Topology ContDiff Laplacian

set_option autoImplicit false

namespace SupportingAnalysis

/-- The Euclidean orthogonal product with the auxiliary real axis. -/
abbrev MeanLiftSpace (m : ℕ) := WithLp 2 (E m × ℝ)

/-- The scalar exponential lift of a function on the spatial ball. -/
noncomputable def subsolutionMeanLift {m : ℕ} (k : ℝ) (f : E m → ℝ) (p : MeanLiftSpace m) : ℝ :=
  Real.exp (k*p.snd) * f p.fst

theorem contDiffAt_subsolutionMeanLift {m : ℕ} {n : ℕ∞ω} (k : ℝ) {f : E m → ℝ} {p : MeanLiftSpace m}
    (hf : ContDiffAt ℝ n f p.fst) : ContDiffAt ℝ n (subsolutionMeanLift k f) p := by
  have hfst : ContDiffAt ℝ n (fun q : MeanLiftSpace m => q.fst) p :=
    (WithLp.fstL 2 ℝ (E m) ℝ).contDiff.contDiffAt
  have hsnd : ContDiffAt ℝ n (fun q : MeanLiftSpace m => q.snd) p :=
    (WithLp.sndL 2 ℝ (E m) ℝ).contDiff.contDiffAt
  exact (contDiffAt_const.mul hsnd).exp.mul (hf.comp p hfst)

/-- The second derivative along a straight line is the ambient Hessian
applied twice to its velocity. -/
theorem subsolutionMean_line_second {E' F : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E' → F} {x : E'} (hf : ContDiffAt ℝ 2 f x) (v : E') :
    deriv (deriv (fun t : ℝ => f (x + t • v))) 0 = iteratedFDeriv ℝ 2 f x ![v,v] := by
  let L : ℝ → E' := fun t => x + t • v
  have hL (t : ℝ) : HasDerivAt L v t := by
    simpa only [L, id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_add x
  have hL0 : L 0 = x := by simp [L]
  have hNear : ∀ᶠ t in 𝓝 (0:ℝ), ContDiffAt ℝ 1 f (L t) := by
    have h : ∀ᶠ y in 𝓝 (L 0), ContDiffAt ℝ 1 f y := by
      rw [hL0]
      exact (hf.eventually (by decide)).mono (fun _ h => h.of_le (by norm_num))
    exact (hL 0).continuousAt.eventually h
  have hD : deriv (f ∘ L) =ᶠ[𝓝 (0:ℝ)] (fun t => fderiv ℝ f (L t) v) := by
    filter_upwards [hNear] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hL t)).deriv
  let applyV := ContinuousLinearMap.apply ℝ F v
  have hFder₁ : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  have hFder := hFder₁.differentiableAt (by norm_num)
  have hF : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
    applyV.differentiableAt.comp x hFder
  have hApply : fderiv ℝ (fun y => fderiv ℝ f y v) x v =
      fderiv ℝ (fderiv ℝ f) x v v := by
    change fderiv ℝ (applyV ∘ fderiv ℝ f) x v = _
    rw [fderiv_comp x applyV.differentiableAt hFder, applyV.fderiv]
    rfl
  have hD' := (hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hL 0) hL0.symm).congr_of_eventuallyEq hD
  change deriv (deriv (f ∘ L)) 0 = _
  rw [hD'.deriv, hApply, iteratedFDeriv_two_apply]
  rfl

private theorem subsolutionMean_exp_translate_second (k t₀ : ℝ) :
    deriv (deriv (fun t : ℝ => Real.exp (k*(t₀+t)))) 0 = k^2 * Real.exp (k*t₀) := by
  have hD : deriv (fun t : ℝ => Real.exp (k*(t₀+t))) =
      fun t => k * Real.exp (k*(t₀+t)) := by
    funext t
    have h : HasDerivAt (fun s => k*(t₀+s)) k t := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_add t₀).const_mul k
    exact h.exp.deriv.trans (mul_comm _ _)
  rw [hD, deriv_const_mul_field, hD]
  simp only [add_zero]
  ring

/-- The true Laplacian of the lift in the L² product splits into the horizontal
Laplacian and the second derivative along the new axis. -/
theorem laplacian_subsolutionMeanLift {m : ℕ} (k : ℝ) {f : E m → ℝ} {p : MeanLiftSpace m}
    (hf : ContDiffAt ℝ 2 f p.fst) :
    Laplacian.laplacian (subsolutionMeanLift k f) p =
      Real.exp (k*p.snd) * (Laplacian.laplacian f p.fst + k^2*f p.fst) := by
  classical
  let B := EuclideanSpace.basisFun (Fin m) ℝ
  let B' := B.prod (OrthonormalBasis.singleton Unit ℝ)
  let W := subsolutionMeanLift k f
  have hW : ContDiffAt ℝ 2 W p := contDiffAt_subsolutionMeanLift k hf
  have hBase (i : Fin m) :
      iteratedFDeriv ℝ 2 W p ![B' (Sum.inl i), B' (Sum.inl i)] =
        Real.exp (k*p.snd) * iteratedFDeriv ℝ 2 f p.fst ![B i,B i] := by
    have hLine : (fun t : ℝ => W (p + t • B' (Sum.inl i))) =
        fun t => Real.exp (k*p.snd) * f (p.fst+t • B i) := by
      funext t
      simp [W, subsolutionMeanLift, B', OrthonormalBasis.prod_apply]
    rw [← subsolutionMean_line_second hW, hLine, deriv_const_mul_field', deriv_const_mul_field,
      subsolutionMean_line_second hf]
  have hAxis (i : Unit) :
      iteratedFDeriv ℝ 2 W p ![B' (Sum.inr i), B' (Sum.inr i)] =
        Real.exp (k*p.snd) * (k^2 * f p.fst) := by
    have hLine : (fun t : ℝ => W (p + t • B' (Sum.inr i))) =
        fun t => Real.exp (k*(p.snd+t)) * f p.fst := by
      funext t
      simp [W, subsolutionMeanLift, B', OrthonormalBasis.prod_apply, smul_eq_mul]
    rw [← subsolutionMean_line_second hW, hLine, deriv_mul_const_field', deriv_mul_const_field,
      subsolutionMean_exp_translate_second]
    ring
  change Laplacian.laplacian W p = _
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis W B',
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f B]
  dsimp only
  rw [Fintype.sum_sum_type]
  simp only [hBase, hAxis, Finset.mul_sum, Fintype.sum_unique, mul_add]

end SupportingAnalysis
