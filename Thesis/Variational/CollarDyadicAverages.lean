module

public import Thesis.Variational.CollarRectangularSlabs

/-! The summable dyadic increments bound the normalized gradient mass
in every slab of a physical wall chart. -/

public section

open Filter MeasureTheory Metric Set Topology
open scoped ContDiff ENNReal NNReal

set_option autoImplicit false
noncomputable section

namespace Thesis

private theorem exists_dyadic_height_between {b t : ℝ} (ht : 0 < t) (htb : t ≤ b) :
    ∃ n : ℕ, t ≤ b * (1/2:ℝ)^n ∧ b * (1/2:ℝ)^n < 2*t := by
  let d (n : ℕ) := b * (1/2:ℝ)^n
  have hLim : Tendsto d atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ))
        (by norm_num : (1/2:ℝ) < 1)).const_mul b
  have h : ∃ n, d n < t := (hLim.eventually_lt tendsto_const_nhds ht).exists
  let m := Nat.find h
  have hm : d m < t := Nat.find_spec h
  have hm₀ : 0 < m := by
    by_contra! hn
    have hm0 : m = 0 := Nat.le_zero.mp hn
    have hd0 : d m = b := by simp [hm0,d]
    exact (not_lt_of_ge htb) (hd0 ▸ hm)
  let n := m-1
  have hNm : n+1=m := Nat.sub_add_cancel hm₀
  have hD : d m = d n/2 := by rw [← hNm]; dsimp only [d]; rw [pow_succ]; ring
  exact ⟨n, le_of_not_gt (Nat.find_min h (show n < m by omega)), by linarith only [hm,hD]⟩

private theorem normalized_nonnegative_integral_le
    {μ : Measure Point} [IsFiniteMeasure μ] {S : Set Point} {b : ℝ} (hb : 0 < b)
    (g : Point → ℝ) (hg : MemLp g 2 μ) :
    (∫ x in S, g x ∂μ) / b ≤
      (Real.sqrt (μ.real univ) / b) * Real.sqrt (∫ x, g x^2 ∂μ) := by
  have hs := square_integral_le_measure_mul_integral_square (hg.restrict S)
  have hM : (μ.restrict S).real univ ≤ μ.real univ := by
    rw [Measure.real,Measure.real,Measure.restrict_apply_univ]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
  have hI : (∫ x in S, g x^2 ∂μ) ≤ ∫ x, g x^2 ∂μ :=
    integral_mono_measure Measure.restrict_le_self (.of_forall fun _ => sq_nonneg _) hg.integrable_sq
  have hM₀ : 0 ≤ μ.real univ := measureReal_nonneg
  have hI₀ : 0 ≤ ∫ x in S, g x^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hB := Real.le_sqrt_of_sq_le (hs.trans (mul_le_mul hM hI hI₀ hM₀))
  rw [Real.sqrt_mul hM₀] at hB
  exact (div_le_div_of_nonneg_right hB hb.le).trans_eq (by ring)

/-- The gradient mass of every wall slab is linear in its height,
with its constant controlled by the actual fractional pair energy. -/
theorem exists_wallChartSlab_mass_le
    {U : Set Point} (hU : IsBoundedDomain U) {b r : ℝ} (hb : 0 < b) (hr : 1/2 < r)
    (Φ : WallChartPoint ≃ₜ Point) (hΦ : MeasurePreserving Φ)
    (hInside : Φ '' wallChartSlab b b ⊆ U)
    {K : ℝ≥0} (hK : 0 < (K : ℝ)) (hLip : LipschitzOnWith K Φ (wallChartClosedBox b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Point → ℝ), MemLp g 2 (volume.restrict U) → (∀ x, 0 ≤ g x) →
      scalarFractionalPairEnergy r (volume.restrict U) g < ⊤ →
      ∀ t : ℝ, 0 < t → t ≤ b →
        (∫ x in Φ '' wallChartSlab b t, g x ∂volume.restrict U) ≤ C*t*
          (Real.sqrt (∫ x in U, g x^2) +
            Real.sqrt (scalarFractionalPairEnergy r (volume.restrict U) g).toReal) := by
  let μ := volume.restrict U
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.2.2.measure_lt_top.ne
  let p := r-1/2
  have hp : 0 < p := sub_pos.mpr hr
  let q := (1/2:ℝ)^p
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq₁ : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  have hqPos : 0 < 1-q := sub_pos.mpr hq₁
  let B := Real.sqrt (μ.real univ)/b
  let A := Real.sqrt (2*(2*b)^2*(K:ℝ)^(3+2*r)) * b^p
  have hA : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hb.le _)
  have hB : 0 ≤ B := div_nonneg (Real.sqrt_nonneg _) hb.le
  let C := B + A/(1-q)
  have hC : 0 ≤ C := add_nonneg hB (div_nonneg hA hqPos.le)
  refine ⟨2*C,mul_nonneg (by norm_num) hC,?_⟩
  intro g hg hg₀ hE t ht htB
  let e := (scalarFractionalPairEnergy r μ g).toReal
  let N := Real.sqrt (∫ x, g x^2 ∂μ)+Real.sqrt e
  have hN : 0 ≤ N := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let d (n : ℕ) := b*(1/2:ℝ)^n
  let M (n : ℕ) := (∫ x in Φ '' wallChartSlab b (d n), g x ∂μ)/(d n)
  have hd (n : ℕ) : 0 < d n := mul_pos hb (pow_pos (by norm_num) n)
  have hdB (n : ℕ) : d n ≤ b := mul_le_of_le_one_right hb.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hHalf (n : ℕ) : d (n+1) = d n/2 := by dsimp only [d]; rw [pow_succ]; ring
  have hAd (n : ℕ) : d n ^ p = b^p*q^n := by
    dsimp only [d,q]
    rw [Real.mul_rpow hb.le (pow_nonneg (by norm_num) _),
      ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 1/2),
      mul_comm (n:ℝ) p, Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 1/2)]
  have hStep (n : ℕ) : M (n+1) ≤ M n + (A*Real.sqrt e)*q^n := by
    let j := 2^(n+1)
    have hj : (j:ℝ)*d n = 2*b := by
      have hP : (2:ℝ)^n * (1/2:ℝ)^n = 1 := by rw [← mul_pow,show (2:ℝ)*(1/2)=1 by norm_num,one_pow]
      dsimp only [j,d]
      rw [Nat.cast_pow,Nat.cast_ofNat,pow_succ]
      calc
        _ = 2*b*((2:ℝ)^n*(1/2:ℝ)^n) := by ring
        _ = _ := by rw [hP,mul_one]
    have h := squared_wallChartSlabAverage_difference_le hU hb Φ hΦ hInside hK hLip
      (hd n) (hdB n) j hj (by linarith : 0 < r) g hg hE
    have hR : d n ^ (2*r-1) = (d n ^ p)^2 := by
      rw [← Real.rpow_mul_natCast (hd n).le]
      congr 1
      dsimp only [p]
      ring
    have hS : (M (n+1)-M n)^2 ≤ ((A*Real.sqrt e)*q^n)^2 := by
      dsimp only [M]
      rw [hHalf]
      refine h.trans_eq ?_
      rw [hR,hAd]
      have hK₀ : 0 ≤ 2*(2*b)^2*(K:ℝ)^(3+2*r) := by positivity
      have hASq : A^2 = (2*(2*b)^2*(K:ℝ)^(3+2*r))*(b^p)^2 := by
        dsimp only [A]
        rw [mul_pow,Real.sq_sqrt hK₀]
      have hRSq : ((A*Real.sqrt e)*q^n)^2 = (A^2*e)*(q^n)^2 := by
        rw [mul_pow,mul_pow,Real.sq_sqrt (show 0 ≤ e from ENNReal.toReal_nonneg)]
      rw [hRSq,hASq]
      dsimp only [e]
      ring
    have hAbs : |M (n+1)-M n| ≤ (A*Real.sqrt e)*q^n := by
      apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (mul_nonneg hA (Real.sqrt_nonneg _)) (pow_nonneg hq.le _))).1
      rwa [sq_abs]
    linarith only [(le_abs_self (M (n+1)-M n)).trans hAbs]
  let P := A * Real.sqrt e
  have hP : 0 ≤ P := mul_nonneg hA (Real.sqrt_nonneg _)
  let F (n : ℕ) := M n + P*q^n/(1-q)
  have hF (n : ℕ) : F n ≤ F 0 := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      refine (?_ : F (n+1) ≤ F n).trans ih
      dsimp only [F]
      have h' : M (n+1) ≤ M n + P*q^n := hStep n
      refine (add_le_add h' le_rfl).trans_eq ?_
      rw [pow_succ]
      field_simp [hqPos.ne']
      ring
  have hM0 : M 0 ≤ B*Real.sqrt (∫ x, g x^2 ∂μ) := by
    dsimp only [M,d]
    rw [pow_zero,mul_one]
    exact normalized_nonnegative_integral_le hb g hg
  have hMn (n : ℕ) : M n ≤ C*N := by
    calc
      _ ≤ F n := le_add_of_nonneg_right (div_nonneg (mul_nonneg hP (pow_nonneg hq.le _)) hqPos.le)
      _ ≤ F 0 := hF n
      _ ≤ B*Real.sqrt (∫ x, g x^2 ∂μ) + (A/(1-q))*Real.sqrt e := by
        have hQ : P*q^0/(1-q) = (A/(1-q))*Real.sqrt e := by dsimp only [P]; rw [pow_zero,mul_one]; ring
        change M 0 + P*q^0/(1-q) ≤ _
        rw [hQ]
        exact add_le_add hM0 le_rfl
      _ ≤ B*N + (A/(1-q))*N :=
        add_le_add (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hB)
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.sqrt_nonneg _)) (div_nonneg hA hqPos.le))
      _ = _ := by dsimp only [C]; ring
  obtain ⟨n,htn,hnt⟩ := exists_dyadic_height_between ht htB
  have hS : Φ '' wallChartSlab b t ⊆ Φ '' wallChartSlab b (d n) :=
    image_mono (fun _ hx => ⟨hx.1,hx.2.1,hx.2.2.trans htn⟩)
  have hInt : Integrable g μ := hg.integrable (by norm_num)
  calc
    _ ≤ ∫ x in Φ '' wallChartSlab b (d n), g x ∂μ :=
      setIntegral_mono_set hInt.integrableOn (.of_forall hg₀) (Eventually.of_forall hS)
    _ ≤ (C*N)*d n := (div_le_iff₀ (hd n)).1 (hMn n)
    _ ≤ (C*N)*(2*t) := mul_le_mul_of_nonneg_left hnt.le (mul_nonneg hC hN)
    _ = _ := by ring

end Thesis

end
