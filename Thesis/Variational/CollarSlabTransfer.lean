module

public import Thesis.Definitions
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-! Comparison of adjacent collar slabs using pairs in the same
horizontal cell. -/

public section

open Filter Function MeasureTheory Metric Set Topology
open scoped BigOperators ENNReal

set_option autoImplicit false
noncomputable section

namespace Thesis

@[expose] def scalarFractionalPairEnergy (r : ℝ) (μ : Measure Point) (g : Point → ℝ) : ℝ≥0∞ :=
  ∫⁻ z : Point × Point,
    ENNReal.ofReal ((g z.1 - g z.2)^2 / dist z.1 z.2 ^ (3 + 2*r)) ∂μ.prod μ

theorem square_integral_le_measure_mul_integral_square
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {h : X → ℝ} (hh : MemLp h 2 μ) :
    (∫ x, h x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, (h x)^2 ∂μ := by
  have h' : MemLp h (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hh
  have h₁ : MemLp (fun _ : X => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := memLp_const _
  have hH : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hC := integral_mul_norm_le_Lp_mul_Lq hH h' h₁
  simp only [norm_one, mul_one, integral_const, smul_eq_mul, Real.rpow_ofNat] at hC
  rw [show (1 / 2 : ℝ) = 1/2 from rfl, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hC
  have hSqInt : 0 ≤ ∫ x, (h x)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hN : ‖∫ x, h x ∂μ‖ ≤ ∫ x, ‖h x‖ ∂μ := norm_integral_le_integral_norm _
  simp only [Real.norm_eq_abs, sq_abs, one_pow, mul_one] at hC
  have hNN : (∫ x, h x ∂μ) ^ 2 = ‖∫ x, h x ∂μ‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [hNN]
  refine (pow_le_pow_left₀ (norm_nonneg _) (hN.trans hC) 2).trans_eq ?_
  rw [mul_pow, Real.sq_sqrt, Real.sq_sqrt]
  · exact mul_comm _ _
  · exact measureReal_nonneg
  · exact hSqInt

private theorem integral_pair_sub_on_prod
    {μ : Measure Point} [IsFiniteMeasure μ] {g : Point → ℝ} (hg : Integrable g μ)
    (A B : Set Point) :
    (∫ z in B ×ˢ A, g z.1 - g z.2 ∂μ.prod μ) =
      μ.real A * (∫ x in B, g x ∂μ) - μ.real B * (∫ x in A, g x ∂μ) := by
  rw [← Measure.prod_restrict B A, integral_sub (hg.integrableOn.comp_fst _) (hg.integrableOn.comp_snd _)]
  calc
    _ = ((∫ x in B, g x ∂μ) * (μ.restrict A).real univ) -
        ((μ.restrict B).real univ * ∫ x in A, g x ∂μ) := by
      congr 1
      · simpa [integral_const,smul_eq_mul] using
          (integral_prod_mul (μ := μ.restrict B) (ν := μ.restrict A) g (fun _ => (1:ℝ)))
      · simpa [integral_const,smul_eq_mul] using
          (integral_prod_mul (μ := μ.restrict B) (ν := μ.restrict A) (fun _ => (1:ℝ)) g)
    _ = _ := by simp only [Measure.real, Measure.restrict_apply_univ]; ring

private theorem ofReal_square_pair_le_scaled_energy
    {r K d : ℝ} (hr : 0 < r) (hK : 0 < K) (hd : 0 < d)
    (g : Point → ℝ) {z : Point × Point} (hDist : dist z.1 z.2 ≤ K*d) :
    ENNReal.ofReal ((g z.1-g z.2)^2) ≤
      ENNReal.ofReal ((K*d)^(3+2*r)) *
        ENNReal.ofReal ((g z.1-g z.2)^2 / dist z.1 z.2 ^ (3+2*r)) := by
  by_cases hz : z.1 = z.2
  · simp [hz]
  have hp : 0 < dist z.1 z.2 ^ (3+2*r) := Real.rpow_pos_of_pos (dist_pos.mpr hz) _
  have hD := Real.rpow_le_rpow dist_nonneg hDist (by linarith : 0 ≤ 3+2*r)
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg hK.le hd.le) _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = dist z.1 z.2 ^ (3+2*r) * ((g z.1-g z.2)^2 / dist z.1 z.2 ^ (3+2*r)) := by
      field_simp [hp.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right hD (div_nonneg (sq_nonneg _) hp.le)

/-- The normalized slab integral changes by a controlled power at the
next dyadic scale. Volumes and distances are those of the physical cells. -/
theorem squared_slabAverage_difference_le
    {μ : Measure Point} [IsFiniteMeasure μ] {r K d L : ℝ} (hr : 0 < r) (hK : 0 < K) (hd : 0 < d)
    {ι : Type*} [Fintype ι] (hCard : (Fintype.card ι : ℝ) * d^2 = L^2)
    (A B : ι → Set Point) (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hAd : Pairwise (Disjoint on A)) (hBd : Pairwise (Disjoint on B))
    (hAV : ∀ i, μ (A i) = ENNReal.ofReal (d^3)) (hBV : ∀ i, μ (B i) = ENNReal.ofReal (d^3/2))
    (hDist : ∀ i x, x ∈ B i → ∀ y, y ∈ A i → dist x y ≤ K*d)
    (g : Point → ℝ) (hg : MemLp g 2 μ) (hE : scalarFractionalPairEnergy r μ g < ⊤) :
    ((∫ x in ⋃ i, B i, g x ∂μ)/(d/2) - (∫ x in ⋃ i, A i, g x ∂μ)/d)^2 ≤
      2 * L^2 * K^(3+2*r) * d^(2*r-1) * (scalarFractionalPairEnergy r μ g).toReal := by
  let D (i : ι) := B i ×ˢ A i
  let S := ⋃ i, D i
  let ν := (μ.prod μ).restrict S
  let w (z : Point × Point) := g z.1-g z.2
  have hw : MemLp w 2 (μ.prod μ) := (hg.comp_fst μ).sub (hg.comp_snd μ)
  have hwS : MemLp w 2 ν := hw.restrict _
  have hD (i : ι) : MeasurableSet (D i) := (hB i).prod (hA i)
  have hS : MeasurableSet S := MeasurableSet.iUnion hD
  have hDd : Pairwise (Disjoint on D) := by
    intro i j hij
    exact disjoint_left.2 (fun z hz hz' => disjoint_left.1 (hBd hij) hz.1 hz'.1)
  have hmD (i : ι) : (μ.prod μ) (D i) = ENNReal.ofReal (d^6/2) := by
    rw [Measure.prod_prod,hBV,hAV,← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hmS : ν.real univ = L^2*d^4/2 := by
    rw [Measure.real, show ν univ = (μ.prod μ) S by simp [ν], measure_iUnion hDd hD]
    simp_rw [hmD]
    rw [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal (by positivity)]
    calc
      _ = ((Fintype.card ι : ℝ)*d^2)*d^4/2 := by ring
      _ = _ := by rw [hCard]
  have hIw : Integrable w (μ.prod μ) := hw.integrable (by norm_num)
  have hIg : Integrable g μ := hg.integrable (by norm_num)
  have hI : (∫ z, w z ∂ν) =
      d^3*(∫ x in ⋃ i, B i, g x ∂μ) - (d^3/2)*(∫ x in ⋃ i, A i, g x ∂μ) := by
    rw [integral_iUnion_fintype hB hBd (fun _ => hIg.integrableOn),
      integral_iUnion_fintype hA hAd (fun _ => hIg.integrableOn), Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    change (∫ z in S,w z ∂μ.prod μ) = _
    rw [integral_iUnion_fintype hD hDd (fun _ => hIw.integrableOn)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_pair_sub_on_prod hIg, Measure.real, Measure.real, hAV, hBV,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  have hEn : (∫ z, w z ^ 2 ∂ν) ≤ (K*d)^(3+2*r) * (scalarFractionalPairEnergy r μ g).toReal := by
    have hInt : Integrable (fun z => w z ^ 2) ν := hwS.integrable_sq
    let Q (z : Point × Point) := ENNReal.ofReal ((g z.1-g z.2)^2 / dist z.1 z.2 ^ (3+2*r))
    have hQMeas : AEMeasurable Q (μ.prod μ) := by
      have hDen : Measurable (fun z : Point × Point => dist z.1 z.2 ^ (3+2*r)) := by fun_prop
      exact ENNReal.measurable_ofReal.comp_aemeasurable ((hw.1.aemeasurable.pow_const _).div hDen.aemeasurable)
    have hBound : ENNReal.ofReal (∫ z, w z ^ 2 ∂ν) ≤
        ENNReal.ofReal ((K*d)^(3+2*r)) * scalarFractionalPairEnergy r μ g := by
      rw [ofReal_integral_eq_lintegral_ofReal hInt (.of_forall fun _ => sq_nonneg _)]
      calc
        _ ≤ ∫⁻ z, ENNReal.ofReal ((K*d)^(3+2*r)) * Q z ∂ν := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hS] with z hz
          obtain ⟨i,hi⟩ := mem_iUnion.mp hz
          exact ofReal_square_pair_le_scaled_energy hr hK hd g (hDist i z.1 hi.1 z.2 hi.2)
        _ = ENNReal.ofReal ((K*d)^(3+2*r)) * (∫⁻ z, Q z ∂ν) := by
          rw [lintegral_const_mul'' _ (hQMeas.mono_measure Measure.restrict_le_self)]
        _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono' Measure.restrict_le_self le_rfl)
    rw [← ENNReal.ofReal_toReal hE.ne, ← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg hK.le hd.le) _)] at hBound
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hBound
  let e := scalarFractionalPairEnergy r μ g
  let F := (∫ x in ⋃ i, B i, g x ∂μ)/(d/2) - (∫ x in ⋃ i, A i, g x ∂μ)/d
  have hF : (∫ z, w z ∂ν) = (d^4/2) * F := by rw [hI]; dsimp only [F]; field_simp [hd.ne']
  have hCS := (square_integral_le_measure_mul_integral_square hwS).trans
    (mul_le_mul_of_nonneg_left hEn measureReal_nonneg)
  rw [hF, hmS, mul_pow] at hCS
  change F^2 ≤ _
  have hp : 0 < d^4/2 := by positivity
  calc
    _ ≤ (L^2*d^4/2*((K*d)^(3+2*r)*e.toReal)) / (d^4/2)^2 :=
      (le_div_iff₀ (sq_pos_of_pos hp)).2 (by simpa only [mul_comm (F^2)] using hCS)
    _ = _ := by
      rw [Real.mul_rpow hK.le hd.le]
      have hdPow : d^(3+2*r) = d^(2*r-1)*d^(4:ℕ) := by
        rw [← Real.rpow_ofNat d 4, ← Real.rpow_add hd]
        congr 1
        ring
      rw [hdPow]
      field_simp [hd.ne']
      ring

end Thesis

end
