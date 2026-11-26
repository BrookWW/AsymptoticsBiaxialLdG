module

public import Thesis.Variational.InteriorBiaxialSystem
import Thesis.Variational.BoundarySmallEnergy
import Thesis.Variational.EnergyEstimate

/-! Uniform differentiated interior estimates for the biaxial system. -/

public section

open Filter Metric Set Topology
open scoped ContDiff Matrix.Norms.Frobenius

noncomputable section

namespace Thesis

/-- The biaxial system after a spatial dilation. The field of gradient
columns keeps its original amplitude. -/
structure RescaledBiaxialSystem (a : BulkCoefficients) (d ell β : ℝ) (U : Set Point) where
  tensor : Point → S0
  columns : Point → Gradient
  defects : Point → ScalarDefectPair
  tensor_smooth : ContDiffOn ℝ ∞ tensor U
  columns_smooth : ContDiffOn ℝ ∞ columns U
  defects_smooth : ContDiffOn ℝ ∞ defects U
  column_of_tensor : ∀ x ∈ U, ∀ j : Fin 3, coordDeriv j tensor x = d • columns x j
  poisson : ∀ x ∈ U, ∀ j : Fin 3, laplacian (fun y => columns y j) x =
    d • coordDeriv j (fun y => biaxialTensorForce a (β, tensor y, defects y)) x
  screened : ∀ x ∈ U, ∀ j : Fin 2,
    -ell ^ 2 * laplacian (fun y => defects y j) x + scalarDefectMass a j * defects x j =
      biaxialGradientSource (tensor x, columns x) j + β * biaxialDefectCorrection a (β, defects x) j

variable {a : BulkCoefficients} {d ell β : ℝ} {U : Set Point}

@[expose] def RescaledBiaxialSystem.tensorRhs (S : RescaledBiaxialSystem a d ell β U) (x : Point) : S0 :=
  biaxialTensorForce a (β, S.tensor x, S.defects x)

@[expose] def RescaledBiaxialSystem.defectRhs (S : RescaledBiaxialSystem a d ell β U) (x : Point) : ScalarDefectPair :=
  biaxialGradientSource (S.tensor x, S.columns x)

@[expose] def RescaledBiaxialSystem.defectCorrection (S : RescaledBiaxialSystem a d ell β U)
    (x : Point) : ScalarDefectPair :=
  biaxialDefectCorrection a (β, S.defects x)

theorem RescaledBiaxialSystem.tensorRhs_smooth (S : RescaledBiaxialSystem a d ell β U) :
    ContDiffOn ℝ ∞ S.tensorRhs U :=
  (contDiff_biaxialTensorForce a).comp_contDiffOn
    (contDiffOn_const.prodMk (S.tensor_smooth.prodMk S.defects_smooth))

theorem RescaledBiaxialSystem.defectRhs_smooth (S : RescaledBiaxialSystem a d ell β U) :
    ContDiffOn ℝ ∞ S.defectRhs U :=
  contDiff_biaxialGradientSource.comp_contDiffOn (S.tensor_smooth.prodMk S.columns_smooth)

theorem RescaledBiaxialSystem.defectCorrection_smooth (S : RescaledBiaxialSystem a d ell β U) :
    ContDiffOn ℝ ∞ S.defectCorrection U :=
  (contDiff_biaxialDefectCorrection a).comp_contDiffOn (contDiffOn_const.prodMk S.defects_smooth)

theorem RescaledBiaxialSystem.differentiateColumn (S : RescaledBiaxialSystem a d ell β U)
    (hU : IsOpen U) (j : Fin 3) (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ U) :
    iteratedCoordinateDerivative (n + 1) (Fin.snoc i j) S.tensor x =
      d • iteratedCoordinateDerivative n i (fun y => S.columns y j) x := by
  have hV := contDiffOn_pi.mp S.columns_smooth j
  have hEq : EqOn (coordDeriv j S.tensor) (fun y => d • S.columns y j) U :=
    fun y hy => S.column_of_tensor y hy j
  rw [iteratedCoordinateDerivative_snoc, iteratedCoordinateDerivative_congr_open hU hEq n i hx,
    iteratedCoordinateDerivative_const_smul hU hV d n i hx]

theorem RescaledBiaxialSystem.differentiatePoisson (S : RescaledBiaxialSystem a d ell β U)
    (hU : IsOpen U) (j : Fin 3) (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ U) :
    laplacian (iteratedCoordinateDerivative n i (fun y => S.columns y j)) x =
      d • iteratedCoordinateDerivative (n + 1) (Fin.snoc i j) S.tensorRhs x := by
  have hV := contDiffOn_pi.mp S.columns_smooth j
  have hEq : EqOn (laplacian (fun y => S.columns y j)) (fun y => d • coordDeriv j S.tensorRhs y) U :=
    fun y hy => S.poisson y hy j
  rw [laplacian_iteratedCoordinateDerivative_tensor hU hV n i hx,
    iteratedCoordinateDerivative_congr_open hU hEq n i hx,
    iteratedCoordinateDerivative_const_smul hU (contDiffOn_coordDeriv_infty hU S.tensorRhs_smooth j) d n i hx,
    iteratedCoordinateDerivative_snoc]

theorem RescaledBiaxialSystem.differentiateScreened (S : RescaledBiaxialSystem a d ell β U)
    (hU : IsOpen U) (j : Fin 2) (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ U) :
    let w := iteratedCoordinateDerivative n i (fun y => S.defects y j);
    -ell ^ 2 * laplacian w x + scalarDefectMass a j * w x =
      iteratedCoordinateDerivative n i S.defectRhs x j + β * iteratedCoordinateDerivative n i S.defectCorrection x j := by
  let w (y : Point) := S.defects y j
  let b (y : Point) := S.defectRhs y j
  let c (y : Point) := S.defectCorrection y j
  have hW : ContDiffOn ℝ ∞ w U := contDiffOn_pi.mp S.defects_smooth j
  have hB : ContDiffOn ℝ ∞ b U := contDiffOn_pi.mp S.defectRhs_smooth j
  have hC : ContDiffOn ℝ ∞ c U := contDiffOn_pi.mp S.defectCorrection_smooth j
  have hEq : EqOn (fun y => (-ell ^ 2) • laplacian w y + scalarDefectMass a j • w y)
      (fun y => b y + β • c y) U := fun y hy => S.screened y hy j
  have h := iteratedCoordinateDerivative_congr_open hU hEq n i hx
  rw [iteratedCoordinateDerivative_add hU ((contDiffOn_classical_laplacian_infty hU hW).const_smul _)
    (hW.const_smul _) n i hx, iteratedCoordinateDerivative_add hU hB (hC.const_smul _) n i hx,
    iteratedCoordinateDerivative_const_smul hU (contDiffOn_classical_laplacian_infty hU hW) _ n i hx,
    iteratedCoordinateDerivative_const_smul hU hW _ n i hx,
    iteratedCoordinateDerivative_const_smul hU hC _ n i hx,
    ← laplacian_iteratedCoordinateDerivative_scalar hU hW n i hx] at h
  rw [iteratedCoordinateDerivative_pi_apply hU S.defectRhs_smooth n i hx,
    iteratedCoordinateDerivative_pi_apply hU S.defectCorrection_smooth n i hx]
  exact h

/-- The rescaled solution uses the original gradient and scalar defects at
the same affine argument. Its screened length is the elastic scale divided
by the spatial dilation factor. -/
theorem exists_rescaled_biaxial_system (a : BulkCoefficients) (ε : ElasticScale)
    {Ω V : Set Point} (hΩ : IsOpen Ω) (hV : IsOpen V)
    {Q : Point → S0} (hQ : ContDiffOn ℝ ∞ Q Ω)
    (hEuler : ∀ x ∈ Ω, (ε : ℝ) ^ 2 • (laplacian Q x : S0).val = bulkGradient a (Q x))
    (c : Point) {d : ℝ} (hd : 0 < d) (hMap : MapsTo (fun y => c + d • y) V Ω) :
    ∃ S : RescaledBiaxialSystem a d ((ε : ℝ) / d) ((ε : ℝ) ^ 2) V,
      S.tensor = (fun y => Q (c + d • y)) ∧ S.columns = (fun y => ClassicalGradient Q (c + d • y)) ∧
        S.defects = (fun y => scalarDefectPair a ε (Q (c + d • y))) := by
  let Z (y : Point) := c + d • y
  let β := (ε : ℝ) ^ 2
  let W := scalarDefectPair a ε ∘ Q
  let R (x : Point) := biaxialTensorForce a (β, Q x, W x)
  have hZ : ContDiff ℝ ∞ Z := contDiff_const.add (contDiff_id.const_smul d)
  have hG (j : Fin 3) : ContDiffOn ℝ ∞ (coordDeriv j Q) Ω := contDiffOn_coordDeriv_infty hΩ hQ j
  have hQC : ContDiffOn ℝ ∞ (ClassicalGradient Q) Ω := contDiffOn_pi.mpr hG
  have hW : ContDiffOn ℝ ∞ W Ω := (contDiff_scalarDefectPair a ε).comp_contDiffOn hQ
  have hClass (x : Point) (hx : x ∈ Ω) := classical_biaxial_poisson_screened_system a ε hΩ
    ((contDiffOn_infty.mp hQ) 2) hx (hEuler x hx)
  let S : RescaledBiaxialSystem a d ((ε : ℝ) / d) β V := {
    tensor := Q ∘ Z
    columns := ClassicalGradient Q ∘ Z
    defects := W ∘ Z
    tensor_smooth := hQ.comp hZ.contDiffOn hMap
    columns_smooth := hQC.comp hZ.contDiffOn hMap
    defects_smooth := hW.comp hZ.contDiffOn hMap
    column_of_tensor := by
      intro y hy j
      have hY := hMap hy
      exact coordDeriv_affine_dilation c d y ((hQ.differentiableOn (by simp) _ hY).differentiableAt
        (hΩ.mem_nhds hY)) j
    poisson := by
      intro y hy j
      have hY := hMap hy
      have hD := ((contDiffOn_classical_laplacian_infty hΩ hQ).differentiableOn (by simp) _ hY).differentiableAt
        (hΩ.mem_nhds hY)
      have hEq : (laplacian Q ∘ Z) =ᶠ[𝓝 y] (R ∘ Z) := by
        filter_upwards [hV.mem_nhds hy] with z hz using (hClass (Z z) (hMap hz)).1
      change laplacian (fun z => coordDeriv j Q (Z z)) y = d • coordDeriv j (R ∘ Z) y
      calc
        _ = d ^ 2 • laplacian (coordDeriv j Q) (Z y) :=
          laplacian_affine_dilation hΩ ((contDiffOn_infty.mp (hG j)) 2) c d hY
        _ = d ^ 2 • coordDeriv j (laplacian Q) (Z y) :=
          congrArg (d ^ 2 • ·) (laplacian_coordDeriv_comm hΩ hQ hY j)
        _ = d • coordDeriv j (laplacian Q ∘ Z) y := by
          have hCoord := coordDeriv_affine_dilation c d y hD j
          change coordDeriv j (fun z => laplacian Q (Z z)) y = d • coordDeriv j (laplacian Q) (Z y) at hCoord
          change _ = d • coordDeriv j (fun z => laplacian Q (Z z)) y
          rw [hCoord, smul_smul, pow_two]
        _ = _ := congrArg (d • ·) (DFunLike.congr_fun hEq.fderiv_eq (axis j))
    screened := by
      intro y hy j
      have hY := hMap hy
      have hWi := contDiffOn_pi.mp hW j
      have hLap : laplacian (fun z => W (Z z) j) y = d ^ 2 • laplacian (fun z => W z j) (Z y) :=
        laplacian_affine_dilation hΩ ((contDiffOn_infty.mp hWi) 2) c d hY
      change -((ε : ℝ) / d) ^ 2 * laplacian (fun z => W (Z z) j) y + scalarDefectMass a j * W (Z y) j = _
      rw [hLap, smul_eq_mul, ← mul_assoc]
      have hFactor : -((ε : ℝ) / d) ^ 2 * d ^ 2 = -β := by dsimp only [β]; field_simp
      rw [hFactor]
      exact (hClass (Z y) hY).2 j }
  exact ⟨S, rfl, rfl, rfl⟩

/-- Common coordinate bounds through a fixed order for the gradient columns
and for both scalar defects. -/
structure BiaxialCoordinateBounds (S : RescaledBiaxialSystem a d ell β U)
    (n : ℕ) (M : ℝ) (V : Set Point) : Prop where
  tensor : ∀ x ∈ V, ‖S.tensor x‖ ≤ M
  columns : ∀ x ∈ V, ∀ k ≤ n, ∀ (i : Fin k → Fin 3) (j : Fin 3),
    ‖iteratedCoordinateDerivative k i (fun y => S.columns y j) x‖ ≤ M
  defects : ∀ x ∈ V, ∀ k ≤ n, ∀ (i : Fin k → Fin 3) (j : Fin 2),
    |iteratedCoordinateDerivative k i (fun y => S.defects y j) x| ≤ M

private theorem BiaxialCoordinateBounds.tensorDerivatives {S : RescaledBiaxialSystem a d ell β U}
    {n : ℕ} {M : ℝ} {V : Set Point} (B : BiaxialCoordinateBounds S n M V)
    (hU : IsOpen U) (hd : d ∈ Icc 0 1) {x : Point} (hx : x ∈ U) (hxV : x ∈ V) :
    ∀ k ≤ n + 1, ∀ i : Fin k → Fin 3, ‖iteratedCoordinateDerivative k i S.tensor x‖ ≤ M := by
  intro k hk i
  cases k with
  | zero => exact B.tensor x hxV
  | succ j =>
      conv_lhs => rw [← Fin.snoc_init_self (q := i)]
      rw [S.differentiateColumn hU _ _ _ hx, norm_smul, Real.norm_of_nonneg hd.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hd.2).trans
        (B.columns x hxV j (Nat.le_of_succ_le_succ hk) (Fin.init i) (i (Fin.last j)))

theorem norm_coordDerivative_const_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z : E} {M : ℝ} (hM : 0 ≤ M) (hz : ‖z‖ ≤ M) (k : ℕ) (i : Fin k → Fin 3) (x : Point) :
    ‖iteratedCoordinateDerivative k i (fun _ : Point => z) x‖ ≤ M := by
  cases k with
  | zero => exact hz
  | succ k => rw [iteratedCoordinateDerivative_const _ (Nat.succ_ne_zero _) i z x, norm_zero]; exact hM

theorem norm_coordDerivative_pair_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hU : IsOpen U) {f : Point → E} {g : Point → F}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (k : ℕ) (i : Fin k → Fin 3) {x : Point} (hx : x ∈ U) {M : ℝ}
    (hF : ‖iteratedCoordinateDerivative k i f x‖ ≤ M) (hG : ‖iteratedCoordinateDerivative k i g x‖ ≤ M) :
    ‖iteratedCoordinateDerivative k i (fun y => (f y, g y)) x‖ ≤ M := by
  rw [iteratedCoordinateDerivative_prod_mk hU hf hg k i hx, Prod.norm_def]
  exact max_le hF hG

private theorem exists_biaxial_rhs_coordinate_bound (a : BulkCoefficients) (n : ℕ)
    (M : ℝ) (hM : 1 ≤ M) :
    ∃ C > (0 : ℝ), ∀ {d ell β : ℝ} {U : Set Point},
      IsOpen U → β ∈ Icc 0 1 → ∀ S : RescaledBiaxialSystem a d ell β U, ∀ x ∈ U,
      ‖S.columns x‖ ≤ M → ‖S.defects x‖ ≤ M →
      (∀ k ≤ n, ∀ i : Fin k → Fin 3, ‖iteratedCoordinateDerivative k i S.tensor x‖ ≤ M) →
      (∀ k < n, ∀ i : Fin k → Fin 3, ‖iteratedCoordinateDerivative k i S.columns x‖ ≤ M) →
      (∀ k < n, ∀ i : Fin k → Fin 3, ‖iteratedCoordinateDerivative k i S.defects x‖ ≤ M) →
      ∀ P Q : ℝ, 0 ≤ P → 0 ≤ Q →
      (∀ i : Fin n → Fin 3, ‖iteratedCoordinateDerivative n i S.columns x‖ ≤ P) →
      (∀ i : Fin n → Fin 3, ‖iteratedCoordinateDerivative n i S.defects x‖ ≤ Q) →
      ∀ i : Fin n → Fin 3,
        ‖iteratedCoordinateDerivative n i S.tensorRhs x‖ ≤ C * (1 + Q) ∧
        ‖iteratedCoordinateDerivative n i S.defectRhs x‖ ≤ C * (1 + P) ∧
        ‖iteratedCoordinateDerivative n i S.defectCorrection x‖ ≤ C * (1 + Q) := by
  obtain ⟨A, hA, hA'⟩ := exists_coordinateDerivative_comp_bound (biaxialTensorForce a)
    (contDiff_biaxialTensorForce a) n M hM
  obtain ⟨B, hB, hB'⟩ := exists_coordinateDerivative_comp_bound biaxialGradientSource
    contDiff_biaxialGradientSource n M hM
  obtain ⟨D, hD, hD'⟩ := exists_coordinateDerivative_comp_bound (biaxialDefectCorrection a)
    (contDiff_biaxialDefectCorrection a) n M hM
  let C := (A + B + D) * (1 + M)
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro d ell β U hU hβ S x hx hV₀ hW₀ hQ hV hW P Q hP hT hVtop hWtop i
  let u (y : Point) := (β, S.tensor y, S.defects y)
  let v (y : Point) := (S.tensor y, S.columns y)
  let w (y : Point) := (β, S.defects y)
  have hc : ‖β‖ ≤ M := by rw [Real.norm_of_nonneg hβ.1]; exact hβ.2.trans hM
  have hConst (k : ℕ) (i : Fin k → Fin 3) :
      ‖iteratedCoordinateDerivative k i (fun _ : Point => β) x‖ ≤ M :=
    norm_coordDerivative_const_le hM₀ hc k i x
  have hUby (k : ℕ) (hk : k ≤ n) (i : Fin k → Fin 3) (T : ℝ)
      (hTW : ‖iteratedCoordinateDerivative k i S.defects x‖ ≤ T) :
      ‖iteratedCoordinateDerivative k i u x‖ ≤ max M T := by
    refine norm_coordDerivative_pair_le hU contDiffOn_const (S.tensor_smooth.prodMk S.defects_smooth) k i hx
      ((hConst k i).trans (le_max_left _ _)) ?_
    exact norm_coordDerivative_pair_le hU S.tensor_smooth S.defects_smooth k i hx
      ((hQ k hk i).trans (le_max_left _ _)) (hTW.trans (le_max_right _ _))
  have hVby (k : ℕ) (hk : k ≤ n) (i : Fin k → Fin 3) (T : ℝ)
      (hTV : ‖iteratedCoordinateDerivative k i S.columns x‖ ≤ T) :
      ‖iteratedCoordinateDerivative k i v x‖ ≤ max M T :=
    norm_coordDerivative_pair_le hU S.tensor_smooth S.columns_smooth k i hx
      ((hQ k hk i).trans (le_max_left _ _)) (hTV.trans (le_max_right _ _))
  have hWby (k : ℕ) (i : Fin k → Fin 3) (T : ℝ)
      (hTW : ‖iteratedCoordinateDerivative k i S.defects x‖ ≤ T) :
      ‖iteratedCoordinateDerivative k i w x‖ ≤ max M T :=
    norm_coordDerivative_pair_le hU contDiffOn_const S.defects_smooth k i hx
      ((hConst k i).trans (le_max_left _ _)) (hTW.trans (le_max_right _ _))
  have hu0 : ‖u x‖ ≤ M := max_le hc (max_le (hQ 0 (Nat.zero_le n) (fun _ => 0)) hW₀)
  have hv0 : ‖v x‖ ≤ M := max_le (hQ 0 (Nat.zero_le n) (fun _ => 0)) hV₀
  have hw0 : ‖w x‖ ≤ M := max_le hc hW₀
  have hu := hA' hU (contDiffOn_const.prodMk (S.tensor_smooth.prodMk S.defects_smooth)) x hx hu0
    (fun k hk j => (hUby k hk.le j M (hW k hk j)).trans (max_self M).le)
    (max M Q) (hM₀.trans (le_max_left _ _)) (fun j => hUby n le_rfl j Q (hWtop j)) i
  have hv := hB' hU (S.tensor_smooth.prodMk S.columns_smooth) x hx hv0
    (fun k hk j => (hVby k hk.le j M (hV k hk j)).trans (max_self M).le)
    (max M P) (hM₀.trans (le_max_left _ _)) (fun j => hVby n le_rfl j P (hVtop j)) i
  have hw := hD' hU (contDiffOn_const.prodMk S.defects_smooth) x hx hw0
    (fun k hk j => (hWby k j M (hW k hk j)).trans (max_self M).le)
    (max M Q) (hM₀.trans (le_max_left _ _)) (fun j => hWby n j Q (hWtop j)) i
  have hWeight (X : ℝ) (hX : 0 ≤ X) : 1 + max M X ≤ (1 + M) * (1 + X) := by
    have h := max_le (le_add_of_nonneg_right hX) (le_add_of_nonneg_left hM₀)
    nlinarith only [h, mul_nonneg hM₀ hX]
  have hScale {T : ℝ} (hT₀ : 0 ≤ T) (hTS : T ≤ A + B + D) (X : ℝ) (hX : 0 ≤ X) :
      T * (1 + max M X) ≤ C * (1 + X) := by
    refine (mul_le_mul (hTS) (hWeight X hX) (by positivity) (by positivity)).trans_eq ?_
    dsimp only [C]
    ring
  exact ⟨hu.trans (hScale hA.le (by linarith) Q hT),
    hv.trans (hScale hB.le (by linarith) P hP), hw.trans (hScale hD.le (by linarith) Q hT)⟩

private theorem coordinateDerivative_succ_tensor_component_le_gradientSum
    {ι : Type*} [Fintype ι] (f : Point → ι → S0) (n : ℕ) (i : Fin (n + 1) → Fin 3) (j : ι) (x : Point) :
    ‖iteratedCoordinateDerivative (n + 1) i (fun y => f y j) x‖ ≤
      tensorFamilyGradientSum (fun p : ι × (Fin n → Fin 3) =>
        iteratedCoordinateDerivative n p.2 (fun y => f y p.1)) x := by
  let V (p : ι × (Fin n → Fin 3)) := iteratedCoordinateDerivative n p.2 (fun y => f y p.1)
  let p : ι × (Fin n → Fin 3) := (j, Fin.tail i)
  have h₁ : ‖coordDeriv (i 0) (V p) x‖ ≤ ∑ k : Fin 3, ‖coordDeriv k (V p) x‖ :=
    Finset.single_le_sum (fun k _ => norm_nonneg (coordDeriv k (V p) x)) (Finset.mem_univ (i 0))
  exact h₁.trans (Finset.single_le_sum
    (fun q _ => Finset.sum_nonneg (fun k _ => norm_nonneg (coordDeriv k (V q) x)))
    (Finset.mem_univ p))

private theorem coordinateDerivative_succ_scalar_component_le_gradientSum
    {ι : Type*} [Fintype ι] (f : Point → ι → ℝ) (n : ℕ) (i : Fin (n + 1) → Fin 3) (j : ι) (x : Point) :
    |iteratedCoordinateDerivative (n + 1) i (fun y => f y j) x| ≤
      scalarFamilyGradientSum (fun p : ι × (Fin n → Fin 3) =>
        iteratedCoordinateDerivative n p.2 (fun y => f y p.1)) x := by
  let V (p : ι × (Fin n → Fin 3)) := iteratedCoordinateDerivative n p.2 (fun y => f y p.1)
  let p : ι × (Fin n → Fin 3) := (j, Fin.tail i)
  have h₁ : |coordDeriv (i 0) (V p) x| ≤ ∑ k : Fin 3, |coordDeriv k (V p) x| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (coordDeriv k (V p) x)) (Finset.mem_univ (i 0))
  exact h₁.trans (Finset.single_le_sum (fun q _ => Finset.sum_nonneg fun k _ => abs_nonneg (coordDeriv k (V q) x))
    (Finset.mem_univ p))

theorem norm_coordinateDerivative_pi_le {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set Point} (hU : IsOpen U) {f : Point → ι → E} (hf : ContDiffOn ℝ ∞ f U)
    (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ U) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ j, ‖iteratedCoordinateDerivative n i (fun y => f y j) x‖ ≤ M) :
    ‖iteratedCoordinateDerivative n i f x‖ ≤ M := by
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro j
  rw [iteratedCoordinateDerivative_pi_apply hU hf n i hx]
  exact h j

/-- Uniform one-order gain for all gradient columns and both scalar defects
on a smaller ball. The coefficient depends only on the material, order,
lower derivative bounds and Poisson estimate. -/
theorem exists_biaxialCoordinateBounds_succ (a : BulkCoefficients)
    (hEstimate : InteriorPoissonGradientEstimate) (n : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    ∃ A > (0 : ℝ), ∀ {d ell β : ℝ} {U V : Set Point},
      IsOpen U → IsOpen V → V ⊆ U → d ∈ Icc 0 1 → 0 < ell → β ∈ Icc 0 1 → β ≤ ell →
      ∀ (S : RescaledBiaxialSystem a d ell β U), BiaxialCoordinateBounds S n M V →
      ∀ {c : Point} {s t : ℝ}, 0 < s → s < t → closedBall c t ⊆ V →
        BiaxialCoordinateBounds S (n + 1) (A * (1 + (t - s)⁻¹)) (ball c s) := by
  obtain ⟨C₀, hC₀, hRhs₀⟩ := exists_biaxial_rhs_coordinate_bound a n M hM
  obtain ⟨C₁, hC₁, hRhs₁⟩ := exists_biaxial_rhs_coordinate_bound a (n + 1) M hM
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  let μ := min (bulkRadialMass a) (bulkBiaxialMass a)
  let m := scalarDefectMass a
  have hμ : 0 < μ := lt_min (bulkRadialMass_pos a) (bulkBiaxialMass_pos a)
  have hm (j : Fin 2) : μ ≤ m j := scalarDefectMass_lower a j
  let Uₘ := bulkRadialMass a + bulkBiaxialMass a
  have hUₘ : 0 ≤ Uₘ := add_nonneg (bulkRadialMass_pos a).le (bulkBiaxialMass_pos a).le
  have hm' (j : Fin 2) : m j ≤ Uₘ := by
    fin_cases j
    · exact le_add_of_nonneg_right (bulkBiaxialMass_pos a).le
    · exact le_add_of_nonneg_left (bulkRadialMass_pos a).le
  let F := 1 + M + Uₘ * M + 2 * C₀ * (1 + M) + 2 * C₁
  have hF : 1 ≤ F := by
    dsimp only [F]
    linarith only [hM₀, mul_nonneg hUₘ hM₀, mul_nonneg hC₀.le (show 0 ≤ 1 + M by positivity), hC₁]
  have hMF : M ≤ F := by
    dsimp only [F]
    linarith only [mul_nonneg hUₘ hM₀, mul_nonneg hC₀.le (show 0 ≤ 1 + M by positivity), hC₁]
  have hF₀ : Uₘ * M + 2 * C₀ * (1 + M) ≤ F := by dsimp only [F]; linarith only [hM₀, hC₁]
  have hF₁ : 2 * C₁ ≤ F := by
    dsimp only [F]
    linarith only [hM₀, mul_nonneg hUₘ hM₀, mul_nonneg hC₀.le (show 0 ≤ 1 + M by positivity)]
  let I := Fin 3 × (Fin n → Fin 3)
  let J := Fin 2 × (Fin n → Fin 3)
  obtain ⟨A, hA, hStep⟩ := exists_interior_gradient_bound_for_screened_families
    (ι := I) (κ := J) hEstimate F μ hF hμ
  refine ⟨A + M, by positivity, ?_⟩
  intro d ell β U V hU hV hVU hd hell hβ hβell S B c s t hs hst hClosed
  let v (j : I) := iteratedCoordinateDerivative n j.2 (fun y => S.columns y j.1)
  let w (j : J) := iteratedCoordinateDerivative n j.2 (fun y => S.defects y j.1)
  let P := tensorFamilyGradientSum v
  let Q := scalarFamilyGradientSum w
  have hP (x : Point) : 0 ≤ P x := tensorFamilyGradientSum_nonneg _ _
  have hQ (x : Point) : 0 ≤ Q x := scalarFamilyGradientSum_nonneg _ _
  have hVs (j : I) : ContDiffOn ℝ ∞ (v j) V :=
    (contDiffOn_iteratedCoordinateDerivative hU (contDiffOn_pi.mp S.columns_smooth j.1) _ _).mono hVU
  have hWs (j : J) : ContDiffOn ℝ ∞ (w j) V :=
    (contDiffOn_iteratedCoordinateDerivative hU (contDiffOn_pi.mp S.defects_smooth j.1) _ _).mono hVU
  have hVlow (x : Point) (hx : x ∈ V) (k : ℕ) (hk : k ≤ n) (i : Fin k → Fin 3) :
      ‖iteratedCoordinateDerivative k i S.columns x‖ ≤ M :=
    norm_coordinateDerivative_pi_le hU S.columns_smooth k i (hVU hx) hM₀ (B.columns x hx k hk i)
  have hWlow (x : Point) (hx : x ∈ V) (k : ℕ) (hk : k ≤ n) (i : Fin k → Fin 3) :
      ‖iteratedCoordinateDerivative k i S.defects x‖ ≤ M :=
    norm_coordinateDerivative_pi_le hU S.defects_smooth k i (hVU hx) hM₀
      (fun j => by simpa only [Real.norm_eq_abs] using B.defects x hx k hk i j)
  have hVtop (x : Point) (hx : x ∈ V) (i : Fin (n + 1) → Fin 3) :
      ‖iteratedCoordinateDerivative (n + 1) i S.columns x‖ ≤ P x :=
    norm_coordinateDerivative_pi_le hU S.columns_smooth _ i (hVU hx) (hP x)
      (fun j => coordinateDerivative_succ_tensor_component_le_gradientSum S.columns n i j x)
  have hWtop (x : Point) (hx : x ∈ V) (i : Fin (n + 1) → Fin 3) :
      ‖iteratedCoordinateDerivative (n + 1) i S.defects x‖ ≤ Q x :=
    norm_coordinateDerivative_pi_le hU S.defects_smooth _ i (hVU hx) (hQ x) (fun j => by
      simpa only [Real.norm_eq_abs] using coordinateDerivative_succ_scalar_component_le_gradientSum S.defects n i j x)
  have hR₀ (x : Point) (hx : x ∈ V) (i : Fin n → Fin 3) :=
    hRhs₀ hU hβ S x (hVU hx) (hVlow x hx 0 (Nat.zero_le _) (fun _ => 0)) (hWlow x hx 0 (Nat.zero_le _) (fun _ => 0))
      (fun k hk => B.tensorDerivatives hU hd (hVU hx) hx k (hk.trans (Nat.le_succ _)))
      (fun k hk => hVlow x hx k hk.le) (fun k hk => hWlow x hx k hk.le)
      M M hM₀ hM₀ (hVlow x hx n le_rfl) (hWlow x hx n le_rfl) i
  have hR₁ (x : Point) (hx : x ∈ V) (i : Fin (n + 1) → Fin 3) :=
    hRhs₁ hU hβ S x (hVU hx) (hVlow x hx 0 (Nat.zero_le _) (fun _ => 0)) (hWlow x hx 0 (Nat.zero_le _) (fun _ => 0))
      (B.tensorDerivatives hU hd (hVU hx) hx)
      (fun k hk => hVlow x hx k (Nat.le_of_lt_succ hk)) (fun k hk => hWlow x hx k (Nat.le_of_lt_succ hk))
      (P x) (Q x) (hP x) (hQ x) (hVtop x hx) (hWtop x hx) i
  have hEval (f : ScalarDefectPair) (i : Fin 2) : |f i| ≤ ‖f‖ := by
    simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mp le_rfl i
  have hvLap (x : Point) (hx : x ∈ V) (j : I) : ‖v j x‖ ≤ F ∧ ‖laplacian (v j) x‖ ≤ F * (1 + Q x) := by
    refine ⟨(B.columns x hx n le_rfl j.2 j.1).trans hMF, ?_⟩
    have hEq := S.differentiatePoisson hU j.1 n j.2 (hVU hx)
    change ‖laplacian (v j) x‖ ≤ _
    rw [hEq, norm_smul, Real.norm_of_nonneg hd.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hd.2).trans
      ((hR₁ x hx (Fin.snoc j.2 j.1)).1.trans (mul_le_mul_of_nonneg_right
        ((le_mul_of_one_le_left hC₁.le (by norm_num : (1 : ℝ) ≤ 2)).trans hF₁) (add_nonneg zero_le_one (hQ x))))
  have hwLap (x : Point) (hx : x ∈ V) (j : J) : |w j x| ≤ F ∧ |laplacian (w j) x| ≤ F / ell ^ 2 := by
    have hW := B.defects x hx n le_rfl j.2 j.1
    refine ⟨hW.trans hMF, ?_⟩
    have hEq := S.differentiateScreened hU j.1 n j.2 (hVU hx)
    let A₀ := iteratedCoordinateDerivative n j.2 S.defectRhs x j.1
    let B₀ := iteratedCoordinateDerivative n j.2 S.defectCorrection x j.1
    have hA₀ : |A₀| ≤ C₀ * (1 + M) := (hEval _ j.1).trans (hR₀ x hx j.2).2.1
    have hB₀ : |B₀| ≤ C₀ * (1 + M) := (hEval _ j.1).trans (hR₀ x hx j.2).2.2
    have hE : ell ^ 2 * laplacian (w j) x = m j.1 * w j x - A₀ - β * B₀ := by
      change -ell ^ 2 * laplacian (w j) x + m j.1 * w j x = A₀ + β * B₀ at hEq
      linarith only [hEq]
    apply (le_div_iff₀ (sq_pos_of_pos hell)).mpr
    rw [mul_comm, ← abs_of_nonneg (sq_nonneg ell), ← abs_mul, hE]
    refine (abs_sub _ _).trans ((add_le_add (abs_sub _ _) (by rfl)).trans ?_)
    rw [abs_mul, abs_mul, abs_of_pos (hμ.trans_le (hm j.1)), abs_of_nonneg hβ.1]
    have h1 := mul_le_mul (hm' j.1) hW (abs_nonneg _) hUₘ
    have h2 := (mul_le_mul_of_nonneg_right hβ.2 (abs_nonneg B₀)).trans_eq (one_mul _)
    exact le_trans (add_le_add (add_le_add h1 hA₀) (h2.trans hB₀)) (by linarith only [hF₀])
  have hwScr (x : Point) (hx : x ∈ V) (j : J) (i : Fin 3) :
      |-ell ^ 2 * laplacian (coordDeriv i (w j)) x + m j.1 * coordDeriv i (w j) x| ≤ F * (1 + P x + β * Q x) := by
    let k : Fin (n + 1) → Fin 3 := Fin.cons i j.2
    have hW' : iteratedCoordinateDerivative (n + 1) k (fun y => S.defects y j.1) = coordDeriv i (w j) := by
      simp only [iteratedCoordinateDerivative, k, Fin.cons_zero, Fin.tail_cons, w]
    have hEq := S.differentiateScreened hU j.1 (n + 1) k (hVU hx)
    dsimp only at hEq
    rw [hW'] at hEq
    let A₁ := iteratedCoordinateDerivative (n + 1) k S.defectRhs x j.1
    let B₁ := iteratedCoordinateDerivative (n + 1) k S.defectCorrection x j.1
    have hA₁ : |A₁| ≤ C₁ * (1 + P x) := (hEval _ j.1).trans (hR₁ x hx k).2.1
    have hB₁ : |B₁| ≤ C₁ * (1 + Q x) := (hEval _ j.1).trans (hR₁ x hx k).2.2
    change _ = A₁ + β * B₁ at hEq
    rw [hEq]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hβ.1]
    refine (add_le_add hA₁ (mul_le_mul_of_nonneg_left hB₁ hβ.1)).trans ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_right hF₁
      (add_nonneg (add_nonneg zero_le_one (hP x)) (mul_nonneg hβ.1 (hQ x))))
    nlinarith only [mul_le_mul_of_nonneg_left hβ.2 hC₁.le, mul_nonneg hC₁.le (hP x),
      mul_nonneg (mul_nonneg hC₁.le hβ.1) (hQ x)]
  have hGrad := hStep hV hs hst hClosed ell β hell hβ.1 hβ.2 hβell (fun j => m j.1) (fun j => hm j.1)
    v w hVs hWs hvLap hwLap hwScr
  have hExpand : M ≤ (A + M) * (1 + (t - s)⁻¹) := by
    have hGap : 0 ≤ (t - s)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hst.le)
    exact (le_add_of_nonneg_left hA.le).trans (le_mul_of_one_le_right (by positivity) (by linarith))
  have hSmall : ball c s ⊆ V := (ball_subset_ball hst.le).trans (ball_subset_closedBall.trans hClosed)
  have hGrad' (x : Point) (hx : x ∈ ball c s) : P x + Q x ≤ (A + M) * (1 + (t - s)⁻¹) :=
    (hGrad x hx).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hM₀)
      (by have := sub_pos.mpr hst; positivity))
  refine ⟨fun x hx => (B.tensor x (hSmall hx)).trans hExpand, ?_, ?_⟩
  · intro x hx k hk i j
    rcases hk.lt_or_eq with hlt | rfl
    · exact (B.columns x (hSmall hx) k (Nat.le_of_lt_succ hlt) i j).trans hExpand
    · exact (coordinateDerivative_succ_tensor_component_le_gradientSum S.columns n i j x).trans
        ((le_add_of_nonneg_right (hQ x)).trans (hGrad' x hx))
  · intro x hx k hk i j
    rcases hk.lt_or_eq with hlt | rfl
    · exact (B.defects x (hSmall hx) k (Nat.le_of_lt_succ hlt) i j).trans hExpand
    · exact (coordinateDerivative_succ_scalar_component_le_gradientSum S.defects n i j x).trans
        ((le_add_of_nonneg_left (hP x)).trans (hGrad' x hx))

theorem BiaxialCoordinateBounds.mono {S : RescaledBiaxialSystem a d ell β U}
    {n : ℕ} {M N : ℝ} {V W : Set Point} (B : BiaxialCoordinateBounds S n M V)
    (hMN : M ≤ N) (hWV : W ⊆ V) : BiaxialCoordinateBounds S n N W :=
  ⟨fun x hx => (B.tensor x (hWV hx)).trans hMN,
    fun x hx k hk i j => (B.columns x (hWV hx) k hk i j).trans hMN,
    fun x hx k hk i j => (B.defects x (hWV hx) k hk i j).trans hMN⟩

/-- The rescaled system has uniform derivatives of each order on the
half-unit ball, under a common order-zero bound on the unit ball. -/
theorem exists_biaxialCoordinateBounds_halfUnitBall (a : BulkCoefficients)
    (hEstimate : InteriorPoissonGradientEstimate) (n : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    ∃ C > (0 : ℝ), ∀ {d ell β : ℝ}, d ∈ Icc 0 1 → 0 < ell → β ∈ Icc 0 1 → β ≤ ell →
      ∀ S : RescaledBiaxialSystem a d ell β (ball (0 : Point) 1),
        BiaxialCoordinateBounds S 0 M (ball 0 1) →
        BiaxialCoordinateBounds S n C (ball 0 (1 / 2)) := by
  let r (k : ℕ) := (1 + (1 / 2 : ℝ) ^ k) / 2
  have hr0 : r 0 = 1 := by norm_num [r]
  have hR (k : ℕ) : 1 / 2 < r k := by
    dsimp only [r]
    have h := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k
    linarith
  have hR₁ (k : ℕ) : r k ≤ 1 := by
    dsimp only [r]
    have h : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hRR (k : ℕ) : r (k + 1) < r k := by
    dsimp only [r]
    rw [pow_succ]
    have h := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k
    linarith
  have hOrder (k : ℕ) :
      ∃ C : ℝ, 1 ≤ C ∧ ∀ {d ell β : ℝ}, d ∈ Icc 0 1 → 0 < ell → β ∈ Icc 0 1 → β ≤ ell →
        ∀ S : RescaledBiaxialSystem a d ell β (ball (0 : Point) 1),
          BiaxialCoordinateBounds S 0 M (ball 0 1) →
          BiaxialCoordinateBounds S k C (ball 0 (r k)) := by
    induction k with
    | zero =>
        refine ⟨M, hM, ?_⟩
        intro d ell β hd hell hβ hβell S B
        rwa [hr0]
    | succ k ih =>
        obtain ⟨C, hC, hInd⟩ := ih
        obtain ⟨A, hA, hGain⟩ := exists_biaxialCoordinateBounds_succ a hEstimate k C hC
        let t := (r k + r (k + 1)) / 2
        have hs : 0 < r (k + 1) := (by norm_num : (0 : ℝ) < 1 / 2).trans (hR _)
        have hst : r (k + 1) < t := by dsimp only [t]; linarith only [hRR k]
        have ht : t < r k := by dsimp only [t]; linarith only [hRR k]
        let N := A * (1 + (t - r (k + 1))⁻¹)
        refine ⟨max 1 N, le_max_left _ _, ?_⟩
        intro d ell β hd hell hβ hβell S B
        have hB := hInd hd hell hβ hβell S B
        have hClosed : closedBall (0 : Point) t ⊆ ball 0 (r k) :=
          fun _ hy => mem_ball.mpr ((mem_closedBall.mp hy).trans_lt ht)
        exact (hGain isOpen_ball isOpen_ball (ball_subset_ball (hR₁ k)) hd hell hβ hβell S hB hs hst hClosed).mono
          (le_max_right _ _) subset_rfl
  obtain ⟨C, hC, hDer⟩ := hOrder n
  refine ⟨C, zero_lt_one.trans_le hC, ?_⟩
  intro d ell β hd hell hβ hβell S B
  exact (hDer hd hell hβ hβell S B).mono le_rfl (ball_subset_ball (hR n).le)

theorem iteratedCoordinateDerivative_affine_dilation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω V : Set Point}
    (hΩ : IsOpen Ω) (hV : IsOpen V) {f : Point → E}
    (hf : ContDiffOn ℝ ∞ f Ω) (c : Point) (d : ℝ)
    (hMap : MapsTo (fun y => c + d • y) V Ω)
    (n : ℕ) (i : Fin n → Fin 3) {x : Point} (hx : x ∈ V) :
    iteratedCoordinateDerivative n i (fun y => f (c + d • y)) x =
      d ^ n • iteratedCoordinateDerivative n i f (c + d • x) := by
  induction n generalizing x with
  | zero => change f (c + d • x) = d ^ 0 • f (c + d • x); rw [pow_zero, one_smul]
  | succ n ih =>
      let Z (y : Point) := c + d • y
      let g := iteratedCoordinateDerivative n (Fin.tail i) f
      have hg : ContDiffOn ℝ ∞ g Ω := contDiffOn_iteratedCoordinateDerivative hΩ hf _ _
      have hZ : ContDiff ℝ ∞ Z := contDiff_const.add (contDiff_id.const_smul d)
      have hgZ := hg.comp hZ.contDiffOn hMap
      have hEq : iteratedCoordinateDerivative n (Fin.tail i) (fun y => f (Z y)) =ᶠ[𝓝 x]
          (fun y => d ^ n • g (Z y)) := by
        filter_upwards [hV.mem_nhds hx] with y hy using ih (Fin.tail i) hy
      have hD := (hgZ.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx)
      have hgD := (hg.differentiableOn (by simp) (Z x) (hMap hx)).differentiableAt (hΩ.mem_nhds (hMap hx))
      change coordDeriv (i 0) (iteratedCoordinateDerivative n (Fin.tail i) (fun y => f (Z y))) x =
        d ^ (n + 1) • coordDeriv (i 0) g (Z x)
      calc
        _ = coordDeriv (i 0) (fun y => d ^ n • g (Z y)) x := DFunLike.congr_fun hEq.fderiv_eq (axis (i 0))
        _ = d ^ n • coordDeriv (i 0) (fun y => g (Z y)) x :=
          DFunLike.congr_fun (hD.hasFDerivAt.const_smul (d ^ n)).fderiv (axis (i 0))
        _ = _ := by
          have h := coordDeriv_affine_dilation c d x hgD (i 0)
          change coordDeriv (i 0) (fun y => g (Z y)) x = d • coordDeriv (i 0) g (Z x) at h
          rw [h, smul_smul, pow_succ]

private theorem coordinateDerivative_bound_from_unitBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set Point}
    (hΩ : IsOpen Ω) {f : Point → E} (hf : ContDiffOn ℝ ∞ f Ω) (x : Point) {d C : ℝ} (hd : 0 < d)
    (hMap : MapsTo (fun y => x + d • y) (ball (0 : Point) 1) Ω)
    (n : ℕ) (i : Fin n → Fin 3)
    (h : ‖iteratedCoordinateDerivative n i (fun y => f (x + d • y)) 0‖ ≤ C) :
    ‖iteratedCoordinateDerivative n i f x‖ ≤ C * d⁻¹ ^ n := by
  have hD := iteratedCoordinateDerivative_affine_dilation hΩ isOpen_ball hf x d hMap n i
    (mem_ball_self (x := (0 : Point)) zero_lt_one)
  rw [hD, smul_zero, add_zero, norm_smul, Real.norm_of_nonneg (pow_nonneg hd.le n)] at h
  calc
    _ = (d ^ n)⁻¹ * (d ^ n * ‖iteratedCoordinateDerivative n i f x‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hd.ne'), one_mul]
    _ ≤ (d ^ n)⁻¹ * C := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (pow_nonneg hd.le n))
    _ = _ := by rw [inv_pow, mul_comm]

private theorem inverse_local_dilation_power_le (j : ℕ) {r ρ : ℝ} (h : ρ < r) :
    (min 1 ((r - ρ) / 2))⁻¹ ^ j ≤ (2 : ℝ) ^ j * (1 + (r - ρ)⁻¹ ^ j) := by
  have hGap := sub_pos.mpr h
  rcases le_total (1 : ℝ) ((r - ρ) / 2) with h₁ | h₁
  · rw [min_eq_left h₁, inv_one, one_pow]
    have h₂ : 1 ≤ (2 : ℝ) ^ j := by
      simpa only [pow_zero] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le j)
    exact h₂.trans (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (by positivity)))
  · rw [min_eq_right h₁, show ((r - ρ) / 2)⁻¹ = 2 * (r - ρ)⁻¹ by field_simp, mul_pow]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)

/-- Uniform estimates for the actual two scalar defects and the tensor
derivatives of any order in a smaller ball. The loss depends only on the
distance between the two radii. -/
theorem exists_interior_classical_biaxial_derivative_bound (a : BulkCoefficients)
    (hEstimate : InteriorPoissonGradientEstimate) (j : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C > (0 : ℝ), ∀ (ε : ElasticScale) (c : Point) (r ρ : ℝ), 0 < ρ → ρ < r →
      ∀ Q : Point → S0, ContDiffOn ℝ ∞ Q (ball c r) →
        (∀ y ∈ ball c r, (ε : ℝ) ^ 2 • (laplacian Q y : S0).val = bulkGradient a (Q y)) →
        (∀ y ∈ ball c r, |scaledNormDefect a ε (Q y)| ≤ C₀ ∧ |scaledCubicTrace a ε (Q y)| ≤ C₀ ∧
          Real.sqrt (gradientNormSq (ClassicalGradient Q y)) ≤ C₀) →
        ∀ x ∈ ball c ρ,
          ‖iteratedFDeriv ℝ j (scaledNormDefect a ε ∘ Q) x‖ +
          ‖iteratedFDeriv ℝ j (scaledCubicTrace a ε ∘ Q) x‖ +
          ‖iteratedFDeriv ℝ (j + 1) Q x‖ ≤ C * (1 + (r - ρ)⁻¹ ^ j) := by
  let R₀ := Real.sqrt (2 * vacuumRadius a ^ 2 + C₀)
  let M := max 1 (max C₀ R₀)
  have hM : 1 ≤ M := le_max_left _ _
  have hMC : C₀ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hMR : R₀ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨A, hA, hUnit⟩ := exists_biaxialCoordinateBounds_halfUnitBall a hEstimate j M hM
  let C := 5 * (3 : ℝ) ^ j * A * (2 : ℝ) ^ j
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro ε c r ρ hρ hρr Q hQ hEuler hBase x hx
  let Ω := ball c r
  let V := ball (0 : Point) 1
  let d := min 1 ((r - ρ) / 2)
  let Z (y : Point) := x + d • y
  let β := (ε : ℝ) ^ 2
  have hd : 0 < d := lt_min zero_lt_one (half_pos (sub_pos.mpr hρr))
  have hd₁ : d ≤ 1 := min_le_left _ _
  have hd₂ : d ≤ (r - ρ) / 2 := min_le_right _ _
  have hβ : β ∈ Icc 0 1 := ⟨sq_nonneg _,
    (pow_le_pow_left₀ ε.2.1.le ε.2.2.le 2).trans_eq (one_pow 2)⟩
  have hβell : β ≤ (ε : ℝ) / d := by
    have hβ₁ : β ≤ (ε : ℝ) := by
      change (ε : ℝ) ^ 2 ≤ (ε : ℝ)
      rw [pow_two]
      exact mul_le_of_le_one_right ε.2.1.le ε.2.2.le
    refine hβ₁.trans ((le_div_iff₀ hd).mpr ?_)
    exact mul_le_of_le_one_right ε.2.1.le hd₁
  have hMap : MapsTo Z V Ω := by
    intro y hy
    have hy' : ‖y‖ < 1 := by simpa only [V, mem_ball, dist_zero_right] using hy
    have hdist : dist (Z y) x < d := by
      rw [dist_eq_norm, show Z y - x = d • y from add_sub_cancel_left _ _, norm_smul, Real.norm_of_nonneg hd.le]
      simpa only [mul_one] using mul_lt_mul_of_pos_left hy' hd
    have hT := dist_triangle (Z y) x c
    exact mem_ball.mpr (by linarith only [hT, hdist, hd₂, mem_ball.mp hx, hρr])
  obtain ⟨S, hT, hCols, hW⟩ := exists_rescaled_biaxial_system a ε isOpen_ball isOpen_ball hQ hEuler x hd hMap
  have hMass (y : Point) (hy : y ∈ Ω) : ‖Q y‖ ≤ R₀ := by
    apply Real.le_sqrt_of_sq_le
    rw [norm_sq_eq_trace_sq, trace_sq_eq_scaledNormDefect a ε (Q y)]
    have hh : scaledNormDefect a ε (Q y) ≤ C₀ := (le_abs_self _).trans (hBase y hy).1
    exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left hh hβ.1).trans
      (mul_le_of_le_one_left hC₀ hβ.2))
  have hBaseS : BiaxialCoordinateBounds S 0 M V := by
    refine ⟨fun y hy => ?_, ?_, ?_⟩
    · rw [hT]
      exact (hMass (Z y) (hMap hy)).trans hMR
    · intro y hy k hk i l
      have hk₀ : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      change ‖S.columns y l‖ ≤ M
      rw [hCols]
      have hG : ‖ClassicalGradient Q (Z y) l‖ ≤ Real.sqrt (gradientNormSq (ClassicalGradient Q (Z y))) := by
        rw [gradientNormSq_eq_sum_norm_sq]
        exact Real.le_sqrt_of_sq_le (Finset.single_le_sum
          (fun l _ => sq_nonneg ‖(ClassicalGradient Q (Z y)) l‖) (Finset.mem_univ l))
      exact hG.trans ((hBase _ (hMap hy)).2.2.trans hMC)
    · intro y hy k hk i l
      have hk₀ : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      change |S.defects y l| ≤ M
      rw [hW]
      fin_cases l
      · exact (hBase _ (hMap hy)).1.trans hMC
      · exact (hBase _ (hMap hy)).2.1.trans hMC
  have hBound := hUnit ⟨hd.le, hd₁⟩ (div_pos ε.2.1 hd) hβ hβell S hBaseS
  have h0 : (0 : Point) ∈ ball (0 : Point) (1 / 2) := mem_ball_self (by norm_num)
  have hxΩ : x ∈ Ω := ball_subset_ball hρr.le hx
  have hGs (l : Fin 3) := contDiffOn_coordDeriv_infty isOpen_ball hQ l
  have hHs : ContDiffOn ℝ ∞ (scaledNormDefect a ε ∘ Q) Ω :=
    (contDiff_pi.mp (contDiff_scalarDefectPair a ε) (0 : Fin 2)).comp_contDiffOn hQ
  have hTs : ContDiffOn ℝ ∞ (scaledCubicTrace a ε ∘ Q) Ω :=
    (contDiff_pi.mp (contDiff_scalarDefectPair a ε) (1 : Fin 2)).comp_contDiffOn hQ
  have hGradient (i : Fin j → Fin 3) (l : Fin 3) :
      ‖iteratedCoordinateDerivative j i (coordDeriv l Q) x‖ ≤ A * d⁻¹ ^ j := by
    apply coordinateDerivative_bound_from_unitBall isOpen_ball (hGs l) x hd hMap j i
    have h := hBound.columns 0 h0 j le_rfl i l
    rw [hCols] at h
    exact h
  have hH (i : Fin j → Fin 3) : ‖iteratedCoordinateDerivative j i (scaledNormDefect a ε ∘ Q) x‖ ≤ A * d⁻¹ ^ j := by
    apply coordinateDerivative_bound_from_unitBall isOpen_ball hHs x hd hMap j i
    have h := hBound.defects 0 h0 j le_rfl i (0 : Fin 2)
    rw [hW] at h
    exact h
  have hTr (i : Fin j → Fin 3) : ‖iteratedCoordinateDerivative j i (scaledCubicTrace a ε ∘ Q) x‖ ≤ A * d⁻¹ ^ j := by
    apply coordinateDerivative_bound_from_unitBall isOpen_ball hTs x hd hMap j i
    have h := hBound.defects 0 h0 j le_rfl i (1 : Fin 2)
    rw [hW] at h
    exact h
  have hNext (i : Fin (j + 1) → Fin 3) : ‖iteratedCoordinateDerivative (j + 1) i Q x‖ ≤ A * d⁻¹ ^ j := by
    conv_lhs => rw [← Fin.snoc_init_self (q := i)]
    rw [iteratedCoordinateDerivative_snoc]
    exact hGradient (Fin.init i) (i (Fin.last j))
  have hD : 0 ≤ A * d⁻¹ ^ j := by positivity
  have h₁ := norm_iteratedFDeriv_le_of_coordinateBounds isOpen_ball hHs j hxΩ hD hH
  have h₂ := norm_iteratedFDeriv_le_of_coordinateBounds isOpen_ball hTs j hxΩ hD hTr
  have h₃ := norm_iteratedFDeriv_le_of_coordinateBounds isOpen_ball hQ (j + 1) hxΩ hD hNext
  calc
    _ ≤ (3 : ℝ) ^ j * (A * d⁻¹ ^ j) + (3 : ℝ) ^ j * (A * d⁻¹ ^ j) +
        (3 : ℝ) ^ (j + 1) * (A * d⁻¹ ^ j) := add_le_add (add_le_add h₁ h₂) h₃
    _ = (5 * (3 : ℝ) ^ j * A) * d⁻¹ ^ j := by rw [pow_succ]; ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left (inverse_local_dilation_power_le j hρr) (by positivity)).trans_eq
      (by dsimp only [C]; ring)

end Thesis

end
