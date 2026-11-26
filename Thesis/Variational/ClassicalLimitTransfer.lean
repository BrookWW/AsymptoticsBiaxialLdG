module

public import Thesis.Foundation.WeakGradient

/-! Replacing Sobolev maps by their actual classical representatives. -/

public section

open Filter MeasureTheory Set
open scoped ENNReal Matrix.Norms.Frobenius Topology

namespace Thesis

theorem StrongH1.subsequence {U : Set Point} {u : ℕ → Point → S0} {D : ℕ → Point → Gradient}
    {v : Point → S0} {G : Point → Gradient} {κ : ℕ → ℕ}
    (h : StrongH1 U u D v G) (hκ : Tendsto κ atTop atTop) :
    StrongH1 U (u ∘ κ) (D ∘ κ) v G :=
  ⟨fun n => h.1 (κ n), h.2.1, h.2.2.comp hκ⟩

theorem ConvergesCjLoc.subsequence {j : ℕ} {U : Set Point} {u : ℕ → Point → S0}
    {v : Point → S0} {κ : ℕ → ℕ} (h : ConvergesCjLoc j U u v) (hκ : Tendsto κ atTop atTop) :
    ConvergesCjLoc j U (u ∘ κ) v := by
  refine ⟨fun n => h.1 (κ n), h.2.1, fun k hk K hK hKU s hs => ?_⟩
  exact hκ.eventually (h.2.2 k hk K hK hKU s hs)

theorem ConvergesC1HolderLoc.subsequence {α : ℝ} {U S : Set Point} {u : ℕ → Point → S0}
    {v : Point → S0} {κ : ℕ → ℕ} (h : ConvergesC1HolderLoc α U S u v)
    (hκ : Tendsto κ atTop atTop) : ConvergesC1HolderLoc α U S (u ∘ κ) v := by
  refine ⟨fun n => h.1 (κ n), h.2.1, fun K hK hKW => ?_⟩
  obtain ⟨hFinite, hFinitev, hVal, hGrad, hSemi⟩ := h.2.2 K hK hKW
  exact ⟨fun n => hFinite (κ n), hFinitev, fun s hs => hκ.eventually (hVal s hs),
    fun s hs => hκ.eventually (hGrad s hs), hSemi.comp hκ⟩

theorem StrongH1.congr_ae_graphs {U : Set Point}
    {u v : ℕ → Point → S0} {D E : ℕ → Point → Gradient}
    {p q : Point → S0} {G H : Point → Gradient}
    (h : StrongH1 U u D p G)
    (hu : ∀ n, u n =ᵐ[volume.restrict U] v n) (hD : ∀ n, D n =ᵐ[volume.restrict U] E n)
    (hp : p =ᵐ[volume.restrict U] q) (hG : G =ᵐ[volume.restrict U] H) :
    StrongH1 U v E q H :=
  ⟨fun n => (h.1 n).congr_ae (hu n) (hD n), h.2.1.congr_ae hp hG,
    h.2.2.congr fun n => h1Deviation_congr_ae (hu n) hp (hD n) hG⟩

theorem StrongH1Loc.congr_ae_on_subset {U Ω : Set Point}
    {u v : ℕ → Point → S0} {D E : ℕ → Point → Gradient}
    {p q : Point → S0} {G H : Point → Gradient}
    (h : StrongH1Loc Ω u D p G) (hU : U ⊆ Ω)
    (hu : ∀ n, u n =ᵐ[volume.restrict U] v n) (hD : ∀ n, D n =ᵐ[volume.restrict U] E n)
    (hp : p =ᵐ[volume.restrict U] q) (hG : G =ᵐ[volume.restrict U] H) :
    StrongH1Loc U v E q H := by
  intro W hW hWU
  have hSub : W ⊆ U := subset_closure.trans hWU.2
  have hIn (n : ℕ) := ae_restrict_of_ae_restrict_of_subset hSub (hu n)
  have hDI (n : ℕ) := ae_restrict_of_ae_restrict_of_subset hSub (hD n)
  have hOut := ae_restrict_of_ae_restrict_of_subset hSub hp
  have hGI := ae_restrict_of_ae_restrict_of_subset hSub hG
  exact (h W hW ⟨hWU.1, hWU.2.trans hU⟩).congr_ae_graphs hIn hDI hOut hGI

theorem ConvergesScaledPotentialLoc.congr_ae_on_subset {a : BulkCoefficients}
    {U Ω : Set Point} {ε : ℕ → ElasticScale} {u v : ℕ → Point → S0}
    (h : ConvergesScaledPotentialLoc a Ω ε u) (hU : U ⊆ Ω)
    (hu : ∀ n, u n =ᵐ[volume.restrict U] v n) :
    ConvergesScaledPotentialLoc a U ε v := by
  intro W hW hWU
  have hSub : W ⊆ U := subset_closure.trans hWU.2
  have hEq (n : ℕ) : (fun x => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (u n x)) =ᵐ[volume.restrict W]
      fun x => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a (v n x) :=
    (ae_restrict_of_ae_restrict_of_subset hSub (hu n)).mono fun _ hx =>
      congrArg (fun z => (ε n : ℝ)⁻¹ ^ 2 * bulkPotential a z) hx
  obtain ⟨hLp, hT⟩ := h W hW ⟨hWU.1, hWU.2.trans hU⟩
  exact ⟨fun n => (hLp n).ae_eq (hEq n), hT.congr fun n => eLpNorm_congr_ae (hEq n)⟩

theorem LocallyFiniteIn.isOpen_sdiff {Ω S : Set Point}
    (hS : LocallyFiniteIn Ω S) (hΩ : IsOpen Ω) : IsOpen (Ω \ S) := by
  apply isOpen_iff_mem_nhds.2
  intro x hx
  obtain ⟨R, hR, hB⟩ := Metric.isOpen_iff.1 hΩ x hx.1
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hrΩ := (Metric.closedBall_subset_ball (half_lt_self hR)).trans hB
  have hFin := hS (Metric.closedBall x r) (isCompact_closedBall _ _) hrΩ
  have hopen : IsOpen (Metric.ball x r \ (S ∩ Metric.closedBall x r)) :=
    Metric.isOpen_ball.sdiff hFin.isClosed
  have hx' : x ∈ Metric.ball x r \ (S ∩ Metric.closedBall x r) :=
    ⟨Metric.mem_ball_self hr, fun h => hx.2 h.1⟩
  exact mem_of_superset (hopen.mem_nhds hx') fun y hy =>
    ⟨hrΩ (Metric.ball_subset_closedBall hy.1), fun h => hy.2 ⟨h, Metric.ball_subset_closedBall hy.1⟩⟩

end Thesis
