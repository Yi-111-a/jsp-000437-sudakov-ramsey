import Mathlib

namespace JSP437

/-- Handshake bound: an isolate-free finite simple graph on `m` edges has
at most `2m` vertices. Proof: `card V = ∑ v, 1 ≤ ∑ v, G.degree v = 2 * m`. -/
theorem card_le_twice_edge_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ v, ∃ w, G.Adj v w) :
    Fintype.card V ≤ 2 * G.edgeFinset.card := by
  rw [← G.sum_degrees_eq_twice_card_edges, ← Finset.card_univ, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v _ ↦ (G.degree_pos_iff_exists_adj v).mpr (h v)

end JSP437
