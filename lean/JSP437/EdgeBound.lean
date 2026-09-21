import Mathlib
import JSP437.Ramsey
import JSP437.Handshake
import JSP437.SqrtBound

namespace JSP437

/-- Combine handshake + arithmetic bound: for isolate-free `G`,
the capped Ramsey number is at most `2 ^ (250 * √m)`, `m` = edge count. -/
theorem ramseyNumber_le_two_pow_250_sqrt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ v, ∃ w, G.Adj v w) :
    ramseyNumber G ≤ 2 ^ (250 * G.edgeFinset.card.sqrt) := by
  calc ramseyNumber G ≤ Fintype.card V := ramseyNumber_le_card G
    _ ≤ 2 * G.edgeFinset.card := card_le_twice_edge_card G h
    _ ≤ 2 ^ (250 * G.edgeFinset.card.sqrt) := two_mul_le_two_pow_250_mul_sqrt _

end JSP437
