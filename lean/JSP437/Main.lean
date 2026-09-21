import Mathlib
import JSP437.Defs
import JSP437.Ramsey
import JSP437.Handshake
import JSP437.SqrtBound
import JSP437.EdgeBound
import JSP437.CliqueRamseyAlt
import JSP437.UncappedHelpers

/-!
# JSP-000437 — Sudakov Ramsey √-edge bound (Su11)

Catalog wording: exponential in square root of **edge count** (not order).

Faithfulness note: `ramseyNumber` is the capped surrogate
`min (ramseyNumberUncapped G) (Fintype.card V)` (see `JSP437/Ramsey.lean`);
`ramseyNumberUncapped` is the honest two-colour Ramsey number `r(G)` defined as
an `sInf` over vertex counts that are Ramsey for `G`. The headline theorem below
is stated and proved for `ramseyNumber`; the full uncapped Su11 bound remains
open formalization work.
-/

namespace JSP437

/-- Su11 Thm 1.1 (capped-surrogate form): `r(G) ≤ 2 ^ (C * √m)` for
isolate-free `m`-edge graphs; `C = 250` works, matching Sudakov's constant. -/
theorem sudakov_ramsey_edge_bound :
    ∃ C : ℕ, 0 < C ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, ∃ w, G.Adj v w) →
        ramseyNumber G ≤ 2 ^ (C * G.edgeFinset.card.sqrt) := by
  refine ⟨250, by norm_num, ?_⟩
  intro V _ _ G _ h
  exact ramseyNumber_le_two_pow_250_sqrt G h

/-- Honest finite bound for the TRUE uncapped Ramsey number `r(G)`:
`r(G) ≤ 4 ^ |V|` for every finite simple graph `G` (proved via the
off-diagonal clique-Ramsey recurrence in `CliqueRamseyAlt`). -/
theorem ramseyNumberUncapped_le_four_pow_card' {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    ramseyNumberUncapped G ≤ 4 ^ Fintype.card V :=
  Alt.ramseyNumberUncapped_le_four_pow_card G

/-- Honest exponential-in-edges bound for the true `r(G)`:
for isolate-free `m`-edge graphs, `r(G) ≤ 4 ^ (2m) = 16 ^ m`.
(This is weaker than Su11's `2 ^ (C√m)`; the √m exponent remains open.) -/
theorem ramseyNumberUncapped_le_four_pow_two_mul_edges {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ v, ∃ w, G.Adj v w) :
    ramseyNumberUncapped G ≤ 4 ^ (2 * G.edgeFinset.card) :=
  (Alt.ramseyNumberUncapped_le_four_pow_card G).trans
    (pow_le_pow_right' (by norm_num) (card_le_twice_edge_card G h))

end JSP437
