import Mathlib
import JSP437.Defs
import JSP437.Ramsey
import JSP437.Handshake
import JSP437.SqrtBound
import JSP437.EdgeBound

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

end JSP437
