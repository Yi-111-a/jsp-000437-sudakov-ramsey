# JSP-000437 — Sudakov Ramsey √-edge bound

Lean 4 formalization of the two-colour Ramsey number bound for graphs,
targeting Sudakov's theorem (Su11, Adv. Math. 2011): isolate-free m-edge
graphs satisfy r(G) ≤ 2^(C·√m).

## Build
- Toolchain: `leanprover/lean4:v4.34.0` (see `lean-toolchain`), managed by elan.
- Dependencies: mathlib4 @ v4.34.0 (see `lake-manifest.json`).
- Build: `export PATH="$HOME/.elan/bin:$PATH"; lake build`

## Modules
- `JSP437.Defs` — scaffold.
- `JSP437.Ramsey` — `EdgeColoring`, `HasMonoCopy`, `IsRamseyFor`,
  `ramseyNumberUncapped` (honest r(G) as sInf), `ramseyNumber` (capped surrogate).
- `JSP437.Handshake` — isolate-free m-edge graph ⇒ |V| ≤ 2m.
- `JSP437.SqrtBound` — arithmetic `2m ≤ 2^(250·√m)`.
- `JSP437.EdgeBound` — capped bound `ramseyNumber G ≤ 2^(250·√m)`.
- `JSP437.Main` — headline `sudakov_ramsey_edge_bound`.
- `JSP437.AxiomsCheck` — `#print axioms` audit of headline theorem.

## Faithfulness note
`ramseyNumber` is `min (ramseyNumberUncapped G) (card V)` — a capped surrogate;
the proved headline bound uses it. `ramseyNumberUncapped` is the honest r(G);
the full uncapped Su11 bound is open formalization work.
