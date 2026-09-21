# ACCEPTANCE — JSP-000437 (prize-ready gate)

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000437
- Awards CONTRIBUTING: https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md

## Exact original question (English)

> Can every graph's Ramsey number be bounded exponentially in the square root of its edge count?

The accepted resolution: Yes. Sudakov (Su11, Adv. Math.) proved: if G is a graph with m edges and no isolated vertices, then the two-colour Ramsey number satisfies r(G) ≤ 2^{250√m}. The catalog wording is edge count (√m), not vertex order.

## Required Lean theorem name(s) (FULL statement)

| Lean name | Intended statement |
|---|---|
| `sudakov_ramsey_edge_bound` | Su11 Thm 1.1: if G has m edges and no isolated vertices, then r(G) ≤ 2^{250 √m} (hence r(G) = 2^{O(√m)}). Bound is in √edges, not √order. |

**Not sufficient for prize_ready:** weaker special cases, finite truncations, or intermediate lemmas alone.

## Checklist (all must pass)

- [ ] `lake build` succeeds in `lean/`
- [ ] Zero `sorry` / `admit` in all `*.lean` (excluding `.lake`)
- [ ] `#print axioms` on headline theorem(s) shows only standard axioms
- [ ] Public repo HEAD is a full 40-character commit SHA
- [ ] README documents build instructions
- [ ] `formalization.yaml` and/or `ATTRIBUTION.md` name `Yi-111-a` / operators
- [ ] Named headline theorem(s) above exist and are proved

## Harness rule

`prize_ready=true` **only** when every checklist item passes **and** the named headline theorem(s) exist and are proved.
