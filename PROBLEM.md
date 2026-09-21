# JSP-000437 — Can every graph's Ramsey number be bounded exponentially in the square root of its edge count?

- **id:** JSP-000437
- **title:** Can every graph's Ramsey number be bounded exponentially in the square root of its edge count?
- **area:** Graph theory / Ramsey theory
- **status:** Solved
- **Lean:** No (formalization target)
- **Eligible / Claim:** No / Unavailable
- **role:** Formalize path (Solved + Lean=No)

## Statement

Can every graph's Ramsey number be bounded exponentially in the square root of its edge count?

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0401-0500.md#JSP-000437
- Awards home: https://github.com/TheJustinSunPrize/awards

## Primary papers

- Sudakov (Su11), Adv. Math. (2011), 601–609 — full resolution
- Alon–Krivelevich–Sudakov (AKS03), Combin. Probab. Comput. (2003)

## Accepted mathematical answer

Yes. Sudakov (Su11, Adv. Math.) proved: if G is a graph with m edges and no isolated vertices, then the two-colour Ramsey number satisfies r(G) ≤ 2^{250√m}. The catalog wording is edge count (√m), not vertex order.

## Success criteria

- `lake build` succeeds
- Zero `sorry` / `admit`
- Named headline theorem(s) in ACCEPTANCE.md proved
