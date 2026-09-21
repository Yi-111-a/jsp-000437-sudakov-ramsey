import Mathlib

/-!
# JSP-000437 — Ramsey number definitions for finite graphs

Two-colourings of the edges of `K_n`, monochromatic embedded copies,
and the honest Ramsey number `r(G)` defined as an `sInf` over `ℕ`.
-/

namespace JSP437

/-- A 2-colouring of the edges of the complete graph on `n` vertices,
encoded as a `Bool`-valued function on ordered pairs. -/
abbrev EdgeColoring (n : ℕ) := Fin n → Fin n → Bool

/-- A colouring is valid when it is symmetric and the diagonal is `false`. -/
def EdgeColoring.Valid {n : ℕ} (c : EdgeColoring n) : Prop :=
  (∀ i j, c i j = c j i) ∧ ∀ i, c i i = false

/-- `G` has a monochromatic copy under `c`: an injective vertex map sending
every edge of `G` to a single colour `b`. -/
def HasMonoCopy {V : Type*} (G : SimpleGraph V) {n : ℕ} (c : EdgeColoring n) : Prop :=
  ∃ (f : V → Fin n) (b : Bool), Function.Injective f ∧
    ∀ ⦃v w : V⦄, G.Adj v w → c (f v) (f w) = b

/-- `n` is a Ramsey number for `G`: every valid 2-colouring of `K_n`
contains a monochromatic copy of `G`. -/
def IsRamseyFor {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ c : EdgeColoring n, c.Valid → HasMonoCopy G c

/-- The honest Ramsey number of `G`: the least `n` such that every valid
2-colouring of `K_n` contains a monochromatic copy of `G`
(`0` by convention if no such `n` exists). -/
noncomputable def ramseyNumberUncapped {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {n | IsRamseyFor G n}

/-- Surrogate Ramsey number capped at `|V|`.

The cap by `Fintype.card V` is a provisional placeholder pending the full
Su11 proof; `ramseyNumberUncapped` is the true (uncapped) Ramsey number. -/
noncomputable def ramseyNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  min (ramseyNumberUncapped G) (Fintype.card V)

theorem ramseyNumber_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ramseyNumber G ≤ Fintype.card V :=
  min_le_right _ _

/-- Any `n` that is Ramsey for `G` must be at least `|V|`, since an
injective copy of `G` inside `K_n` forces `Fintype.card V ≤ n`. -/
theorem card_le_of_isRamseyFor {V : Type*} [Fintype V] (G : SimpleGraph V) {n : ℕ}
    (h : IsRamseyFor G n) : Fintype.card V ≤ n := by
  have hvalid : EdgeColoring.Valid (fun i j : Fin n => if i = j then false else true) := by
    constructor
    · intro i j
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [hij, hij.symm]
    · intro i
      simp
  obtain ⟨f, _b, hf, _⟩ := h _ hvalid
  simpa using Fintype.card_le_of_injective f hf

/-- Monotonicity in the number of vertices: restrict a colouring of `K_m`
to `K_n` via `Fin.castLE` and lift the monochromatic copy back. -/
theorem IsRamseyFor.mono {V : Type*} (G : SimpleGraph V) {n m : ℕ}
    (h : IsRamseyFor G n) (hnm : n ≤ m) : IsRamseyFor G m := by
  intro c hc
  obtain ⟨f', b, hf'_inj, hf'_mono⟩ :=
    h (fun i j : Fin n => c (i.castLE hnm) (j.castLE hnm))
      ⟨fun i j => hc.1 _ _, fun i => hc.2 _⟩
  exact ⟨fun v => (f' v).castLE hnm, b,
    (Fin.castLE_injective hnm).comp hf'_inj,
    fun _ _ hvw => hf'_mono hvw⟩

end JSP437
