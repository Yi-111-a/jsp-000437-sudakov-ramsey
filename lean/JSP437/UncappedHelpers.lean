import Mathlib
import JSP437.Ramsey

/-!
# JSP-000437 — Helper lemmas about `ramseyNumberUncapped`

Small API lemmas around the uncapped Ramsey number, plus concrete
non-vacuity instances: the empty graph `⊥` on any finite vertex type
(`ramseyNumberUncapped ≤ |V|`) and the complete graph `⊤` on `Fin 2`
(`ramseyNumberUncapped ≤ 2`).
-/

namespace JSP437

/-- If `n` is Ramsey for `G`, the uncapped Ramsey number is at most `n`. -/
theorem ramseyNumberUncapped_le_of_isRamseyFor {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (h : IsRamseyFor G n) : ramseyNumberUncapped G ≤ n :=
  Nat.sInf_le h

/-- The capped surrogate never exceeds the true uncapped value. -/
theorem ramseyNumber_le_uncapped {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ramseyNumber G ≤ ramseyNumberUncapped G :=
  min_le_left _ _

/-- When the uncapped value already fits inside `|V|`, the cap is inactive. -/
theorem ramseyNumber_eq_uncapped_of_le_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : ramseyNumberUncapped G ≤ Fintype.card V) :
    ramseyNumber G = ramseyNumberUncapped G :=
  min_eq_left h

/-- The empty graph on `V` embeds monochromatically into `K_{|V|}` for the
trivial reason that it has no edges at all. -/
theorem isRamseyFor_bot {V : Type*} [Fintype V] :
    IsRamseyFor (⊥ : SimpleGraph V) (Fintype.card V) := by
  intro c _hc
  exact ⟨(Fintype.equivFin V : V → Fin (Fintype.card V)), true,
    (Fintype.equivFin V).injective,
    fun {v w} hvw => ((SimpleGraph.bot_adj v w).mp hvw).elim⟩

theorem ramseyNumberUncapped_bot_le {V : Type*} [Fintype V] :
    ramseyNumberUncapped (⊥ : SimpleGraph V) ≤ Fintype.card V :=
  ramseyNumberUncapped_le_of_isRamseyFor _ isRamseyFor_bot

/-- `K₂` is Ramsey for `K₂`: under any valid colouring the single edge
`{0, 1}` is a monochromatic copy of `⊤` on `Fin 2`. -/
theorem isRamseyFor_top_two :
    IsRamseyFor (⊤ : SimpleGraph (Fin 2)) 2 := by
  intro c hc
  refine ⟨id, c 0 1, Function.injective_id, fun {v w} hvw => ?_⟩
  rw [SimpleGraph.top_adj] at hvw
  have hvw' : (v = 0 ∧ w = 1) ∨ (v = 1 ∧ w = 0) := by
    fin_cases v <;> fin_cases w <;> simp_all
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hvw'
  · rfl
  · exact hc.1 _ _

theorem ramseyNumberUncapped_top_two_le :
    ramseyNumberUncapped (⊤ : SimpleGraph (Fin 2)) ≤ 2 :=
  ramseyNumberUncapped_le_of_isRamseyFor _ isRamseyFor_top_two

end JSP437
