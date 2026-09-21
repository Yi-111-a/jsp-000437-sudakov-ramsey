import JSP437.Ramsey

/-!
# Alternative clique–Ramsey bound for `ramseyNumberUncapped`

An independent proof that the honest (uncapped) two-colour Ramsey number of a
finite simple graph is finite, with the explicit bound `r(G) ≤ 4 ^ |V|`.

The route is the off-diagonal clique–Ramsey recurrence
`R(a,b) ≤ R(a-1,b) + R(a,b-1)` with `R(0,b) = R(a,0) = 1` (the empty clique),
which yields `AltCliqueRamsey a b (2 ^ (a + b))` by induction on `a + b`.
For `a = b = |V|` this gives `4 ^ |V|`, and a monochromatic clique of size
`|V|` yields a monochromatic copy of `G` via `Fintype.equivOfCardEq`.

Everything lives in `JSP437.Alt` to avoid name clashes.
-/

namespace JSP437.Alt

/-- A finset of vertices all of whose distinct pairs carry colour `col`. -/
def IsAltMonoClique {n : ℕ} (c : EdgeColoring n) (col : Bool) (s : Finset (Fin n)) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → c x y = col

/-- Off-diagonal clique Ramsey property: every valid 2-colouring of `K_n`
contains a `true`-clique of size `a` or a `false`-clique of size `b`. -/
def AltCliqueRamsey (a b n : ℕ) : Prop :=
  ∀ c : EdgeColoring n, c.Valid →
    (∃ s : Finset (Fin n), s.card = a ∧ IsAltMonoClique c true s) ∨
    (∃ s : Finset (Fin n), s.card = b ∧ IsAltMonoClique c false s)

/-- Transport a monochromatic clique along an order embedding `e : Fin R ↪o Fin n`:
the image `u.map e` is a clique of the same colour inside any `s` containing the
range of `e`. -/
theorem alt_liftClique {n R : ℕ} {c : EdgeColoring n} (e : Fin R ↪o Fin n)
    {s : Finset (Fin n)} (he : ∀ i, e i ∈ s) {col : Bool} {k : ℕ}
    {u : Finset (Fin R)} (hucard : u.card = k)
    (hucl : ∀ x ∈ u, ∀ y ∈ u, x ≠ y → c (e x) (e y) = col) :
    (u.map e.toEmbedding).card = k ∧
      (∀ x ∈ u.map e.toEmbedding, x ∈ s) ∧
      (∀ x ∈ u.map e.toEmbedding, ∀ y ∈ u.map e.toEmbedding, x ≠ y → c x y = col) := by
  refine ⟨by rw [Finset.card_map, hucard], fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    exact he i
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact hucl i hi j hj fun h => hxy (by rw [h])

/-- Extend a monochromatic clique `u` by a vertex `v` joined to every vertex of
`u` by the same colour. -/
theorem alt_extendClique {n : ℕ} {c : EdgeColoring n} (hc : c.Valid) {v : Fin n}
    {u : Finset (Fin n)} {col : Bool} {k : ℕ} (hvc : ∀ x ∈ u, c v x = col)
    (hvu : v ∉ u) (hucard : u.card = k)
    (hucl : ∀ x ∈ u, ∀ y ∈ u, x ≠ y → c x y = col) :
    (insert v u).card = k + 1 ∧
      (∀ x ∈ insert v u, ∀ y ∈ insert v u, x ≠ y → c x y = col) := by
  refine ⟨by rw [Finset.card_insert_of_notMem hvu, hucard], fun x hx y hy hxy => ?_⟩
  rcases Finset.mem_insert.mp hx with rfl | hxu
  · rcases Finset.mem_insert.mp hy with rfl | hyu
    · exact absurd rfl hxy
    · exact hvc y hyu
  · rcases Finset.mem_insert.mp hy with rfl | hyu
    · rw [hc.1]; exact hvc x hxu
    · exact hucl x hxu y hyu hxy

/-- The clique Ramsey bound `R(a,b) ≤ 2 ^ (a + b)`, proved by induction on the
budget `k ≥ a + b`. -/
theorem altCliqueRamsey_le :
    ∀ (k a b : ℕ), a + b ≤ k → AltCliqueRamsey a b (2 ^ (a + b)) := by
  intro k
  induction k with
  | zero =>
      intro a b hab c _
      have ha : a = 0 := by omega
      subst ha
      exact Or.inl ⟨∅, Finset.card_empty, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | succ k ih =>
      intro a b hab c hc
      rcases a with _ | a'
      · exact Or.inl ⟨∅, Finset.card_empty, fun x hx => absurd hx (Finset.notMem_empty x)⟩
      rcases b with _ | b'
      · exact Or.inr ⟨∅, Finset.card_empty, fun x hx => absurd hx (Finset.notMem_empty x)⟩
      -- a = a'+1, b = b'+1; apply the recurrence via a distinguished vertex v.
      have hnn : 2 ^ (a' + 1 + (b' + 1)) = 2 * 2 ^ (a' + b' + 1) := by
        rw [show a' + 1 + (b' + 1) = a' + b' + 1 + 1 by omega, pow_succ]; ring
      have hNpos : 0 < 2 ^ (a' + 1 + (b' + 1)) := by positivity
      have v : Fin (2 ^ (a' + 1 + (b' + 1))) := ⟨0, hNpos⟩
      have ihA := ih a' (b' + 1) (by omega)
      have ihB := ih (a' + 1) b' (by omega)
      have hs_card : (Finset.univ.erase v).card = 2 ^ (a' + 1 + (b' + 1)) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
      have hsum : ((Finset.univ.erase v).filter fun w => c v w = true).card
            + ((Finset.univ.erase v).filter fun w => ¬ c v w = true).card
            = 2 ^ (a' + 1 + (b' + 1)) - 1 := by
        rw [← hs_card]
        exact Finset.card_filter_add_card_filter_not _
      have hsplit :
          2 ^ (a' + b' + 1) ≤ ((Finset.univ.erase v).filter fun w => c v w = true).card
            ∨ 2 ^ (a' + b' + 1)
              ≤ ((Finset.univ.erase v).filter fun w => ¬ c v w = true).card := by
        omega
      rcases hsplit with hbig | hbig
      · -- Many `true` neighbours of `v`: find an `a'`-true-clique among them and
        -- extend it by `v`, or else a `b`-false-clique directly.
        have hbig' : 2 ^ (a' + (b' + 1))
            ≤ ((Finset.univ.erase v).filter fun w => c v w = true).card := hbig
        obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hbig'
        have hc' : EdgeColoring.Valid (fun i j : Fin (2 ^ (a' + (b' + 1))) =>
              c (t.orderEmbOfFin htcard i) (t.orderEmbOfFin htcard j)) :=
          ⟨fun i j => hc.1 _ _, fun i => hc.2 _⟩
        rcases ihA _ hc' with ⟨s', hs'card, hs'cl⟩ | ⟨s', hs'card, hs'cl⟩
        · obtain ⟨hucard, husub, hucl⟩ := alt_liftClique (t.orderEmbOfFin htcard)
            (fun i => Finset.orderEmbOfFin_mem t htcard i) hs'card hs'cl
          have hvc : ∀ x ∈ s'.map (t.orderEmbOfFin htcard).toEmbedding, c v x = true := by
            intro x hx
            have hx1 := htsub (husub x hx)
            exact (Finset.mem_filter.mp hx1).2
          have hvu : v ∉ s'.map (t.orderEmbOfFin htcard).toEmbedding := by
            intro hv
            have hv1 := htsub (husub v hv)
            exact (Finset.mem_erase.mp (Finset.mem_filter.mp hv1).1).1 rfl
          obtain ⟨hwcard, hwcl⟩ := alt_extendClique hc hvc hvu hucard hucl
          exact Or.inl ⟨_, hwcard, hwcl⟩
        · obtain ⟨hucard, _, hucl⟩ := alt_liftClique (t.orderEmbOfFin htcard)
            (fun i => Finset.orderEmbOfFin_mem t htcard i) hs'card hs'cl
          exact Or.inr ⟨_, hucard, hucl⟩
      · -- Many `false` neighbours of `v`: symmetric.
        have hbig2 : 2 ^ (a' + 1 + b')
            ≤ ((Finset.univ.erase v).filter fun w => ¬ c v w = true).card := by
          have hEq : a' + 1 + b' = a' + b' + 1 := by omega
          rw [hEq]; exact hbig
        obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hbig2
        have hc' : EdgeColoring.Valid (fun i j : Fin (2 ^ (a' + 1 + b')) =>
              c (t.orderEmbOfFin htcard i) (t.orderEmbOfFin htcard j)) :=
          ⟨fun i j => hc.1 _ _, fun i => hc.2 _⟩
        rcases ihB _ hc' with ⟨s', hs'card, hs'cl⟩ | ⟨s', hs'card, hs'cl⟩
        · obtain ⟨hucard, _, hucl⟩ := alt_liftClique (t.orderEmbOfFin htcard)
            (fun i => Finset.orderEmbOfFin_mem t htcard i) hs'card hs'cl
          exact Or.inl ⟨_, hucard, hucl⟩
        · obtain ⟨hucard, husub, hucl⟩ := alt_liftClique (t.orderEmbOfFin htcard)
            (fun i => Finset.orderEmbOfFin_mem t htcard i) hs'card hs'cl
          have hvc : ∀ x ∈ s'.map (t.orderEmbOfFin htcard).toEmbedding, c v x = false := by
            intro x hx
            have hx1 := htsub (husub x hx)
            have hne := (Finset.mem_filter.mp hx1).2
            simpa using hne
          have hvu : v ∉ s'.map (t.orderEmbOfFin htcard).toEmbedding := by
            intro hv
            have hv1 := htsub (husub v hv)
            exact (Finset.mem_erase.mp (Finset.mem_filter.mp hv1).1).1 rfl
          obtain ⟨hwcard, hwcl⟩ := alt_extendClique hc hvc hvu hucard hucl
          exact Or.inr ⟨_, hwcard, hwcl⟩

/-- A monochromatic clique of size `|V|` yields a monochromatic copy of `G`. -/
theorem alt_hasMonoCopy {V : Type*} [Fintype V] (G : SimpleGraph V) {n : ℕ}
    {c : EdgeColoring n} (s : Finset (Fin n)) {col : Bool}
    (hcard : s.card = Fintype.card V) (hcl : IsAltMonoClique c col s) :
    HasMonoCopy G c := by
  have hcard' : Fintype.card V = Fintype.card s := by
    rw [Fintype.card_coe, hcard]
  let e : V ≃ s := Fintype.equivOfCardEq hcard'
  refine ⟨fun v => (e v).val, col, fun x y hxy => ?_, fun v w hvw => ?_⟩
  · exact e.injective (Subtype.ext hxy)
  · exact hcl (e v).val (e v).property (e w).val (e w).property
      (fun h => G.ne_of_adj hvw (e.injective (Subtype.ext h)))

/-- `4 ^ |V|` is a Ramsey number for `G`. -/
theorem alt_isRamseyFor_four_pow {V : Type*} [Fintype V] (G : SimpleGraph V) :
    IsRamseyFor G (4 ^ Fintype.card V) := by
  have hexp : (4 : ℕ) ^ Fintype.card V = 2 ^ (Fintype.card V + Fintype.card V) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    omega
  rw [hexp]
  intro c hc
  have h := altCliqueRamsey_le (2 * Fintype.card V) (Fintype.card V) (Fintype.card V)
    (by omega) c hc
  rcases h with ⟨s, hscard, hscl⟩ | ⟨s, hscard, hscl⟩
  · exact alt_hasMonoCopy G s hscard hscl
  · exact alt_hasMonoCopy G s hscard hscl

/-- The honest (uncapped) two-colour Ramsey number of a finite simple graph is
at most `4 ^ |V|`. -/
theorem ramseyNumberUncapped_le_four_pow_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    ramseyNumberUncapped G ≤ 4 ^ Fintype.card V :=
  Nat.sInf_le (alt_isRamseyFor_four_pow G)

end JSP437.Alt
