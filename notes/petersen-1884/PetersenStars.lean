import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Lean.Elab.Tactic.Omega

namespace PetersenStars

abbrev Vertex := Fin 10
abbrev Edge := Vertex × Vertex
abbrev Star := Vertex × Finset Vertex

def pair (a b : Vertex) : Edge := if a ≤ b then (a, b) else (b, a)

def edges : List Edge :=
  [(0,1), (1,2), (2,3), (3,4), (0,4), (0,5), (1,6), (2,7), (3,8), (4,9),
   (5,7), (7,9), (6,9), (6,8), (5,8)]

def centers : List Star → Finset Vertex
  | [] => ∅
  | s :: rest => insert s.1 (centers rest)

def drawn : List Star → Finset Edge
  | [] => ∅
  | s :: rest => s.2.image (pair s.1) ∪ drawn rest

def reads : List Star → Nat
  | [] => 0
  | s :: rest => s.2.card + reads rest

-- A nonempty list of nonempty stars uses this many gates when each star has
-- its own binary OR tree, followed by AND with its center and a final OR tree.
def gateCount (stars : List Star) : Nat := reads stars + stars.length - 1

def meetsEveryEdge (s : Finset Vertex) : Bool :=
  edges.all fun e => decide (e.1 ∈ s ∨ e.2 ∈ s)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem coverFloor : ∀ s : Finset Vertex, meetsEveryEdge s = true → 6 ≤ s.card := by
  decide

theorem edgeCount : edges.toFinset.card = 15 := by decide

theorem centerBound (ss : List Star) : (centers ss).card ≤ ss.length := by
  induction ss with
  | nil => simp [centers]
  | cons s rest ih =>
    exact (Finset.card_insert_le s.1 (centers rest)).trans (Nat.add_le_add_right ih 1)

theorem readBound (ss : List Star) : (drawn ss).card ≤ reads ss := by
  induction ss with
  | nil => simp [drawn, reads]
  | cons s rest ih =>
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le ih)

theorem incident (ss : List Star) (e : Edge) (he : e ∈ drawn ss) :
    e.1 ∈ centers ss ∨ e.2 ∈ centers ss := by
  induction ss with
  | nil => simp [drawn] at he
  | cons s rest ih =>
    rcases Finset.mem_union.mp he with hs | hr
    · obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hs
      by_cases h : s.1 ≤ w
      · exact Or.inl (by simp [centers, pair, h])
      · exact Or.inr (by simp [centers, pair, h])
    · rcases ih hr with h | h
      · exact Or.inl (Finset.mem_insert_of_mem h)
      · exact Or.inr (Finset.mem_insert_of_mem h)

theorem lowerBound (ss : List Star) (cover : edges.toFinset ⊆ drawn ss) :
    20 ≤ gateCount ss := by
  have hc : meetsEveryEdge (centers ss) = true := by
    apply List.all_eq_true.mpr
    intro e he
    exact decide_eq_true (incident ss e (cover (List.mem_toFinset.mpr he)))
  have hs := (coverFloor (centers ss) hc).trans (centerBound ss)
  have hr := (Finset.card_le_card cover).trans (readBound ss)
  rw [edgeCount] at hr
  unfold gateCount
  omega

def exampleCover : List Star :=
  [(0, {1, 4, 5}), (1, {2, 6}), (3, {2, 4, 8}), (7, {2, 5, 9}),
   (8, {6, 5}), (9, {4, 6})]

theorem attained : drawn exampleCover = edges.toFinset ∧ gateCount exampleCover = 20 := by
  decide

-- A product of two disjunctions generates all pairs in the Cartesian product.
abbrev Block := Finset Vertex × Finset Vertex

def blockEdges (t : Block) : Finset Edge := t.1.biUnion fun a => t.2.image (pair a)

def valid (t : Block) : Prop :=
  t.1.Nonempty ∧ t.2.Nonempty ∧ ∀ a ∈ t.1, ∀ b ∈ t.2, pair a b ∈ edges

def blockDrawn : List Block → Finset Edge
  | [] => ∅
  | t :: rest => blockEdges t ∪ blockDrawn rest

def blockGates : List Block → Nat
  | [] => 0
  | t :: rest => (t.1.card + t.2.card - 1) + blockGates rest

theorem pair_comm (a b : Vertex) : pair a b = pair b a := by
  rcases lt_trichotomy a b with h | h | h
  · simp [pair, h.le, not_le.mpr h]
  · subst b; rfl
  · simp [pair, h.le, not_le.mpr h]

-- Two distinct vertices have at most one common neighbor.
set_option maxHeartbeats 3000000 in
theorem noRectangle : ∀ a a' b b' : Vertex, a ≠ a' → b ≠ b' →
    pair a b ∈ edges → pair a b' ∈ edges → pair a' b ∈ edges → pair a' b' ∉ edges := by
  decide

theorem singletonSide (A B : Finset Vertex) (ok : valid (A, B)) :
    (∃ a, A = {a}) ∨ (∃ b, B = {b}) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hed⟩ := ok
  by_cases hA : ∀ x ∈ A, x = a
  · exact Or.inl ⟨a, Finset.eq_singleton_iff_unique_mem.mpr ⟨ha, hA⟩⟩
  push Not at hA
  obtain ⟨a', ha', hne⟩ := hA
  refine Or.inr ⟨b, Finset.eq_singleton_iff_unique_mem.mpr ⟨hb, ?_⟩⟩
  intro b' hb'
  by_contra hdiff
  exact noRectangle a' a b' b hne hdiff (hed a' ha' b' hb') (hed a' ha' b hb)
    (hed a ha b' hb') (hed a ha b hb)

theorem asStar (t : Block) (ok : valid t) :
    ∃ s : Star, blockEdges t = s.2.image (pair s.1) ∧
      t.1.card + t.2.card - 1 = s.2.card := by
  obtain ⟨A, B⟩ := t
  rcases singletonSide A B ok with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact ⟨(a, B), by simp [blockEdges], by simp⟩
  · refine ⟨(b, A), ?_, by simp⟩
    ext e
    simp [blockEdges, pair_comm b, eq_comm]

theorem normalize (bs : List Block) (ok : ∀ t ∈ bs, valid t) :
    ∃ ss : List Star, blockDrawn bs = drawn ss ∧ blockGates bs = reads ss ∧
      bs.length = ss.length := by
  induction bs with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | cons t rest ih =>
    obtain ⟨s, hE, hG⟩ := asStar t (ok t (by simp))
    obtain ⟨ss, hD, hR, hL⟩ := ih (fun u hu => ok u (by simp [hu]))
    exact ⟨s :: ss, by simp only [blockDrawn, drawn, hD, hE],
      by simp only [blockGates, reads, hG, hR], by simp only [List.length_cons, hL]⟩

theorem blockLowerBound (bs : List Block) (ok : ∀ t ∈ bs, valid t)
    (cover : edges.toFinset ⊆ blockDrawn bs) :
    20 ≤ blockGates bs + bs.length - 1 := by
  obtain ⟨ss, hD, hR, hL⟩ := normalize bs ok
  rw [hD] at cover
  rw [hR, hL]
  exact lowerBound ss cover

def fires (bs : List Block) (x : Vertex → Bool) : Prop :=
  ∃ t ∈ bs, (∃ a ∈ t.1, x a = true) ∧ (∃ b ∈ t.2, x b = true)

def edgeValue (x : Vertex → Bool) : Prop :=
  ∃ e ∈ edges, x e.1 = true ∧ x e.2 = true

instance (x : Vertex → Bool) : Decidable (edgeValue x) := by
  unfold edgeValue
  infer_instance

def selectPair (a b i : Vertex) : Bool := decide (i = a ∨ i = b)

theorem twoVertexTest : ∀ a b : Vertex, edgeValue (selectPair a b) ↔ pair a b ∈ edges := by
  decide

theorem onlyPair : ∀ (e : Edge), e ∈ edges → ∀ a b : Vertex,
    selectPair e.1 e.2 a = true → selectPair e.1 e.2 b = true →
    pair a b ∈ edges → pair a b = e := by
  decide

theorem memberBlock (bs : List Block) (t : Block) (ht : t ∈ bs)
    (a b : Vertex) (ha : a ∈ t.1) (hb : b ∈ t.2) : pair a b ∈ blockDrawn bs := by
  induction bs with
  | nil => simp at ht
  | cons u rest ih =>
    rcases List.mem_cons.mp ht with rfl | h
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨a, ha, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩)
    · exact Finset.mem_union_right _ (ih h)

theorem sourceBlock (bs : List Block) (e : Edge) (he : e ∈ blockDrawn bs) :
    ∃ t ∈ bs, ∃ a ∈ t.1, ∃ b ∈ t.2, pair a b = e := by
  induction bs with
  | nil => simp [blockDrawn] at he
  | cons t rest ih =>
    rcases Finset.mem_union.mp he with ht | hr
    · obtain ⟨a, ha, h⟩ := Finset.mem_biUnion.mp ht
      obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp h
      exact ⟨t, by simp, a, ha, b, hb, hab⟩
    · obtain ⟨u, hu, h⟩ := ih hr
      exact ⟨u, List.mem_cons_of_mem t hu, h⟩

theorem selected (x : Vertex → Bool) (a b : Vertex) :
    (x (pair a b).1 = true ∧ x (pair a b).2 = true) ↔ (x a = true ∧ x b = true) := by
  by_cases h : a ≤ b
  · simp [pair, h]
  · simp [pair, h, and_comm]

theorem correctOfEdges (bs : List Block) (cover : blockDrawn bs = edges.toFinset)
    (x : Vertex → Bool) : fires bs x ↔ edgeValue x := by
  constructor
  · rintro ⟨t, ht, ⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩
    have hp := memberBlock bs t ht a b ha hb
    rw [cover] at hp
    exact ⟨pair a b, List.mem_toFinset.mp hp, (selected x a b).mpr ⟨hxa, hxb⟩⟩
  · rintro ⟨e, he, hx, hy⟩
    have h : e ∈ blockDrawn bs := cover ▸ List.mem_toFinset.mpr he
    obtain ⟨t, ht, a, ha, b, hb, hab⟩ := sourceBlock bs e h
    have hh := (selected x a b).mp (hab ▸ And.intro hx hy)
    exact ⟨t, ht, ⟨a, ha, hh.1⟩, ⟨b, hb, hh.2⟩⟩

-- With separate binary trees for the input disjunctions, the products, and the
-- output disjunction, every formula that computes the edge function costs at
-- least twenty gates. Other circuit shapes can share internal gates.
theorem formulaLowerBound (bs : List Block)
    (nonempty : ∀ t ∈ bs, t.1.Nonempty ∧ t.2.Nonempty)
    (correct : ∀ x, fires bs x ↔ edgeValue x) :
    20 ≤ blockGates bs + bs.length - 1 := by
  have ok (t : Block) (ht : t ∈ bs) : valid t := by
    refine ⟨(nonempty t ht).1, (nonempty t ht).2, ?_⟩
    intro a ha b hb
    apply (twoVertexTest a b).mp
    exact (correct _).mp ⟨t, ht, ⟨a, ha, by simp [selectPair]⟩,
      ⟨b, hb, by simp [selectPair]⟩⟩
  apply blockLowerBound bs ok
  intro e he
  have he' := List.mem_toFinset.mp he
  have active : edgeValue (selectPair e.1 e.2) :=
    ⟨e, he', by simp [selectPair], by simp [selectPair]⟩
  obtain ⟨t, ht, ⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩ := (correct _).mpr active
  have hpair := onlyPair e he' a b hxa hxb ((ok t ht).2.2 a ha b hb)
  rw [← hpair]
  exact memberBlock bs t ht a b ha hb

def exampleFormula : List Block := exampleCover.map fun s => ({s.1}, s.2)

theorem exampleCost : blockGates exampleFormula + exampleFormula.length - 1 = 20 := by
  decide

theorem exampleCorrect (x : Vertex → Bool) : fires exampleFormula x ↔ edgeValue x := by
  exact correctOfEdges exampleFormula (by decide) x

end PetersenStars
