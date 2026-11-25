import PEqualNP.Defs.CircuitLowerBounds

namespace PetersenInput

abbrev Vertex := Fin 10

def edge (x : Vertex → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

-- For each vertex choose an incident edge. Its other endpoint alone is independent.
def partner (v : Vertex) : Vertex :=
  ([1, 0, 1, 2, 3, 0, 1, 2, 3, 4] : List Vertex).getD v.val 0

def singletonInput (v i : Vertex) : Bool := decide (i = partner v)
def pairInput (v i : Vertex) : Bool := decide (i = partner v ∨ i = v)

theorem witnesses : ∀ v : Vertex,
    edge (singletonInput v) = false ∧ edge (pairInput v) = true := by decide

theorem offVertex (v i : Vertex) (hi : i ≠ v) : singletonInput v i = pairInput v i := by
  simp [singletonInput, pairInput, hi]

def wires (r : Vertex → Vertex) (u : Bool → Bool) (x : Vertex → Bool) : List Bool :=
  List.ofFn (x ∘ r) ++ [u (x 0)]

-- Applies even to an unrestricted decoder of the eleven wires.
theorem missingInput (decode : List Bool → Bool) (r : Vertex → Vertex) (u : Bool → Bool)
    (v : Vertex) (missing : ∀ i, r i ≠ v) (invisible : v ≠ 0 ∨ u false = u true) :
    ∃ x, decode (wires r u x) ≠ edge x := by
  have ordinary : singletonInput v ∘ r = pairInput v ∘ r :=
    funext fun i => offVertex v (r i) (missing i)
  have extra : u (singletonInput v 0) = u (pairInput v 0) := by
    rcases invisible with hv | hu
    · rw [offVertex v 0 (Ne.symm hv)]
    · cases singletonInput v 0 <;> cases pairInput v 0 <;> simp_all
  have same : wires r u (singletonInput v) = wires r u (pairInput v) := by
    simp only [wires, ordinary, extra]
  by_cases h : decode (wires r u (singletonInput v)) = edge (singletonInput v)
  · refine ⟨pairInput v, ?_⟩
    rw [← same, h, (witnesses v).1, (witnesses v).2]
    decide
  · exact ⟨singletonInput v, h⟩

-- Every vertex absent from the ten input positions must be vertex zero, encoded
-- by a nonconstant extra wire. The gate basis and the gate budget are arbitrary.
theorem coversInputs (c : PEqualNP.CircuitLowerBounds.Circuit)
    (r : Vertex → Vertex) (u : Bool → Bool)
    (correct : ∀ x, c.eval (wires r u x) = edge x)
    (v : Vertex) (missing : ∀ i, r i ≠ v) : v = 0 ∧ u false ≠ u true := by
  constructor
  · by_contra hn
    obtain ⟨x, hx⟩ := missingInput c.eval r u v missing (Or.inl hn)
    exact hx (correct x)
  · intro hu
    obtain ⟨x, hx⟩ := missingInput c.eval r u v missing (Or.inr hu)
    exact hx (correct x)

end PetersenInput
