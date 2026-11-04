module

public import StacksFrontier.CategoryTheory.Sites.DisjointCoverSections

/-!
# Sections of a sheaf over a covering by two disjoint pieces

For a covering of an object by two disjoint monomorphisms, a section of a sheaf of types over the
object is exactly a pair of sections over the two pieces.

## Main definitions

* `CategoryTheory.pairFamily` and `CategoryTheory.pairHom` present two objects, respectively two
  morphisms with common target, as a family indexed by `Bool`.

## Main results

* `CategoryTheory.pairHom_disjoint`: the pairwise disjointness condition of
  `CategoryTheory.Presieve.IsSheaf.existsUnique_section_of_disjoint_arrows` for a two-element
  family is the single condition that a common source of the two legs is covered by the empty
  sieve.
* `CategoryTheory.Presieve.IsSheaf.existsUnique_section_of_pair`: for a sheaf of types, a
  section over the target of a disjoint covering pair is uniquely determined by, and may be
  prescribed as, a pair of sections over the two members.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Two objects, read as a family indexed by `Bool`. -/
def pairFamily (A A' : C) : Bool → C
  | true => A
  | false => A'

/-- Two morphisms with a common target, read as a family indexed by `Bool` over
`CategoryTheory.pairFamily`. -/
def pairHom {A A' V : C} (a : A ⟶ V) (a' : A' ⟶ V) : ∀ i, pairFamily A A' i ⟶ V
  | true => a
  | false => a'

variable {J : GrothendieckTopology C} {A A' V : C}

/-- **Disjointness of a two-element family is a single condition.**  If every common source of
`a` and `a'` is covered by the empty sieve, then the family `pairHom a a'` is pairwise disjoint:
every common source of two of its legs with distinct indices is covered by the empty sieve. -/
theorem pairHom_disjoint (a : A ⟶ V) (a' : A' ⟶ V)
    (hdisj : ∀ {Z : C} (g : Z ⟶ A) (g' : Z ⟶ A'), g ≫ a = g' ≫ a' → (⊥ : Sieve Z) ∈ J Z) :
    ∀ i j : Bool, i ≠ j → ∀ {Z : C} (gi : Z ⟶ pairFamily A A' i) (gj : Z ⟶ pairFamily A A' j),
      gi ≫ pairHom a a' i = gj ≫ pairHom a a' j → (⊥ : Sieve Z) ∈ J Z := by
  rintro (_ | _) (_ | _) hij Z gi gj h
  exacts [absurd rfl hij, hdisj gj gi h.symm, hdisj gi gj h, absurd rfl hij]

/-- **A section over the target of a disjoint covering pair is a pair of sections.**  Let
`a : A ⟶ V` and `a' : A' ⟶ V` be monomorphisms which cover `V` and whose common sources are
covered by the empty sieve.  For a sheaf of types every pair of sections over `A` and `A'`
extends to a unique section over `V`. -/
theorem Presieve.IsSheaf.existsUnique_section_of_pair {P : Cᵒᵖ ⥤ Type w}
    (hP : Presieve.IsSheaf J P) (a : A ⟶ V) (a' : A' ⟶ V)
    (hcov : Sieve.ofArrows (pairFamily A A') (pairHom a a') ∈ J V)
    (hmono : Mono a) (hmono' : Mono a')
    (hdisj : ∀ {Z : C} (g : Z ⟶ A) (g' : Z ⟶ A'), g ≫ a = g' ≫ a' → (⊥ : Sieve Z) ∈ J Z)
    (s : P.obj (op A)) (t : P.obj (op A')) :
    ∃! x : P.obj (op V), P.map a.op x = s ∧ P.map a'.op x = t := by
  obtain ⟨x, hx, hu⟩ := hP.existsUnique_section_of_disjoint_arrows (pairHom a a') hcov
    (by rintro (_ | _) <;> assumption) (pairHom_disjoint a a' hdisj) (fun i ↦ Bool.rec t s i)
  refine ⟨x, ⟨hx true, hx false⟩, fun y hy ↦ hu y ?_⟩
  rintro (_ | _)
  exacts [hy.2, hy.1]

end CategoryTheory

end
