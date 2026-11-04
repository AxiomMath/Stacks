module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# Combinatorial and tautological equivalence of families of morphisms with fixed target

A family of morphisms with fixed target `U` in a category `C` — a collection
`{φ_i : U_i ⟶ U}_{i ∈ I}` — is Mathlib's `CategoryTheory.PreZeroHypercover U`, whose fields
`I₀`, `X` and `f` are the index type, the sources and the morphisms. Stacks 00VT (1) is
`PreZeroHypercover.HomOver` and Stacks 00VT (2), refinement, is Mathlib's
`PreZeroHypercover.Hom`; both are in `StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver`.

This file adds the two equivalence relations of Stacks 00VU on top of that structure:

* `CombinatoriallyEquivalent` — the morphisms are identified on the nose (00VU (1));
* `TautologicallyEquivalent` — they are identified up to isomorphism of the sources (00VU (2)).

Combinatorial equivalence is the stronger notion: it forces the sources to be *equal*, where
tautological equivalence asks only for compatible isomorphisms between them. Stacks 00VV, in
`EquivalenceComparison`, proves that implication and that both relations are equivalence
relations.

## Both relations are stated with two index maps, not a bijection

Stacks 00VU asks for maps `α : I → J` and `β : J → I`, and two maps in opposite directions
need not be mutually inverse. A bijection is therefore strictly stronger, and stating either
relation that way makes every downstream statement about a different relation from the
source's.

## Neither relation constrains the two index universes

`E` and `F` are allowed to be indexed in different universes. Nothing in either definition
compares the index types, only maps between them, so tying the two together would be a
restriction the source does not impose.
-/

@[expose] public section

namespace CategoryTheory.PreZeroHypercover

universe w w' v u

variable {C : Type u} [Category.{v} C] {U : C}

/-- **Stacks 00VU (1).** Two families of morphisms with the same fixed target `U` are
*combinatorially equivalent* if there are maps `α : I → J` and `β : J → I` with
`φ_i = ψ_{α i}` and `ψ_j = φ_{β j}`.

An equality of morphisms `φ_i = ψ_{α i}` presupposes an equality of their sources
`U_i = V_{α i}`, which is the `h` below; `eqToHom` transports along it. -/
@[stacks 00VU "(1)"]
def CombinatoriallyEquivalent
    (E : PreZeroHypercover.{w} U) (F : PreZeroHypercover.{w'} U) : Prop :=
  (∃ α : E.I₀ → F.I₀, ∃ h : ∀ i, E.X i = F.X (α i),
    ∀ i, E.f i = eqToHom (h i) ≫ F.f (α i)) ∧
  (∃ β : F.I₀ → E.I₀, ∃ h : ∀ j, F.X j = E.X (β j),
    ∀ j, F.f j = eqToHom (h j) ≫ E.f (β j))

/-- **Stacks 00VU (2).** Two families of morphisms with the same fixed target `U` are
*tautologically equivalent* if there are maps `α : I → J` and `β : J → I` together with, for
every index, a commutative triangle over `U` whose horizontal arrow is an *isomorphism*:
`U_i ≅ V_{α i}` over `U`, and `V_j ≅ U_{β j}` over `U`. -/
@[stacks 00VU "(2)"]
def TautologicallyEquivalent
    (E : PreZeroHypercover.{w} U) (F : PreZeroHypercover.{w'} U) : Prop :=
  (∃ α : E.I₀ → F.I₀, ∀ i, ∃ e : E.X i ≅ F.X (α i), e.hom ≫ F.f (α i) = E.f i) ∧
  (∃ β : F.I₀ → E.I₀, ∀ j, ∃ e : F.X j ≅ E.X (β j), e.hom ≫ E.f (β j) = F.f j)

/-- Combinatorial equivalence is symmetric, by swapping the two halves of the definition. -/
lemma CombinatoriallyEquivalent.symm {E : PreZeroHypercover.{w} U}
    {F : PreZeroHypercover.{w'} U} (h : CombinatoriallyEquivalent E F) :
    CombinatoriallyEquivalent F E :=
  ⟨h.2, h.1⟩

/-- Tautological equivalence is symmetric, by swapping the two halves of the definition. -/
lemma TautologicallyEquivalent.symm {E : PreZeroHypercover.{w} U}
    {F : PreZeroHypercover.{w'} U} (h : TautologicallyEquivalent E F) :
    TautologicallyEquivalent F E :=
  ⟨h.2, h.1⟩

/-- A morphism that factors through `F.f j` after transport along an equality of sources
belongs to the presieve `F` generates. -/
lemma presieve₀_of_eq (F : PreZeroHypercover.{w'} U) (j : F.I₀) {Y : C} (g : Y ⟶ U)
    (hX : Y = F.X j) (hg : g = eqToHom hX ≫ F.f j) : F.presieve₀ g := by
  subst hX
  -- `presieve₀_f` is a `simp` lemma, so rewriting by `hg` and cancelling `eqToHom rfl` closes it.
  simp [hg]

/-- One half of `presieve₀_eq_of_combinatoriallyEquivalent`. -/
lemma presieve₀_le_of_combinatoriallyEquivalent {E : PreZeroHypercover.{w} U}
    {F : PreZeroHypercover.{w'} U} (h : CombinatoriallyEquivalent E F) :
    E.presieve₀ ≤ F.presieve₀ := by
  obtain ⟨⟨α, hX, hf⟩, -⟩ := h
  rintro Y g ⟨i⟩
  exact presieve₀_of_eq F (α i) (E.f i) (hX i) (hf i)

/-- Combinatorially equivalent families generate the *same* presieve. Only the two index maps
are used, so the two families' index types may differ entirely: `Presieve.ofArrows` forgets
the indexing, and combinatorial equivalence gives mutual inclusion of the images. -/
lemma presieve₀_eq_of_combinatoriallyEquivalent {E : PreZeroHypercover.{w} U}
    {F : PreZeroHypercover.{w'} U} (h : CombinatoriallyEquivalent E F) :
    E.presieve₀ = F.presieve₀ :=
  le_antisymm (presieve₀_le_of_combinatoriallyEquivalent h)
    (presieve₀_le_of_combinatoriallyEquivalent h.symm)

end CategoryTheory.PreZeroHypercover
