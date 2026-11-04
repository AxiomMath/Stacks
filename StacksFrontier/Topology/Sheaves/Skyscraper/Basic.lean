module

public import Mathlib.Topology.Sheaves.Skyscraper
public import StacksCore.Tactic.StacksAttribute

/-!
# Being a skyscraper sheaf

Stacks 009A introduces skyscraper sheaves on a topological space `X`. Its clauses (1)–(3)
construct, for a point `x` of `X` and an object `A` — a set, an abelian group, or an
algebraic structure — the sheaf `i_{x,*} A` obtained by pushing `A` forward along the
inclusion `i_x : {x} → X`. Its clauses (5)–(7) define the *predicate* "`F` is a skyscraper",
namely that `F ≅ i_{x,*} A` for some point `x` and some `A`.

Mathlib has the construction, uniformly in the target category, as `skyscraperSheaf`, and
identifies it with the pushforward from the one-point space
(`skyscraperPresheaf_eq_pushforward`); those two declarations are registered here for clauses
(1)–(3), one target category covering all three. It has no form of the predicate, which is
supplied here as `SkyscraperSheaves.IsSkyscraperSheaf`, again uniformly in the target
category, covering clauses (5)–(7).

Clauses (4) and (8) of the tag — the case of a ringed space `(X, 𝒪_X)`, where `i_x` is read as
a morphism of ringed spaces `({x}, 𝒪_{X,x}) → (X, 𝒪_X)` and `A` is an `𝒪_{X,x}`-module, so
that `i_{x,*} A` is a sheaf of `𝒪_X`-modules — are **not** treated here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat

universe v u

namespace SkyscraperSheaves

variable {X : TopCat.{u}} {C : Type v} [Category.{u} C] [HasTerminal C]

/- **Stacks 009A (1), (2), (3).** The skyscraper sheaf `i_{x,*} A` at a point `x` with value
`A`. Mathlib's construction is stated for an arbitrary target category with a terminal object,
so the same declaration serves the set-valued case (1), the abelian case (2) and the case of
an arbitrary type of algebraic structure (3). -/
add_to_stacks 009A "The skyscraper sheaf at a point with a given value: the sheaf whose
  sections over `U` are the given object if `x ∈ U` and a terminal object otherwise. Mathlib's
  construction is uniform in the target category, so one declaration covers the tag's set,
  abelian-group and algebraic-structure cases; the ringed-space case, clause (4), is not
  covered." skyscraperSheaf

/- That the skyscraper sheaf really is `i_{x,*} A`, the pushforward of `A` — viewed as a sheaf
on the one-point space — along the inclusion of `x`. This is what clause (1) of the tag takes
as the definition. -/
add_to_stacks 009A "The skyscraper is the pushforward along the map from the one-point space
  sending the point to `x`, which is how the tag defines `i_{x,*} A`."
  skyscraperPresheaf_eq_pushforward

/-- The skyscraper sheaf `i_{x,*} A` at `x` with value `A`, with the decidability of `x ∈ U`
supplied classically.

Mathlib's `skyscraperSheaf` takes a `Decidable (x ∈ U)` instance for every open `U`. Stating
"`F` is a skyscraper sheaf" quantifies over `x`, so no such instance family can be a
hypothesis of the statement; this wrapper fixes the classical one. -/
noncomputable def skyscraper (x : X) (A : C) : TopCat.Sheaf C X :=
  letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
  skyscraperSheaf x A

/-- **Stacks 009A (5), (6), (7).** A sheaf `F` on `X` is a *skyscraper sheaf* if there are a
point `x` of `X` and an object `A` of the target category with `F ≅ i_{x,*} A`.

The target category is arbitrary, so this single predicate is the tag's clause (5) for sheaves
of sets, its clause (6) for sheaves of abelian groups and its clause (7) for sheaves of
algebraic structures. Clause (8), for sheaves of modules on a ringed space, is not covered
here. -/
@[stacks 009A "(5), (6), (7)"]
def IsSkyscraperSheaf (F : TopCat.Sheaf C X) : Prop :=
  ∃ (x : X) (A : C), Nonempty (F ≅ skyscraper x A)

/-- A skyscraper sheaf is a skyscraper sheaf. -/
theorem isSkyscraperSheaf_skyscraper (x : X) (A : C) :
    IsSkyscraperSheaf (skyscraper x A) :=
  ⟨x, A, ⟨Iso.refl _⟩⟩

/-- Being a skyscraper sheaf is invariant under isomorphism. -/
theorem isSkyscraperSheaf_of_iso {F G : TopCat.Sheaf C X} (e : F ≅ G)
    (hF : IsSkyscraperSheaf F) : IsSkyscraperSheaf G := by
  obtain ⟨x, A, ⟨i⟩⟩ := hF
  exact ⟨x, A, ⟨e.symm ≪≫ i⟩⟩

end SkyscraperSheaves
