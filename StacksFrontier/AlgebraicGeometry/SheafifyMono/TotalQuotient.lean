module

public import StacksFrontier.AlgebraicGeometry.SheafifyMono.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient

/-!
# A sheaf of rings embeds in its sheaf of total quotient rings

The canonical morphism `AlgebraicGeometry.toTotalQuotientSheaf` from a sheaf of commutative
rings on a topological space to its sheaf of total quotient rings is a monomorphism, and so is
its specialization `AlgebraicGeometry.Scheme.toTotalQuotientSheaf` at the structure sheaf of a
scheme.

## Main results

* `Stacks.SheafifyMono.mono_toTotalQuotientSheaf`: `AlgebraicGeometry.toTotalQuotientSheaf O` is
  a monomorphism of sheaves of commutative rings, for every sheaf of commutative rings `O` on a
  topological space.
* `Stacks.SheafifyMono.mono_scheme_toTotalQuotientSheaf`: the same for
  `AlgebraicGeometry.Scheme.toTotalQuotientSheaf`.  This needs its own instance rather than
  following from the previous one by unfolding: the scheme-level morphism is a definition and
  not an abbreviation, so instance search keyed on the morphism of a sheaf on a space does not
  reach it.

## Implementation notes

The proof has two inputs.  Objectwise, the localization map into the presheaf of total
quotient rings is injective, because the denominators are germwise nonzerodivisors: this is the
instance `Mono F.presheaf.toTotalQuotientPresheaf` of `Mathlib.Topology.Sheaves.CommRingCat`.
Sheafification then preserves that monomorphism, which is
`Stacks.SheafifyMono.mono_homEquivSymm_comp_toSheafify`.  The composite is exactly the definition
of `AlgebraicGeometry.toTotalQuotientSheaf`, recorded by
`AlgebraicGeometry.toTotalQuotientSheaf_hom`.

The objectwise instance has to be moved into the local context by hand before the general lemma
is applied.  It is stated for a presheaf on a topological space, whose type `TopCat.Presheaf C X`
is an `implicit_reducible` abbreviation of the functor category `(Opens X)ᵒᵖ ⥤ C`.  The general
lemma speaks of the functor category, and instance search keyed on the abbreviation does not fire
at that spelling, although the two types are interchangeable once a term has to be checked
against a known type.  So the monomorphism is named at the abbreviation's spelling, where
instance search does fire, and then used.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace Stacks.SheafifyMono

/-- A sheaf of commutative rings on a topological space embeds in its sheaf of total quotient
rings: the canonical morphism `AlgebraicGeometry.toTotalQuotientSheaf` is a monomorphism. -/
instance mono_toTotalQuotientSheaf {X : TopCat.{u}} (O : TopCat.Sheaf CommRingCat.{u} X) :
    Mono (AlgebraicGeometry.toTotalQuotientSheaf O) :=
  haveI : Mono O.presheaf.toTotalQuotientPresheaf := inferInstance
  mono_homEquivSymm_comp_toSheafify _

/-- The structure sheaf of a scheme embeds in its sheaf of total quotient rings. -/
instance mono_scheme_toTotalQuotientSheaf (Y : AlgebraicGeometry.Scheme.{u}) :
    Mono Y.toTotalQuotientSheaf :=
  mono_toTotalQuotientSheaf Y.sheaf

end Stacks.SheafifyMono
