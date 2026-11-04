module

public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Monomorphisms into a sheafification

Let `(C, J)` be a site whose `A`-valued presheaves admit a left exact sheafification, let `P` be
a sheaf and let `Q` be an arbitrary presheaf.  A monomorphism `η : P ⟶ Q` stays a monomorphism
after it is followed by the sheafification unit `Q ⟶ Q^sh`, and the sheaf morphism `P ⟶ Q^sh`
which corresponds to it under the adjunction is a monomorphism of sheaves.

This is the input needed wherever a sheaf is compared with the sheafification of a presheaf
containing it: the comparison map is injective, and so a pullback along it is computed by either
of its two projections.

## Main results

* `Stacks.SheafifyMono.mono_comp_toSheafify`: for a sheaf `P`, a monomorphism `η : P ⟶ Q` of
  presheaves composed with `CategoryTheory.toSheafify J Q` is a monomorphism of presheaves.
* `Stacks.SheafifyMono.mono_homEquivSymm_comp_toSheafify`: the same morphism read as a morphism
  of sheaves `P ⟶ (presheafToSheaf J A).obj Q`, via the full faithfulness of the inclusion of
  sheaves into presheaves, is a monomorphism of sheaves.

## Implementation notes

Mathlib already has every ingredient, and the hypothesis `CategoryTheory.HasSheafify` is exactly
what makes them available.  `HasSheafify` carries left exactness of sheafification
(`CategoryTheory.HasSheafify.isLeftExact`), from which
`CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape` gives
`(presheafToSheaf J A).PreservesMonomorphisms`; this synthesizes by instance
search alone at this pin.  Since
`CategoryTheory.sheafifyMap J η = ((presheafToSheaf J A).map η).hom` by definition, and a
monomorphism of sheaves has a monomorphic underlying presheaf morphism, `sheafifyMap J η` is a
monomorphism too.  What is left is the identification
`CategoryTheory.toSheafify_naturality`, together with
`CategoryTheory.isIso_toSheafify`, which says that the unit at a sheaf is invertible.

The monomorphism hypothesis is kept instance-implicit.  A caller whose presheaf lives behind an
`implicit_reducible` abbreviation of the functor category — `TopCat.Presheaf C X` is one — must
put the monomorphism into the local context at its own spelling first, because an instance keyed
on that abbreviation is not found at the functor-category spelling of the same category.
-/

@[expose] public section

open CategoryTheory Limits

universe v v' u u'

namespace Stacks.SheafifyMono

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A] [HasSheafify J A]

/-- A monomorphism out of a sheaf stays a monomorphism after the sheafification unit: if `P` is a
sheaf and `η : P ⟶ Q` is a monomorphism of presheaves, then `η ≫ toSheafify J Q` is one. -/
theorem mono_comp_toSheafify {P Q : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P) (η : P ⟶ Q) [Mono η] :
    Mono (η ≫ toSheafify J Q) :=
  have := isIso_toSheafify J hP
  (toSheafify_naturality J η) ▸ inferInstance

/-- The sheaf morphism `P ⟶ Q^sh` adjunct to a monomorphism `η : P.val ⟶ Q` out of a sheaf `P`
is a monomorphism of sheaves. -/
theorem mono_homEquivSymm_comp_toSheafify {P : Sheaf J A} {Q : Cᵒᵖ ⥤ A} (η : P.obj ⟶ Q)
    [Mono η] :
    Mono ((fullyFaithfulSheafToPresheaf J A).homEquiv.symm (η ≫ toSheafify J Q)) :=
  have : Mono ((fullyFaithfulSheafToPresheaf J A).homEquiv.symm
      (η ≫ toSheafify J Q)).hom := mono_comp_toSheafify P.property η
  Sheaf.Hom.mono_of_presheaf_mono _ _ _

end Stacks.SheafifyMono
