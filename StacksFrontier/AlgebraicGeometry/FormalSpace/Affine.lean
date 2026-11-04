module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Yoneda
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.Sites.Density

/-!
# Affine formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. An *affine formal algebraic space* over
`S` is an fppf sheaf on the big fppf site of `S` which is a directed colimit of affine schemes
whose transition morphisms are thickenings, and which satisfies the set-theoretic condition: it
receives a surjection from a representable sheaf whose kernel pair in turn receives a surjection
from a representable sheaf.

## Main definitions

* `AlgebraicGeometry.FormalSpace.FppfSheaf`: the sheaves of sets on the big fppf site of `S`.
* `AlgebraicGeometry.FormalSpace.SatisfiesSetTheoreticCondition`: the set-theoretic condition
  on an fppf sheaf.
* `AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace`: the predicate of being an affine
  formal algebraic space.

## Implementation notes

The affine objects of the site form the full subcategory `AlgebraicGeometry.BigAffineFppf`; an
affine stage of a presentation is an object of that subcategory rather than a bare affine
scheme, so that its structure morphism to the base is part of the datum. A stage is turned
into a sheaf by `CategoryTheory.Sheaf.sheafifiedYoneda`, which is the sheafification of its
Yoneda presheaf; this avoids assuming that the chosen big fppf site is subcanonical, which is
not part of its interface. For the same reason the set-theoretic condition records
representability by an isomorphism of the underlying presheaf with a (universe-lifted) Yoneda
presheaf rather than by an equality.

The indexing category of a presentation is a directed preorder in `Type (u + 1)`, one universe
above the schemes, because the colimit is taken in sheaves of `Type (u + 1)`. The preorder is
an explicit existential witness rather than an instance argument, so that the predicate is a
`Prop` with no instance parameters.
The identification of the sheaf with the colimit is an isomorphism wrapped in `Nonempty`, so
that the predicate is proof-irrelevant.

Surjections of sheaves of sets are categorical epimorphisms and the kernel pair is the
categorical pullback, both taken in the sheaf category, which has them by
`CategoryTheory.Sheaf.instHasLimitsOfSize`.

## References

* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheaves of sets on the big fppf site of `S`, in the universe one above the schemes. -/
abbrev FppfSheaf := Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))

/-- An fppf sheaf satisfies the *set-theoretic condition* when there is a representable sheaf
surjecting onto it and a representable sheaf surjecting onto the kernel pair of that surjection.
Representability is recorded by an isomorphism of underlying presheaves with a universe-lifted
Yoneda presheaf. -/
@[stacks 0AIS "the set-theoretic condition"]
abbrev SatisfiesSetTheoreticCondition (X : FppfSheaf B S hS) : Prop :=
  let J := BigFppfOver.topology B S hS
  ∃ (U R : BigFppfOver B S hS) (hU hR : Sheaf J (Type (u + 1))),
      Nonempty (hU.obj ≅ (uliftYoneda.{u + 1}).obj U) ∧
      Nonempty (hR.obj ≅ (uliftYoneda.{u + 1}).obj R) ∧
      ∃ f : hU ⟶ X, Epi f ∧ ∃ g : hR ⟶ pullback f f, Epi g

/-- An *affine formal algebraic space* over `S` is an fppf sheaf on the big fppf site of `S`
which satisfies the set-theoretic condition
`AlgebraicGeometry.FormalSpace.SatisfiesSetTheoreticCondition` and which is the colimit of a
directed diagram of affine schemes over `S` all of whose transition morphisms are thickenings. -/
@[stacks 0AI7]
abbrev IsAffineFormalAlgebraicSpace (X : FppfSheaf B S hS) : Prop :=
  SatisfiesSetTheoreticCondition B S hS X ∧
    ∃ (I : Type (u + 1)) (pre : Preorder I),
      letI : Preorder I := pre
      Nonempty I ∧ IsDirected I (· ≤ ·) ∧
        ∃ D : I ⥤ BigAffineFppf B S hS,
          (∀ ⦃i j : I⦄ (f : i ⟶ j),
            Stacks.Thickenings.IsThickening
              ((BigAffineFppf.toScheme B S hS).map (D.map f))) ∧
            Nonempty (X ≅ colimit
              (D ⋙ BigAffineFppf.inclusion B S hS ⋙
                Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))

end AlgebraicGeometry.FormalSpace

end
