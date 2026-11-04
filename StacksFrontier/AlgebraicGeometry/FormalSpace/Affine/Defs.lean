module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Yoneda
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.Sites.Density

/-!
# Affine formal algebraic spaces

An *affine formal algebraic space* over a scheme `S` is a sheaf on the big fppf site of `S`
which can be written as a directed colimit of affine schemes along thickenings, and which
satisfies a set-theoretic condition: a representable sheaf surjects onto it, and a
representable sheaf surjects onto the resulting kernel pair.

## Main definitions

* `AlgebraicGeometry.SatisfiesSetTheoreticCondition`: the two-stage presentation of a sheaf
  by representable sheaves.
* `AlgebraicGeometry.IsAffineFormalAlgebraicSpace`: the predicate cutting out the affine
  formal algebraic spaces among the sheaves on the big fppf site of `S`.

## Implementation notes

Representability of an auxiliary sheaf is recorded by an isomorphism of its underlying
presheaf with a Yoneda presheaf, rather than by asking the chosen big site to be
subcanonical, which is not part of its interface. Surjections of sheaves of sets are
categorical epimorphisms, and the second surjection targets the categorical pullback of the
first map along itself.

The affine stages of a presentation are objects of the big affine fppf site, the full
subcategory of the big fppf site of `S` on affine schemes; the thickening condition is
imposed on the images of the transition maps in schemes. The sheaf represented by a stage is
its sheafified Yoneda presheaf, and the colimit is taken in sheaves. The sheaf is identified
with that colimit by an isomorphism, not an equality. Morphisms of affine formal algebraic
spaces are morphisms in the ambient sheaf category.

## References

* [Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A sheaf on the big fppf site of `S` satisfies the *set-theoretic condition* when it has a
two-stage presentation by representable sheaves: a representable sheaf surjects onto it, and
another representable sheaf surjects onto the resulting kernel pair. -/
abbrev SatisfiesSetTheoreticCondition
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) : Prop :=
  let J := BigFppfOver.topology B S hS
  ∃ (U R : BigFppfOver B S hS)
    (hU hR : Sheaf J (Type (u + 1))),
      Nonempty (hU.obj ≅ (uliftYoneda.{u + 1}).obj U) ∧
      Nonempty (hR.obj ≅ (uliftYoneda.{u + 1}).obj R) ∧
      ∃ f : hU ⟶ X, Epi f ∧ ∃ g : hR ⟶ pullback f f, Epi g

/-- An *affine formal algebraic space* over `S` is a sheaf on the big fppf site of `S` which
satisfies the set-theoretic condition and is a directed colimit of sheaves represented by affine
schemes whose transition morphisms are thickenings. -/
@[stacks 0AI7]
abbrev IsAffineFormalAlgebraicSpace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) : Prop :=
  SatisfiesSetTheoreticCondition B S hS X ∧
    ∃ (I : Type (u + 1)) (pre : Preorder I),
      letI : Preorder I := pre
      Nonempty I ∧ IsDirected I (· ≤ ·) ∧
        ∃ D : I ⥤ BigAffineFppf B S hS,
          (∀ ⦃i j : I⦄ (f : i ⟶ j),
            Stacks.Thickenings.IsThickening
              ((BigAffineFppf.toScheme B S hS).map (D.map f))) ∧
            Nonempty (X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
              Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))

end AlgebraicGeometry
