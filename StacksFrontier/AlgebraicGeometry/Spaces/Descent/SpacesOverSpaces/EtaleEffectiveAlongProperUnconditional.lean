module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EtaleSpaceDescentEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentProperSurjective

/-!
# Étale descent data along a proper surjective morphism are effective (Stacks 0GG0)

Let `f : X ⟶ Y` be a proper surjective morphism of algebraic spaces over a scheme `S`
contained in a big fppf site `B`. A descent datum `(U/X, φ)` relative to `f` whose underlying
space `U` is étale over `X` is effective; more precisely, there is an étale morphism `V ⟶ Y`
of algebraic spaces whose canonical descent datum is isomorphic to `(U/X, φ)`. This is
**Stacks 0GG0**, proved here with no hypotheses beyond those of the source.

The proof follows the source. The space `U` étale over `X` is read as the sheaf it represents
on the spaces-étale site of `X`, and the descent datum on `U` as a descent datum of
spaces-étale sheaves relative to `{X ⟶ Y}`. The proper case of Stacks 0GFW,
`AlgebraicGeometry.Space.descentEffectiveAlongProperSurjective`, says that spaces-étale sheaves
descend effectively along `f`, so that datum comes from a sheaf on `Y`. By Stacks 0GF6, with its
set-theoretic condition, that sheaf is represented by an algebraic space `V` étale over `Y`, and
the isomorphism of sheaf descent data becomes an isomorphism of descent data of spaces. These
two translations are `AlgebraicGeometry.Space.etaleSpaceDescentEffectiveOfSheafDescent`. The
two theorems are supplied to
`AlgebraicGeometry.Space.isEffective_homDescentData_of_isEtale_of_isProper_isSurjective`, which
derives the conclusion from them.

## Implementation notes

A descent datum relative to `f` is
`AlgebraicGeometry.Space.Descent.HomDescentData f.hom Y.property X.property`, descent data for
the one-member family indexed by `PUnit`, whose single object `D.obj PUnit.unit` is `U` over
`X`; effectivity (Stacks 0ADQ) is
`AlgebraicGeometry.Space.Descent.HomDescentData.IsEffective`, membership in the essential image
of `AlgebraicGeometry.Space.Descent.canonicalDescentFunctor`.

## Main results

* `AlgebraicGeometry.Space.isEffective_and_exists_isEtale_iso_of_isProper_isSurjective` is
  **Stacks 0GG0**: both the effectivity and the sharper form naming an étale `V ⟶ Y`.

## References

* [Stacks Project, Tag 0GG0](https://stacks.math.columbia.edu/tag/0GG0)
* [Stacks Project, Tag 0GFW](https://stacks.math.columbia.edu/tag/0GFW)
* [Stacks Project, Tag 0GF6](https://stacks.math.columbia.edu/tag/0GF6)
* [Stacks Project, Tag 0ADG](https://stacks.math.columbia.edu/tag/0ADG)
* [Stacks Project, Tag 0ADQ](https://stacks.math.columbia.edu/tag/0ADQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GG0.** Let `f : X ⟶ Y` be a proper surjective morphism of algebraic spaces over
`S`. Any descent datum `(U/X, φ)` relative to `f` (Stacks 0ADG) with `U` étale over `X` is
effective (Stacks 0ADQ). More precisely, there exists an algebraic space `V` over `Y`, étale
over `Y`, whose canonical descent datum is isomorphic to `(U/X, φ)`. -/
@[stacks 0GG0 "the effectivity of the descent datum and the sharper form: an étale \
V ⟶ Y whose canonical descent datum is isomorphic to the given one"]
theorem isEffective_and_exists_isEtale_iso_of_isProper_isSurjective
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsurj : IsSurjective B S hS f.hom) (hproper : IsProper B S hS f.hom)
    (D : Descent.HomDescentData.{u, 0} f.hom Y.property X.property)
    (hD : IsEtale B S hS (D.obj PUnit.unit).hom) :
    Descent.HomDescentData.IsEffective.{u, 0} D ∧
      ∃ V : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) Y.1,
        IsEtale B S hS V.obj.hom ∧
          Nonempty ((Descent.canonicalDescentFunctor.{u, 0} f.hom Y.property
            X.property).obj V ≅ D) :=
  isEffective_homDescentData_of_isEtale_of_isProper_isSurjective B S hS
    (descentEffectiveAlongProperSurjective B S hS)
    (etaleSpaceDescentEffectiveOfSheafDescent B S hS) f hsurj hproper D hD

end AlgebraicGeometry.Space

end
