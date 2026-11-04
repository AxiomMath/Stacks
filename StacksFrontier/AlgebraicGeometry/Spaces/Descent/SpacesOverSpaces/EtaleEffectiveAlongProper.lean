module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.Effective
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentSurjective

/-!
# Étale descent data along a proper surjective morphism are effective

Let `f : X ⟶ Y` be a proper surjective morphism of algebraic spaces over a scheme `S`
contained in a big fppf site `B`. A descent datum `(U/X, φ)` relative to `f` whose underlying
space `U` is étale over `X` is effective: there is an étale morphism `V ⟶ Y` of algebraic
spaces whose canonical descent datum is isomorphic to `(U/X, φ)`. This is **Stacks 0GG0**.

The source proves it by translating the descent datum of spaces into a descent datum for
sheaves on the spaces-étale site — the space `U` becomes the sheaf it represents — applying
Stacks 0GFW to see that the sheaf-theoretic datum is effective, and translating the resulting
sheaf on `Y` back into an étale morphism of algebraic spaces by Stacks 0GF6. The translation
between the two kinds of descent datum is not available in the library, so it enters here as
the named hypothesis
`AlgebraicGeometry.Space.EtaleSpaceDescentEffectiveOfSheafDescent`: for a morphism along which
descent of spaces-étale sheaves is effective, an étale descent datum of spaces is effective
through an étale morphism to the target. The proper case of Stacks 0GFW, which is the case
appealed to here, is itself carried by its formalization in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentSurjective`, so the whole of
this statement rests on hypotheses; what the file settles is the shape of Stacks 0GG0 in the
library's vocabulary for descent data of algebraic spaces and for effectivity.

## Main definitions

* `AlgebraicGeometry.Space.EtaleSpaceDescentEffectiveOfSheafDescent` is the translation between
  descent data of spaces étale over the source and descent data for spaces-étale sheaves, as a
  statement about the big fppf site, to be carried as a hypothesis.

## Main results

* `AlgebraicGeometry.Space.isEffective_homDescentData_of_isEtale_of_isProper_isSurjective` is
  **Stacks 0GG0**, with that translation and the proper case of Stacks 0GFW carried.

## Implementation notes

A descent datum relative to `f : X ⟶ Y` is
`AlgebraicGeometry.Space.Descent.HomDescentData f.hom Y.property X.property`, descent data for
the one-member family indexed by `PUnit`; its single object `D.obj PUnit.unit` is the space
`U` over `X` together with its structure morphism, and effectivity is membership in the
essential image of `AlgebraicGeometry.Space.Descent.canonicalDescentFunctor`. The conclusion is
stated as the conjunction of that membership with the sharper form of the source, which also
records that the algebraic space over `Y` produced is étale over `Y`.

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

/-- The translation between the two kinds of descent datum used by Stacks 0GG0, as a statement
about the big fppf site `B` over `S`, to be carried as a hypothesis: if descent of spaces-étale
sheaves along `f : X ⟶ Y` is effective, then every descent datum relative to `f` whose
underlying space is étale over `X` is isomorphic to the canonical descent datum of an algebraic
space over `Y` which is étale over `Y`. In the source this is the passage from a space étale
over `X` to the sheaf it represents, together with Stacks 0GF6 in the other direction. -/
abbrev EtaleSpaceDescentEffectiveOfSheafDescent : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence →
    ∀ D : Descent.HomDescentData.{u, 0} f.hom Y.property X.property,
      IsEtale B S hS (D.obj PUnit.unit).hom →
      ∃ V : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) Y.1,
        IsEtale B S hS V.obj.hom ∧
          Nonempty ((Descent.canonicalDescentFunctor.{u, 0} f.hom Y.property
            X.property).obj V ≅ D)

/-- **Stacks 0GG0.** Let `f : X ⟶ Y` be a proper surjective morphism of algebraic spaces over
`S`. A descent datum relative to `f` whose underlying space is étale over `X` is effective;
more precisely, it is isomorphic to the canonical descent datum of an algebraic space over `Y`
which is étale over `Y`.

Two statements of the source are carried as hypotheses rather than proved: `hproperCase` is the
proper case of Stacks 0GFW, which is the case Stacks 0GG0 appeals to, and `hbridge` is the
translation between descent data of spaces and descent data of spaces-étale sheaves. -/
@[stacks 0GG0 "both the effectivity and the sharper form naming an étale V ⟶ Y, stated in \
the library's vocabulary for descent data of spaces; the translation between descent data of \
spaces and of étale sheaves and the proper case of Stacks 0GFW are carried as hypotheses"]
theorem isEffective_homDescentData_of_isEtale_of_isProper_isSurjective
    (hproperCase : DescentEffectiveAlongProperSurjective B S hS)
    (hbridge : EtaleSpaceDescentEffectiveOfSheafDescent B S hS)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hsurj : IsSurjective B S hS f.hom) (hproper : IsProper B S hS f.hom)
    (D : Descent.HomDescentData.{u, 0} f.hom Y.property X.property)
    (hD : IsEtale B S hS (D.obj PUnit.unit).hom) :
    Descent.HomDescentData.IsEffective.{u, 0} D ∧
      ∃ V : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) Y.1,
        IsEtale B S hS V.obj.hom ∧
          Nonempty ((Descent.canonicalDescentFunctor.{u, 0} f.hom Y.property
            X.property).obj V ≅ D) := by
  have hdescent :
      ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence :=
    hproperCase f hsurj hproper
  obtain ⟨V, hV, hiso⟩ := hbridge f hdescent D hD
  exact ⟨⟨V, hiso⟩, V, hV, hiso⟩

end AlgebraicGeometry.Space

end
