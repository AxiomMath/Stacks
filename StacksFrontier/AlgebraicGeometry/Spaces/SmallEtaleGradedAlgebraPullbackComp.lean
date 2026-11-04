module

public import StacksFrontier.AlgebraicGeometry.Spaces.GradedAlgebraPushforwardTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIso

/-!
# Pullback of sheaves of graded algebras along a composite of morphisms of algebraic spaces

For `f : X ⟶ Y` and `g : Y ⟶ Z` morphisms of algebraic spaces over a scheme `S` contained in a
big fppf site `B`, this file supplies the comparison

`(f ≫ g)^* ≅ g^* ∘ f^*`

of pullbacks of sheaves of **graded** algebras of [Stacks Project, Tag 0FQX], part (2) — the
multiplicative form of the Stacks 03LU composition comparison
`AlgebraicGeometry.Space.modulePullbackCompIso`, whose degreewise components are morphisms of
sheaves of modules only.

The unconditional multiplicative comparison
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedPullbackCompIsoOfComp` is stated for the
honest composite `g ∘ f` of two morphisms of ringed topoi, and the morphism of ringed topoi of
Stacks 03G8 is *not* functorial on the nose: `AlgebraicGeometry.Space.smallEtaleRingedToposHom`
of a composite is only 2-isomorphic to the composite of the two, by
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` on the geometric halves and
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharpRing` on the structure maps.  What
makes the comparison available here is that
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedPullbackCompIso` takes an *arbitrary*
morphism in the role of the composite, together with a comparison of the direct images of
sheaves of graded algebras; and that comparison is obtained by transporting the one for the
honest composite along the 2-isomorphism, which is
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.pushforwardGradedAlgebraFunctorIsoOfNatIso`.

## Main definitions

* `AlgebraicGeometry.Space.compRingedToposHom`: the composite of the two morphisms of
  small étale ringed topoi of Stacks 03G8.
* `AlgebraicGeometry.Space.gradedAlgebraPushforwardCompTransport`: the direct image of sheaves
  of graded algebras of that composite, identified with the direct image along the morphism of
  ringed topoi of the composite morphism of algebraic spaces.
* `AlgebraicGeometry.Space.gradedAlgebraPushforwardCompIso`: the comparison
  `f_* ∘ g_* ≅ (f ≫ g)_*` of direct images of sheaves of graded algebras.
* `AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso`: **the comparison
  `(f ≫ g)^* ≅ g^* ∘ f^*` of pullbacks of sheaves of graded algebras.**

Multiplicativity of the comparison of pullbacks is one of its fields, since it is a morphism in
the category of sheaves of graded algebras: it is what the `What is not proved` sections of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraFunctorial.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraEtaleRestriction.lean` record as missing
for `AlgebraicGeometry.Space.modulePullbackCompIso`.

## Implementation notes

**Why the pullbacks need no transport of their own.**  The comparison produced here is between
the pullback functors of the morphisms of ringed topoi of Stacks 03G8, and
`AlgebraicGeometry.Space.modulePullback_eq` says that the inverse image of `𝒪`-modules along a
morphism of algebraic spaces *is* the ringed-topos pullback of that morphism of ringed topoi, as
an equation that holds by reflexivity.  The direct image is the side where the two developments
differ by `AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`, which is not a
reflexivity; and the direct image enters here only as the right adjoint used to compare the two
left adjoints, never in a statement.  So none of the `eqToHom` trouble recorded in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean` arises.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedToposHom)
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull gradedPush gradedPushCompIso
  gradedPullbackCompIso pushforwardGradedAlgebraFunctor
  pushforwardGradedAlgebraFunctorIsoOfNatIso)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-- **The direct image of sheaves of graded algebras along the composite of the two morphisms of
ringed topoi of Stacks 03G8, identified with the direct image along the morphism of ringed topoi
of the composite morphism of algebraic spaces.**

This is the graded analogue of
`AlgebraicGeometry.Space.pushforwardModulesCompTransport`: the transport of
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.pushforwardGradedAlgebraFunctorIsoOfNatIso` along
the same 2-isomorphism, whose geometric half is
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` and whose structure-map half is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharpRing`. -/
noncomputable def gradedAlgebraPushforwardCompTransport (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforwardGradedAlgebraFunctor (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Z) (compRingedToposHom B S hS f g) ≅
      pushforwardGradedAlgebraFunctor (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHom B S hS (f ≫ g)) :=
  pushforwardGradedAlgebraFunctorIsoOfNatIso (compRingedToposHom B S hS f g)
    (smallEtaleRingedToposHom B S hS (f ≫ g))
    (smallToposMorphismTypeU_comp B S hS f g)
    (smallEtaleRingedToposHom_comp_fSharpRing B S hS f g)

/-- **The comparison `f_* ∘ g_* ≅ (f ≫ g)_*` of direct images of sheaves of graded algebras**
along a composite of morphisms of algebraic spaces: part (1) of [Stacks Project, Tag 0FQX] for a
composite.

It is the ringed-topos comparison
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedPushCompIso` for the honest composite of the
two morphisms of ringed topoi, followed by the transport
`AlgebraicGeometry.Space.gradedAlgebraPushforwardCompTransport` onto the morphism of ringed
topoi of `f ≫ g`.  So it is the graded analogue of
`AlgebraicGeometry.Space.modulePushforwardCompIso`, assembled out of the same two factors. -/
noncomputable def gradedAlgebraPushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    gradedPush (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f) ⋙
        gradedPush (X := smallEtaleRingedTopos B S hS Y)
          (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS g) ≅
      gradedPush (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHom B S hS (f ≫ g)) :=
  gradedPushCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g) ≪≫
    gradedAlgebraPushforwardCompTransport B S hS f g

/-- **The comparison `(f ≫ g)^* ≅ g^* ∘ f^*` of pullbacks of sheaves of graded algebras** along
a composite of morphisms of algebraic spaces: part (2) of [Stacks Project, Tag 0FQX] for a
composite, and the multiplicative form of the Stacks 03LU comparison
`AlgebraicGeometry.Space.modulePullbackCompIso`.

Both sides are left adjoint to `f_* ∘ g_*` — the left-hand side by the Stacks 0FQX adjunction of
`f ≫ g` transported along `AlgebraicGeometry.Space.gradedAlgebraPushforwardCompIso`, the
right-hand side because adjunctions compose — so they agree by uniqueness of left adjoints.
Being an isomorphism of sheaves of **graded algebras**, each of its degreewise components
preserves products of homogeneous local sections: that is the field
`SheafOfModules.GradedAlgebra.Hom.map_mul` of `(gradedAlgebraPullbackCompIso ..).hom.app A`, and
it is what the degreewise comparison `AlgebraicGeometry.Space.modulePullbackCompIso` of sheaves
of modules leaves open. -/
noncomputable def gradedAlgebraPullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    gradedPull (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHom B S hS (f ≫ g)) ≅
      gradedPull (X := smallEtaleRingedTopos B S hS Y) (Y := smallEtaleRingedTopos B S hS Z)
          (smallEtaleRingedToposHom B S hS g) ⋙
        gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f) :=
  gradedPullbackCompIso (smallEtaleRingedToposHom B S hS f)
    (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS (f ≫ g))
    (gradedAlgebraPushforwardCompIso B S hS f g)

end AlgebraicGeometry.Space

end
