module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverGraphSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Scheme

/-!
# The complementary summand of the graph splitting is a scheme

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` with `X`
representable and `g` **integral**. Then the fibre product `X ×_Z Y` is representable, and so is
every closed subspace of it — in particular the complementary summand `C` of
`AlgebraicGeometry.Space.exists_graphComplement_decomposition`, which is a closed subspace by the
second clause of that result.

This is the representability of the piece `W` of the splitting `U ×_X Y = U ⨿ W` of the inductive
step of [Stacks, Tag 09YB], with `f = j : U ⟶ Y` the quasi-compact open immersion of the relative
compactification, `g = π : Y ⟶ X` the integral morphism it is followed by, and `X = h_U` the
étale chart, a scheme.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_pullback_of_isIntegralHom`: `X ×_Z Y` is a scheme when
  `X` is a scheme and `g` is integral.
* `AlgebraicGeometry.Space.isRepresentable_graphComplement`: **the complementary summand is a
  scheme.**

## Implementation notes

**Why not the fibre-product criterion.** `AlgebraicGeometry.Space.isRepresentable_pullback` needs
*both* factors of the fibre product representable, and here only one of them is: `Y` is the
relative compactification, an algebraic space and not in general a scheme. What makes `X ×_Z Y` a
scheme is instead that its *first* projection — the base change of the integral `g` along
`f ≫ g` — is integral, by Stacks 03ZS, onto the scheme `X`; and a presheaf integral over a scheme
is a scheme, which is `AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom`.

**The closed half of clopen is what is used.** The summand `C` is both an open and a closed
subspace, and representability needs only the closed half, through
`AlgebraicGeometry.Space.isRepresentable_of_isClosedSubspace`. The open half
(`AlgebraicGeometry.Space.isRepresentable_of_isOpenSubspace`) would serve equally; neither is
restated here.

## What is and is not proved

Nothing here carries a Stacks attribute and no part of [Stacks, Tag 09YB] is registered. Both
results are compositions of results already in the library; they are recorded because the inductive step needs the
summand as an *object of the site* and the composition is not otherwise available in one step.

## References

* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Graph

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The fibre product of the graph splitting is a scheme.** If `X` is representable and
`g : Y ⟶ Z` is integral, then `X ×_Z Y` is representable.

The first projection of `X ×_Z Y` is the base change of `g` along `f ≫ g`, hence integral by
Stacks 03ZS, and a presheaf integral over a scheme is a scheme. -/
theorem isRepresentable_pullback_of_isIntegralHom (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hg : IsIntegralHom B S hS g)
    (hXrep : X.IsRepresentable) :
    (pullback (f ≫ g) g).IsRepresentable :=
  isRepresentable_of_isIntegralHom B S hS
    (isAlgebraicSpace_pullback B S hS (f ≫ g) g hX hY hZ)
    (pullback.fst (f ≫ g) g)
    (isIntegralHom_of_isPullback B S hS (IsPullback.of_hasPullback (f ≫ g) g).flip hg)
    hXrep

/-- **The complementary summand of the graph splitting is a scheme.** For `X` representable and
`g` integral, a closed subspace of `X ×_Z Y` is representable; the summand `C` produced by
`AlgebraicGeometry.Space.exists_graphComplement_decomposition` is such a closed subspace.

This is the representability of the piece `W` of `U ×_X Y = U ⨿ W`. -/
theorem isRepresentable_graphComplement (f : X ⟶ Y) (g : Y ⟶ Z)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hg : IsIntegralHom B S hS g)
    (hXrep : X.IsRepresentable) (C : Subfunctor (pullback (f ≫ g) g))
    (hC : IsClosedSubspace B S hS C) :
    C.toFunctor.IsRepresentable :=
  isRepresentable_of_isClosedSubspace B S hS hC
    (isRepresentable_pullback_of_isIntegralHom B S hS f g hX hY hZ hg hXrep)

end Graph

end AlgebraicGeometry.Space

end
