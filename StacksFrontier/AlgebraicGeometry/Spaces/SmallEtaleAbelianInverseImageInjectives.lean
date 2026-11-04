module

public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportEtaleLocalHigher
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianRestrictionInverseImage

/-!
# Inverse image along an étale morphism preserves injective abelian sheaves

`StacksFrontier/AlgebraicGeometry/Spaces/HigherPushforwardBaseChange.lean` proves Stacks 03LR
part (2) — étale base change for the higher direct images of abelian sheaves — from a single
named hypothesis `h03F3`: that the inverse image of abelian sheaves along the top arrow `i` of
the cartesian square carries injective abelian sheaves to injective ones.  Its implementation
notes record that hypothesis as the one input the file leaves unproved, and name what is needed
to discharge it: Stacks 03F3 read through Stacks 03LQ at abelian coefficients.

Both halves are now available.  Restriction along postcomposition of étale charts preserves
injective abelian sheaves — that is
`AlgebraicGeometry.Space.preservesInjectiveObjects_etaleAbelianRestriction`, proved by
constructing the left adjoint `f_!` and showing it left exact — and
`AlgebraicGeometry.Space.smallToposMorphism_abelianInverseImageIso` identifies that restriction
with the inverse image of abelian sheaves along the morphism of small étale topoi.  So `h03F3`
holds whenever `i` is étale, which for a cartesian square with étale bottom arrow it is, by
Stacks 03FU.  Stacks 03LR part (2) is therefore unconditional.

## Main results

* `AlgebraicGeometry.Space.preservesInjectiveObjects_abelianInverseImage`: for an étale morphism
  of algebraic spaces, the inverse image of abelian sheaves along the morphism of small étale
  topoi preserves injective objects.  This is `h03F3`.
* `AlgebraicGeometry.Space.smallEtaleHigherPushforwardBaseChangeIso'` and
  `AlgebraicGeometry.Space.smallEtaleHigherPushforwardPlusBaseChangeIso'`: **Stacks 03LR
  part (2) with no hypothesis beyond the cartesian square and étaleness of `g`**, in the two
  conventions for `R^n`.

## Implementation notes

The étaleness of `i` is not assumed: it is `AlgebraicGeometry.Space.isEtale_of_isPullback`,
Stacks 03FU, applied to the flipped square, exactly as the notes of
`HigherPushforwardBaseChange.lean` anticipate.

What is *not* removed is the other gap that file records of itself and inherits from part (1):
these isomorphisms have the right endpoints but are not proved to be the adjunction mates of
the inverse-image identification, i.e. not identified with the canonical base-change comparison
maps.  That is why the primed declarations here, like the hypothesised ones they are built from,
carry no attribute for Tag 03LR.  Part (2) for the canonical comparison is proved separately,
in `StacksFrontier/AlgebraicGeometry/Spaces/Topologies/SmallEtaleAbelianBaseChangeMate.lean`, as
`AlgebraicGeometry.Space.isIso_smallEtaleAbelianHigherBaseChangeMap`; it consumes
`AlgebraicGeometry.Space.preservesInjectiveObjects_abelianInverseImage` from this file.

For the same reason `preservesInjectiveObjects_abelianInverseImage` carries no
`@[stacks 03F3]` attribute.  Stacks 03F3 is a statement about restriction to a *localization* of
an arbitrary site, of which this is the consequence for the small étale site of an algebraic
space, obtained along Stacks 03LQ; the general statement is not proved here.

## References

* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- **Stacks 03F3 for the small étale site of an algebraic space, in its topos-theoretic form.**
For an étale morphism `h : U ⟶ V` of algebraic spaces, the inverse image of abelian sheaves
along the morphism of small étale topoi `h_{small}` of Stacks 03G2, part (3) carries injective
abelian sheaves to injective abelian sheaves.

This is the hypothesis `h03F3` of
`AlgebraicGeometry.Space.smallEtaleHigherPushforwardBaseChangeIso`.  It is
`AlgebraicGeometry.Space.preservesInjectiveObjects_etaleAbelianRestriction` — the same statement
for restriction along postcomposition of étale charts — transported along
`AlgebraicGeometry.Space.smallToposMorphism_abelianInverseImageIso`, which is Stacks 03LQ at
abelian coefficients.  Injectivity is invariant under isomorphism, so the transport is
`CategoryTheory.Injective.of_iso` applied to that isomorphism at the sheaf. -/
theorem preservesInjectiveObjects_abelianInverseImage {U V : AlgebraicSpaces B S hS}
    (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    (Sites.abelianInverseImage (smallToposMorphism B S hS h)).PreservesInjectiveObjects where
  injective_obj {G} hG := by
    have := preservesInjectiveObjects_etaleAbelianRestriction B S hS h hh
    have := hG
    exact Injective.of_iso
      ((smallToposMorphism_abelianInverseImageIso B S hS h hh).app G).symm inferInstance

/-- **Stacks 03LR, part (2), with no hypothesis left over**, in the injective-resolution
convention `CategoryTheory.Functor.rightDerived`.

For a cartesian square of algebraic spaces whose bottom arrow `g` is étale, the higher direct
images of abelian sheaves on the small étale sites commute with restriction:
`R^n f'_{small,*}(F|_{X'}) = (R^n f_{small,*}F)|_{Y'}` for every `n`, naturally in the abelian
sheaf `F`.

This is `AlgebraicGeometry.Space.smallEtaleHigherPushforwardBaseChangeIso` with its hypothesis
`h03F3` discharged by `AlgebraicGeometry.Space.preservesInjectiveObjects_abelianInverseImage`,
the étaleness of `i` being Stacks 03FU for the flipped square. -/
noncomputable def smallEtaleHigherPushforwardBaseChangeIso' (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (n : ℕ) :
    Sites.abelianInverseImage (smallToposMorphism B S hS i) ⋙
        (Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X'.obj)
          (smallToposMorphism B S hS f')).rightDerived n ≅
      (Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X.obj)
          (smallToposMorphism B S hS f)).rightDerived n ⋙
        Sites.abelianInverseImage (smallToposMorphism B S hS g) :=
  smallEtaleHigherPushforwardBaseChangeIso B S hS i f' f g sq hg
    (preservesInjectiveObjects_abelianInverseImage B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg)) n

/-- **Stacks 03LR, part (2), with no hypothesis left over**, in the derived-category convention
`CategoryTheory.Functor.rightDerivedPlus`, which is the one Stacks 0A4K is stated in.

This is `AlgebraicGeometry.Space.smallEtaleHigherPushforwardPlusBaseChangeIso` with its
hypothesis `h03F3` discharged exactly as in
`AlgebraicGeometry.Space.smallEtaleHigherPushforwardBaseChangeIso'`. -/
noncomputable def smallEtaleHigherPushforwardPlusBaseChangeIso' (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (n : ℕ) :
    Sites.abelianInverseImage (smallToposMorphism B S hS i) ⋙
        (Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X'.obj)
          (smallToposMorphism B S hS f')).rightDerivedPlus (n : ℤ) ≅
      (Stacks.Topos.AbelianPushforward.abelianPushforward (SmallEtale.topology B S hS X.obj)
          (smallToposMorphism B S hS f)).rightDerivedPlus (n : ℤ) ⋙
        Sites.abelianInverseImage (smallToposMorphism B S hS g) :=
  smallEtaleHigherPushforwardPlusBaseChangeIso B S hS i f' f g sq hg
    (preservesInjectiveObjects_abelianInverseImage B S hS i
      (isEtale_of_isPullback B S hS f' i g f sq.flip hg)) n

end AlgebraicGeometry.Space

end
