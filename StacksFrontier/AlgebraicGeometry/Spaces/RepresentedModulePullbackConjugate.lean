module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.NatIsoSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange

/-!
# The unit characterisation of the square of inverse images of a representable morphism

`AlgebraicGeometry.Space.representedModulePullbackIso` identifies, for a morphism `g : T' ⟶ T`
of the big fppf category over `S`, the inverse image of modules of Stacks 03LU along the
represented morphism of algebraic spaces with pullback along the morphism of small étale ringed
sites of Stacks 070R (2) attached to the underlying morphism of schemes, read through the
identifications of the small étale site of `yoneda.obj U` with the small étale site of the scheme
underlying `U`.  It is the comparison of two *left* adjoints of one and the same functor, so it
has no formula; this file records the only equation that determines it.

The comparison is `CategoryTheory.Adjunction.leftAdjointUniq` of the two composite adjunctions
round the square, with the second transported along
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`.  The mate of such a comparison
is the isomorphism it was transported along, so the conjugate of the square of inverse images is
the square of direct images, with nothing else in it.

## Main results

* `AlgebraicGeometry.Space.conjugateIsoEquiv_representedModulePullbackIso`: **the square of
  inverse images is conjugate to the square of direct images.**
* `AlgebraicGeometry.Space.conjugateEquiv_representedModulePullbackIso_hom`: the same read on
  the underlying morphisms of functors, which is the form a composite of conjugates consumes.

## Implementation notes

`CategoryTheory.conjugateEquiv` is a bijection, so either statement pins the comparison: no other
isomorphism of the two composite inverse images has that mate.  This is what reduces a coherence
for the inverse images to the corresponding coherence for the direct images, where every factor
is a restriction of sections; the pasting coherence of the square of direct images is
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso_comp`
(`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePushforwardSquareComp.lean`).

The local `implicit_reducible` attribute on `AlgebraicGeometry.Space.smallEtaleRingedSite`
collapses the two spellings of the category of `𝒪`-modules, as it does in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsIdComparison.lean`; without it the two
composite adjunctions cannot be written down at the spelling the square uses.

No tag is registered.  Stacks 03LU is tagged where the inverse image of modules is constructed,
and what is added here is which comparison
`AlgebraicGeometry.Space.representedModulePullbackIso` is.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Represented

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/- The two spellings of the category of `𝒪`-modules are definitionally equal through
`AlgebraicGeometry.Space.smallEtaleRingedSite`; collapsing them is what lets the two composite
adjunctions be written at the spelling of the square.  See the implementation notes. -/
attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **The square of inverse images of a representable morphism is conjugate to the square of
direct images.**  Going round the square of small étale ringed sites on the pullback side —
reading a sheaf of modules on the small étale site of the scheme underlying `T` on the small
étale site of `yoneda.obj T` and then taking the inverse image of Stacks 03LU along the
represented morphism, against pulling it back along the morphism of ringed sites of
Stacks 070R (2) and then reading the result — has as its mate, with respect to the two composite
pullback–pushforward adjunctions, exactly
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`.

`CategoryTheory.conjugateEquiv` is a bijection, so this pins
`AlgebraicGeometry.Space.representedModulePullbackIso`: it is the only isomorphism of the two
composite inverse images with that mate. -/
theorem conjugateIsoEquiv_representedModulePullbackIso :
    conjugateIsoEquiv
        ((representedSmallEtaleModuleEquivalence B S hS T).symm.toAdjunction.comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (representedSchemeStructureMapRing B S hS g)))
        ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).comp
          (representedSmallEtaleModuleEquivalence B S hS T').symm.toAdjunction)
        (representedModulePullbackIso B S hS g hg) =
      representedModulePushforwardSquareIso B S hS g hg :=
  Stacks.Mates.conjugateIsoEquiv_leftAdjointUniq_ofNatIsoRight _ _ _

/-- **The square of inverse images is conjugate to the square of direct images, on morphisms.**
This is `AlgebraicGeometry.Space.conjugateIsoEquiv_representedModulePullbackIso` read on the
underlying morphisms of functors, which is the form a composite of conjugates consumes:
`CategoryTheory.conjugateEquiv` is compatible with composition and whiskering on morphisms, not
on isomorphisms. -/
theorem conjugateEquiv_representedModulePullbackIso_hom :
    conjugateEquiv
        ((representedSmallEtaleModuleEquivalence B S hS T).symm.toAdjunction.comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (representedSchemeStructureMapRing B S hS g)))
        ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS g)).comp
          (representedSmallEtaleModuleEquivalence B S hS T').symm.toAdjunction)
        (representedModulePullbackIso B S hS g hg).hom =
      (representedModulePushforwardSquareIso B S hS g hg).hom :=
  Stacks.Mates.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _

end Represented

end AlgebraicGeometry.Space

end
