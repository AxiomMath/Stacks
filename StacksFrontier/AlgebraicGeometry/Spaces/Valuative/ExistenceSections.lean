module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Criterion

/-!
# Lifts of a valuative square, read as sections of the source presheaf

Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of a scheme `S` and let `q` be a
valuative square for it (Stacks 03IX). A dotted arrow filling `q` is a morphism
`yoneda.obj (Spec R) ⟶ X`, that is — by the Yoneda lemma — a section of `X` over the site object
attached to the spectrum of the valuation ring. This file records the dictionary: a section whose
restriction to the spectrum of the fraction field is the generic point of `q`, and whose image
under `f` is the bottom edge of `q`, *is* a dotted arrow.

## Main definitions

* `AlgebraicGeometry.Space.ValuativeSquare.genericMap`: the canonical morphism of site objects
  from the spectrum of the fraction field to the spectrum of the valuation ring.
* `AlgebraicGeometry.Space.ValuativeSquare.liftOfSection`: the dotted arrow attached to a
  compatible section.

## Implementation notes

`genericMap` is the morphism written out in the `comm` field of
`AlgebraicGeometry.Space.ValuativeSquare` and in the `generic_comm` field of
`AlgebraicGeometry.Space.ValuativeSquare.Lift`; naming it is what lets the compatibility
hypotheses of `liftOfSection` be stated as restriction of sections rather than as composition of
morphisms of presheaves.

The two compatibilities of the dotted arrow are the images of the two hypotheses under
`CategoryTheory.yonedaEquiv`, so both proofs are the corresponding naturality of the inverse of
that bijection; nothing is checked by hand.

## References

* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
* [Stacks Project, Tag 0H1V](https://stacks.math.columbia.edu/tag/0H1V)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

/-- The canonical morphism of site objects from the spectrum of the fraction field of a valuative
square to the spectrum of its valuation ring: the one induced by the inclusion of the valuation
ring in its fraction field. It is the left column of the square. -/
noncomputable abbrev ValuativeSquare.genericMap (q : ValuativeSquare f) :
    siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) ⟶
      siteObject B S hS q.ring_mem q.base :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K))) :
    B.obj q.field_mem ⟶ B.obj q.ring_mem)

/-- **A dotted arrow from a section of the source.** A section `z` of `X` over the spectrum of the
valuation ring of a valuative square whose restriction along the left column is the generic point,
and whose image under `f` is the bottom edge, is a dotted arrow filling the square. -/
noncomputable def ValuativeSquare.liftOfSection (q : ValuativeSquare f)
    (z : X.obj (op (siteObject B S hS q.ring_mem q.base)))
    (hgeneric : X.map q.genericMap.op z = yonedaEquiv q.generic)
    (hspecial : f.app (op (siteObject B S hS q.ring_mem q.base)) z =
      yonedaEquiv q.special) :
    q.Lift where
  map := yonedaEquiv.symm z
  generic_comm :=
    (yonedaEquiv_symm_naturality_left q.genericMap X z).trans
      ((congrArg yonedaEquiv.symm hgeneric).trans (yonedaEquiv.symm_apply_apply q.generic))
  special_comm :=
    (yonedaEquiv_symm_naturality_right _ f z).trans
      ((congrArg yonedaEquiv.symm hspecial).trans (yonedaEquiv.symm_apply_apply q.special))

end AlgebraicGeometry.Space

end
