module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineCanonicalEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineCanonicalFull

/-!
# The Beauville--Laszlo glueing equivalence on affine glueable spaces (Stacks 0F9Q)

Let `(g : R → R', f)` be a Beauville--Laszlo glueing pair and let `X = Spec R`, `U = Spec R_f`,
`X' = Spec R'`, `U' = Spec R'_{g f}` be the four affine schemes of the associated square of a big
fppf site. The glueing functor of Stacks 0F9N restricts, by
`BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction`, to a functor from the affine algebraic
spaces over `X` which are glueable for `(g, f)` to the cartesian glueing triples whose three
components are affine. That restriction is faithful (Stacks 0F9S, via
`BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction_faithful`), full
(`BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction_full`) and essentially surjective
(`BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction_essSurj`); this module puts the three
together into the equivalence asserted by Stacks 0F9Q.

## Main results

* `BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction_isEquivalence`: **Stacks 0F9Q**, the
  glueing functor of Stacks 0F9N restricts to an equivalence between the affine glueable algebraic
  spaces over `Spec R` and the cartesian glueing triples with three affine components.
* `BeauvilleLaszlo.Space.affineGlueingEquivalence`: the same conclusion packaged as a term of
  `BeauvilleLaszlo.Space.AffineGlueingEquivalenceSpec`, so that the equivalence comes with the
  identification of its forward functor with the glueing functor of Stacks 0F9N.

## Implementation notes

`CategoryTheory.Functor.IsEquivalence` has exactly the three fields `faithful`, `full` and
`essSurj`, so the first result is the anonymous constructor applied to the three inputs and there
is no coherence condition to discharge. The second is
`BeauvilleLaszlo.Space.affineGlueingEquivalenceOfParts` applied to the same three: the forward
functor of the resulting equivalence is the ambient functor by construction, since
`BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction` is an
`CategoryTheory.ObjectProperty.lift` of it, so the natural isomorphism is `CategoryTheory.Iso.refl`
and no further input is needed.

## References

* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9S](https://stacks.math.columbia.edu/tag/0F9S)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace BeauvilleLaszlo.Space

/-- **Stacks 0F9Q.** For a Beauville--Laszlo glueing pair `(g : R → R', f)`, the glueing functor
of Stacks 0F9N restricts to an **equivalence** between the category of affine algebraic spaces
over `X = Spec R` which are glueable for `(g, f)` and the full subcategory of those glueing
triples `(V, V', Y')` over `U ← U' → X'` whose three components are affine.

The functor in question is `BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction`, which is by
definition the restriction of `BeauvilleLaszlo.Space.beauvilleLaszloGlueingSpaces`, the glueing
functor of Stacks 0F9N, to those two full subcategories. -/
@[stacks 0F9Q]
theorem canonicalAffineGlueableRestriction_isEquivalence {R R' : Type u} [CommRing R] [CommRing R']
    (g : R →+* R') (f : R) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) :
    (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).IsEquivalence :=
  ⟨canonicalAffineGlueableRestriction_faithful g f B hU' hU hX' hX hcomm hglue,
    canonicalAffineGlueableRestriction_full g f B hU' hU hX' hX hcomm hglue,
    canonicalAffineGlueableRestriction_essSurj g f B hU' hU hX' hX hcomm hglue⟩

/-- **The affine Beauville--Laszlo glueing equivalence as data.** The equivalence of Stacks 0F9Q
together with the identification of its forward functor with the glueing functor of
Stacks 0F9N. -/
noncomputable def affineGlueingEquivalence {R R' : Type u} [CommRing R] [CommRing R']
    (g : R →+* R') (f : R) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) :
    AffineGlueingEquivalenceSpec g f B _ _ _ hU' hU hX' hX _ _
      (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _ hcomm).functor :=
  affineGlueingEquivalenceOfParts g f B hU' hU hX' hX hcomm
    (canonicalAffineGlueableRestriction_faithful g f B hU' hU hX' hX hcomm hglue)
    (canonicalAffineGlueableRestriction_full g f B hU' hU hX' hX hcomm hglue)
    (canonicalAffineGlueableRestriction_essSurj g f B hU' hU hX' hX hcomm hglue)

end BeauvilleLaszlo.Space
