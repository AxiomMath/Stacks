module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple

/-!
# The relatively ample objects of the Picard stack

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, and let
`Picardstack_{X/Y}` be the Picard stack of Section 0372: an object is a scheme `T` over `Y`
together with an invertible module `L` on the base change `X_T`. This file isolates the property
of such an object that `L` is ample on `X_T/T` in the sense of Stacks 0D31, and shows that it is
inherited along every morphism of the Picard stack.

This is the property cutting out the image of the polarized families in the proof of
Stacks 0D41: an object of the 2-fibre product of `Polarized` with a scheme-valued point of
`Spaces'_{fp, flat, proper}` is a pair `(T/S, L)` with `L` ample on `X_T/T`, and the source shows
that this locus is open (Stacks 0D3D).

## Main definitions

* `AlgebraicGeometry.Space.picardAmple`: the property of an object of the Picard stack that its
  invertible module is ample relative to the base change.

## Main results

* `AlgebraicGeometry.Space.picardAmple_of_hom`: the property is inherited along morphisms of the
  Picard stack. A morphism `(T', L') ⟶ (T, L)` exhibits `X_{T'}` as the base change of `X_T`
  along `T' ⟶ T` (`AlgebraicGeometry.Space.isPullback_baseChangeMap`) and `L'` as isomorphic to
  the pullback of `L`, so this is Stacks 0D33 together with the invariance of relative ampleness
  under isomorphism.
* `AlgebraicGeometry.Space.picardAmple_isClosedUnderIsomorphisms`: in particular the property is
  closed under isomorphisms.

## References

* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D33](https://stacks.math.columbia.edu/tag/0D33)
* [Stacks Project, Tag 0D41](https://stacks.math.columbia.edu/tag/0D41)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hc : ModulePushforwardCoherence B S hS) (s : PicardSituation B S hS)

/-- The property of an object `(T, L)` of `Picardstack_{X/Y}` that the invertible module `L` is
ample on `X_T/T` (Stacks 0D31). -/
def picardAmple : ObjectProperty (picardCFG hc s).val.obj := fun A =>
  IsRelativelyAmple B S hS (baseChangeInclusion s.f A.T) A.lineBundle

variable {hc s}

/-- **The relatively ample objects are inherited along morphisms of the Picard stack.** A
morphism `(T', L') ⟶ (T, L)` makes `X_{T'}` the base change of `X_T` along `T' ⟶ T` and `L'` the
pullback of `L`, up to isomorphism, so this is Stacks 0D33. -/
theorem picardAmple_of_hom {A C : (picardCFG hc s).val.obj} (m : A ⟶ C)
    (hC : picardAmple hc s C) : picardAmple hc s A := by
  have hpull : IsRelativelyAmple B S hS (baseChangeInclusion s.f A.T)
      ((modulePullback B S hS (baseChangeMap s.f (PicardHom.base m))).obj C.lineBundle) :=
    isRelativelyAmple_baseChange (isPullback_baseChangeMap s.f (PicardHom.base m)) _ hC
  have := PicardHom.isIso_fibre m
  exact (isRelativelyAmple_congr _ (asIso (PicardHom.fibre m))).mp hpull

variable (hc s)

/-- The relatively ample objects of the Picard stack form a property closed under
isomorphisms. -/
theorem picardAmple_isClosedUnderIsomorphisms :
    (picardAmple hc s).IsClosedUnderIsomorphisms :=
  ⟨fun e hX => picardAmple_of_hom e.inv hX⟩

end AlgebraicGeometry.Space

end
