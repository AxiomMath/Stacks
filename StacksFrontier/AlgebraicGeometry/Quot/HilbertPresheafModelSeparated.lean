module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProperTransfer

/-!
# Separatedness of a model of the Hilbert functor over the base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site. The
Hilbert presheaf `AlgebraicGeometry.Space.hilbertPresheaf` of Stacks 0CZY takes values in
`Type (u + 1)`, so its canonical morphism `AlgebraicGeometry.Space.hilbertPresheafToBase` to `Y`
can only be separated in the sense of `AlgebraicGeometry.Space.IsSeparatedULift`, the form of
Stacks 03HL for presheaves with values in a larger universe, while separatedness of
`Hilb_{X/Y} ⟶ Y` as a morphism of presheaves of `Type u` is a statement about a model
`AlgebraicGeometry.Space.HilbertPresheafModel` of the Hilbert presheaf. This file shows that the
two agree: the morphism to the base of any model is separated exactly when the canonical
morphism of the Hilbert presheaf itself is.

## Main results

* `AlgebraicGeometry.Space.HilbertPresheafModel.whiskerRight_toBase`: the universe lift of the
  morphism to the base of a model is the canonical morphism to the base of the Hilbert presheaf,
  read through the identification of the lift of the model with the Hilbert presheaf.
* `AlgebraicGeometry.Space.HilbertPresheafModel.isSeparated_toBase_iff`: the morphism to the base
  of a model is separated exactly when the canonical morphism of the Hilbert presheaf is.

## Implementation notes

The universe lift of the morphism to the base of a model is the canonical morphism of the
Hilbert presheaf precomposed with an isomorphism, and the relative diagonal of a composite with
an isomorphism on the source is the relative diagonal of the morphism up to isomorphisms of its
source and target, so the transfer is
`AlgebraicGeometry.Space.isSeparatedULift_whiskerRight_iff` followed by invariance of the
diagonal property under isomorphisms.

## References

* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
    {f : X ⟶ Y}

namespace HilbertPresheafModel

/-- **A model of the Hilbert presheaf is a model over the base.** The universe lift of its
morphism to the base is the canonical morphism to the base of Stacks 0CZY, read through the
identification of the lift of the model with the Hilbert presheaf; this holds for every model, by
the very definition of `AlgebraicGeometry.Space.HilbertPresheafModel.toBase`. -/
theorem whiskerRight_toBase (M : HilbertPresheafModel f) :
    Functor.whiskerRight M.toBase uliftFunctor.{u + 1, u} =
      M.iso.hom ≫ hilbertPresheafToBase f := by
  ext T z
  rfl

/-- **Separatedness of a model of the Hilbert functor.** The morphism to the base of a model of
the Hilbert presheaf of `f` is separated exactly when the canonical morphism of the Hilbert
presheaf to the base is separated, in the sense of Stacks 03HL for presheaves with values in the
larger universe. -/
theorem isSeparated_toBase_iff (M : HilbertPresheafModel f) :
    IsSeparated B S hS M.toBase ↔ IsSeparatedULift.{u + 1} B S hS (hilbertPresheafToBase f) := by
  rw [← isSeparatedULift_whiskerRight_iff.{u + 1} B S hS M.toBase, M.whiskerRight_toBase]
  exact ((MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}).diagonal.cancel_left_of_respectsIso
      M.iso.hom (hilbertPresheafToBase f)

end HilbertPresheafModel

end AlgebraicGeometry.Space

end
