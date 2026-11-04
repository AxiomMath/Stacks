module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Limits.AffineFromSurjectiveUniversallyClosed

/-!
# Fibre products over a quasi-affine base (Stacks 0F9U, step 4)

Step 4 of the proof of Stacks 0F9U applies the affine equivalence of Stacks 0F9Q a second time,
to the triple

```
((U ×_X T) ×_V (U ×_X T), (U' ×_X T) ×_{V'} (U' ×_X T), (X' ×_X T) ×_{Y'} (X' ×_X T))
```

whose realizing object is the relation `W`. For that application the triple must have affine
components, and here the affineness does *not* come from the square: these are fibre products
over `V`, `V'`, `Y'`, which are the components of the original triple and so are only
**quasi-affine**. Base change of affines along the four affine schemes of the
Beauville--Laszlo square, which is what gives the components of the first triple their
affineness, says nothing about a fibre product over a quasi-affine base.

This module supplies the missing affineness. It is not special to quasi-affine bases: what is
used is that a quasi-affine scheme is separated, and that a morphism from an affine scheme to a
separated scheme is an affine morphism. An affine morphism on one leg and an affine scheme on the
other give an affine fibre product.

## Main results

* `AlgebraicGeometry.isAffine_pullback_of_isQuasiAffine_base`: the fibre product of two affine
  schemes over a quasi-affine base is affine.
* `AlgebraicGeometry.isAffine_pullback_of_isSeparated_base`: the same with only separatedness of
  the base, which is all the proof uses.

## References

* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A fibre product of two affine schemes over a separated base is affine.** A morphism from an
affine scheme to a separated scheme is an affine morphism, and an affine morphism on one leg with
an affine scheme on the other has affine fibre product. -/
theorem isAffine_pullback_of_isSeparated_base {A A' V : Scheme.{u}}
    (a : A ⟶ V) (a' : A' ⟶ V) (hA : IsAffine A) (hA' : IsAffine A')
    (hV : V.IsSeparated) : IsAffine (pullback a a') := by
  have _ : IsAffine A := hA
  have _ : IsAffine A' := hA'
  have _ : V.IsSeparated := hV
  have _ : IsAffineHom a :=
    Stacks.AffineFromUniversallyClosed.isAffineHom_of_isAffine_of_isSeparated a
  infer_instance

/-- **A fibre product of two affine schemes over a quasi-affine base is affine.**

This is the affineness that step 4 of the proof of Stacks 0F9U needs and that step 2 does not
supply: the components of the relation triple are fibre products over the quasi-affine components
`V`, `V'`, `Y'` of the original triple, not over affine schemes, so their affineness — which is
what lets Stacks 0F9Q be applied a second time — does not follow from base change along the
square. A quasi-affine scheme is separated, so this is
`AlgebraicGeometry.isAffine_pullback_of_isSeparated_base`. -/
theorem isAffine_pullback_of_isQuasiAffine_base {A A' V : Scheme.{u}}
    (a : A ⟶ V) (a' : A' ⟶ V) (hA : IsAffine A) (hA' : IsAffine A')
    (hV : V.IsQuasiAffine) : IsAffine (pullback a a') :=
  have _ : V.IsQuasiAffine := hV
  isAffine_pullback_of_isSeparated_base a a' hA hA' inferInstance

end AlgebraicGeometry

end
