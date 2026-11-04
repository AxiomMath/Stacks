module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points

/-!
# Residue fields after extension of the ground field

The residue field of a point of a fibre product is the residue field of the corresponding prime
of the tensor product of the residue fields of its two images.

## Main results

* `AlgebraicGeometry.Scheme.Pullback.isIso_residueFieldMap_to_residueField_specOfPoint`
  identifies the residue field of a point of a fibre product with the residue field at its
  corresponding prime.

## Implementation notes

The result is stated for an arbitrary fibre product. Specializing one factor and the base to
spectra of fields gives the source statement. For a point `y` of the pullback,
`AlgebraicGeometry.Scheme.Pullback.Triplet.ofPoint y` records its three images. Its `tensor` is
the pushout of their residue fields. The point `AlgebraicGeometry.Scheme.Pullback.SpecOfPoint y`
is the kernel of the canonical map from this tensor product to `κ(y)`. The initial
`AlgebraicGeometry.Scheme.residueFieldCongr` in the displayed composite pins down the
identification between `y` and the point reconstructed from that prime.

## References

* [Stacks Project, Tag 0C4Y](https://stacks.math.columbia.edu/tag/0C4Y)
-/

@[expose] public section

open CategoryTheory Limits IsIso

universe u

namespace AlgebraicGeometry.Scheme.Pullback

/-- **Stacks Project, Tag 0C4Y (residue field).** If `y` is a point of the base change of a
scheme over `k` to a field extension `K/k`, its residue field is canonically isomorphic to the
residue field at the corresponding prime of `κ(x) ⊗[k] K`. -/
@[stacks 0C4Y "residue_field"]
public theorem isIso_residueFieldMap_to_residueField_specOfPoint
    {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (y : (pullback f g : Scheme)) :
    let T := Scheme.Pullback.Triplet.ofPoint y
    let p := Scheme.Pullback.SpecOfPoint y
    IsIso (((pullback f g : Scheme).residueFieldCongr
        (Scheme.Pullback.SpecTensorTo_SpecOfPoint y).symm).hom ≫
      T.SpecTensorTo.residueFieldMap p ≫
      (Scheme.Spec.residueFieldIso T.tensor p).hom) :=
  comp_isIso' inferInstance (isIso_residueFieldMap_specTensorTo_comp_residueFieldIso _ _)

end AlgebraicGeometry.Scheme.Pullback
