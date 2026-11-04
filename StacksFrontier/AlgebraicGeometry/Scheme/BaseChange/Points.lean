module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute

/-!
# Points of a fibre product of schemes

The points of a fibre product `X ×_S Y` are classified by triples `(x, y, s)` of points of `X`,
`Y` and `S` lying over one another together with a prime ideal of `κ(x) ⊗_{κ(s)} κ(y)`, and the
residue field of the resulting point of the fibre product is the residue field at that prime.

The classification itself is Mathlib's `AlgebraicGeometry.Scheme.Pullback.carrierEquiv`, so only
the residue-field half needs proving here.

## Main results

* `AlgebraicGeometry.Scheme.Pullback.isIso_residueFieldMap_specTensorTo_comp_residueFieldIso`:
  for a classified prime `p`, the canonical residue-field map induced by
  `Triplet.SpecTensorTo`, composed with `AlgebraicGeometry.Scheme.Spec.residueFieldIso`, is an
  isomorphism.

## Implementation notes

`AlgebraicGeometry.Scheme.Pullback.Triplet` packages `(x, y, s)` together with the two equalities
over `S`. Its `tensor` is the pushout of the corresponding residue fields, hence the tensor
product `κ(x) ⊗_{κ(s)} κ(y)`, and a point of its spectrum is a prime ideal; so `carrierEquiv` is
precisely the asserted bijection and is recorded rather than restated.

The residue-field comparison is proved from the splitting criterion
`isIso_of_specMap_comp_eq_fromSpecResidueField`: a map of fields out of `κ(x)` whose `Spec` fits
into the canonical triangle over the scheme is both a monomorphism and a split epimorphism, hence
an isomorphism. The input triangle is `Triplet.Spec_ofPointTensor_SpecTensorTo`.

## References

* [Stacks Project, Tag 01JT](https://stacks.math.columbia.edu/tag/01JT)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Pullback

open AlgebraicGeometry

add_to_stacks 01JT "points" AlgebraicGeometry.Scheme.Pullback.carrierEquiv
add_to_sga "3 V 7.3" "partial" AlgebraicGeometry.Scheme.Pullback.carrierEquiv
add_to_ega "I 3.4.9" "partial" AlgebraicGeometry.Scheme.Pullback.carrierEquiv

/-- A map of fields into a residue field whose `Spec` factors the canonical map from that residue
field is an isomorphism: it is injective, and the factorization splits it. -/
private lemma isIso_of_specMap_comp_eq_fromSpecResidueField
    {X : Scheme.{u}} (x : X) {K : Type u} [Field K]
    (f : CommRingCat.of K ⟶ X.residueField x) (a : Spec (.of K) ⟶ X)
    (h : Spec.map f ≫ a = X.fromSpecResidueField x) : IsIso f := by
  obtain ⟨⟨y, k⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective a
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h
  have hy := congrArg (fun m : Spec (X.residueField x) ⟶ X ↦ m default) h
  simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at hy
  subst y
  have : Mono f := ConcreteCategory.mono_of_injective f f.hom.injective
  have : IsSplitEpi f := ⟨⟨k, by
    simpa only [← Spec.map_inj, Spec.map_comp, Spec.map_id,
      ← cancel_mono (X.fromSpecResidueField x), Category.assoc, Category.id_comp] using h⟩⟩
  exact isIso_of_mono_of_isSplitEpi f

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- **Stacks Project, Tag 01JT (residue fields).** For a point of the fibre
product represented by a prime `p` of `κ(x) ⊗[κ(s)] κ(y)`, the canonical map
from the residue field of the corresponding point to the residue field at `p`
is an isomorphism. -/
@[stacks 01JT "residue fields"]
public theorem isIso_residueFieldMap_specTensorTo_comp_residueFieldIso
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor) :
    IsIso (T.SpecTensorTo.residueFieldMap p ≫
      (Scheme.Spec.residueFieldIso T.tensor p).hom) := by
  have : IsIso (T.SpecTensorTo.residueFieldMap p) :=
    isIso_of_specMap_comp_eq_fromSpecResidueField p _ _
      (T.Spec_ofPointTensor_SpecTensorTo p)
  infer_instance

end AlgebraicGeometry.Scheme.Pullback
