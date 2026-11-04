module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.MaximalIdealCotangent

/-!
# Residue field extensions at a closed point over an algebraically closed field

At a closed point of a scheme locally of finite type over an algebraically closed field the
residue field is the ground field, so the residue field extension induced by a morphism is an
isomorphism. Such an extension is both separable and purely inseparable, which discharges the
hypotheses that the tangent-space and closed-immersion criteria carry.

## Main results

* `Algebra.IsSeparable.of_bijective_algebraMap` and
  `IsPurelyInseparable.of_bijective_algebraMap`: a field extension whose structural map is
  bijective is separable, and is purely inseparable.
* `AlgebraicGeometry.isSeparable_residueField_of_isClosed`: the residue field extension of a
  morphism at a closed point over an algebraically closed field is separable.
* `AlgebraicGeometry.isPurelyInseparable_residueField_of_isClosed`: the same extension, taken
  along the canonical comparison with the residue field at the image, is purely inseparable.

## Implementation notes

Both field-theoretic statements are transfers along the isomorphism determined by the structural
map: separability from `Algebra.IsSeparable F F` and pure inseparability from
`IsPurelyInseparable F F`.

The two geometric statements differ only in how the algebra structure on the residue field at the
point is presented. The separability statement uses the canonical algebra attached to the local
homomorphism of stalks, which is the form the tangent-space criterion of Tag 0B2E asks for. The
pure inseparability statement uses the algebra attached to an explicit homomorphism, composing the
residue-field comparison at the image with the residue-field map, which is the form Tag 04DG asks
for; its hypothesis is the equality of the image of the point with the given point of the target.

## References

* [Stacks Project, Tag 04DG](https://stacks.math.columbia.edu/tag/04DG)
* [Stacks Project, Tag 0B2E](https://stacks.math.columbia.edu/tag/0B2E)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

/-- A field extension whose structural map is bijective is separable. -/
public theorem Algebra.IsSeparable.of_bijective_algebraMap {F E : Type*} [Field F] [Field E]
    [Algebra F E] (h : Function.Bijective (algebraMap F E)) : Algebra.IsSeparable F E :=
  Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl F) (RingEquiv.ofBijective _ h) rfl

/-- A field extension whose structural map is bijective is purely inseparable. -/
public theorem IsPurelyInseparable.of_bijective_algebraMap {F E : Type*} [Field F] [Field E]
    [Algebra F E] (h : Function.Bijective (algebraMap F E)) : IsPurelyInseparable F E :=
  (AlgEquiv.ofBijective (Algebra.ofId F E) h).isPurelyInseparable

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.stalkMapAlgebra
  AlgebraicGeometry.stalkMapIsLocalHom AlgebraicGeometry.residueFieldMapAlgebra

/-- **The residue field extension at a closed point over an algebraically closed field is
separable**, being an isomorphism: both residue fields are the ground field. -/
public theorem isSeparable_residueField_of_isClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType (f ≫ q)]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    Algebra.IsSeparable (Y.residueField (f.base x)) (X.residueField x) :=
  have : IsIso (f.residueFieldMap x) := isIso_residueFieldMap_of_isClosed f q x hx
  Algebra.IsSeparable.of_bijective_algebraMap
    (ConcreteCategory.bijective_of_isIso (f.residueFieldMap x))

/-- **The residue field extension at a closed point over an algebraically closed field is purely
inseparable**, being an isomorphism. The algebra structure is the one attached to the composite of
the residue-field comparison at the image with the residue-field map, as in Tag 04DG. -/
public theorem isPurelyInseparable_residueField_of_isClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType (f ≫ q)]
    (s : Y) (x : X) (hxs : f.base x = s) (hx : IsClosed ({x} : Set X)) :
    letI := ((Y.residueFieldCongr hxs).inv ≫ f.residueFieldMap x).hom.toAlgebra
    IsPurelyInseparable (Y.residueField s) (X.residueField x) := by
  have : IsIso (f.residueFieldMap x) := isIso_residueFieldMap_of_isClosed f q x hx
  let := ((Y.residueFieldCongr hxs).inv ≫ f.residueFieldMap x).hom.toAlgebra
  refine IsPurelyInseparable.of_bijective_algebraMap ?_
  rw [RingHom.algebraMap_toAlgebra]
  exact ConcreteCategory.bijective_of_isIso ((Y.residueFieldCongr hxs).inv ≫ f.residueFieldMap x)

end AlgebraicGeometry

end
