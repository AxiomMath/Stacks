module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Decency
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericRationalFunctions

/-!
# Function fields and residue fields on a good algebraic space

In the situation of Stacks 0EDT let `X/B` be good. If `X` is integral then its function field
`R(X)` is defined and is the residue field of `X` at its generic point. Every point `ξ` of `X`
is the generic point of exactly one integral closed subspace `Z ⊆ X`, and the residue field
`κ(ξ)` is the function field of that `Z`.

## Main definitions

* `AlgebraicGeometry.Space.residueFieldCongr`: the identification of the residue fields at two
  equal points.
* `AlgebraicGeometry.Space.integralClosedSubspaceOfPoint`: the integral closed subspace whose
  generic point is a prescribed point, namely the reduced induced subspace on the closure of
  that point.
* `AlgebraicGeometry.Space.residueFieldGenericPointRingEquiv`: the identification of the
  residue field of `X` at the generic point of an integral closed subspace `Z` with the
  function field of `Z`.
* `AlgebraicGeometry.Space.residueFieldRingEquivRationalFunctions`: the same identification,
  read at an arbitrary point of `X` and the integral closed subspace it is the generic point
  of.
* `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.functionFieldRingEquiv`: the function
  field of a good integral algebraic space is the residue field at its generic point.
* `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.residueFieldRingEquivFunctionField`: the
  residue field of a good algebraic space at a point is the function field of the unique
  integral closed subspace whose generic point is that point.

## Main results

* `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.isField_functionField`: the function
  field of a good integral algebraic space is defined, its ring of rational functions being a
  field.
* `AlgebraicGeometry.Space.isGenericPoint_integralClosedSubspaceOfPoint` and
  `AlgebraicGeometry.Space.pointsMap_genericPoint_integralClosedSubspaceOfPoint`: the
  prescribed point is a generic point of the point set of that subspace, and it is the image
  of the generic point of the subspace.
* `AlgebraicGeometry.Space.bijective_residueFieldHom_ι_genericPoint`: the inclusion of an
  integral closed subspace identifies the residue field of the ambient space at the generic
  point of the subspace with the residue field of the subspace there.

## Implementation notes

The function field `R(X)` of Stacks 0ENE is the ring `AlgebraicGeometry.Space.rationalFunctions`
of rational functions of Stacks 0EMP.

## References

* [Stacks Project, Tag 0ENX](https://stacks.math.columbia.edu/tag/0ENX)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDV](https://stacks.math.columbia.edu/tag/0EDV)
* [Stacks Project, Tag 0END](https://stacks.math.columbia.edu/tag/0END)
* [Stacks Project, Tag 0ENE](https://stacks.math.columbia.edu/tag/0ENE)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0EMP](https://stacks.math.columbia.edu/tag/0EMP)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0EMX](https://stacks.math.columbia.edu/tag/0EMX)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The residue field at a point, transported along an equality of points -/

/-- The residue fields of a decent algebraic space at two equal points are identified. -/
noncomputable def residueFieldCongr (hdec : IsDecentSpace B S hS X)
    {x y : points B S hS X} (h : x = y) :
    residueField B S hS X hdec x ≃+* residueField B S hS X hdec y := by
  subst h
  exact RingEquiv.refl _

/-! ### The integral closed subspace with a prescribed generic point -/

/-- The integral closed subspace of a decent algebraic space over `S` whose generic point is a
prescribed point: the reduced induced closed subspace on the closure of that point. -/
noncomputable def integralClosedSubspaceOfPoint (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (ξ : points B S hS X) :
    IntegralClosedSubspace B S hS X :=
  integralClosedSubspaceOfPoints B S hS hX hdec (IrreducibleCloseds.closureSingleton ξ)

/-- The point set of the integral closed subspace attached to a point is the closure of that
point. -/
@[simp]
theorem subspacePointSet_integralClosedSubspaceOfPoint (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (ξ : points B S hS X) :
    subspacePointSet B S hS X (integralClosedSubspaceOfPoint B S hS hX hdec ξ).subspace =
      closure {ξ} :=
  subspacePointSet_integralClosedSubspaceOfPoints B S hS hX hdec _

/-- The prescribed point is a generic point of the point set of the integral closed subspace
attached to it. -/
theorem isGenericPoint_integralClosedSubspaceOfPoint (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (ξ : points B S hS X) :
    IsGenericPoint ξ
      (subspacePointSet B S hS X (integralClosedSubspaceOfPoint B S hS hX hdec ξ).subspace) :=
  (subspacePointSet_integralClosedSubspaceOfPoint B S hS hX hdec ξ).symm

/-- **Stacks 0EDV, uniqueness.** An integral closed subspace whose point set has `ξ` as a
generic point is the subspace attached to `ξ`. -/
theorem eq_integralClosedSubspaceOfPoint (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (ξ : points B S hS X)
    (Z : IntegralClosedSubspace B S hS X)
    (hZ : IsGenericPoint ξ (subspacePointSet B S hS X Z.subspace)) :
    Z = integralClosedSubspaceOfPoint B S hS hX hdec ξ :=
  eq_integralClosedSubspaceOfPoints B S hS hX hdec Z
    (IrreducibleCloseds.closureSingleton ξ) hZ.symm

/-- The inclusion of the integral closed subspace attached to a point carries the generic
point of that subspace to the point itself. -/
theorem pointsMap_genericPoint_integralClosedSubspaceOfPoint (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (ξ : points B S hS X) :
    pointsMap B S hS (integralClosedSubspaceOfPoint B S hS hX hdec ξ).subspace.toFunctor
        (integralClosedSubspaceOfPoint B S hS hX hdec ξ).subspace.ι
        ((integralClosedSubspaceOfPoint B S hS hX hdec ξ).genericPoint B S hS) = ξ :=
  (eq_pointsMap_genericPoint_of_isGenericPoint B S hS hX _ ξ
    (isGenericPoint_integralClosedSubspaceOfPoint B S hS hX hdec ξ)).symm

/-! ### The residue field at the generic point of an integral closed subspace -/

/-- The generic point of an integral closed subspace is the generic point of that subspace
read as an integral algebraic space over `S`. -/
theorem genericPoint_eq_genericPoint_integralClosedSubspace
    (Z : IntegralClosedSubspace B S hS X) :
    genericPoint B S hS Z.isClosedSubspace.1 Z.isIntegralSpace = Z.genericPoint B S hS :=
  rfl

/-- The morphism to `X` from the spectrum of the residue field of an integral closed subspace
at its generic point is a monomorphism. -/
theorem mono_residueFieldMorphism_comp_ι (Z : IntegralClosedSubspace B S hS X) :
    Mono (residueFieldMorphism B S hS Z.subspace.toFunctor Z.isIntegralSpace.2.1
      (Z.genericPoint B S hS) ≫ Z.subspace.ι) :=
  have := (residueFieldRepresentative B S hS Z.subspace.toFunctor Z.isIntegralSpace.2.1
    (Z.genericPoint B S hS)).2.2
  mono_comp _ _

/-- **Stacks 0EMX** at the generic point of an integral closed subspace. The inclusion of an
integral closed subspace `Z ⊆ X` induces a bijection from the residue field of `X` at the
image of the generic point of `Z` onto the residue field of `Z` at that generic point. -/
theorem bijective_residueFieldHom_ι_genericPoint (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : IntegralClosedSubspace B S hS X) :
    Function.Bijective (residueFieldHom B S hS Z.subspace.toFunctor X hX
      Z.isIntegralSpace.2.1 hdec Z.subspace.ι (Z.genericPoint B S hS)) := by
  have : IsIso (CommRingCat.ofHom (residueFieldHom B S hS Z.subspace.toFunctor X hX
      Z.isIntegralSpace.2.1 hdec Z.subspace.ι (Z.genericPoint B S hS))) :=
    (isIso_residueFieldHom_iff_mono B S hS Z.subspace.toFunctor X hX
      Z.isIntegralSpace.2.1 hdec Z.subspace.ι (Z.genericPoint B S hS)).2
      (mono_residueFieldMorphism_comp_ι B S hS Z)
  simpa using ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (residueFieldHom B S hS Z.subspace.toFunctor X hX
      Z.isIntegralSpace.2.1 hdec Z.subspace.ι (Z.genericPoint B S hS)))

/-- The residue field of `X` at the image of the generic point of an integral closed subspace
`Z ⊆ X` is the function field of `Z`: the inclusion identifies it with the residue field of
`Z` at its generic point, which is the function field of `Z` by Stacks 0END. -/
noncomputable def residueFieldGenericPointRingEquiv (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : IntegralClosedSubspace B S hS X) :
    residueField B S hS X hdec
        (pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι (Z.genericPoint B S hS)) ≃+*
      rationalFunctions B S hS Z.isClosedSubspace.1 :=
  (RingEquiv.ofBijective _ (bijective_residueFieldHom_ι_genericPoint B S hS hX hdec Z)).trans
    (rationalFunctionsRingEquiv B S hS Z.isClosedSubspace.1 Z.isIntegralSpace).symm

/-- The residue field of a decent algebraic space `X` over `S` at a point `ξ` is the function
field of the integral closed subspace whose generic point is `ξ`. -/
noncomputable def residueFieldRingEquivRationalFunctions (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (ξ : points B S hS X) :
    residueField B S hS X hdec ξ ≃+*
      rationalFunctions B S hS
        (integralClosedSubspaceOfPoint B S hS hX hdec ξ).isClosedSubspace.1 :=
  (residueFieldCongr B S hS hdec
      (pointsMap_genericPoint_integralClosedSubspaceOfPoint B S hS hX hdec ξ).symm).trans
    (residueFieldGenericPointRingEquiv B S hS hX hdec
      (integralClosedSubspaceOfPoint B S hS hX hdec ξ))

end General

section Situation

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- In the situation of Stacks 0EDT let `X/B` be good and let `X` be integral. Then the
function field `R(X)` of `X` is defined: the ring of rational functions of
`X` is a field. -/
@[stacks 0ENX "the function field R(X) of a good integral algebraic space is defined: its \
  ring of rational functions is a field"]
theorem BaseSpaceDimensionSituation.isField_functionField (f : X ⟶ D.space)
    (hf : D.IsGood f) (hInt : IsIntegralSpace D.site D.base D.base_mem X) :
    IsField (rationalFunctions D.site D.base D.base_mem hf.1) :=
  isField_rationalFunctions D.site D.base D.base_mem hf.1 hInt

/-- In the situation of Stacks 0EDT let `X/B` be good and let `X` be integral. Then the
function field `R(X)` of `X` is the residue field of `X` at its generic point. -/
@[stacks 0ENX "the function field R(X) of a good integral algebraic space is the residue \
  field at its generic point"]
noncomputable def BaseSpaceDimensionSituation.functionFieldRingEquiv (f : X ⟶ D.space)
    (hf : D.IsGood f) (hInt : IsIntegralSpace D.site D.base D.base_mem X) :
    rationalFunctions D.site D.base D.base_mem hf.1 ≃+*
      residueField D.site D.base D.base_mem X hInt.2.1
        (genericPoint D.site D.base D.base_mem hf.1 hInt) :=
  rationalFunctionsRingEquiv D.site D.base D.base_mem hf.1 hInt

/-- In the situation of Stacks 0EDT let `X/B` be good. For a point `ξ` of `X` the residue field
`κ(ξ)` is the function field of the unique integral closed subspace `Z ⊆ X` whose generic point
is `ξ`. -/
@[stacks 0ENX "for any point x of a good algebraic space, the residue field κ(x) is the \
  function field of the unique integral closed subspace whose generic point is x"]
noncomputable def BaseSpaceDimensionSituation.residueFieldRingEquivFunctionField
    (f : X ⟶ D.space) (hf : D.IsGood f) (ξ : points D.site D.base D.base_mem X) :
    residueField D.site D.base D.base_mem X (D.isDecentSpace_of_isGood f hf) ξ ≃+*
      rationalFunctions D.site D.base D.base_mem
        (integralClosedSubspaceOfPoint D.site D.base D.base_mem hf.1
          (D.isDecentSpace_of_isGood f hf) ξ).isClosedSubspace.1 :=
  residueFieldRingEquivRationalFunctions D.site D.base D.base_mem hf.1
    (D.isDecentSpace_of_isGood f hf) ξ

end Situation

end AlgebraicGeometry.Space

end
