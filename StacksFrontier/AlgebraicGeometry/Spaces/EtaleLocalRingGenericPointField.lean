module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricLength
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedLocalRings
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk

/-!
# The étale local ring of a reduced space at a codimension-zero point is a field

Let `X` be a reduced algebraic space over a scheme `S` contained in a big fppf site `B` and let
`x̄` be a geometric point of `X` whose image has a local ring of dimension zero — for a decent
`X` that is exactly a generic point of an irreducible component of `|X|`, by Stacks 0ABV.  Then
the étale local ring `𝒪_{X, x̄}` of Stacks 04KG is a field.

This is the étale-local-ring form of the familiar statement that the local ring of a reduced
scheme at a maximal point is a field, and it is what makes the multiplicity of an integral
closed subspace *in itself* equal to one: the length of `𝒪_{X, x̄}` over itself is one when that
ring is a field.  The source uses it inside the proof of Stacks 0EPB, part (2), where the module
`M = (ℱ|_V)_v` is read at the generic point of an integral closed subspace, and in the proofs of
Stacks 0EE4 and 0EE9.

Two inputs feed the ring-theoretic step, that a reduced local ring of Krull dimension zero is a
field:

* Krull dimension: by Stacks 04N9, `AlgebraicGeometry.Space.localRingDimension_eq_tfae` — in
  the form `AlgebraicGeometry.Space.ringKrullDim_etaleLocalRing_eq_localRingDimension` — the
  Krull dimension of `𝒪_{X, x̄}` is the dimension of the local ring of `X` at the image of `x̄`,
  which is zero at a generic point of a component by
  `AlgebraicGeometry.Space.localRingDimension_eq_zero_of_mem_genericPoints` (Stacks 0ABV,
  (1) implies (4)).
* Reducedness: by Stacks 0BGS,
  `AlgebraicGeometry.Space.isReduced_iff_forall_localRing_isReduced`, a reduced algebraic space
  has reduced local rings, and by Stacks 0E01,
  `AlgebraicGeometry.Space.isReduced_etaleLocalRing_iff_hasLocalRingPropertyAtPoint`, that is
  reducedness of `𝒪_{X, x̄}`.

## Main results

* `AlgebraicGeometry.Space.isField_etaleLocalRing_of_localRingDimension_eq_zero`: the étale
  local ring of a reduced algebraic space at a geometric point over a point of codimension zero
  is a field.
* `AlgebraicGeometry.Space.isField_etaleLocalRing_of_mem_genericPoints`: the same at a geometric
  point over a generic point of an irreducible component of a reduced decent space.
* `AlgebraicGeometry.Space.isField_etaleLocalRing_of_mem_genericPoints_of_isIntegralSpace`:
  **the same on an integral algebraic space**, where reducedness and decency are part of
  Stacks 0AD4 and so need not be assumed.
* `AlgebraicGeometry.Space.geometricLength_structureSheafModule_eq_one_of_isField` and
  `AlgebraicGeometry.Space.geometricLength_structureSheafModule_eq_one_of_isIntegralSpace`:
  **the structure sheaf has length one there**, so the multiplicity of an integral algebraic
  space in itself, in the sense of Stacks 0EE9, is one.

## Implementation notes

No tag attribute is claimed.  The statement is not a clause of any tag of the source: it is the
conjunction of Stacks 04N9, Stacks 0ABV, Stacks 0BGS and Stacks 0E01 with the commutative-algebra
fact `Ring.KrullDimLE.isField_of_isReduced`, each of which carries its attribute where it is
proved, and it is used as a step in the proofs of Stacks 0EE4, 0EE9 and 0EPB.

Local Noetherianity is not needed, and neither is any finiteness: a reduced local ring of Krull
dimension zero is a field outright.

## References

* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
* [Stacks Project, Tag 04N9](https://stacks.math.columbia.edu/tag/04N9)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 0BGS](https://stacks.math.columbia.edu/tag/0BGS)
* [Stacks Project, Tag 0E01](https://stacks.math.columbia.edu/tag/0E01)
* [Stacks Project, Tag 0EE4](https://stacks.math.columbia.edu/tag/0EE4)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The étale local ring of a reduced algebraic space at a codimension-zero point is a
field.**  Let `X` be a reduced algebraic space over `S` and let `x̄` be a geometric point whose
image has a local ring of dimension zero.  Then `𝒪_{X, x̄}` is a field.

By Stacks 04N9 the Krull dimension of `𝒪_{X, x̄}` is the dimension of the local ring at the
image of `x̄`, hence zero; by Stacks 0BGS and Stacks 0E01 the ring `𝒪_{X, x̄}` is reduced; and a
reduced local ring of Krull dimension zero is a field. -/
theorem isField_etaleLocalRing_of_localRingDimension_eq_zero
    (hX : IsAlgebraicSpace B S hS X)
    (hred : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsReduced Y))
    (xbar : GeometricPoint B S hS X)
    (hdim : localRingDimension B S hS xbar.image = 0) :
    IsField (etaleLocalRing B S hS X xbar) := by
  have := isLocalRing_etaleLocalRing B S hS X hX xbar
  have : _root_.IsReduced (etaleLocalRing B S hS X xbar) :=
    (isReduced_etaleLocalRing_iff_hasLocalRingPropertyAtPoint hX xbar).mpr
      ((isReduced_iff_forall_localRing_isReduced B S hS X hX).mp hred xbar.image)
  have : Ring.KrullDimLE 0 (etaleLocalRing B S hS X xbar) := Ring.krullDimLE_iff.mpr <| by
    rw [ringKrullDim_etaleLocalRing_eq_localRingDimension hX xbar, hdim]
    simp
  exact Ring.KrullDimLE.isField_of_isReduced

/-- **The étale local ring of a reduced decent algebraic space at a generic point of an
irreducible component is a field.**  By Stacks 0ABV, (1) implies (4), the local ring of a decent
space at a generic point of an irreducible component of `|X|` has dimension zero, so this is
`AlgebraicGeometry.Space.isField_etaleLocalRing_of_localRingDimension_eq_zero`. -/
theorem isField_etaleLocalRing_of_mem_genericPoints
    (hX : IsAlgebraicSpace B S hS X)
    (hred : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsReduced Y))
    (hdec : IsDecentSpace B S hS X)
    (xbar : GeometricPoint B S hS X)
    (hgen : xbar.image ∈ genericPoints (points B S hS X)) :
    IsField (etaleLocalRing B S hS X xbar) :=
  isField_etaleLocalRing_of_localRingDimension_eq_zero B S hS hX hred xbar
    (localRingDimension_eq_zero_of_mem_genericPoints B S hS hX hdec hgen)

/-- **The étale local ring of an integral algebraic space at a geometric point over a generic
point is a field.**  An integral algebraic space is reduced and decent by Stacks 0AD4, so the
two hypotheses of
`AlgebraicGeometry.Space.isField_etaleLocalRing_of_mem_genericPoints` come for free. -/
theorem isField_etaleLocalRing_of_mem_genericPoints_of_isIntegralSpace
    (hX : IsAlgebraicSpace B S hS X) (hint : IsIntegralSpace B S hS X)
    (xbar : GeometricPoint B S hS X)
    (hgen : xbar.image ∈ genericPoints (points B S hS X)) :
    IsField (etaleLocalRing B S hS X xbar) :=
  isField_etaleLocalRing_of_mem_genericPoints B S hS hX hint.1 hint.2.1 xbar hgen

/-! ### The length of the structure sheaf at such a point -/

section Length

variable (Z : AlgebraicSpaces B S hS)

/-- **The structure sheaf has length one at a geometric point whose étale local ring is a
field.**  By `AlgebraicGeometry.Space.structureSheafGeometricStalkEquiv` the stalk of `𝒪_Z` at
`z̄` is `𝒪_{Z, z̄}` as a module over itself; a field is a simple module over itself, so that
length is one. -/
theorem geometricLength_structureSheafModule_eq_one_of_isField
    (z : GeometricPoint B S hS Z.1) (hfield : IsField (etaleLocalRing B S hS Z.1 z)) :
    geometricLength B S hS Z z (structureSheafModule B S hS Z) = 1 := by
  have hself : IsSimpleModule (etaleLocalRing B S hS Z.1 z) (etaleLocalRing B S hS Z.1 z) :=
    isSimpleModule_self_iff_isUnit.mpr ⟨⟨hfield.exists_pair_ne⟩, fun a ha =>
      (hfield.mul_inv_cancel ha).elim fun b hb => IsUnit.of_mul_eq_one b hb⟩
  have hstalk : IsSimpleModule (etaleLocalRing B S hS Z.1 z)
      (geometricModuleStalk B S hS Z z (structureSheafModule B S hS Z)) :=
    IsSimpleModule.congr (structureSheafGeometricStalkEquiv B S hS Z z)
  exact Module.length_eq_one _ _

/-- **The multiplicity of an integral algebraic space in itself is one.**  The structure sheaf
of an integral algebraic space has length one at every geometric point over a generic point of
its point space.

This is the normalisation that makes the coefficient of an integral closed subspace in its own
cycle equal to one, in the sense of Stacks 0EE9, and it is used at the generic point of the
integral closed subspaces appearing in Stacks 0EPB. -/
theorem geometricLength_structureSheafModule_eq_one_of_isIntegralSpace
    (hint : IsIntegralSpace B S hS Z.1) (z : GeometricPoint B S hS Z.1)
    (hgen : z.image ∈ genericPoints (points B S hS Z.1)) :
    geometricLength B S hS Z z (structureSheafModule B S hS Z) = 1 :=
  geometricLength_structureSheafModule_eq_one_of_isField B S hS Z z
    (isField_etaleLocalRing_of_mem_genericPoints_of_isIntegralSpace B S hS Z.2 hint z hgen)

end Length

end AlgebraicGeometry.Space

end
