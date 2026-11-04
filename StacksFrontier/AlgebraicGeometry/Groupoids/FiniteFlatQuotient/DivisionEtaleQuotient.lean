module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.Fppf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.SubgroupoidDivisionDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.OpenIdentityUnramifiedSource
import all StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient

/-!
# The quotient of a groupoid by an open subgroupoid has étale structure maps

Let `(U, R, s, t, c)` be a groupoid scheme with `s` flat and locally of finite presentation, and
let `(U, P)` be a subgroupoid which can be divided out in the sense of **Stacks 04S4** and whose
arrow scheme is an *open* subscheme of `R`.  Then the source and target maps of the quotient
groupoid `(Ū, R̄, s̄, t̄, c̄)` are étale.

Two things combine.  First, the divided-out subgroupoid is exactly the part of `R` lying over the
identity of `R̄`, so the identity `ē : Ū ⟶ R̄` is an open immersion — that is
`AlgebraicGeometry.GroupoidScheme.Division.isOpenImmersion_descended_identity`.  Second,
flatness and local finite presentation descend from `s` to `s̄` along the finite locally free
surjection `U ⟶ Ū`, because `(U, R)` is the restriction of `(Ū, R̄)` and both properties are
local at source and at target for the fppf precoverage; that is
`AlgebraicGeometry.Bootstrap04S6.property_source_of_fppf_fullyFaithful_groupoid`.  A groupoid
scheme whose identity is an open immersion and whose source is flat and locally of finite
presentation has étale source by
`Stacks.Groupoids.GroupoidScheme.etale_source_of_flat_of_isOpenImmersion_identity`, which uses
**Stacks 047W** at unramifiedness and asks nothing of the arrows beyond the groupoid axioms.

This is the "after the division" half of the proof of **Stacks 06N0**: there `(U, R)` is the
groupoid of a flat, locally finitely presented field-valued presentation of a stack, `P` is the
open and closed piece of `R` through the identity, and `Ū = Spec k₀` is the spectrum of the field
of invariants.

## Main results

* `AlgebraicGeometry.GroupoidScheme.Division.etale_descended_source`: the source map of the
  quotient groupoid is étale.
* `AlgebraicGeometry.GroupoidScheme.Division.etale_descended_target`: so is its target map.

## References

* [Stacks Project, Tag 047W](https://stacks.math.columbia.edu/tag/047W)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Groupoids.GroupoidScheme

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {G H : Stacks.Groupoids.GroupoidScheme S}
  {i : Stacks.Groupoids.GroupoidScheme.Hom H G} {hobj : H.objects = G.objects}

/-- Flatness of the source map of the quotient groupoid: it descends from the source map of the
ambient groupoid along the finite locally free surjection `U ⟶ Ū`. -/
theorem Division.flat_descended_source (D : Division G H i hobj) [Flat G.source.left] :
    Flat D.descended.source.left := by
  let := D.surjective_descend_mapObjects
  let := D.flat_descend_mapObjects
  let := D.locallyOfFinitePresentation_descend_mapObjects
  let : MorphismProperty.IsLocalAtSource (@Flat : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtSource.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  let : MorphismProperty.IsLocalAtTarget (@Flat : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact Bootstrap04S6.property_source_of_fppf_fullyFaithful_groupoid (@Flat) D.descend
    D.descend_fullyFaithful inferInstance

/-- Local finite presentation of the source map of the quotient groupoid: it descends from the
source map of the ambient groupoid along the finite locally free surjection `U ⟶ Ū`. -/
theorem Division.locallyOfFinitePresentation_descended_source (D : Division G H i hobj)
    [LocallyOfFinitePresentation G.source.left] :
    LocallyOfFinitePresentation D.descended.source.left := by
  let := D.surjective_descend_mapObjects
  let := D.flat_descend_mapObjects
  let := D.locallyOfFinitePresentation_descend_mapObjects
  let : MorphismProperty.IsLocalAtTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact Bootstrap04S6.property_source_of_fppf_fullyFaithful_groupoid (@LocallyOfFinitePresentation)
    D.descend D.descend_fullyFaithful inferInstance

/-- **The source map of the quotient groupoid is étale.**  If the subgroupoid divided out has an
open arrow scheme and the source map of the ambient groupoid is flat and locally of finite
presentation, then the source map `s̄` of the groupoid on the quotient `Ū` is étale.

The identity of the quotient groupoid is an open immersion by
`AlgebraicGeometry.GroupoidScheme.Division.isOpenImmersion_descended_identity`, and flatness and
local finite presentation of `s̄` descend from `s`; **Stacks 047W** at unramifiedness then makes
`s̄` unramified, and a flat formally unramified morphism is étale. -/
theorem Division.etale_descended_source (D : Division G H i hobj)
    [IsOpenImmersion i.mapArrows.left] [Flat G.source.left]
    [LocallyOfFinitePresentation G.source.left] : Etale D.descended.source.left := by
  let := D.isOpenImmersion_descended_identity
  let := D.flat_descended_source
  let := D.locallyOfFinitePresentation_descended_source
  let : LocallyOfFiniteType D.descended.source.left := inferInstance
  let := D.descended.isIso_inverse
  let : IsIso D.descended.inverse.left := (Over.forget S).map_isIso D.descended.inverse
  let : LocallyOfFiniteType D.descended.target.left := by
    have h : D.descended.target.left = D.descended.inverse.left ≫ D.descended.source.left :=
      congrArg Over.Hom.left D.descended.source_inverse.symm
    rw [h]
    infer_instance
  exact etale_source_of_flat_of_isOpenImmersion_identity D.descended

/-- **The target map of the quotient groupoid is étale.**  The inverse of the quotient groupoid
carries its target to its source and is an isomorphism. -/
theorem Division.etale_descended_target (D : Division G H i hobj)
    [IsOpenImmersion i.mapArrows.left] [Flat G.source.left]
    [LocallyOfFinitePresentation G.source.left] : Etale D.descended.target.left := by
  let := D.etale_descended_source
  let := D.descended.isIso_inverse
  let : IsIso D.descended.inverse.left := (Over.forget S).map_isIso D.descended.inverse
  have h : D.descended.target.left = D.descended.inverse.left ≫ D.descended.source.left :=
    congrArg Over.Hom.left D.descended.source_inverse.symm
  rw [h]
  infer_instance

end AlgebraicGeometry.GroupoidScheme
