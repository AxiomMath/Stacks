module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CycleOfClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Decency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.IntegralClosedSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence

/-!
# Irreducible components of a closed subspace of a good algebraic space

In the situation of Stacks 0EDT let `X/B` be good and let `Y ⊂ X` be a closed subspace.
Stacks 0EE8 observes that there are one-to-one correspondences between

1. the irreducible components `T` of `|Y|`,
2. the generic points of irreducible components of `|Y|`, and
3. the integral closed subspaces `Z ⊂ Y` such that `|Z|` is an irreducible component of `|Y|`,

and calls `Z` as in (3) an irreducible component of `Y` and the generic point of `|Z|` its
generic point. The two notions are `AlgebraicGeometry.Space.IsIrreducibleComponent` and
`AlgebraicGeometry.Space.IsGenericPointOf`; this module proves the correspondences.

## Main results

* `AlgebraicGeometry.Space.bijective_closure_genericPoint_irreducibleComponents`: taking the
  closure of a point is a bijection from (2) onto (1).
* `AlgebraicGeometry.Space.bijective_range_irreducibleComponent`: taking the set of points is a
  bijection from (3) onto (1).
* `AlgebraicGeometry.Space.existsUnique_isGenericPointOf_of_isIrreducibleComponent` and
  `AlgebraicGeometry.Space.existsUnique_isIrreducibleComponent_isGenericPointOf`: the
  correspondence between (3) and (2), given by the generic point.

## Implementation notes

A good algebraic space is decent, and a closed subspace of a decent algebraic space is decent,
so `|Y|` is sober (Stacks 0EDU, through Stacks 03K3 and 03K6); this gives the correspondence
between (1) and (2). The correspondence between (1) and (3) is the restriction of the bijection
of Stacks 0ENF between integral closed subspaces of `Y` and irreducible closed subsets of `|Y|`
to those subsets which are irreducible components, as in Stacks 0EDV.

## References

* [Stacks Project, Tag 0EE8](https://stacks.math.columbia.edu/tag/0EE8)
* [Stacks Project, Tag 0EDU](https://stacks.math.columbia.edu/tag/0EDU)
* [Stacks Project, Tag 0EDV](https://stacks.math.columbia.edu/tag/0EDV)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (f : X ⟶ D.space)
    {Y : Subfunctor X}

/-- A closed subspace of a good algebraic space over the base of Situation 0EDT is decent. -/
theorem isDecentSpace_of_isClosedSubspace_of_isGood (hf : D.IsGood f)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) :
    IsDecentSpace D.site D.base D.base_mem Y.toFunctor :=
  isDecentSpace_of_isClosedSubspace D.site D.base D.base_mem (D.isDecentSpace_of_isGood f hf) hY

/-- **Stacks 0EE8, (2) to (1).** For a closed subspace `Y` of a good algebraic space, taking the
closure of a point is a bijection from the generic points of irreducible components of `|Y|`
onto the irreducible components of `|Y|`. -/
@[stacks 0EE8 "(1) and (2) correspond, by the closure of a point"]
theorem bijective_closure_genericPoint_irreducibleComponents (hf : D.IsGood f)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) :
    Function.Bijective
      (fun ξ : {ξ : points D.site D.base D.base_mem Y.toFunctor //
          closure {ξ} ∈ irreducibleComponents (points D.site D.base D.base_mem Y.toFunctor)} =>
        (⟨closure {ξ.1}, ξ.2⟩ :
          irreducibleComponents (points D.site D.base D.base_mem Y.toFunctor))) := by
  have hdec := isDecentSpace_of_isClosedSubspace_of_isGood D f hf hY
  have : T0Space (points D.site D.base D.base_mem Y.toFunctor) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hY.1 hdec
  have : QuasiSober (points D.site D.base D.base_mem Y.toFunctor) :=
    quasiSober_points_of_isDecentSpace D.site D.base D.base_mem hY.1 hdec
  refine ⟨fun ξ η h => Subtype.ext ?_, fun T => ?_⟩
  · exact (inseparable_iff_closure_eq.2 (congrArg Subtype.val h)).eq
  · obtain ⟨ξ, hξ⟩ := QuasiSober.sober (T.2.1)
      (isClosed_of_mem_irreducibleComponents _ T.2)
    exact ⟨⟨ξ, hξ.def ▸ T.2⟩, Subtype.ext hξ.def⟩

/-- The integral closed subspace of `Y` underlying an irreducible component of `Y`. -/
def IsIrreducibleComponent.toIntegralClosedSubspace
    {hY : IsAlgebraicSpace D.site D.base D.base_mem Y.toFunctor} {Z : Subfunctor Y.toFunctor}
    (hZ : IsIrreducibleComponent D.site D.base D.base_mem hY Z) :
    IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor :=
  ⟨Z, hZ.1, hZ.2.1⟩

/-- An integral closed subspace whose set of points is an irreducible component is an
irreducible component. -/
theorem isIrreducibleComponent_of_mem_irreducibleComponents
    {hY : IsAlgebraicSpace D.site D.base D.base_mem Y.toFunctor}
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor)
    (hW : Set.range (pointsMap D.site D.base D.base_mem W.subspace.toFunctor W.subspace.ι) ∈
      irreducibleComponents (points D.site D.base D.base_mem Y.toFunctor)) :
    IsIrreducibleComponent D.site D.base D.base_mem hY W.subspace :=
  ⟨W.isClosedSubspace, W.isIntegralSpace, hW⟩

/-- An irreducible component of a closed subspace `Y` of a good algebraic space is determined by
its set of points, and every irreducible component of `|Y|` is the set of points of one. -/
theorem existsUnique_isIrreducibleComponent_range_eq (hf : D.IsGood f)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    {T : Set (points D.site D.base D.base_mem Y.toFunctor)}
    (hT : T ∈ irreducibleComponents (points D.site D.base D.base_mem Y.toFunctor)) :
    ∃! Z : Subfunctor Y.toFunctor, IsIrreducibleComponent D.site D.base D.base_mem hY.1 Z ∧
      Set.range (pointsMap D.site D.base D.base_mem Z.toFunctor Z.ι) = T := by
  have hdec := isDecentSpace_of_isClosedSubspace_of_isGood D f hf hY
  obtain ⟨W, hW⟩ := surjective_integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 hdec
    ⟨T, hT.1, isClosed_of_mem_irreducibleComponents _ hT⟩
  have hWT := congrArg IrreducibleCloseds.carrier hW
  change Set.range (pointsMap D.site D.base D.base_mem W.subspace.toFunctor W.subspace.ι) = T
    at hWT
  refine ⟨W.subspace, ⟨isIrreducibleComponent_of_mem_irreducibleComponents D W (hWT ▸ hT), hWT⟩,
    fun Z hZ => ?_⟩
  have h := injective_integralClosedSubspaceSupport D.site D.base D.base_mem hY.1
    (a₁ := hZ.1.toIntegralClosedSubspace D) (a₂ := W)
    (IrreducibleCloseds.ext (hZ.2.trans hWT.symm))
  exact congrArg IntegralClosedSubspace.subspace h

/-- **Stacks 0EE8, (3) to (1).** For a closed subspace `Y` of a good algebraic space, taking the
set of points is a bijection from the irreducible components of `Y` (integral closed subspaces
`Z ⊂ Y` with `|Z|` an irreducible component of `|Y|`) onto the irreducible components of
`|Y|`. -/
@[stacks 0EE8 "(3) and (1) correspond, by the set of points"]
theorem bijective_range_irreducibleComponent (hf : D.IsGood f)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) :
    Function.Bijective
      (fun Z : {Z : Subfunctor Y.toFunctor //
          IsIrreducibleComponent D.site D.base D.base_mem hY.1 Z} =>
        (⟨Set.range (pointsMap D.site D.base D.base_mem Z.1.toFunctor Z.1.ι), Z.2.2.2⟩ :
          irreducibleComponents (points D.site D.base D.base_mem Y.toFunctor))) := by
  refine ⟨fun Z₁ Z₂ h => Subtype.ext ?_, fun T => ?_⟩
  · obtain ⟨W, -, hW⟩ := existsUnique_isIrreducibleComponent_range_eq D f hf hY Z₂.2.2.2
    exact (hW Z₁.1 ⟨Z₁.2, congrArg Subtype.val h⟩).trans (hW Z₂.1 ⟨Z₂.2, rfl⟩).symm
  · obtain ⟨Z, ⟨hZ, hZT⟩, -⟩ := existsUnique_isIrreducibleComponent_range_eq D f hf hY T.2
    exact ⟨⟨Z, hZ⟩, Subtype.ext hZT⟩

/-- **Stacks 0EE8, (3) to (2).** An irreducible component of a closed subspace `Y` of a good
algebraic space has exactly one generic point. -/
@[stacks 0EE8 "(3) and (2) correspond: an irreducible component has a unique generic point"]
theorem existsUnique_isGenericPointOf_of_isIrreducibleComponent (hf : D.IsGood f)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y) {Z : Subfunctor Y.toFunctor}
    (hZ : IsIrreducibleComponent D.site D.base D.base_mem hY.1 Z) :
    ∃! ξ : points D.site D.base D.base_mem Y.toFunctor,
      IsGenericPointOf D.site D.base D.base_mem hY.1 Z ξ := by
  have hdec := isDecentSpace_of_isClosedSubspace_of_isGood D f hf hY
  have : T0Space (points D.site D.base D.base_mem Y.toFunctor) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hY.1 hdec
  have : QuasiSober (points D.site D.base D.base_mem Y.toFunctor) :=
    quasiSober_points_of_isDecentSpace D.site D.base D.base_mem hY.1 hdec
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (hZ.2.2.1)
    (isClosed_of_mem_irreducibleComponents _ hZ.2.2)
  exact ⟨ξ, hξ, fun η hη => hη.eq hξ⟩

/-- **Stacks 0EE8, (2) to (3).** A generic point of an irreducible component of `|Y|`, for `Y` a
closed subspace of a good algebraic space, is the generic point of exactly one irreducible
component of `Y`. -/
@[stacks 0EE8 "(2) and (3) correspond: a generic point belongs to a unique irreducible component"]
theorem existsUnique_isIrreducibleComponent_isGenericPointOf (hf : D.IsGood f)
    (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    {ξ : points D.site D.base D.base_mem Y.toFunctor}
    (hξ : closure {ξ} ∈ irreducibleComponents (points D.site D.base D.base_mem Y.toFunctor)) :
    ∃! Z : Subfunctor Y.toFunctor, IsIrreducibleComponent D.site D.base D.base_mem hY.1 Z ∧
      IsGenericPointOf D.site D.base D.base_mem hY.1 Z ξ := by
  obtain ⟨Z, ⟨hZ, hZT⟩, hu⟩ := existsUnique_isIrreducibleComponent_range_eq D f hf hY hξ
  exact ⟨Z, ⟨hZ, isGenericPoint_def.2 hZT.symm⟩,
    fun W hW => hu W ⟨hW.1, (isGenericPoint_def.1 hW.2).symm⟩⟩

end AlgebraicGeometry.Space

end
