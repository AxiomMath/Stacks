module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBase

/-!
# The two notions of local quasi-finiteness agree for a representable 1-morphism

The library carries two predicates spelled *locally quasi-finite* for a 1-morphism of algebraic
stacks over `S`, and they are not the same notion:

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyQuasiFinite` (**Stacks 06PU**), for an
  arbitrary 1-morphism, is the conjunction of quasi-DM-ness (**Stacks 04YW**), local finite type
  (**Stacks 06FS**, part (1)) and discreteness of the space of points of the fibre over every
  field-valued point of the target;
* `AlgebraicGeometry.Stack.IsLocallyQuasiFinite`, for a 1-morphism representable by algebraic
  spaces, is the relative property of **Stacks 04XB** at
  `AlgebraicGeometry.Space.locallyQuasiFiniteProperty`: every algebraic space representing a base
  change of the 1-morphism along a scheme-valued point of the target has locally quasi-finite
  structural morphism.

This file proves that for a 1-morphism **representable by algebraic spaces** the two agree. The
two notions are therefore interchangeable exactly where the source of Stacks 06ME uses them, and
nothing is lost by stating a conclusion about such a 1-morphism at either one.

## The proof

Both directions are **Stacks 06UA**, the characterisation of the relative notion by local finite
type together with discreteness of the field-valued fibres, which
`StacksFrontier/AlgebraicGeometry/Stacks/LocallyQuasiFiniteRepresentable.lean` carries in both
directions as
`AlgebraicGeometry.Stack.isLocallyQuasiFinite_of_isLocallyOfFiniteType_of_discreteTopology` and
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_and_discreteTopology_of_isLocallyQuasiFinite`. Those
two conditions are precisely the second and third conjuncts of Stacks 06PU, so the whole comparison
reduces to the **first** conjunct, quasi-DM-ness, and that conjunct is automatic for a
representable 1-morphism: a 1-morphism representable by algebraic spaces is Deligne-Mumford by
**Stacks 050E**
(`AlgebraicGeometry.Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces`), and
Deligne-Mumford implies quasi-DM, again by Stacks 050E
(`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDMWithRepresentableDiagonal_of_isDM`).

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source`: a
  1-morphism from the algebraic stack of an algebraic space to an algebraic stack is representable
  by algebraic spaces.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_iff_isLocallyQuasiFinite_hom`: the
  comparison of the two notions for a 1-morphism representable by algebraic spaces.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_iff_of_algebraicSpaceStack_source`:
  the comparison in the shape **Stacks 06ME** and **Stacks 06N2** consume it, for a 1-morphism
  whose source is the algebraic stack of an algebraic space, where the representability hypothesis
  is discharged.

## Implementation notes

The representability of a 1-morphism out of the algebraic stack of an algebraic space is the
implication (1) ⟹ (8) of **Stacks 045G**, available here as
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack`: only the
representable diagonal of the target and the representability of the source by an algebraic space
are used, and the latter is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_fibredCategory`.

No `@[stacks]` attribute is placed on the comparison. It is not a statement of the source: Stacks
06PU is a definition two sections after Stacks 06ME, so the source never compares the two, and the
comparison is an artefact of the library carrying both predicates under one leaf name. The two
`@[stacks 06UA]` declarations it is assembled from already carry that tag.

The implementation note of
`StacksFrontier/AlgebraicGeometry/Stacks/ChartShrinkingQuasiFiniteEtale.lean` records that whether
the conclusion stated there is exactly the source's "turns on the comparison of the two notions
for a representable 1-morphism, which this file neither proves nor cites". That comparison is the
content of this file, and the answer is that they agree; so the Stacks 06PU rendering of the
conclusion of Stacks 06ME is *not* stronger than the relative rendering the source's proof
produces, and the quantification over every field-valued point of the target that the note worried
about is discharged by Stacks 06UA rather than being an extra demand.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06ME](https://stacks.math.columbia.edu/tag/06ME)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 06UA](https://stacks.math.columbia.edu/tag/06UA)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism from the algebraic stack of an algebraic space to an algebraic stack is
representable by algebraic spaces.** This is the implication (1) ⟹ (8) of **Stacks 045G** in the
only case the chapter needs: the target has a diagonal representable by algebraic spaces because
it is an algebraic stack, and the source is representable by an algebraic space. -/
theorem isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
    (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
  isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS 𝒳.property
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU) f.hom

namespace AlgebraicStacks

/-- **For a 1-morphism of algebraic stacks representable by algebraic spaces the notion of local
quasi-finiteness of Stacks 06PU and the relative notion of Stacks 04XB agree.**

The second and third conjuncts of Stacks 06PU — local finite type and discreteness of every
field-valued fibre — are equivalent to the relative notion by **Stacks 06UA**, so only the first
conjunct is at issue, and it holds for every representable 1-morphism: such a 1-morphism is
Deligne-Mumford, hence quasi-DM, both by **Stacks 050E**. -/
theorem isLocallyQuasiFinite_iff_isLocallyQuasiFinite_hom
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    IsLocallyQuasiFinite B S hS f ↔ Stack.IsLocallyQuasiFinite B S hS f.hom := by
  refine ⟨fun h => Stack.isLocallyQuasiFinite_of_isLocallyOfFiniteType_of_discreteTopology
    B S hS f hf h.2.1 h.2.2, fun h => ?_⟩
  obtain ⟨hft, hfib⟩ :=
    Stack.isLocallyOfFiniteType_and_discreteTopology_of_isLocallyQuasiFinite B S hS f hf h
  exact ⟨isQuasiDMWithRepresentableDiagonal_of_isDM B S hS f
    (Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS f hf),
    hft, hfib⟩

/-- **The comparison of the two notions of local quasi-finiteness, in the shape Stacks 06ME and
Stacks 06N2 consume it.** For a 1-morphism `f : U ⟶ 𝒳` whose source is the algebraic stack of an
algebraic space, the representability hypothesis of
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_iff_isLocallyQuasiFinite_hom` is
automatic, by
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source`. -/
theorem isLocallyQuasiFinite_iff_of_algebraicSpaceStack_source
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
    (f : Stack.algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳) :
    IsLocallyQuasiFinite B S hS f ↔ Stack.IsLocallyQuasiFinite B S hS f.hom :=
  isLocallyQuasiFinite_iff_isLocallyQuasiFinite_hom B S hS f
    (Stack.isRepresentableByAlgebraicSpaces_of_algebraicSpaceStack_source B S hS 𝒳 U hU f)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
