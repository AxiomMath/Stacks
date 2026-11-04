module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackNecessity
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackSufficiency

/-!
# Stacks 0EX9: stacks in groupoids on the h site, by the generator almost blowup squares

A category fibred in groupoids `p : 𝒮 ⥤ (Sch/S)_h` over the big h site of Stacks 0EU1 is a stack
in groupoids for the h topology if and only if

1. it is a stack in groupoids for the Zariski topology,
2. it has effective descent, with descent of morphisms, along every surjective flat proper morphism
   of finite presentation `X ⟶ Y` of the site with `Y` affine, and
3. for every almost blowup square of the site with affine base of the shape of Example 0EVG or of
   Example 0EVH, the functor `𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}` is an equivalence.

## Main results

* `AlgebraicGeometry.BigHOver.isStackInGroupoids_iff_generatorSquares`: **Stacks 0EX9**, with
  condition (2) in its descent form.

## Implementation notes

**What is corrected.**  Conditions (1) and (3) are the source's.  The source's condition (2) asks
for the comparison functor `𝒮_Y ⟶ 𝒮_X ×_{𝒮_{X ×_Y X}} 𝒮_X` onto the two-fibre product to be an
equivalence, `AlgebraicGeometry.BigHOver.IsAffineFlatProperFinitePresentationStack`.  That is false
for h stacks: it fails for every stack in groupoids for the Zariski topology with a nontrivial
automorphism of an object over an affine object, at the fold map `Y ⊔ Y ⟶ Y`, by the computation in
the module documentation of
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackCriterion`.  It is
replaced by `AlgebraicGeometry.BigHOver.IsAffineFlatProperFinitePresentationDescent`, the same
condition with the two-fibre product replaced by the category of descent data of `{X ⟶ Y}`, which
carries in addition the cocycle condition over `X ×_Y X ×_Y X`; that is the form the source's proof
uses.

The source's standing hypothesis that `p` be fibred in groupoids is dropped: both sides of the
equivalence imply it, a stack in groupoids being fibred in groupoids by definition.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t v u

namespace AlgebraicGeometry

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 : Type t} [Category.{v} 𝒳] (p : 𝒳 ⥤ BigHOver B S hS) [p.IsFibered]

/-- **Stacks 0EX9.** A category fibred over the big h category over `S` is a stack in groupoids
for the h topology if and only if it is a stack in groupoids for the Zariski topology, has
effective descent along every surjective flat proper morphism of finite presentation onto an
affine object of the site, and has `𝒮_X ⟶ 𝒮_Z ×_{𝒮_E} 𝒮_{X'}` an equivalence for every almost
blowup square of the site with affine base of the shape of Example 0EVG or of Example 0EVH.

Condition (2) is in its descent form: the source's literal condition (2), equivalence onto the
two-fibre product, is false for h stacks, as recorded in the module documentation.  Conditions (1)
and (3) are the source's. -/
@[stacks 0EX9 "with condition (2) in its descent form: the source's literal condition (2) is \
false for h stacks, see `AlgebraicGeometry.BigHOver.IsAffineFlatProperFinitePresentationDescent`"]
public theorem isStackInGroupoids_iff_generatorSquares :
    p.IsStackInGroupoids.{u + 1} (BigHOver.topology B S hS) ↔
      IsZariskiStackInGroupoids B S hS p ∧ IsAffineFlatProperFinitePresentationDescent B S hS p ∧
        IsOneGeneratorAlmostBlowUpStack B S hS p ∧ IsTwoGeneratorAlmostBlowUpStack B S hS p :=
  ⟨fun hp ↦ ⟨isZariskiStackInGroupoids_of_isStackInGroupoids B S hS p hp,
      isAffineFlatProperFinitePresentationDescent_of_isStackInGroupoids B S hS p hp,
      isOneGeneratorAlmostBlowUpStack_of_isStackInGroupoids B S hS p hp,
      isTwoGeneratorAlmostBlowUpStack_of_isStackInGroupoids B S hS p hp⟩,
    fun ⟨h1, h2, h3, h4⟩ ↦ isStackInGroupoids_of_generatorSquares h1 h2 h3 h4⟩

end BigHOver

end AlgebraicGeometry

end
