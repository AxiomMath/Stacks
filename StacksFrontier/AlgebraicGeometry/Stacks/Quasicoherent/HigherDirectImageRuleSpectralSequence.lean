module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageRuleSpectralSequenceAbutment
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmoothLocalHigherDirectImageCriterionProof

/-!
# The smooth-local criterion for higher direct images

**Stacks 076Z** is the criterion
`AlgebraicGeometry.Stack.SmoothLocalHigherDirectImageCriterion`: if a rule `M` assigning to an
algebraic stack a subcategory of `Mod(𝒳_étale, 𝒪_𝒳)` cuts out a weak Serre subcategory
everywhere (hypothesis (1)), is stable under inverse image along a smooth 1-morphism
(hypothesis (2)), is local for a jointly surjective family of smooth 1-morphisms
(hypothesis (3)) and is preserved by the higher direct images between stacks representable by
affine schemes (hypothesis (4)), then it is preserved by the higher direct images along every
quasi-compact (**Stacks 050U**) quasi-separated (**Stacks 04YW**) 1-morphism of algebraic stacks,
in every degree.

## Main results

* `AlgebraicGeometry.Stack.smoothLocalHigherDirectImageCriterion`: **Stacks 076Z**, another name
  for `AlgebraicGeometry.Stack.smoothLocalHigherDirectImageCriterion_unconditional`.

The file also keeps three other names:
`AlgebraicGeometry.Stack.StackEtaleModuleRule.objectPropertyAt`,
`AlgebraicGeometry.Stack.StackEtaleModuleRule.HasCechSpectralSequenceInRule` and
`AlgebraicGeometry.Stack.preservesHigherDirectImages_of_hasCechSpectralSequenceInRule`, for
`AlgebraicGeometry.Stack.StackEtaleModuleRule.toObjectProperty`,
`AlgebraicGeometry.Stack.StackEtaleModuleRule.HasCechSpectralSequenceWithPageInRule` and
`AlgebraicGeometry.Stack.preservesHigherDirectImages_of_hasCechSpectralSequenceWithPageInRule`:
the rule at an algebraic stack as a property of objects, the outcome of the geometric half of the
source's proof (a spectral sequence abutting to the higher direct images with a page in the
rule), and the homological half (part (4) of **Stacks 0132**: the abutment is then in the rule).

## Implementation notes

The proof of `AlgebraicGeometry.Stack.smoothLocalHigherDirectImageCriterion_unconditional` does
not go through `HasCechSpectralSequenceWithPageInRule`. It first reduces to a target
representable by an affine scheme, by hypothesis (3) and base change of higher direct images
(**Stacks 075H**), and then applies part (4) of **Stacks 0132** at every step of the improvement
of the source along smooth charts, to the spectral sequence of **Stacks 072G** of that step
(`AlgebraicGeometry.Stack.StackEtaleModuleRule.mem_higherDirectImage_of_cechPages`), rather than
once to a single spectral sequence for the given 1-morphism. It asks hypothesis (3) of the
families indexed in a universe containing `u`, which the source's hypothesis (3) implies, so the
statement is no weaker than the source's.

## References

* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u t s

namespace AlgebraicGeometry.Stack

namespace StackEtaleModuleRule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A rule at an algebraic stack, as a property of objects.** Another name for
`AlgebraicGeometry.Stack.StackEtaleModuleRule.toObjectProperty`: the rule `M` evaluated on the
sheaves of modules on `𝒴_étale`, which is the ambient category `Mod(𝒴_étale, 𝒪_𝒴)` of
**Stacks 076Z**. -/
abbrev objectPropertyAt (M : StackEtaleModuleRule B S hS) (𝒴 : AlgebraicStacks.{u, t} B S hS) :
    ObjectProperty (SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B))) :=
  toObjectProperty.{u, t} B S hS M 𝒴

/-- **The geometric half of the proof of Stacks 076Z.** Another name for
`AlgebraicGeometry.Stack.StackEtaleModuleRule.HasCechSpectralSequenceWithPageInRule`: along every
quasi-compact quasi-separated 1-morphism `f` of algebraic stacks and at every member `ℱ` of the
rule, a spectral sequence abutting to the higher direct images `Rⁿf_*ℱ` one of whose pages lies
in the rule. -/
noncomputable abbrev HasCechSpectralSequenceInRule (M : StackEtaleModuleRule B S hS) : Prop :=
  HasCechSpectralSequenceWithPageInRule.{u, t} B S hS M

end StackEtaleModuleRule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The homological half of the proof of Stacks 076Z.** Another name for
`AlgebraicGeometry.Stack.preservesHigherDirectImages_of_hasCechSpectralSequenceWithPageInRule`:
a rule which cuts out a weak Serre subcategory at every algebraic stack and admits the spectral
sequence of the geometric half is preserved by the higher direct images along every quasi-compact
quasi-separated 1-morphism, in every degree. -/
alias preservesHigherDirectImages_of_hasCechSpectralSequenceInRule :=
  preservesHigherDirectImages_of_hasCechSpectralSequenceWithPageInRule

/-- **Stacks 076Z.** Let `M` be a rule assigning to a category fibred in groupoids over `S` a
predicate on the modules on its étale site. If `M` cuts out a weak Serre subcategory everywhere,
is stable under inverse image along a smooth 1-morphism, is local for every jointly surjective
family of smooth 1-morphisms indexed in `Type (max u s)`, and is preserved by the higher direct
images between algebraic stacks representable by affine schemes, then the higher direct images
carry the rule into the rule along every quasi-compact (**Stacks 050U**) quasi-separated
(**Stacks 04YW**) 1-morphism of algebraic stacks, in every degree.

This is `AlgebraicGeometry.Stack.smoothLocalHigherDirectImageCriterion_unconditional`.
Hypothesis (3) is the source's, read for the families indexed in `Type (max u s)`: the source asks
it of every jointly surjective family whatever its index set, so its hypothesis implies this one
and this statement implies the source's. -/
@[stacks 076Z "the whole statement: every rule satisfying the source's four hypotheses, every \
  quasi-compact quasi-separated 1-morphism of algebraic stacks and every degree; hypothesis (3) is \
  read for the families indexed in a universe containing u, which the source's hypothesis \
  implies, so the statement is no weaker than the source's"]
alias smoothLocalHigherDirectImageCriterion := smoothLocalHigherDirectImageCriterion_unconditional

end AlgebraicGeometry.Stack

end
