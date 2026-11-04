module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageQuasiSeparatedTower
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageTargetReduction

/-!
# Stacks 076Z

Let `M` be a rule assigning to every category fibred in groupoids over `S` a property of the
modules on its étale site (`AlgebraicGeometry.Stack.StackEtaleModuleRule`). **Stacks 076Z** says:
if

1. `M` cuts out a weak Serre subcategory of the modules on the étale site of every algebraic
   stack,
2. `M` is preserved by inverse image along every smooth 1-morphism of algebraic stacks,
3. membership in `M` is local for every jointly surjective family of smooth 1-morphisms, and
4. the higher direct images along every 1-morphism between algebraic stacks representable by
   affine schemes carry `M` into `M`,

then the higher direct images along every quasi-compact quasi-separated 1-morphism of algebraic
stacks carry `M` into `M`, in every degree. This file proves it, as
`AlgebraicGeometry.Stack.smoothLocalHigherDirectImageCriterion_unconditional`.

## The proof

This is the source's proof, assembled from two pieces.

* The reduction to a target representable by an affine scheme, by hypothesis (3) along a smooth
  cover of the target by affine schemes and base change of higher direct images (**Stacks 075H**):
  `AlgebraicGeometry.Stack.StackEtaleModuleRule.preservedBy_of_affineTarget`.
* Over the stack of an affine scheme, the source is improved along smooth charts by affine
  schemes, by the Čech spectral sequence of **Stacks 072G** together with hypotheses (1) and (2),
  until the terms of the Čech nerves are representable by affine schemes and (4) applies:
  `AlgebraicGeometry.Stack.StackEtaleModuleRule.preservedBy_of_isQuasiCompact_of_isQuasiSeparated`,
  resting on `AlgebraicGeometry.Stack.StackEtaleModuleRule.preservedBy_of_hasAffineDiagonal_charts`
  and `AlgebraicGeometry.Stack.StackEtaleModuleRule.preservedBy_of_hasAffineDiagonal`.

## The universe of the families in hypothesis (3)

`AlgebraicGeometry.Stack.SmoothLocalHigherDirectImageCriterion.{u, t, s'}` asks hypothesis (3)
only of families indexed by a type in the universe `s'`. The theorem here is that statement at
`s' = max u s`, for every universe `s`. This is no weaker than the source's lemma: the source's
hypothesis (3) is asked of every jointly surjective family of smooth 1-morphisms, whatever its
index set, so a rule satisfying the source's hypothesis (3) satisfies in particular its
restriction to families indexed in `Type (max u s)`, and the theorem applies to it with the
source's conclusion. Restricting the hypothesis to fewer families can only strengthen the theorem.
The universe `max u s` contains `u`, which is what the reduction to an affine target uses: it
indexes the smooth cover of the target by affine schemes of the site, a family indexed by a type
in `Type u`.

## References

* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u t s

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `M` be a rule on the modules on the étale sites of the algebraic stacks over `S` such that
(1) it cuts out a weak Serre subcategory on every algebraic stack, (2) it is preserved by inverse
image along every smooth 1-morphism, (3) membership in it is local for every jointly surjective
family of smooth 1-morphisms indexed in `Type (max u s)`, and (4) the higher direct images along
every 1-morphism between algebraic stacks representable by affine schemes carry it into itself.
Then the higher direct images along every quasi-compact quasi-separated 1-morphism of algebraic
stacks carry `M` into `M`, in every degree.

Hypothesis (3) is the source's, read for the families indexed in `Type (max u s)`: the source asks
it of every jointly surjective family whatever its index set, so its hypothesis implies this one
and this statement implies the source's (see the module documentation). -/
@[stacks 076Z "the whole statement: every rule satisfying the source's four hypotheses, every \
  quasi-compact quasi-separated 1-morphism of algebraic stacks and every degree; hypothesis (3) is \
  read for the families indexed in a universe containing u, which the source's hypothesis \
  implies, so the statement is no weaker than the source's"]
theorem smoothLocalHigherDirectImageCriterion_unconditional :
    SmoothLocalHigherDirectImageCriterion.{u, t, max u s} B S hS :=
  fun M hserre hpull hloc haff _ _ f hqc hqs i =>
    StackEtaleModuleRule.preservedBy_of_affineTarget.{u, t, s} B S hS M hserre hpull hloc
      (fun hX f' hqc' hqs' j =>
        StackEtaleModuleRule.preservedBy_of_isQuasiCompact_of_isQuasiSeparated B S hS M hserre
          hpull haff hX f' hqc' hqs' j) f hqc hqs i

end AlgebraicGeometry.Stack

end
