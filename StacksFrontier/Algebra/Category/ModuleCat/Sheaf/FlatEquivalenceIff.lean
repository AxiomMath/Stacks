module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalenceConverse
public import StacksCore.Tactic.StacksAttribute

/-!
# The equational criterion for flatness: the equivalence

Let `(C, O)` be a ringed site and let `F` be a sheaf of `O`-modules. Stacks 08FC asserts the
equivalence of three conditions: (1) `F` is flat, (2) every single relation among finitely many
sections of `F` locally factors through a finite free module annihilating that relation, and (3)
the same for a finite matrix of relations.

The three implications are proved elsewhere:
`Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_of_isFlat_freeUniverse`
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalence`) for (1) `⟹` (2),
`Stacks.SheafOfModules.isFlat_of_hasLocalSingleRelationFactorizations_freeUniverse`
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalenceConverse`) for (2) `⟹` (1), and
`Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_iff_finite`
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelations`) for (2) `⟺` (3). This file does
nothing but pair the first two into the single biconditional, which is the shape in which the
criterion is applied.

## Main results

* `Stacks.SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations_freeUniverse`: parts
  (1) and (2) of Stacks 08FC are equivalent.
* `Stacks.SheafOfModules.isFlat_iff_hasLocalFiniteRelationFactorizations`: the same for parts (1)
  and (3), obtained by composing with the equivalence of (2) and (3).

## Implementation notes

No `@[stacks 08FC]` attribute is placed here. The covering-set rule allows several declarations
to share a tag only when they state different things, and the two biconditionals of this file are
exactly the conjunctions of statements already carrying the tag: the two implications of part
(1) `⟺` (2) are tagged where they are proved, and part (2) `⟺` (3) is tagged in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRelations`. Tagging the pairing as well would
make the tag's coverage look larger than it is. The `max v w` pairing in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCriterionConverse` does carry
`@[stacks 08FC "parts (1) and (2)"]`, because at those universes neither implication is tagged
separately, so there the pairing is the only carrier of that content.

The section universe is an independent `w`, as it is in both halves; see the implementation notes
of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalence` for how the (1) `⟹` (2)
direction avoids constraining it to the morphism universe of the site. This is what makes the two
halves composable at all: pairing them while (1) `⟹` (2) was stated at `max v w` produced
`stuck at solving universe constraint w =?= max v ?u`. The same failure is why the `max v w`
pairing cannot simply be reused here: applied at a free `w` it reports
`stuck at solving universe constraint max v ?u =?= w`.

The hypotheses are exactly those under which `Stacks.SheafOfModules.IsFlat` is stated, namely
`J.HasSheafCompose (forget₂ CommRingCat RingCat)`, `HasWeakSheafify J AddCommGrpCat` and
`J.WEqualsLocallyBijective AddCommGrpCat`.

## References

* [Stacks Project, Lemma 18.28.14 (Tag 08FC)](https://stacks.math.columbia.edu/tag/08FC)
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w})

/-- **Stacks 08FC, parts (1) and (2).** A sheaf of modules on a ringed site is flat exactly when
every relation `∑ᵢ aᵢ • sᵢ = 0` among finitely many of its sections over an object `U` admits, on
a covering sieve of `U`, a factorisation of the restricted sections through a finite free module
by a matrix annihilating the restricted relation.

This is the universe-general form of
`Stacks.SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCriterionConverse`, which states the same
equivalence for a structure sheaf `O : Sheaf J CommRingCat.{max v w}` on a site with morphisms
in `Type v`. It exists because the source states 08FC over a ringed site with three independent
universes, and that statement cannot be obtained from the `max v w` form: pairing the two halves
there leaves the universe constraint `max v w' =?= w`, which has no solution. Both halves are
therefore taken in their free-universe form,
`Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_of_isFlat_freeUniverse` and
`Stacks.SheafOfModules.isFlat_of_hasLocalSingleRelationFactorizations_freeUniverse`. -/
@[sga "4 V 8.2.11" "(a), special case"]
theorem isFlat_iff_hasLocalSingleRelationFactorizations_freeUniverse
    (F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O)) :
    IsFlat F ↔ HasLocalSingleRelationFactorizations O F :=
  ⟨hasLocalSingleRelationFactorizations_of_isFlat_freeUniverse,
    isFlat_of_hasLocalSingleRelationFactorizations_freeUniverse O F⟩

/-- **Stacks 08FC, parts (1) and (3).** The same criterion for a finite matrix of relations at
once, obtained from
`Stacks.SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations_freeUniverse` and
the equivalence of parts (2) and (3), and so likewise at an independent section universe. -/
theorem isFlat_iff_hasLocalFiniteRelationFactorizations
    (F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O)) :
    IsFlat F ↔ HasLocalFiniteRelationFactorizations O F :=
  (isFlat_iff_hasLocalSingleRelationFactorizations_freeUniverse O F).trans
    (hasLocalSingleRelationFactorizations_iff_finite O F)

end Stacks.SheafOfModules
