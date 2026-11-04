module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkCriterionPartOneAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkCriterionPartOneFlatStalks
import StacksCore.Tactic.StacksAttribute

/-!
# Part (1) of Stacks 0DEN, reduced to one statement

Part (1) of Stacks 0DEN — a K-flat complex of `O`-modules on a ringed site has K-flat stalk at
every point of the site — was reduced by
`Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat` to two obligations, and both have since
been addressed, in different files and by different routes:

* `Stacks.Sheaves.KFlatStalkCriterion.StalkFlatOfSumExtensionByZero`, flatness of the stalk of a
  direct sum of extensions by zero, is **proved unconditionally** as
  `Stacks.Sheaves.KFlatStalkCriterion.stalkFlatOfSumExtensionByZero`, from Stacks 06YS and
  Stacks 05VB;
* `Stacks.Sheaves.KFlatStalkCriterion.StalkKFlatOfAcyclic`, part (1) for a complex that is K-flat
  *and* acyclic, is proved as `Stacks.Sheaves.KFlatStalkCriterion.stalkKFlatOfAcyclic_of_retract`,
  from the single remaining obligation
  `Stacks.Sheaves.KFlatStalkCriterion.StalkRetractFinitelyPresented`.

This file is the composition, and it exists to make the resulting frontier a machine-checked
statement rather than a claim: **part (1) of Stacks 0DEN holds as soon as every finitely
presented module over the stalk ring is a retract of the stalk of a sheaf of `O`-modules.**

## Main results

* `Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat_of_stalkRetract`: part (1) of Stacks
  0DEN, with `Stacks.Sheaves.KFlatStalkCriterion.StalkRetractFinitelyPresented` as its only
  hypothesis beyond those of Stacks 0DEN.

## Implementation notes

The composition is kept out of both input files on purpose.  Each of them stands on its own
imports and neither depends on the other, so a change to one cannot redden the other; only this
file sees both.

**No tag is placed here.**  `StalkRetractFinitelyPresented` is a `Prop`-valued `def` with no
inhabitant in this development, so the statement below is weaker than part (1) and a `0DEN`
`"part (1)"` tag on it would be a false green.  The one `0DEN` tag site in the tree remains
`Stacks.SheafOfModules.SitePointStalkSheafify.kFlat_of_stalks`, carrying `"part (2)"`.

## References

* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace Stacks.Sheaves.KFlatStalkCriterion

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J CommRingCat.{u})
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).Additive]
  [∀ X, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).obj X).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor O) (ComplexShape.up ℤ)]

/-- **Part (1) of Stacks 0DEN, on one obligation.**  A K-flat complex of `O`-modules on a ringed
site has K-flat stalk at every point of the site, granted that every finitely presented module
over the stalk ring is a retract of the stalk of a sheaf of `O`-modules.

Both of the obligations of `Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat` are discharged
  here: the flatness
one unconditionally, by `stalkFlatOfSumExtensionByZero`, and the acyclic one by
`stalkKFlatOfAcyclic_of_retract`. -/
theorem kFlatStalk_of_kFlat_of_stalkRetract {Φ : J.Point.{u}}
    (hret : StalkRetractFinitelyPresented O Φ)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat O K) :
    CochainComplex.KFlat.{u, u} (stalkComplex O Φ K) :=
  kFlatStalk_of_kFlat_of_stalkKFlatOfAcyclic O (stalkKFlatOfAcyclic_of_retract O hret) K hK

end Stacks.Sheaves.KFlatStalkCriterion

end

end
