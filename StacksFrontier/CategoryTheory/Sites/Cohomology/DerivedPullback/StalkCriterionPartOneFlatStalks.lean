module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkCriterionPartOne
public import StacksFrontier.CategoryTheory.Sites.Point.FlatModuleStalk
import StacksCore.Tactic.StacksAttribute

/-!
# Discharging the flatness obligation of part (1) of Stacks 0DEN

`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkCriterionPartOne` proves part (1)
of Stacks 0DEN from two `Prop`-valued obligations,
`Stacks.Sheaves.KFlatStalkCriterion.StalkFlatOfSumExtensionByZero` (the stalk of a direct sum of
extensions by zero `j_{U!}O_U` is a flat module over the stalk ring) and
`Stacks.Sheaves.KFlatStalkCriterion.StalkKFlatOfAcyclic` (part (1) for a complex that is K-flat
*and* acyclic).

This file **discharges the first of those two unconditionally**, by composing

* `Stacks.SheafOfModules.KFlatResolution.isFlat_of_isSumOfExtensionByZeroStructureSheaves` — a
  direct sum of extensions by zero is a flat *sheaf* of modules (Stacks 03EX/03EU), with
* `Stacks.isFlatModuleStalk_of_isFlat` — **Stacks 05VB**, the stalk of a flat sheaf of modules is
  a flat module over the stalk ring.

So the weaker obligation tailored to `j_{U!}O_U` is not needed: it follows from 05VB at full
generality.

## Main results

* `Stacks.Sheaves.KFlatStalkCriterion.isFlatModuleStalk_of_isFlat_univ`: Stacks 05VB at this
  file's universes and in the `AlgebraicGeometry.SheafOfModules.IsFlat` spelling, so a consumer
  needs no bridging.
* `Stacks.Sheaves.KFlatStalkCriterion.stalkFlatOfSumExtensionByZero`: the first obligation,
  proved.
* `Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat_of_stalkKFlatOfAcyclic`: **part (1) of
  Stacks 0DEN**, with `Stacks.Sheaves.KFlatStalkCriterion.StalkKFlatOfAcyclic` as its *only*
  hypothesis beyond those of Stacks 0DEN.

## Implementation notes

**No tag is placed in this file.**  `Stacks.Sheaves.KFlatStalkCriterion.StalkKFlatOfAcyclic` is a
`Prop`-valued `def` with no inhabitant in this development, so the remaining result is strictly
weaker than part (1) of Stacks 0DEN.  Part (2) is
`Stacks.SheafOfModules.SitePointStalkSheafify.kFlat_of_stalks`.

**Universes.** Everything is at a single universe `u` with `Category.{u} C`, the narrowing
`Stacks.SheafOfModules.KFlatResolution`, `Stacks.Sheaves.KFlatStalkCriterion` and
`Stacks.SheafOfModules.SitePointStalkSheafify` already carry down the chain from
`Stacks.SheafOfModules.Tensor.ringSheaf`.  `Stacks.isFlatModuleStalk_of_isFlat` is stated at
independent `Category.{v} C` with module universe `max v w`, and is used here at `v = w = u`.

## References

* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
* [Stacks Project, Tag 05VB](https://stacks.math.columbia.edu/tag/05VB)
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

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Stacks 05VB in the exact shape a consumer of part (1) asks for it**, at the single
universe `u` and in the `AlgebraicGeometry.SheafOfModules.IsFlat` spelling that
`Stacks.SheafOfModules.KFlatResolution` and `Stacks.SheafOfModules.FlatTensorShortExact` produce:
the stalk of a flat sheaf of `O`-modules is a flat module over the stalk ring.  This is
`Stacks.isFlatModuleStalk_of_isFlat` with the universes instantiated and the two `IsFlat`
spellings identified, so that no bridging is needed at a call site. -/
theorem isFlatModuleStalk_of_isFlat_univ (Φ : J.Point.{u}) :
    ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := O) F →
        letI := Stacks.hasSheafCompose_forget₂_commRingCat.{u, u, u} J
        Stacks.IsFlatModuleStalk Φ O F :=
  let := Stacks.hasSheafCompose_forget₂_commRingCat.{u, u, u} J
  fun F hF ↦ Stacks.isFlatModuleStalk_of_isFlat F hF Φ

/-- **The first obligation of `kFlatStalk_of_kFlat`, discharged.**  The stalk of a direct sum of
extensions by zero of the structure sheaves of slices is a flat module over the stalk ring: such
a sum is a flat sheaf of modules (Stacks 03EX and 03EU, as packaged by Stacks 06YS) and the stalk
of a flat sheaf of modules is flat (Stacks 05VB). -/
theorem stalkFlatOfSumExtensionByZero (Φ : J.Point.{u}) :
    StalkFlatOfSumExtensionByZero O Φ := fun M hM ↦
  isFlatModuleStalk_of_isFlat_univ O Φ M
    (Stacks.SheafOfModules.KFlatResolution.isFlat_of_isSumOfExtensionByZeroStructureSheaves O M hM)

section Tensor

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).Additive]
  [∀ X, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} O).obj X).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor O) (ComplexShape.up ℤ)]

/-- **Part (1) of Stacks 0DEN, granted only its acyclic case.**  This is
`Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat` with the flatness obligation discharged by
`stalkFlatOfSumExtensionByZero`, so `StalkKFlatOfAcyclic` is the whole of what part (1) still
needs. -/
theorem kFlatStalk_of_kFlat_of_stalkKFlatOfAcyclic {Φ : J.Point.{u}}
    (hacyc : StalkKFlatOfAcyclic O Φ)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat O K) :
    CochainComplex.KFlat.{u, u} (stalkComplex O Φ K) :=
  kFlatStalk_of_kFlat O (stalkFlatOfSumExtensionByZero O Φ) hacyc K hK

end Tensor

end Stacks.Sheaves.KFlatStalkCriterion

end

end
