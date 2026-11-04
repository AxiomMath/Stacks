module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForget
public import StacksFrontier.CategoryTheory.Sites.AbelianRestrictionExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek does not commute with forgetting the module structure

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, `O_D` a sheaf of rings on `D`
and `O_C = g^{-1} O_D` its restriction, as in Stacks 07AC. There are then two lower-shriek
functors in play: `g_! : Mod(O_C) ⥤ Mod(O_D)` on sheaves of modules, and `g_!^{Ab} : Ab(C) ⥤
Ab(D)` on the underlying abelian sheaves, which is the lower-shriek functor of the same morphism
of sites for the constant sheaf of integers as structure sheaf. Already the undifferentiated
functors need not agree — that is
`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic` — and the canonical comparison between
them is `Stacks.SheafOfModules.lowerShriekForgetComparison`.

This file passes that comparison to the unbounded derived categories: the square

```
D(Mod(O_C)) --Lg_!--> D(Mod(O_D))
    |                     |
  forget                forget
    v                     v
  D(Ab(C)) --Lg_!^{Ab}--> D(Ab(D))
```

does not commute, and all one gets is a canonical natural transformation
`Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!`. It is constructed here, and pinned down uniquely by its
compatibility with the two counits exhibiting the two functors as left derived functors, so that
it is this canonical map and not an arbitrary one.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriekAbelian`: the unbounded left derived
  functor `Lg_!^{Ab}` of lower shriek on abelian sheaves.
* `Stacks.Cohomology.DerivedLowerShriek.forgetComparisonOnHomotopy`: the comparison of Stacks
  0798, read on the unbounded homotopy categories.
* `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriekForgetCounit` and
  `Stacks.Cohomology.DerivedLowerShriek.derivedForgetComparisonCounit`: the two transformations
  out of the composites with the localization functor between which the comparison interpolates.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.existsUnique_derivedForgetComparison`: there is a unique
  natural transformation `forget ⋙ Lg_!^{Ab} ⟶ Lg_! ⋙ forget` compatible with the two counits.
* `Stacks.Cohomology.DerivedLowerShriek.existsUnique_derivedForgetComparison_of_acyclic`: the
  same, with the absoluteness hypothesis discharged from the acyclicity statement of Stacks 0794.

## Implementation notes

The existence of `Lg_!^{Ab}` is carried as an instance hypothesis: it is the existence half of
Stacks 07AC for the constant sheaf of integers, and so is an input to this remark rather than
part of it. Likewise `Lg_!` itself is available only in the presence of the pointwise
derivability hypothesis of the section `Derived` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/DerivedAdjunction.lean`.

## References

* [Stacks Project, Tag 07AE](https://stacks.math.columbia.edu/tag/07AE)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DerivedLowerShriek

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{w})
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify K AddCommGrpCat.{w}]
  [(_root_.SheafOfModules.pushforward.{w} (F := f) (idRingMap J K f O)).IsRightAdjoint]
  [(f.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]

/-- The forgetful functor `forget : Mod(g^{-1} O_D) ⥤ Ab(C)` on the source site. -/
abbrev forgetSourceModules :
    _root_.SheafOfModules.{w} (inverseImageRing J K f O) ⥤ Sheaf J AddCommGrpCat.{w} :=
  _root_.SheafOfModules.toSheaf.{w} (inverseImageRing J K f O)

/-- The forgetful functor `forget : Mod(O_D) ⥤ Ab(D)` on the target site. -/
abbrev forgetTargetModules : _root_.SheafOfModules.{w} O ⥤ Sheaf K AddCommGrpCat.{w} :=
  _root_.SheafOfModules.toSheaf.{w} O

/-- **Stacks 0798**, in the notation of Stacks 07AC: the canonical comparison
`g_!^{Ab} ∘ forget ⟶ forget ∘ g_!` of the undifferentiated lower-shriek functors. -/
abbrev forgetComparison :
    forgetSourceModules J K f O ⋙ lowerShriekAbelian J K f ⟶
      lowerShriekModules J K f O ⋙ forgetTargetModules K O :=
  Stacks.SheafOfModules.lowerShriekForgetComparison f (idRingMap J K f O)

/-- The comparison of Stacks 0798, read on the unbounded homotopy categories. -/
def forgetComparisonOnHomotopy :
    (forgetSourceModules J K f O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (lowerShriekAbelian J K f).mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      lowerShriekOnHomotopy J K f O ⋙
        (forgetTargetModules K O).mapHomotopyCategory (ComplexShape.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (forgetSourceModules J K f O ⋙ lowerShriekAbelian J K f))
      (ComplexShape.up ℤ)).hom ≫
    NatTrans.mapHomotopyCategory (forgetComparison J K f O) (ComplexShape.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (lowerShriekModules J K f O ⋙ forgetTargetModules K O))
      (ComplexShape.up ℤ)).inv

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [((lowerShriekAbelian J K f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ))]

/-- The unbounded left derived functor `Lg_!^{Ab}` of lower shriek on abelian sheaves. -/
abbrev derivedLowerShriekAbelian :
    DerivedCategory (Sheaf J AddCommGrpCat.{w}) ⥤ DerivedCategory (Sheaf K AddCommGrpCat.{w}) :=
  ((lowerShriekAbelian J K f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ))

/-- The counit exhibiting `Lg_!^{Ab}` as the left derived functor of degreewise lower shriek on
abelian sheaves. -/
abbrev derivedLowerShriekAbelianComparison :
    DerivedCategory.Qh ⋙ derivedLowerShriekAbelian J K f ⟶
      (lowerShriekAbelian J K f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  ((lowerShriekAbelian J K f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ))

variable [(lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
  (sourceQuasiIso J K f O)]

/-- The transformation exhibiting `Lg_! ⋙ forget` as a candidate left derived functor of
degreewise lower shriek followed by `forget`: the counit of `Lg_!`, whiskered with `forget`.
That it *is* a left derived functor with this transformation is the absoluteness of `Lg_!`. -/
abbrev derivedLowerShriekForgetCounit :
    DerivedCategory.Qh ⋙
        (derivedLowerShriek J K f O ⋙ (forgetTargetModules K O).mapDerivedCategory) ⟶
      (lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh) ⋙
        (forgetTargetModules K O).mapDerivedCategory :=
  (Functor.associator DerivedCategory.Qh (derivedLowerShriek J K f O)
      (forgetTargetModules K O).mapDerivedCategory).inv ≫
    Functor.whiskerRight (derivedLowerShriekComparison J K f O)
      (forgetTargetModules K O).mapDerivedCategory

/-- The transformation from `Q_h ⋙ (forget ⋙ Lg_!^{Ab})` to degreewise `g_! ⋙ forget` followed
by `Q_h`, assembled from the counit of `Lg_!^{Ab}`, the identifications of the derived and
homotopy-category incarnations of the exact functor `forget`, and the comparison of Stacks 0798
applied degreewise. -/
def derivedForgetComparisonCounit :
    DerivedCategory.Qh ⋙
        ((forgetSourceModules J K f O).mapDerivedCategory ⋙
          derivedLowerShriekAbelian J K f) ⟶
      (lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh) ⋙
        (forgetTargetModules K O).mapDerivedCategory :=
  (Functor.associator DerivedCategory.Qh (forgetSourceModules J K f O).mapDerivedCategory
      (derivedLowerShriekAbelian J K f)).inv ≫
    Functor.whiskerRight (forgetSourceModules J K f O).mapDerivedCategoryFactorsh.hom
      (derivedLowerShriekAbelian J K f) ≫
    (Functor.associator ((forgetSourceModules J K f O).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh (derivedLowerShriekAbelian J K f)).hom ≫
    Functor.whiskerLeft ((forgetSourceModules J K f O).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedLowerShriekAbelianComparison J K f) ≫
    (Functor.associator ((forgetSourceModules J K f O).mapHomotopyCategory (ComplexShape.up ℤ))
      ((lowerShriekAbelian J K f).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).inv ≫
    Functor.whiskerRight (forgetComparisonOnHomotopy J K f O) DerivedCategory.Qh ≫
    (Functor.associator (lowerShriekOnHomotopy J K f O)
      ((forgetTargetModules K O).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh).hom ≫
    Functor.whiskerLeft (lowerShriekOnHomotopy J K f O)
      (forgetTargetModules K O).mapDerivedCategoryFactorsh.inv ≫
    (Functor.associator (lowerShriekOnHomotopy J K f O) DerivedCategory.Qh
      (forgetTargetModules K O).mapDerivedCategory).inv

omit [f.IsCocontinuous J K] in
/-- **Stacks 07AE**, the comparison transformation. Whenever the left derived functor `Lg_!` of
lower shriek on modules is absolute against `forget`, there is exactly one natural transformation
`Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!` compatible with the counits of the two left derived functors
and the comparison of Stacks 0798. -/
theorem existsUnique_derivedForgetComparison
    [(derivedLowerShriek J K f O ⋙
      (forgetTargetModules K O).mapDerivedCategory).IsLeftDerivedFunctor
        (derivedLowerShriekForgetCounit J K f O) (sourceQuasiIso J K f O)] :
    ∃! t : (forgetSourceModules J K f O).mapDerivedCategory ⋙
        derivedLowerShriekAbelian J K f ⟶
      derivedLowerShriek J K f O ⋙ (forgetTargetModules K O).mapDerivedCategory,
      Functor.whiskerLeft DerivedCategory.Qh t ≫ derivedLowerShriekForgetCounit J K f O =
        derivedForgetComparisonCounit J K f O := by
  refine ⟨Functor.leftDerivedLift _ (derivedLowerShriekForgetCounit J K f O)
    (sourceQuasiIso J K f O) _ (derivedForgetComparisonCounit J K f O),
    Functor.leftDerived_fac _ _ _ _ _, fun t ht => ?_⟩
  refine Functor.leftDerived_ext _ (derivedLowerShriekForgetCounit J K f O)
    (sourceQuasiIso J K f O) _ _ _ ?_
  rw [ht, Functor.leftDerived_fac]

omit [f.IsCocontinuous J K] in
/-- **The comparison transformation**, conditional only on the acyclicity statement of Stacks 0794
for lower shriek: there is exactly one natural transformation `Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!`
compatible with the counits of the two left derived functors and the comparison of Stacks 0798. -/
@[stacks 07AE "the comparison transformation `Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!`"]
theorem existsUnique_derivedForgetComparison_of_acyclic [Small.{w} C]
    [∀ U : C, (_root_.SheafOfModules.pushforward.{w} (F := Over.forget U)
      (𝟙 ((inverseImageRing J K f O).over U) :
        (inverseImageRing J K f O).over U ⟶ (inverseImageRing J K f O).over U)).IsRightAdjoint]
    (hFP : ∀ (a : ℤ)
      (Lc : CochainComplex (_root_.SheafOfModules.{w} (inverseImageRing J K f O)) ℤ),
      Lc.IsStrictlyLE a →
      (∀ n, IsSumOfExtensionByZeroUnits (inverseImageRing J K f O) (Lc.X n)) → Lc.Acyclic →
      (((lowerShriekModules J K f O).mapHomologicalComplex (ComplexShape.up ℤ)).obj Lc).Acyclic) :
    ∃! t : (forgetSourceModules J K f O).mapDerivedCategory ⋙
        derivedLowerShriekAbelian J K f ⟶
      derivedLowerShriek J K f O ⋙ (forgetTargetModules K O).mapDerivedCategory,
      Functor.whiskerLeft DerivedCategory.Qh t ≫ derivedLowerShriekForgetCounit J K f O =
        derivedForgetComparisonCounit J K f O :=
  have := isLeftDerivedFunctor_derivedLowerShriek_comp_of_acyclic J K f O hFP
    (forgetTargetModules K O).mapDerivedCategory
  existsUnique_derivedForgetComparison J K f O

end Derived

end Stacks.Cohomology.DerivedLowerShriek

end
