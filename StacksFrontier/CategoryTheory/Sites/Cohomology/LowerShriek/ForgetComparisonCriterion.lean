module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedForgetComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ExtensionByZeroLowerShriekModules

/-!
# The canonical maps at the generators appearing in the criterion of Stacks 07AE

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `g : Sh(C) ⟶ Sh(D)` be the
corresponding morphism of topoi, let `O_D` be a sheaf of rings on `D` and set `O_C = g^{-1}O_D`,
as in Stacks 07AC. The warning of Stacks 07AE records three things about the square

```
D(Mod(O_C)) --Lg_!--> D(Mod(O_D))
    |                     |
  forget                forget
    v                     v
  D(Ab(C)) --Lg_!^{Ab}--> D(Ab(D))
```

that it does not commute; that `Lg_!` agrees with `Lg_!^{Ab}` *if and only if* the canonical maps
`Lg_!^{Ab} j_{U!}O_U ⟶ j_{u(U)!}O_{u(U)}` are isomorphisms in `D(D)` for every object `U` of
`C`; and that in general all one has is a natural transformation
`Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!`.

That transformation is `Stacks.Cohomology.DerivedLowerShriek.derivedForgetComparison`. This file
builds the canonical maps the criterion is about. They are not a new construction: the map at `U`
is the component of the comparison at `j_{U!}O_U` placed in degree zero, read into
`j_{u(U)!}O_{u(U)}` through the identification `Lg_!(j_{U!}O_U) = g_! j_{U!}O_U =
j_{u(U)!}O_{u(U)}` which is the displayed chain of Stacks 07AC. So `isIso_...` of the canonical
map and of that component are the same condition, which is
`isIso_derivedForgetComparisonGenerator_iff`, and the forward half of the criterion —
if the square commutes then every canonical map is invertible — is
`isIso_derivedForgetComparisonGenerator`.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriekSingleComparison`: the counit of `Lg_!`
  at `j_{U!}O_U` in degree zero, as a map `Lg_!(j_{U!}O_U) ⟶ g_! j_{U!}O_U` of `D(O_D)`.
* `Stacks.Cohomology.DerivedLowerShriek.derivedForgetComparisonGenerator`: the canonical map
  `Lg_!^{Ab} j_{U!}O_U ⟶ j_{u(U)!}O_{u(U)}` of the criterion.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.isIso_derivedForgetComparisonGenerator_iff`: the
  canonical map at `U` is invertible exactly when the comparison of Stacks 07AE is invertible at
  `j_{U!}O_U` in degree zero.
* `Stacks.Cohomology.DerivedLowerShriek.isIso_derivedForgetComparisonGenerator`: the forward
  implication of the criterion.

## Implementation notes

`derivedLowerShriekSingleComparison` is stated as a *map* and for an arbitrary sheaf of rings,
with the universes of the two sites and of the module sections mutually free. It is invertible
exactly under the acyclicity statement of Stacks 0794, where it becomes the first isomorphism of
the displayed chain of Stacks 07AC; that is
`Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriekSingleExtensionByZeroUnitIso`, which is
available on a small site with a commutative structure sheaf. Here it is carried as a hypothesis,
named `hU`, rather than discharged: it is an input to the warning from Stacks 07AC, not part of
it, and keeping it a hypothesis is what lets this file stay at the hypotheses of Stacks 07AC
rather than at those of the library's form of Stacks 07AC.

The converse implication of the criterion, and the discharge of `hU`, are given by
`Stacks.Cohomology.DerivedLowerShriek.isIso_derivedForgetComparison_iff`, on a small site with a
commutative structure sheaf, where `Lg_!^{Ab}` and its derived adjunction are available.

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
  [UnivLE.{v₁, w}] [UnivLE.{v₂, w}] [UnivLE.{u₁, w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify K AddCommGrpCat.{w}]
  [(_root_.SheafOfModules.pushforward.{w} (F := f) (idRingMap J K f O)).IsRightAdjoint]
  [(f.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsRightAdjoint]
  [∀ U : C, (_root_.SheafOfModules.pushforward.{w} (F := Over.forget U)
    (𝟙 ((inverseImageRing J K f O).over U))).IsRightAdjoint]
  [∀ W : D, (_root_.SheafOfModules.pushforward.{w} (F := Over.forget W)
    (𝟙 (O.over W))).IsRightAdjoint]

section Derived

attribute [local instance] HasDerivedCategory.standard

variable [(lowerShriekOnHomotopy J K f O ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
  (sourceQuasiIso J K f O)]

omit [f.IsCocontinuous J K] in
/-- **The counit of `Lg_!` at the generator `j_{U!} O_U` in degree zero**, as a map
`Lg_!(j_{U!} O_U) ⟶ g_! j_{U!} O_U` in `D(O_D)`. The identification of the derived and the
homotopy-category incarnations of the degreewise functor is the two applications of
`DerivedCategory.quotientCompQhIso`, and the passage of `single` through `g_!` is
`HomologicalComplex.singleMapHomologicalComplex`; the map itself is the counit
`derivedLowerShriekComparison`.

This is the first map of the displayed chain `Lg_!(j_{U!}O_U) = g_! j_{U!}O_U =
j_{u(U)!}O_{u(U)}` of Stacks 07AC. It is invertible under the acyclicity statement of Stacks
0794, `j_{U!}O_U` in degree zero being a bounded above complex of direct sums of the
`j_{V!}O_V`; on a small site with a commutative structure sheaf that is
`derivedLowerShriekSingleExtensionByZeroUnitIso`. -/
def derivedLowerShriekSingleComparison (U : C) :
    (derivedLowerShriek J K f O).obj ((DerivedCategory.singleFunctor _ 0).obj
        (extensionByZeroUnit (inverseImageRing J K f O) U)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        ((lowerShriekModules J K f O).obj (extensionByZeroUnit (inverseImageRing J K f O) U)) :=
  (derivedLowerShriek J K f O).map ((DerivedCategory.quotientCompQhIso _).app _).inv ≫
    (derivedLowerShriekComparison J K f O).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (extensionByZeroUnit (inverseImageRing J K f O) U))) ≫
    ((DerivedCategory.quotientCompQhIso _).app _).hom ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (lowerShriekModules J K f O) (ComplexShape.up ℤ) 0).app _).hom

variable [((lowerShriekAbelian J K f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ))]
  [(derivedLowerShriek J K f O ⋙
      (forgetTargetModules K O).mapDerivedCategory).IsLeftDerivedFunctor
        (derivedLowerShriekForgetCounit J K f O) (sourceQuasiIso J K f O)]

omit [f.IsCocontinuous J K] in
/-- **The canonical map `Lg_!^{Ab} j_{U!} O_U ⟶ j_{u(U)!} O_{u(U)}` of the criterion of Stacks
07AE**, in `D(D)`.

It is the component of the comparison `derivedForgetComparison` at `j_{U!}O_U` placed in degree
zero, followed by the underlying abelian sheaf of the displayed chain of Stacks 07AC:
`derivedLowerShriekSingleComparison` identifies `Lg_!(j_{U!}O_U)` with `g_! j_{U!}O_U`, and
`lowerShriekExtensionByZeroUnitIso` identifies that with `j_{u(U)!}O_{u(U)}`. The criterion of
Stacks 07AE is that `Lg_!` agrees with `Lg_!^{Ab}` exactly when every one of these maps is
invertible. -/
def derivedForgetComparisonGenerator (U : C) :
    (derivedLowerShriekAbelian J K f).obj
        ((forgetSourceModules J K f O).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (extensionByZeroUnit (inverseImageRing J K f O) U))) ⟶
      (forgetTargetModules K O).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj (extensionByZeroUnit O (f.obj U))) :=
  (derivedForgetComparison J K f O).app _ ≫
    (forgetTargetModules K O).mapDerivedCategory.map
      (derivedLowerShriekSingleComparison J K f O U ≫
        (DerivedCategory.singleFunctor _ 0).map
          (((Stacks.SheafOfModules.lowerShriekIsoPullback.{w} J K f O).app _).symm ≪≫
            lowerShriekExtensionByZeroUnitIso J K f O U).hom)

/-- **The canonical map of the criterion of Stacks 07AE is invertible exactly when the comparison
is invertible at the generator.** The two differ by the underlying abelian sheaf of the displayed
chain of Stacks 07AC, whose second map is always invertible and whose first is the hypothesis
`hU`, so the criterion of Stacks 07AE is a condition on the components of
`derivedForgetComparison` at the `j_{U!}O_U` in degree zero. -/
lemma isIso_derivedForgetComparisonGenerator_iff (U : C)
    (hU : IsIso (derivedLowerShriekSingleComparison J K f O U)) :
    IsIso (derivedForgetComparisonGenerator J K f O U) ↔
      IsIso ((derivedForgetComparison J K f O).app
        ((DerivedCategory.singleFunctor _ 0).obj
          (extensionByZeroUnit (inverseImageRing J K f O) U))) := by
  set B := (forgetTargetModules K O).mapDerivedCategory.map
    (derivedLowerShriekSingleComparison J K f O U ≫
      (DerivedCategory.singleFunctor _ 0).map
        (((Stacks.SheafOfModules.lowerShriekIsoPullback.{w} J K f O).app _).symm ≪≫
          lowerShriekExtensionByZeroUnitIso J K f O U).hom) with hB
  have hBiso : IsIso B := by
    rw [hB]
    have : IsIso (derivedLowerShriekSingleComparison J K f O U ≫
        (DerivedCategory.singleFunctor _ 0).map
          (((Stacks.SheafOfModules.lowerShriekIsoPullback.{w} J K f O).app _).symm ≪≫
            lowerShriekExtensionByZeroUnitIso J K f O U).hom) := inferInstance
    infer_instance
  have hfac : derivedForgetComparisonGenerator J K f O U =
      (derivedForgetComparison J K f O).app
        ((DerivedCategory.singleFunctor _ 0).obj
          (extensionByZeroUnit (inverseImageRing J K f O) U)) ≫ B := rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hsplit : (derivedForgetComparison J K f O).app
        ((DerivedCategory.singleFunctor _ 0).obj
          (extensionByZeroUnit (inverseImageRing J K f O) U)) =
        derivedForgetComparisonGenerator J K f O U ≫ inv B := by
      rw [hfac, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [hsplit]
    infer_instance
  · rw [hfac]
    infer_instance

/-- **The forward implication of the criterion of Stacks 07AE.** If the comparison
`Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!` is invertible — which is what it means for the square of the
warning to commute — then every canonical map `Lg_!^{Ab} j_{U!}O_U ⟶ j_{u(U)!}O_{u(U)}` is
invertible in `D(D)`.

The hypothesis `hU` is the first map of the displayed chain of Stacks 07AC being invertible,
which is an input to the warning rather than part of it; see the module docstring. The converse
implication is `isIso_derivedForgetComparison_of_isIso_generator`. -/
theorem isIso_derivedForgetComparisonGenerator
    (h : IsIso (derivedForgetComparison J K f O)) (U : C)
    (hU : IsIso (derivedLowerShriekSingleComparison J K f O U)) :
    IsIso (derivedForgetComparisonGenerator J K f O U) :=
  (isIso_derivedForgetComparisonGenerator_iff J K f O U hU).2 inferInstance

end Derived

end Stacks.Cohomology.DerivedLowerShriek

end
