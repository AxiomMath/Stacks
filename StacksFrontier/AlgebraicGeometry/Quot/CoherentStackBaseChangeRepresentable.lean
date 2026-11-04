module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCanonical
public import StacksFrontier.AlgebraicGeometry.Quot.BaseBasedCategoryElements
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.ULiftHom
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory
public import StacksFrontier.AlgebraicGeometry.Quot.TestSchemeTotalSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRepresentability
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpace
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaBaseChange
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability

/-!
# The base-change 1-morphism of `Coh_{X/Y}` is a base change of `𝒮_{Y'} ⟶ 𝒮_Y`

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces over `S`, the standing data
of Stacks 08KB, and let `g : Y' ⟶ Y` be a morphism of algebraic spaces. Stacks 08LP exhibits
`Coh_{X'/Y'}`, `X' = X ×_Y Y'`, as the 2-fibre product of the projection `Coh_{X/Y} ⟶ 𝒮_Y` with
`𝒮_{Y'} ⟶ 𝒮_Y`. This file reads that square in the 2-category of categories fibred in groupoids
and transports along it representability by algebraic spaces (Stacks 0302) and the relative
properties of Stacks 03YK (Stacks 045C) from `𝒮_{Y'} ⟶ 𝒮_Y` to `Coh_{X'/Y'} ⟶ Coh_{X/Y}`.

## Main definitions

* `AlgebraicGeometry.Space.baseCatFiberedInGroupoids`: `𝒮_Y` as a category fibred in groupoids.
* `AlgebraicGeometry.Space.baseCatMap`: the 1-morphism `𝒮_{Y'} ⟶ 𝒮_Y` attached to `g`.
* `AlgebraicGeometry.Space.CoherentSituation.catBaseChangeSquare`: the square of Stacks 08LP in
  the 2-category of categories fibred in groupoids.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.catBaseChangeSquare_isTwoFibreProduct`: Stacks 08LP
  in that 2-category.
* `AlgebraicGeometry.Space.CoherentSituation.isRepresentableByAlgebraicSpaces_baseChangeMap`
  and `AlgebraicGeometry.Space.CoherentSituation.hasRelativeProperty_baseChangeMap`.

## References

* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `𝒮_Y` as a category fibred in groupoids over the big fppf site of `S`, at the morphism universe
of `Coh_{X/Y}`. -/
def baseCatFiberedInGroupoids (Y : AlgebraicSpaces B S hS) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (baseBasedCategory Y) (baseBasedCategory_isFiberedInGroupoids Y)

/-- The 1-morphism `𝒮_{Y'} ⟶ 𝒮_Y` of categories fibred in groupoids attached to `g : Y' ⟶ Y`. -/
def baseCatMap {Y' Y : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    baseCatFiberedInGroupoids Y' ⟶ baseCatFiberedInGroupoids Y :=
  Bicategory.InducedBicategory.mkHom (baseBasedMap g)

/-! ### `𝒮_Y` is represented by `Y` -/

/-- **The comparison of `𝒮_Y` with the category of elements of `Y`**: a test scheme `(T, h)` over
`Y` goes to the section of `Y` over `T` that `h` is. -/
def baseElementsEquivalence (Y : AlgebraicSpaces B S hS) :
    BaseObjects Y ≌ (Stack.fibredCategory B S hS Y.1).val.obj :=
  (ULiftHom.equiv.symm.trans (schemesOverEquivYoneda Y)).trans
    (PresheafOfCategories.costructuredArrowToElements Y.1).asEquivalence

/-- The functor of `AlgebraicGeometry.Space.baseElementsEquivalence`. -/
abbrev baseToElementsFunctor (Y : AlgebraicSpaces B S hS) :
    BaseObjects Y ⥤ (Stack.fibredCategory B S hS Y.1).val.obj :=
  (baseElementsEquivalence Y).functor

/-- The functor `baseToElementsFunctor Y` is an equivalence of categories. -/
instance (Y : AlgebraicSpaces B S hS) : (baseToElementsFunctor Y).IsEquivalence :=
  (baseElementsEquivalence Y).isEquivalence_functor

/-- The functor `baseToElementsFunctor Y` is full. -/
instance (Y : AlgebraicSpaces B S hS) : (baseToElementsFunctor Y).Full :=
  (baseElementsEquivalence Y).full_functor

/-- The functor `baseToElementsFunctor Y` is faithful. -/
instance (Y : AlgebraicSpaces B S hS) : (baseToElementsFunctor Y).Faithful :=
  (baseElementsEquivalence Y).faithful_functor

/-- The comparison as a 1-morphism over the site. -/
def baseToElementsBased (Y : AlgebraicSpaces B S hS) :
    (baseCatFiberedInGroupoids Y).val ⥤ᵇ (Stack.fibredCategory B S hS Y.1).val where
  toFunctor := baseToElementsFunctor Y
  w := rfl

/-- **`𝒮_Y` is equivalent over the site to the category of elements of `Y`.** -/
def baseEquivalenceOver (Y : AlgebraicSpaces B S hS) :
    StacksRepresentableCFG.EquivalenceOver (baseCatFiberedInGroupoids Y).val.p
      (presheafOfCategories (Y.1 ⋙ typeToCat)).p :=
  haveI : (show (baseCatFiberedInGroupoids Y).val.obj ⥤ (presheafOfCategories (Y.1 ⋙ typeToCat)).obj
    from baseToElementsFunctor Y).Full := (baseElementsEquivalence Y).full_functor
  haveI : (show (baseCatFiberedInGroupoids Y).val.obj ⥤ (presheafOfCategories (Y.1 ⋙ typeToCat)).obj
    from baseToElementsFunctor Y).Faithful := (baseElementsEquivalence Y).faithful_functor
  StacksRepresentableCFG.EquivalenceOver.ofIsEquivalenceOver
    (nonempty_isEquivalenceOver_of_forall_verticalObjPreimage
      (baseCatFiberedInGroupoids Y).val.p (presheafOfCategories (Y.1 ⋙ typeToCat)).p
      (baseToElementsFunctor Y) rfl (fun y => ⟨ULiftHom.objUp.{u + 1, u + 1}
        (CostructuredArrow.mk (ObjectProperty.homMk (yonedaEquiv.symm y.fiber.as) :
          (schemeSpaceFunctor B S hS).obj y.base ⟶ Y)), rfl,
        PresheafOfCategories.elementsIsoOfBaseIso (Iso.refl y.base) (by
          change _ = Y.1.map (𝟙 y.base).op (yonedaEquiv (yonedaEquiv.symm y.fiber.as))
          rw [Equiv.apply_symm_apply]
          simp),
        rfl⟩)).some

/-- **`𝒮_Y` is representable by the algebraic space `Y`.** -/
theorem isRepresentableByAlgebraicSpace_baseCat (Y : AlgebraicSpaces B S hS) :
    Stack.IsRepresentableByAlgebraicSpace B S hS (baseCatFiberedInGroupoids Y) :=
  ⟨Y.1, Y.2, ⟨baseEquivalenceOver Y⟩⟩

/-- **Stacks 02ZZ for `𝒮_{Y'} ⟶ 𝒮_Y`**: it is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_baseBasedMap {Y' Y : AlgebraicSpaces B S hS}
    (g : Y' ⟶ Y) : Stack.IsRepresentableByAlgebraicSpaces B S hS (baseBasedMap g) :=
  Stack.isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS (baseCatMap g)
    (isRepresentableByAlgebraicSpace_baseCat Y') (isRepresentableByAlgebraicSpace_baseCat Y)

/-- The square comparing `𝒮_{Y'} ⟶ 𝒮_Y` with the 1-morphism of categories of elements attached
to `g` commutes. -/
def baseToElementsSquare {Y' Y : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) :
    BasedFunctor.comp (baseToElementsBased Y') (Stack.associatedMap B S hS g.hom).1.hom ≅
      BasedFunctor.comp (baseCatMap g).hom (baseToElementsBased Y) :=
  BasedNatIso.mkNatIso (Iso.refl _)
    (fun _ => IsHomLift.id rfl)

/-- The underlying functor of `baseToElementsBased Y` is an equivalence. -/
private instance (Y : AlgebraicSpaces B S hS) : (baseToElementsBased Y).toFunctor.IsEquivalence :=
  inferInstanceAs (baseToElementsFunctor Y).IsEquivalence

/-- **Relative properties of `𝒮_{Y'} ⟶ 𝒮_Y` are those of `g`.** -/
theorem hasRelativeProperty_baseCatMap_iff {Y' Y : AlgebraicSpaces B S hS} (g : Y' ⟶ Y)
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)] :
    Stack.HasRelativeProperty B S hS P (baseCatMap g)
        (isRepresentableByAlgebraicSpaces_baseBasedMap g) ↔ P g := by
  have ha : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (Stack.associatedMap B S hS g.hom).1.hom :=
    (Stack.isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS g.hom).1
      (Space.isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace B S hS Y'.2 Y.2 g.hom)
  refine (Stack.hasRelativeProperty_iff_of_equivalences B S hS P (baseCatMap g)
    (Stack.associatedMap B S hS g.hom).1 (baseToElementsBased Y') (baseToElementsBased Y)
    (baseToElementsSquare g) ha).symm.trans ?_
  refine (Stack.hasRelativeProperty_iff_prop_representingMap B S hS P _ ha Y'.1 Y.1 Y'.2 Y.2
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)).trans ?_
  rw [Stack.representingMap_associatedMap]
  exact Iff.rfl

namespace CoherentSituation

variable (D : CoherentSituation B S hS) {Y' : AlgebraicSpaces B S hS}

/-- The projection `Coh_{X/Y} ⟶ 𝒮_Y` of Stacks 08LP as a 1-morphism of categories fibred in
groupoids. -/
def toBaseCat : D.coherentCFG ⟶ baseCatFiberedInGroupoids D.Y :=
  Bicategory.InducedBicategory.mkHom (coherentToBase D.categoryData)

/-- **The square of Stacks 08LP in the 2-category of categories fibred in groupoids.** -/
def catBaseChangeSquare (g : Y' ⟶ D.Y) :
    Bicategory.TwoCommSq D.toBaseCat (baseCatMap g) where
  pt := (D.baseChange g).coherentCFG
  fst := Bicategory.InducedBicategory.mkHom (D.canonicalBaseChangeSquare g).fst
  snd := Bicategory.InducedBicategory.mkHom (D.canonicalBaseChangeSquare g).snd
  iso := Bicategory.InducedBicategory.isoMk (D.canonicalBaseChangeSquare g).iso

/-- **Stacks 08LP in the 2-category of categories fibred in groupoids.** -/
def catBaseChangeSquare_isTwoFibreProduct (g : Y' ⟶ D.Y) :
    Bicategory.IsTwoFibreProduct (D.catBaseChangeSquare g) :=
  Bicategory.isTwoFibreProduct_of_underlying (D.canonicalBaseChangeSquare_isTwoFibreProduct g)

/-- **Stacks 0302 for the base-change 1-morphism of `Coh_{X/Y}`.** If `𝒮_{Y'} ⟶ 𝒮_Y` is
representable by algebraic spaces, then so is `Coh_{X'/Y'} ⟶ Coh_{X/Y}`. -/
theorem isRepresentableByAlgebraicSpaces_baseChangeMap (g : Y' ⟶ D.Y)
    (hg : Stack.IsRepresentableByAlgebraicSpaces B S hS (baseBasedMap g)) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS (D.catBaseChangeSquare g).fst.hom :=
  Stack.isRepresentableByAlgebraicSpaces_baseChange.{u, u + 1, u} B S hS
    (baseCatFiberedInGroupoids Y') (baseCatFiberedInGroupoids D.Y) D.coherentCFG
    (baseCatMap g) D.toBaseCat (D.catBaseChangeSquare g)
    (D.catBaseChangeSquare_isTwoFibreProduct g) hg

/-- **Stacks 045C for the base-change 1-morphism of `Coh_{X/Y}`.** -/
theorem hasRelativeProperty_baseChangeMap (g : Y' ⟶ D.Y)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (hg : Stack.IsRepresentableByAlgebraicSpaces B S hS (baseBasedMap g))
    (hPg : Stack.HasRelativeProperty B S hS P (baseCatMap g) hg) :
    Stack.HasRelativeProperty B S hS P (D.catBaseChangeSquare g).fst
      (D.isRepresentableByAlgebraicSpaces_baseChangeMap g hg) :=
  Stack.hasRelativeProperty_baseChange.{u, u + 1, u} B S hS P
    (baseCatFiberedInGroupoids Y') (baseCatFiberedInGroupoids D.Y) D.coherentCFG
    (baseCatMap g) D.toBaseCat (D.catBaseChangeSquare g)
    (D.catBaseChangeSquare_isTwoFibreProduct g) hg hPg

end CoherentSituation

end AlgebraicGeometry.Space

end
