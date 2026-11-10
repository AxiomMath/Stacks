module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable

/-!
# A space representing `Pic_{X/B}` is locally of finite presentation over `B`

Let `f : X ⟶ B` be a morphism of algebraic spaces and `Pic_{X/B}` its relative Picard functor on
the test schemes over `B` (Stacks 0D25). Under the standing assumptions of Section 0DMD, Stacks
0DNI says that `Pic_{X/B} ⟶ B` is quasi-separated and locally of finite presentation. For `f` of
finite presentation, every algebraic space `p : H ⟶ B` representing `Pic_{X/B}` is locally of
finite presentation over `B`.

## Main results

* `PicardSituation.isLocallyOfFinitePresentation_of_represents_picardFunctor`:
  for `f` of finite presentation, an algebraic space over `B` representing `Pic_{X/B}` is locally
  of finite presentation over `B`.

## References

* [Stacks Project, Tag 0DNI](https://stacks.math.columbia.edu/tag/0DNI)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section StageFunctor

variable {Y : AlgebraicSpaces B S hS} (X : BigFppfOver B S hS) (y : Y.1.obj (op X))

/-- The morphism of algebraic spaces `X ⟶ Y` that a section `y` of `Y` over `X` is. -/
private abbrev sectionHom : (schemeSpaceFunctor B S hS).obj X ⟶ Y :=
  ObjectProperty.homMk (yonedaEquiv.symm y)

/-- A scheme over `X` is a test scheme over `Y` through the section `y`. -/
private def overStage : Over X ⥤ SchemesOver Y where
  obj U := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map U.hom ≫ sectionHom X y)
  map {U V} g := CostructuredArrow.homMk g.left (by
    change (schemeSpaceFunctor B S hS).map g.left ≫ (schemeSpaceFunctor B S hS).map V.hom ≫
      sectionHom X y = (schemeSpaceFunctor B S hS).map U.hom ≫ sectionHom X y
    rw [← Category.assoc, ← Functor.map_comp, Over.w g])
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private theorem testPoint_overStage (U : Over X) :
    testPoint ((overStage X y).obj U) = Y.1.map U.hom.op y := by
  change yonedaEquiv (yoneda.map U.hom ≫ yonedaEquiv.symm y) = _
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rfl

variable {H : AlgebraicSpaces B S hS} (p : H ⟶ Y)

/-- The lifts through `p` of the section `y` are the points of `H` over `Y` on the schemes over
`X`, made test schemes over `Y` through `y`. -/
private def sectionFiberIso :
    sectionFiber B S hS p.hom X y ≅ (overStage X y).op ⋙ spacePointsOver p :=
  NatIso.ofComponents
    (fun U => Equiv.toIso (Equiv.subtypeEquivRight (fun x => by
      change _ = _ ↔ _ = testPoint ((overStage X y).obj U.unop)
      rw [testPoint_overStage]
      exact Iff.rfl)))
    (fun _ => by ext; rfl)

end StageFunctor

/-- **A space whose functor of points over `Y` is limit preserving is locally of finite
presentation over `Y`.** Let `p : H ⟶ Y` be a morphism of algebraic spaces whose functor of
points over `Y` is identified (`c`) with a functor `F` on the test schemes over `Y` which is
limit preserving in the sense of Stacks 049J. Then `p` is locally of finite presentation. -/
private theorem isLocallyOfFinitePresentation_of_limitPreserving_spacePointsOver
    {Y H : AlgebraicSpaces B S hS} (p : H ⟶ Y) {F : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)}
    (c : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ F)
    (hF : LimitPreserving.{u, u + 1, u, u}
      (CostructuredArrow.proj (schemeSpaceFunctor B S hS) Y ⋙ BigFppfOver.toScheme B S hS) F) :
    Space.IsLocallyOfFinitePresentation B S hS p.hom := by
  refine Space.isLocallyOfFinitePresentation_of_relativelyLimitPreserving B S hS ?_
  intro X y I _ _ D cn hlim hD hpt
  obtain ⟨h⟩ := hF I (D ⋙ overStage X y) ((overStage X y).mapCone cn) hlim hD hpt
  let e : (overStage X y).op ⋙ F ≅ sectionFiber B S hS p.hom X y ⋙ uliftFunctor.{u + 1, u} :=
    Functor.isoWhiskerLeft (overStage X y).op c.symm ≪≫
      (Functor.isoWhiskerRight (sectionFiberIso X y p) uliftFunctor.{u + 1, u}).symm
  have h' : IsColimit (((overStage X y).op ⋙ F).mapCocone cn.op) := h
  exact ⟨isColimitOfReflects uliftFunctor.{u + 1, u} (IsColimit.mapCoconeEquiv e h')⟩

namespace PicardSituation

variable {s : PicardSituation B S hS} {H : AlgebraicSpaces B S hS} {p : H ⟶ s.base}

/-- **The lfp half of Stacks 0DNI, for any algebraic space representing `Pic_{X/B}`.** Let
`p : H ⟶ B` be an algebraic space over the base `B` of a Picard situation `f : X ⟶ B`, whose
functor of points over `B` is identified (`c`) with the relative Picard functor `Pic_{X/B}`. If
`f` is of finite presentation, then `p` is locally of finite presentation. -/
theorem isLocallyOfFinitePresentation_of_represents_picardFunctor
    (c : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ s.picardFunctor)
    (hfp : IsFinitePresentation B S hS s.f.hom) :
    Space.IsLocallyOfFinitePresentation B S hS p.hom :=
  isLocallyOfFinitePresentation_of_limitPreserving_spacePointsOver p c
    (s.limitPreserving_picardFunctor hfp)

end PicardSituation

end AlgebraicGeometry.Space
