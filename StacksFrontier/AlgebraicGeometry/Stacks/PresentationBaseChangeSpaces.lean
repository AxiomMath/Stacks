module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsGroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationAtlasSmoothSurjective

/-!
# The base-changed object and arrow spaces of a presentation are algebraic spaces

Let `S` be a scheme of a big fppf site, let `g : 𝒳' ⟶ 𝒳` be a 1-morphism of categories fibred in
groupoids representable by algebraic spaces, and let `P = ((U, R, s, t, c), [U/R] ≃ 𝒳)` be a
presentation of `𝒳` in the sense of Stacks 04TI. The 2-fibre products `U' = U ×_𝒳 𝒳'` and
`R' = R ×_𝒳 𝒳'` are represented by algebraic spaces.

Both are instances of Stacks 0300: a 2-fibre product of a 1-morphism representable by
algebraic spaces with a category represented by an algebraic space is represented by an algebraic
space. The two categories being base changed are the universe-lifted fibred categories of the
object and arrow spaces of the presenting groupoid, which are represented by those spaces
themselves (Stacks 04SV).

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidPresentation.arrowSpaceMap`: the composite `𝒮_R ⟶ 𝒳` of the
  source map of the groupoid with the presenting 1-morphism, i.e. the map along which `R` is base
  changed.
* `AlgebraicGeometry.Stack.GroupoidPresentation.baseChangedObjectSpace` and
  `...baseChangedArrowSpace`: the 2-fibre products `U ×_𝒳 𝒳'` and `R ×_𝒳 𝒳'`.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_liftedSpace`: the universe lift of the
  fibred category of an algebraic space is represented by that algebraic space.
* `GroupoidPresentation.isRepresentableByAlgebraicSpace_baseChangedObjectSpace` and
  `GroupoidPresentation.isRepresentableByAlgebraicSpace_baseChangedArrowSpace`: both are
  represented by algebraic spaces.

## Implementation notes

`R` is base changed along the composite of the *source* map with the presenting 1-morphism, as
in `AlgebraicGeometry.Stack.QuotientAtlas.Presentation`, whose `leg` is the source map. Groupoid
inversion identifies this composite with the one through the target map up to isomorphism.

Neither statement needs the algebraicity of `𝒳` or `𝒳'`: Stacks 0300 asks only that `g` be
representable by algebraic spaces.

The object and arrow spaces are reached through `AlgebraicGeometry.Stack.liftedSpace`, the
universe-lifted fibred category of an arbitrary algebraic space, rather than through
`AlgebraicGeometry.Stack.liftedObjectSpace`, since the arrow space of a groupoid is not the object
space of anything.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
* [Stacks Project, Tag 04Y6](https://stacks.math.columbia.edu/tag/04Y6)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The universe lift of the fibred category of an algebraic space is represented, over the big
fppf site, by that algebraic space itself. -/
theorem isRepresentableByAlgebraicSpace_liftedSpace (X : AlgebraicSpaces B S hS) :
    IsRepresentableByAlgebraicSpace B S hS (liftedSpace X) := by
  refine ⟨X.obj, X.property, ⟨?_⟩⟩
  exact
    { hom := ⟨(ULiftHom.down : ULiftHom.{u + 1}
        (fibredCategory B S hS X.obj).val.obj ⥤ _), rfl⟩
      inv := ⟨ULiftHom.up, rfl⟩
      unitIso := Iso.refl _
      counitIso := Iso.refl _
      unit_over :=
        StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl
      counit_over :=
        StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl }

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.GroupoidPresentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 𝒳' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- The composite `𝒮_R ⟶ 𝒳` of the source map of the presenting groupoid, on universe-lifted
fibred categories, with the presenting 1-morphism `𝒮_U ⟶ 𝒳`. -/
noncomputable def arrowSpaceMap (P : GroupoidPresentation B S hS 𝒳.val) :
    (liftedSpace P.groupoid.arrows).val ⥤ᵇ 𝒳.val :=
  BasedFunctor.comp (liftedAssociatedMap P.groupoid.source) P.presentingMap

/-- The base-changed object space `U' = U ×_𝒳 𝒳'`: the canonical 2-fibre product of the
presenting 1-morphism with `g`. -/
noncomputable abbrev baseChangedObjectSpace (P : GroupoidPresentation B S hS 𝒳.val)
    (g : 𝒳'.val ⥤ᵇ 𝒳.val) : CatFiberedInGroupoids (BigFppfOver B S hS) :=
  twoFibreProduct B S hS 𝒳 (liftedSpace P.groupoid.objects) 𝒳' P.presentingMap g

/-- The base-changed arrow space `R' = R ×_𝒳 𝒳'`: the canonical 2-fibre product of
`AlgebraicGeometry.Stack.GroupoidPresentation.arrowSpaceMap` with `g`. -/
noncomputable abbrev baseChangedArrowSpace (P : GroupoidPresentation B S hS 𝒳.val)
    (g : 𝒳'.val ⥤ᵇ 𝒳.val) : CatFiberedInGroupoids (BigFppfOver B S hS) :=
  twoFibreProduct B S hS 𝒳 (liftedSpace P.groupoid.arrows) 𝒳' (arrowSpaceMap P) g

/-- The base change `U' = U ×_𝒳 𝒳'` of the object space of a presentation along a 1-morphism
`g` representable by algebraic spaces is represented by an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_baseChangedObjectSpace
    (P : GroupoidPresentation B S hS 𝒳.val) (g : 𝒳'.val ⥤ᵇ 𝒳.val)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g) :
    IsRepresentableByAlgebraicSpace B S hS (baseChangedObjectSpace P g) :=
  isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳 _ 𝒳' P.presentingMap g hg
    (isRepresentableByAlgebraicSpace_liftedSpace P.groupoid.objects)

/-- The base change `R' = R ×_𝒳 𝒳'` of the arrow space of a presentation along a 1-morphism `g`
representable by algebraic spaces is represented by an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_baseChangedArrowSpace
    (P : GroupoidPresentation B S hS 𝒳.val) (g : 𝒳'.val ⥤ᵇ 𝒳.val)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g) :
    IsRepresentableByAlgebraicSpace B S hS (baseChangedArrowSpace P g) :=
  isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳 _ 𝒳' (arrowSpaceMap P) g hg
    (isRepresentableByAlgebraicSpace_liftedSpace P.groupoid.arrows)

end AlgebraicGeometry.Stack.GroupoidPresentation

end
