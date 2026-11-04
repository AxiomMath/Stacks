module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationAtlasSmoothSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance

/-!
# The atlas of a presentation, read at the morphism universe of the stack

Let `S` be a scheme of a big fppf site, let `𝒳` be an algebraic stack over `S` and let
`P = ((U, R, s, t, c), [U/R] ≃ 𝒳)` be a presentation of it in the sense of Stacks 04TI. The
canonical projection `π : 𝒮_U ⟶ [U/R]` of Stacks 044R goes out of
`AlgebraicGeometry.Stack.liftedObjectSpace`, whose morphisms live one universe above the site's
because a quotient stack is a stackification. This module records the same atlas as the
1-morphism

    a : 𝒮_U ⟶ 𝒳

out of `AlgebraicGeometry.Stack.fibredCategory` of the object space, whose morphisms are small,
and transports the two conclusions of Stacks 04X0 to it.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidPresentation.objectStack` and
  `AlgebraicGeometry.Stack.GroupoidPresentation.atlasMap`: the object space of a presentation and
  its atlas, both at the morphism universe of `𝒳`.
* `AlgebraicGeometry.Stack.GroupoidPresentation.inverseBasedFunctor`: the quasi-inverse of the
  presenting equivalence, read as a 1-morphism over the site.
* `AlgebraicGeometry.Stack.GroupoidPresentation.atlasComparison`: the 2-commutative square
  carrying the projection `π` of Stacks 044R onto that atlas.

## Main results

* `AlgebraicGeometry.Stack.GroupoidPresentation.isRepresentableByAlgebraicSpaces_atlasMap`,
  `...isRelativelySmooth_atlasMap` and `...isRelativelySurjective_atlasMap`: the conclusions of
  Stacks 04WZ and Stacks 04X0 for that atlas.

## References

* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
* [Stacks Project, Tag 04WZ](https://stacks.math.columbia.edu/tag/04WZ)
* [Stacks Project, Tag 04X0](https://stacks.math.columbia.edu/tag/04X0)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.GroupoidPresentation

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

-- `AlgebraicGeometry.Stack.liftedObjectSpace` and `AlgebraicGeometry.Stack.liftedFibredCategory`
-- agree definitionally but not reducibly.
attribute [local implicit_reducible] liftedObjectSpace liftedSpace liftedFibredCategory

/-- **The object space of a presentation, at the morphism universe of the site.** The category
fibred in groupoids of Stacks 0458 attached to the sheaf of points of the object space, without
the universe lift that `AlgebraicGeometry.Stack.liftedObjectSpace` performs. -/
noncomputable abbrev objectStack (P : GroupoidPresentation B S hS 𝒳.val) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  fibredCategory B S hS P.groupoid.objects.obj

/-- **The atlas of a presentation, at the morphism universe of the stack.** The universe lift of
the object space followed by the presenting 1-morphism `𝒮_U ⟶ 𝒳`. -/
noncomputable def atlasMap (P : GroupoidPresentation B S hS 𝒳.val) : objectStack P ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp (liftedFibredCategoryUp P.groupoid.objects) P.presentingMap)

/-- The inverse 1-morphism of the presenting equivalence, as a 1-morphism over the site. -/
noncomputable def inverseBasedFunctor (P : GroupoidPresentation B S hS 𝒳.val) :
    𝒳.val ⥤ᵇ quotientStack P.groupoid :=
  ⟨P.equivalence.inv.functor, P.equivalence.inv.w⟩

/-- The inverse 1-morphism of the presenting equivalence is an equivalence. -/
noncomputable instance isEquivalence_inverseBasedFunctor
    (P : GroupoidPresentation B S hS 𝒳.val) :
    (inverseBasedFunctor P).toFunctor.IsEquivalence :=
  P.equivalence.toEquivalence.isEquivalence_inverse

/-- **The square comparing the two readings of the atlas.** The universe lift of the object space
on the source and the presenting equivalence on the target carry the projection
`π : 𝒮_U ⟶ [U/R]` of Stacks 044R onto `AlgebraicGeometry.Stack.GroupoidPresentation.atlasMap`.
Its filler is the unit of the presenting equivalence, whiskered by the projection. -/
noncomputable def atlasComparison (P : GroupoidPresentation B S hS 𝒳.val) :
    BasedFunctor.comp (liftedFibredCategoryUp P.groupoid.objects)
        (quotientStackProjectionHom P.groupoid).hom ≅
      BasedFunctor.comp (atlasMap P).hom (inverseBasedFunctor P) := by
  refine BasedNatIso.mkNatIso (Functor.isoWhiskerLeft _ P.equivalence.unitIso) (fun x => ?_)
  have hx : (quotientStack P.groupoid).p.obj
      (((liftedFibredCategoryUp P.groupoid.objects).comp
        (quotientStackProjectionHom P.groupoid).hom).toFunctor.obj x) =
      (fibredCategory B S hS P.groupoid.objects.obj).val.p.obj x :=
    congrArg (fun k => k.obj x)
      ((liftedFibredCategoryUp P.groupoid.objects).comp
        (quotientStackProjectionHom P.groupoid).hom).w
  rw [← hx]
  exact P.equivalence.isHomLift_unitIso_hom_app _

/-- **The conclusion of Stacks 04WZ for the atlas at the small morphism universe.** -/
theorem isRepresentableByAlgebraicSpaces_atlasMap
    (P : GroupoidPresentation B S hS 𝒳.val) (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsRepresentableByAlgebraicSpaces B S hS (atlasMap P).hom := by
  have := isEquivalence_liftedFibredCategoryUp P.groupoid.objects
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS (atlasMap P).hom
      (quotientStackProjectionHom P.groupoid).hom
      (liftedFibredCategoryUp P.groupoid.objects) (inverseBasedFunctor P)
      (atlasComparison P)).1
    (isRepresentableByAlgebraicSpaces_projection P h𝒳)

/-- **The conclusion of Stacks 04X0, smoothness, for the atlas at the small morphism universe.** -/
theorem isRelativelySmooth_atlasMap
    (P : GroupoidPresentation B S hS 𝒳.val) (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsRelativelySmooth B S hS (atlasMap P) := by
  have := isEquivalence_liftedFibredCategoryUp P.groupoid.objects
  exact isRelativelySmooth_of_equivalences B S hS (atlasMap P)
    (quotientStackProjectionHom P.groupoid)
    (liftedFibredCategoryUp P.groupoid.objects) (inverseBasedFunctor P)
    (atlasComparison P) (isRelativelySmooth_projection P h𝒳)

/-- **The conclusion of Stacks 04X0, surjectivity, for the atlas at the small morphism
universe.** -/
theorem isRelativelySurjective_atlasMap
    (P : GroupoidPresentation B S hS 𝒳.val) (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) (atlasMap P)
      (isRepresentableByAlgebraicSpaces_atlasMap P h𝒳) := by
  have := isEquivalence_liftedFibredCategoryUp P.groupoid.objects
  exact hasRelativeProperty_of_equivalences.{u, u, u + 1, u + 1, u + 1, u} B S hS
    (Space.surjectiveMorphismProperty B S hS)
    (atlasMap P) (quotientStackProjectionHom P.groupoid)
    (liftedFibredCategoryUp P.groupoid.objects) (inverseBasedFunctor P)
    (atlasComparison P) (isRepresentableByAlgebraicSpaces_projection P h𝒳)
    (isRepresentableByAlgebraicSpaces_atlasMap P h𝒳)
    (isRelativelySurjective_projection P h𝒳)

end AlgebraicGeometry.Stack.GroupoidPresentation

end
