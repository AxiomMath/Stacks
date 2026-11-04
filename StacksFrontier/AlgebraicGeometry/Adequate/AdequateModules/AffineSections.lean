module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocal

/-!
# The affine-section functor and the adequate module-valued functors on a site

Let `S` be a scheme and `B` a chosen big `τ`-site over `S`. The affine-section construction
`𝓕 ↦ F_{𝓕, A}` of [Stacks, Tag 06UT] is defined on objects by
`Stacks.Adequate.affineSectionFunctor`; this module upgrades it to a functor on all sheaves of
modules, and names the strictly full subcategory of adequate module-valued functors on the
`A`-algebras of the site in which the comparison of [Stacks, Tag 06ZJ] lands.

## Main definitions

* `Stacks.Adequate.adequateOn` — the category of adequate module-valued functors on the
  `A`-algebras of the site: the strictly full subcategory of
  `AdequateFunctor.ModuleValuedFunctorOn` cut out by `AdequateFunctor.IsAdequate`. The source's
  `Alg_A` is the algebras of the site, as it is throughout the chapter; the variant indexed by
  *all* `A`-algebras is `AdequateFunctor.adequate`.
* `Stacks.Adequate.affineSectionsFunctor` — the affine-section construction `𝓕 ↦ F_{𝓕, A}` as a
  functor on sheaves of modules. On objects it is `Stacks.Adequate.affineSectionFunctor`; on a
  map of sheaves it is the induced map of affine sections.

## Main results

* `Stacks.Adequate.affineSectionsFunctor_obj` — the functor extends the object-level
  `Stacks.Adequate.affineSectionFunctor`.
* `Stacks.Adequate.affineSectionsFunctor_obj_map` — the restriction maps of `F_{𝓕, A}` are
  those of `𝓕`.

## References

* [Stacks Project, Tag 06UT](https://stacks.math.columbia.edu/tag/06UT)
* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
* [Stacks Project, Tag 07AH](https://stacks.math.columbia.edu/tag/07AH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u m

namespace Stacks.Adequate

/-- The category of adequate module-valued functors on the `A`-algebras of a site: the strictly
full subcategory of `AdequateFunctor.ModuleValuedFunctorOn` cut out by adequacy. This is the
Stacks Project's category of adequate module-valued functors on `Alg_A`, with `Alg_A` the
algebras of the site. -/
public abbrev adequateOn (A : CommRingCat.{u}) (P : ObjectProperty Scheme.{u}) :
    ObjectProperty (AdequateFunctor.ModuleValuedFunctorOn.{m}
      (AdequateFunctor.siteAlgebraInclusion A P)) :=
  fun F ↦ AdequateFunctor.IsAdequate (AdequateFunctor.siteAlgebraInclusion A P) F

/-- The affine-section construction `𝓕 ↦ F_{𝓕, A}` as a functor on sheaves of modules: forget
the sheaf condition, then push forward along the affine-spectrum functor of `A` and the scalar
identification `Stacks.Adequate.affineRingMap`. -/
public noncomputable def affineSectionsFunctor {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (A : CommRingCat.{u}) (f : Spec A ⟶ S) :
    SheafOfModules.{m} B.structureSheaf ⥤
      AdequateFunctor.ModuleValuedFunctorOn.{m}
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) :=
  SheafOfModules.forget B.structureSheaf ⋙ PresheafOfModules.pushforward (affineRingMap B A f)

/-- The functor `Stacks.Adequate.affineSectionsFunctor` extends the object-level affine-section
functor `Stacks.Adequate.affineSectionFunctor`. -/
@[simp] public theorem affineSectionsFunctor_obj {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (F : SheafOfModules.{m} B.structureSheaf) :
    (affineSectionsFunctor B A f).obj F = affineSectionFunctor B F A f := rfl

/-- **The restriction maps of `F_{𝓕, A}`, stated generically in `𝓕`.** Restricting a section of
`𝓕` along a map of algebras of the site is the restriction map of `𝓕` along the induced map of
affine schemes of the site.

The two sides are definitionally equal after unfolding `Stacks.Adequate.affineSectionsFunctor`
and `PresheafOfModules.pushforward` only. At a *specific* `𝓕`, such as an associated module, the
same `rfl` also has to reduce that sheaf, down to `Stacks.Sites.associatedPresheaf`, which does
not fit in the default heartbeat budget; instantiating this lemma avoids that. -/
@[simp] public theorem affineSectionsFunctor_obj_map {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (F : SheafOfModules.{m} B.structureSheaf)
    {X Y : ((AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖ)ᵒᵖ} (g : X ⟶ Y)
    (x : ((affineSectionsFunctor B A f).obj F).obj X) :
    ((affineSectionsFunctor B A f).obj F).map g x =
      F.val.map ((affineSpecOver B A f).op.map g) x := rfl

end Stacks.Adequate

end
