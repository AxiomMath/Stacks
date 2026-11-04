module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeComposition

/-!
# The direct image of modules along base change of charts is compatible with composition

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of algebraic spaces over `S` whose underlying
morphisms of presheaves are representable, together with a representability witness for the
composite.  `AlgebraicGeometry.Space.smallBaseChangeModulePushforward` — the direct image of
modules taken along base change of étale scheme charts and the structure map
`AlgebraicGeometry.Space.smallBaseChangeSharp` — is then defined along all three, and this file
compares the direct image along the composite with the composite of the two direct images.

## Main definitions

* `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardCompIsoOfRepresentable`: the comparison
  `f_* ⋙ g_* ≅ (f ≫ g)_*` of the chart-base-change direct images of modules.

## Main results

* `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardCompIso_hom_app_val_app`: the
  comparison acts on sections by restriction along the comparison of the base-changed charts.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe m u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- The direct image of modules along base change of étale scheme charts is compatible with
composition: for representable `f : X ⟶ Y` and `g : Y ⟶ Z` the composite of the two
chart-base-change direct images is the chart-base-change direct image of `f ≫ g`, through the
comparison `AlgebraicGeometry.Space.smallBaseChange_comp` of the functors of sites. -/
noncomputable def smallBaseChangeModulePushforwardCompIsoOfRepresentable (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) :
    smallBaseChangeModulePushforward.{m, u} B S hS f hf ⋙
        smallBaseChangeModulePushforward.{m, u} B S hS g hg ≅
      smallBaseChangeModulePushforward.{m, u} B S hS (f ≫ g) hfg :=
  letI : (smallBaseChange B S hS g hg ⋙ smallBaseChange B S hS f hf).IsContinuous
      (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS X.1) :=
    Functor.isContinuous_comp (smallBaseChange B S hS g hg) (smallBaseChange B S hS f hf)
      (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B S hS X.1)
  SheafOfModules.pushforwardComp.{m} (smallBaseChangeSharp B S hS g hg)
      (smallBaseChangeSharp B S hS f hf) ≪≫
    SheafOfModules.pushforwardCongr₂.{m} _ (smallBaseChange_comp B S hS f g hf hg hfg).symm (by
      have h := smallBaseChangeSharp_comp B S hS f g hf hg hfg
      rw [Functor.sheafPushforwardContinuousComp'_hom_eq] at h
      exact (Category.assoc _ _ _).trans h.symm)

/-- The comparison `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardCompIsoOfRepresentable`
acts on sections by restriction along the comparison of the base-changed charts. -/
theorem smallBaseChangeModulePushforwardCompIso_hom_app_val_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom)
    (M : SheafOfModules.{m} (smallEtaleRingSheaf B S hS X.1 X.2))
    (W : (SmallEtale B S hS Z.1)ᵒᵖ)
    (x : ((smallBaseChangeModulePushforward.{m, u} B S hS f hf ⋙
      smallBaseChangeModulePushforward.{m, u} B S hS g hg).obj M).val.obj W) :
    ((smallBaseChangeModulePushforwardCompIsoOfRepresentable.{m, u} B S hS f g hf hg hfg).hom.app
      M).val.app W
        x =
      M.val.map ((smallBaseChange_comp B S hS f g hf hg hfg).inv.app W.unop).op x :=
  rfl

end AlgebraicGeometry.Space

end
