module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.PushforwardComparisonWhiskering
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartBaseChangeCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChangeComposition

/-!
# The direct image of modules along base change of charts, composed along a factorisation

`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_comp` identifies the composition comparison
of the direct images of modules of Stacks 03LU with the composition comparison of the
chart-base-change direct images, for a composite written literally as `f ≫ g`.  A consumer whose
composite arrow is given to it under another name — which is the normal situation, a morphism of
represented algebraic spaces being the image of a morphism of the site — cannot use that form
without first unfolding a composition inside a larger elaboration.  This file restates the three
comparisons involved, and that law, for a composite presented by a separate morphism `fg`
together with a factorisation `f ≫ g = fg`, following the idiom of
`AlgebraicGeometry.Space.smallBaseChange_factoredComp`.

It also turns the law round.  As stated, the law composes the two chart identifications in the
forward direction; a consumer that *uses* a chart identification does so in the backward
direction, because the identification enters the comparison of the two direct images of a square
of ringed sites as its inverse.  The backward form is supplied here as
`AlgebraicGeometry.Space.modulePushforwardChartIso_symm_factoredComp`.

## Main definitions

* `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardFactoredCompIso` and
  `AlgebraicGeometry.Space.modulePushforwardFactoredCompIso`: the two composition comparisons at
  a factorised composite, with `AlgebraicGeometry.Space.smallBaseChangeSharp_factoredCompInv`
  the square compatibility that the first one consumes.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardChartIso_compIso`: the composition law of
  `AlgebraicGeometry.Space.modulePushforwardChartIso` as an equality of isomorphisms of
  functors rather than of their forward natural transformations.
* `AlgebraicGeometry.Space.modulePushforwardChartIso_symm_factoredComp`: **that law at a factorised
  composite and in the backward direction.**
* `Stacks.CategoryTheory.isoSymmTrans_of_trans_eq`: the piece of two-categorical algebra used,
  at plain variables of an arbitrary category.

## Implementation notes

The two composition comparisons are presented differently on purpose.
`AlgebraicGeometry.Space.modulePushforwardFactoredCompIso` is obtained by substituting the
factorisation, because `AlgebraicGeometry.Space.modulePushforwardCompIso` is a four-fold
composite containing transports along equalities of functors and nothing is gained by taking it
apart.  `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardFactoredCompIso` is written out
instead, as `CategoryTheory.SheafOfModules.pushforwardComp` followed by
`CategoryTheory.SheafOfModules.pushforwardCongr₂` along the factorised comparison of the
functors of sites, so that a consumer can take it apart by the whiskering calculus of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/PushforwardComparisonWhiskering.lean`.
The two presentations agree at the literal composite, which is recorded as
`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardFactoredCompIso_rfl`.

Worth recording because it shapes everything downstream: the composition
comparison `CategoryTheory.SheafOfModules.pushforwardComp` must be *kept* in such a composite
and never cancelled at a geometric instantiation.  It is `CategoryTheory.Iso.refl`, so
`CategoryTheory.SheafOfModules.pushforward` of a
`CategoryTheory.SheafOfModules.comparisonComp` and the composite of the two pushforwards are
definitionally equal; but asking for that definitional equality *here* — by ascribing the bare
`CategoryTheory.SheafOfModules.pushforwardCongr₂` to the type
`f_* ⋙ g_* ≅ (fg)_*` — is a deterministic 200,000-heartbeat timeout, while the same ascription
of the composite that *begins* with `pushforwardComp` costs nothing, the two ends of that
composite already being written as composites of pushforwards.  So a consumer composing such
comparisons keeps every `pushforwardComp` and moves it with the coherence
`CategoryTheory.SheafOfModules.pushforward_assoc`.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

namespace Stacks.CategoryTheory

open CategoryTheory

/-- **A three-factor identity between isomorphisms, read backwards.**  From
`e₁ ≪≫ e₂ ≪≫ e₃ = e₄ ≪≫ e₅` one gets `e₂⁻¹ ≪≫ e₁⁻¹ ≪≫ e₄ = e₃ ≪≫ e₅⁻¹`: the first two factors
are moved to the other side on the left, and the last one on the right.

Every datum is a variable of an arbitrary category, so an instantiation restates nothing. -/
theorem isoSymmTrans_of_trans_eq {𝒞 : Type*} [Category 𝒞] {W X Y Z Z' : 𝒞}
    {e₁ : W ≅ X} {e₂ : X ≅ Y} {e₃ : Y ≅ Z} {e₄ : W ≅ Z'} {e₅ : Z' ≅ Z}
    (h : e₁ ≪≫ e₂ ≪≫ e₃ = e₄ ≪≫ e₅) :
    e₂.symm ≪≫ e₁.symm ≪≫ e₄ = e₃ ≪≫ e₅.symm := by
  have hh : e₁.hom ≫ e₂.hom ≫ e₃.hom = e₄.hom ≫ e₅.hom := congrArg Iso.hom h
  refine Iso.ext ?_
  change e₂.inv ≫ e₁.inv ≫ e₄.hom = e₃.hom ≫ e₅.inv
  rw [Iso.eq_comp_inv, Category.assoc, Category.assoc, ← hh]
  simp

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-! ### The chart-base-change direct image at a factorised composite -/

/-- **The structure maps of chart base change compose, at a factorised composite**, in the
direction the transport of a direct image of modules consumes: the composite of the two
structure maps, carried backwards along the comparison of the two base-change functors, is the
structure map of base change along the composite.

This is `AlgebraicGeometry.Space.smallBaseChangeSharp_comp` with
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` evaluated to the natural transformation
of restriction functors it is, and with the composite presented by a separate morphism. -/
theorem smallBaseChangeSharp_factoredCompInv (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable fg.hom) (w : f ≫ g = fg) :
    SheafOfModules.comparisonComp (smallBaseChangeSharp B S hS g hg)
          (smallBaseChangeSharp B S hS f hf) ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (smallBaseChange_factoredComp B S hS f g fg hf hg hfg w).inv RingCat.{u}
          (SmallEtale.topology B S hS Z.1) (SmallEtale.topology B S hS X.1)).app
          (smallEtaleRingSheaf B S hS X.1 X.2) =
      smallBaseChangeSharp B S hS fg hfg := by
  subst w
  have h := smallBaseChangeSharp_comp B S hS f g hf hg hfg
  rw [Functor.sheafPushforwardContinuousComp'_hom_eq] at h
  exact (Category.assoc _ _ _).trans h.symm

/-- `AlgebraicGeometry.Space.smallBaseChangeModulePushforwardCompIsoOfRepresentable` at a composite
presented by
a separate morphism together with a factorisation. -/
noncomputable def smallBaseChangeModulePushforwardFactoredCompIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hf : yoneda.relativelyRepresentable f.hom)
    (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable fg.hom) (w : f ≫ g = fg) :
    smallBaseChangeModulePushforward.{u, u} B S hS f hf ⋙
        smallBaseChangeModulePushforward.{u, u} B S hS g hg ≅
      smallBaseChangeModulePushforward.{u, u} B S hS fg hfg :=
  SheafOfModules.pushforwardComp.{u} (smallBaseChangeSharp B S hS g hg)
      (smallBaseChangeSharp B S hS f hf) ≪≫
    SheafOfModules.pushforwardCongr₂.{u} _
      (smallBaseChange_factoredComp B S hS f g fg hf hg hfg w).symm
      (smallBaseChangeSharp_factoredCompInv B S hS f g fg hf hg hfg w)

/-- At the literal composite the factorised comparison is
`AlgebraicGeometry.Space.smallBaseChangeModulePushforwardCompIsoOfRepresentable`. -/
theorem smallBaseChangeModulePushforwardFactoredCompIso_rfl (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) :
    smallBaseChangeModulePushforwardFactoredCompIso B S hS f g (f ≫ g) hf hg hfg rfl =
      smallBaseChangeModulePushforwardCompIsoOfRepresentable.{u, u} B S hS f g hf hg hfg :=
  rfl

/-- `AlgebraicGeometry.Space.modulePushforwardCompIso` at a composite presented by a separate
morphism together with a factorisation. -/
noncomputable def modulePushforwardFactoredCompIso (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (w : f ≫ g = fg) :
    modulePushforward B S hS f ⋙ modulePushforward B S hS g ≅
      modulePushforward B S hS fg := by
  subst w
  exact modulePushforwardCompIso B S hS f g

/-- At the literal composite the factorised comparison is
`AlgebraicGeometry.Space.modulePushforwardCompIso`. -/
theorem modulePushforwardFactoredCompIso_rfl (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforwardFactoredCompIso B S hS f g (f ≫ g) rfl =
      modulePushforwardCompIso B S hS f g :=
  rfl

/-! ### The composition law of the chart identification -/

/-- `AlgebraicGeometry.Space.modulePushforwardChartIso_hom_comp` as an equality of isomorphisms of
functors.  Its two sides are the forward natural transformations of these isomorphisms. -/
theorem modulePushforwardChartIso_compIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) :
    Functor.isoWhiskerRight (modulePushforwardChartIso B S hS f hf)
            (modulePushforward B S hS g) ≪≫
          Functor.isoWhiskerLeft (smallBaseChangeModulePushforward.{u, u} B S hS f hf)
            (modulePushforwardChartIso B S hS g hg) ≪≫
        smallBaseChangeModulePushforwardCompIsoOfRepresentable.{u, u} B S hS f g hf hg hfg =
      modulePushforwardCompIso B S hS f g ≪≫
        modulePushforwardChartIso B S hS (f ≫ g) hfg :=
  Iso.ext (modulePushforwardChartIso_hom_comp B S hS f g hf hg hfg)

/-- **The composition law of the chart identification, at a factorised composite and in the
direction a comparison of direct images consumes it.**  Reading the chart-base-change direct
image along `g` and then along `f` as the direct images of Stacks 03LU, and composing those,
is composing the chart-base-change direct images and reading the result along `fg`. -/
theorem modulePushforwardChartIso_symm_factoredComp (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable fg.hom) (w : f ≫ g = fg) :
    (Functor.isoWhiskerLeft (smallBaseChangeModulePushforward.{u, u} B S hS f hf)
            (modulePushforwardChartIso B S hS g hg)).symm ≪≫
          (Functor.isoWhiskerRight (modulePushforwardChartIso B S hS f hf)
            (modulePushforward B S hS g)).symm ≪≫
        modulePushforwardFactoredCompIso B S hS f g fg w =
      smallBaseChangeModulePushforwardFactoredCompIso B S hS f g fg hf hg hfg w ≪≫
        (modulePushforwardChartIso B S hS fg hfg).symm := by
  subst w
  exact Stacks.CategoryTheory.isoSymmTrans_of_trans_eq
    (modulePushforwardChartIso_compIso B S hS f g hf hg hfg)

end AlgebraicGeometry.Space

end
