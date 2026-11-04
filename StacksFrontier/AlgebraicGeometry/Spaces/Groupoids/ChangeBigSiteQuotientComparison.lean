module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteGroupoidPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointwiseGroupoidMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackChangeBigSite
public import StacksFrontier.CategoryTheory.FiberedCategory.OfPresheafRestriction
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackAdjunction
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PushforwardStack

/-!
# The comparison from the pullback of a quotient stack to the quotient of the pulled-back groupoid

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, let `G`
be a groupoid in algebraic spaces over an algebraic space over `S` for `B`, and let `f` be the
morphism of sites determined by the localized inclusion `i`. This file builds the canonical
1-morphism

`u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]`

of categories over the enlarged localized big fppf site. Since `f⁻¹[U/R]` is the stackification
of `u_p [U/R]` (Stacks 04WJ), this is the 1-morphism out of which the comparison of Stacks 04WX
is obtained.

The route is the adjunction of Stacks 04WI. A 1-morphism `u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]` over the
larger site is the same thing as a 1-morphism `[U/R] ⟶ f_*[f⁻¹U/f⁻¹R]` over the smaller one, and
the latter is produced by the universal property of the stackification (Stacks 0436): the
pushforward `f_*[f⁻¹U/f⁻¹R]` is a stack in groupoids over the smaller site (Stacks 04WD), so it
suffices to give a 1-morphism out of the pointwise groupoid fibration of `G`. That 1-morphism is
the transport of sections: a `T`-point of `U` goes to the corresponding `i T`-point of `f⁻¹U`.

On the comma category of presentations the resulting 1-morphism is, by the explicit description
of the adjunction, the map `(T', φ : T' ⟶ i T, x) ↦ φ^*(x)` of the source of Stacks 04WX.

## Main definitions

* `AlgebraicGeometry.Stack.changeBigSitePointwiseMap`: the map of pointwise groupoid fibrations
  covering the localized inclusion.
* `AlgebraicGeometry.Stack.changeBigSiteQuotientMap`: the 1-morphism `[U/R] ⟶ [f⁻¹U/f⁻¹R]`
  covering the localized inclusion.
* `AlgebraicGeometry.Stack.changeBigSiteQuotientComparison`: the 1-morphism
  `u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]` over the enlarged localized big fppf site.

## Main results

* `AlgebraicGeometry.Stack.isStack_quotientStackPushforward` and
  `AlgebraicGeometry.Stack.isFiberedInGroupoids_quotientStackPushforward`: **Stacks 04WD** for
  the quotient stack of the pulled-back groupoid.
* `AlgebraicGeometry.Stack.isFibredOneMorphism_changeBigSiteQuotientComparison`: the comparison
  is a 1-morphism of fibred categories over the enlarged localized big fppf site.
* `AlgebraicGeometry.Stack.changeBigSiteQuotientComparison_obj_localization`: the comparison
  sends a presentation `(V, φ : V ⟶ i T, ξ)` to the chosen pullback of the image of `ξ` along
  `φ`, which is the formula `(T', φ, x) ↦ φ^*(x)` of Stacks 04WX.
* `AlgebraicGeometry.Stack.changeBigSitePointwiseMap_obj` and
  `AlgebraicGeometry.Stack.changeBigSitePrestackMap_obj`: the comparison of pointwise groupoid
  fibrations sends a `W`-point of the object space to its transport.

## Implementation notes

The category structure of the pushforward is supplied by hand, and so are the instances the
adjunction of Stacks 04WI consumes. Their hom universes are maxima in which a localized big
fppf site contributes its morphisms, which lie in a strictly smaller universe than its objects;
instance search does not reduce such a maximum, so the terms are named and passed explicitly.

## References

* [Stacks Project, Tag 04WD](https://stacks.math.columbia.edu/tag/04WD)
* [Stacks Project, Tag 04WG](https://stacks.math.columbia.edu/tag/04WG)
* [Stacks Project, Tag 04WI](https://stacks.math.columbia.edu/tag/04WI)
* [Stacks Project, Tag 04WJ](https://stacks.math.columbia.edu/tag/04WJ)
* [Stacks Project, Tag 04WX](https://stacks.math.columbia.edu/tag/04WX)
* [Stacks Project, Tag 0436](https://stacks.math.columbia.edu/tag/0436)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite Deformation

namespace AlgebraicGeometry.Stack

universe u

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) {Bs : AlgebraicSpaces B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS Bs)

/-- **The map of pointwise groupoid fibrations covering the localized inclusion.** On objects it
sends a `T`-point of `U` to the corresponding `i T`-point of `f⁻¹U`, and on arrows a `T`-point of
`R` to the corresponding `i T`-point of `f⁻¹R`. -/
def changeBigSitePointwiseMap :
    (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj ⥤
      (presheafOfGroupoids (evaluationGroupoidFunctor
        (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors)).obj :=
  (pointwiseMap (changeBigSiteGroupoidHom B B' h S hS G)).toFunctor ⋙
    PresheafOfCategories.restrictionComparison (inclusionOver h S hS)
      (evaluationGroupoidFunctor
        (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors ⋙ Grpd.forgetToCat)

/-- The map of pointwise groupoid fibrations covers the localized inclusion. -/
theorem changeBigSitePointwiseMap_comp :
    changeBigSitePointwiseMap B B' h S hS G ⋙
        (presheafOfGroupoids (evaluationGroupoidFunctor
          (changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors)).p =
      (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p ⋙
        inclusionOver h S hS := rfl

/-- **The map of pointwise groupoid fibrations on objects**: a `W`-point of the object space of
`G` goes to the corresponding `i W`-point of the object space of the inverse image of `G`. -/
@[simp]
theorem changeBigSitePointwiseMap_obj (W : BigFppfOver B S hS)
    (w : G.objects.obj.obj (op W)) :
    (changeBigSitePointwiseMap B B' h S hS G).obj ⟨W, w⟩ =
      ⟨(inclusionOver h S hS).obj W,
        changeBigSiteSectionEquiv B B' h S hS G.objects W w⟩ := rfl

/-- The composite from the universe-lifted pointwise groupoid fibration of `G` to the quotient
stack of the pulled-back groupoid. -/
def changeBigSitePrestackMap :
    (quotientPrestack G).obj ⥤ (quotientStack (changeBigSiteGroupoid B B' h S hS G)).obj :=
  (quotientPrestackEquivalence G).inverse ⋙ changeBigSitePointwiseMap B B' h S hS G ⋙
    pointwiseToQuotientStack (changeBigSiteGroupoid B B' h S hS G)

/-- That composite covers the localized inclusion. -/
theorem changeBigSitePrestackMap_comp :
    changeBigSitePrestackMap B B' h S hS G ⋙
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p =
      (quotientPrestack G).p ⋙ inclusionOver h S hS := by
  dsimp [changeBigSitePrestackMap]
  simp only [Functor.assoc, (isFibredOneMorphism_pointwiseToQuotientStack
    (changeBigSiteGroupoid B B' h S hS G)).comp_eq]
  rfl

/-- The category structure of the pushforward `f_*[f⁻¹U/f⁻¹R]` along the localized inclusion. -/
instance categoryQuotientStackPushforward :
    Category.{u + 1, u + 1} (StrictPullback (inclusionOver h S hS)
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p) :=
  StrictPullback.instCategory

/-- The quotient stack of the pulled-back groupoid is a fibred category over the enlarged
localized big fppf site. -/
instance isFibered_quotientStack_changeBigSite :
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsFibered :=
  isFibered_quotientStack _

/-- The localized inclusion is continuous for the two localized fppf topologies, in the form in
which the pushforward of a stack consumes it. -/
private theorem isContinuous_inclusionOver_topology :
    (inclusionOver h S hS).IsContinuous (BigFppfOver.topology B S hS)
      (BigFppfOver.topology B' S (largerContains h hS)) :=
  (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous

/-- **Stacks 04WD** for the quotient stack of the pulled-back groupoid: the pushforward
`f_*[f⁻¹U/f⁻¹R]` satisfies descent for the fppf topology of the smaller localized big site. -/
theorem isStack_quotientStackPushforward :
    Functor.IsStack (StrictPullback.structureFunctor (inclusionOver h S hS)
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p)
      (BigFppfOver.topology B S hS) := by
  have : HasFiniteLimits B.Schemes := hasFiniteLimits_siteCategory (τ := .fppf) B
  have : HasFiniteLimits (BigFppfOver B S hS) := inferInstance
  have : PreservesLimitsOfShape WalkingCospan (inclusionOver h S hS) :=
    (inclusionOver_preservesFiniteLimits (τ := .fppf) B B' h S hS).preservesFiniteLimits _
  have := isContinuous_inclusionOver_topology B B' h S hS
  exact StrictPullback.isStack_structureFunctor _ _ _ _
    (isStack_quotientStack (changeBigSiteGroupoid B B' h S hS G))

/-- **Stacks 04WD** for the quotient stack of the pulled-back groupoid: the pushforward
`f_*[f⁻¹U/f⁻¹R]` is fibred in groupoids over the smaller localized big site. -/
theorem isFiberedInGroupoids_quotientStackPushforward :
    (StrictPullback.structureFunctor (inclusionOver h S hS)
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p).IsFiberedInGroupoids :=
  StrictPullback.isFiberedInGroupoids_structureFunctor _ _
    (isFiberedInGroupoids_quotientStack (changeBigSiteGroupoid B B' h S hS G))

/-- The 1-morphism from the pointwise groupoid fibration of `G` to the pushforward
`f_*[f⁻¹U/f⁻¹R]`, over the smaller localized big site. -/
def prestackToPushforward :
    (quotientPrestack G).obj ⥤ StrictPullback (inclusionOver h S hS)
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p :=
  StrictPullback.liftFib (quotientPrestack G).p (changeBigSitePrestackMap B B' h S hS G)
    (changeBigSitePrestackMap_comp B B' h S hS G)

/-- That 1-morphism is strictly over the smaller localized big site. -/
theorem prestackToPushforward_comp :
    prestackToPushforward B B' h S hS G ⋙ StrictPullback.structureFunctor
        (inclusionOver h S hS)
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p =
      (quotientPrestack G).p := rfl

/-- The extension of `prestackToPushforward` along the stackification `[U/_p R] ⟶ [U/R]`,
by the universal property of Stacks 0436. -/
def quotientToPushforward :
    (quotientStack G).obj ⥤ StrictPullback (inclusionOver h S hS)
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p :=
  Functor.Stackification.extendGroupoid (isFiberedInGroupoids_quotientPrestack G)
    (isFiberedInGroupoids_quotientStack G) (isStack_quotientStack G)
    (isFiberedInGroupoids_quotientStackPushforward B B' h S hS G)
    (isStack_quotientStackPushforward B B' h S hS G)
    (isFibredOneMorphism_toQuotientStack G).comp_eq
    (prestackToPushforward_comp B B' h S hS G)
    (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G)

/-- The extension is strictly over the smaller localized big site. -/
theorem quotientToPushforward_comp :
    quotientToPushforward B B' h S hS G ⋙ StrictPullback.structureFunctor
        (inclusionOver h S hS)
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p =
      (quotientStack G).p :=
  Functor.Stackification.extendGroupoid_comp_eq (isFiberedInGroupoids_quotientPrestack G)
    (isFiberedInGroupoids_quotientStack G) (isStack_quotientStack G)
    (isFiberedInGroupoids_quotientStackPushforward B B' h S hS G)
    (isStack_quotientStackPushforward B B' h S hS G)
    (isFibredOneMorphism_toQuotientStack G).comp_eq
    (prestackToPushforward_comp B B' h S hS G)
    (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G)

/-- **The 1-morphism `[U/R] ⟶ [f⁻¹U/f⁻¹R]` covering the localized inclusion**: the extension of
the transport of sections along the stackification, read through the projection of the
pushforward. -/
def changeBigSiteQuotientMap :
    (quotientStack G).obj ⥤ (quotientStack (changeBigSiteGroupoid B B' h S hS G)).obj :=
  quotientToPushforward B B' h S hS G ⋙ StrictPullback.pr (inclusionOver h S hS)
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p

/-- The 1-morphism `[U/R] ⟶ [f⁻¹U/f⁻¹R]` covers the localized inclusion. -/
theorem changeBigSiteQuotientMap_comp :
    changeBigSiteQuotientMap B B' h S hS G ⋙
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p =
      (quotientStack G).p ⋙ inclusionOver h S hS :=
  (congrArg (fun F => quotientToPushforward B B' h S hS G ⋙ F)
      (StrictPullback.pr_comp_eq (inclusionOver h S hS)
        (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p)).trans
    (congrArg (fun F => F ⋙ inclusionOver h S hS)
      (quotientToPushforward_comp B B' h S hS G))

/-- **The 1-morphism `[U/R] ⟶ [f⁻¹U/f⁻¹R]` restricts along the stackification to the transport
of sections.** This is the 2-isomorphism of the universal property of Stacks 0436, read through
the projection of the pushforward. -/
def changeBigSiteQuotientMapUnit :
    toQuotientStack G ⋙ changeBigSiteQuotientMap B B' h S hS G ≅
      changeBigSitePrestackMap B B' h S hS G :=
  Functor.isoWhiskerRight
    (Functor.Stackification.unitGroupoid (isFiberedInGroupoids_quotientPrestack G)
      (isFiberedInGroupoids_quotientStack G) (isStack_quotientStack G)
      (isFiberedInGroupoids_quotientStackPushforward B B' h S hS G)
      (isStack_quotientStackPushforward B B' h S hS G)
      (isFibredOneMorphism_toQuotientStack G).comp_eq
      (prestackToPushforward_comp B B' h S hS G)
      (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G))
    (StrictPullback.pr (inclusionOver h S hS)
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p)

/-- Every component of that 2-isomorphism lies over an identity of the enlarged localized big
fppf site. -/
theorem isHomLift_changeBigSiteQuotientMapUnit_hom_app (z : (quotientPrestack G).obj) :
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsHomLift
      (𝟙 ((inclusionOver h S hS).obj ((quotientPrestack G).p.obj z)))
      ((changeBigSiteQuotientMapUnit B B' h S hS G).hom.app z) := by
  have hv := Functor.Stackification.isHomLift_unitGroupoid_app
    (isFiberedInGroupoids_quotientPrestack G)
    (isFiberedInGroupoids_quotientStack G) (isStack_quotientStack G)
    (isFiberedInGroupoids_quotientStackPushforward B B' h S hS G)
    (isStack_quotientStackPushforward B B' h S hS G)
    (isFibredOneMorphism_toQuotientStack G).comp_eq
    (prestackToPushforward_comp B B' h S hS G)
    (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G) z
  set f := (Functor.Stackification.unitGroupoid (isFiberedInGroupoids_quotientPrestack G)
      (isFiberedInGroupoids_quotientStack G) (isStack_quotientStack G)
      (isFiberedInGroupoids_quotientStackPushforward B B' h S hS G)
      (isStack_quotientStackPushforward B B' h S hS G)
      (isFibredOneMorphism_toQuotientStack G).comp_eq
      (prestackToPushforward_comp B B' h S hS G)
      (isLocallyBijective_toQuotientStack G) (essImage_toQuotientStack G)).hom.app z
  have hd := @IsHomLift.domain_eq _ _ _ _ (StrictPullback.structureFunctor
      (inclusionOver h S hS)
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p) _ _ _ _
    (𝟙 ((quotientPrestack G).p.obj z)) f hv
  have hc := @IsHomLift.codomain_eq _ _ _ _ (StrictPullback.structureFunctor
      (inclusionOver h S hS)
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p) _ _ _ _
    (𝟙 ((quotientPrestack G).p.obj z)) f hv
  have hmain := StrictPullback.isHomLift_fib_of_base_id f (hd.trans hc.symm)
    ((StrictPullback.base_eq_eqToHom hd hc f hv).trans (eqToHom_trans _ _))
  exact Eq.mp (congrArg
    (fun V => (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsHomLift
      (𝟙 ((inclusionOver h S hS).obj V)) f.fib) hd) hmain

/-- Every morphism of `[f⁻¹U/f⁻¹R]` lying over the image of a morphism of the base is strongly
cartesian, the quotient stack being fibred in groupoids. -/
theorem isStronglyCartesian_changeBigSiteQuotientMap_map
    {x y : (quotientStack G).obj} (α : x ⟶ y) :
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsStronglyCartesian
      (((quotientStack G).p ⋙ inclusionOver h S hS).map α)
      ((changeBigSiteQuotientMap B B' h S hS G).map α) := by
  have h1 : (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p.IsHomLift
      (((quotientStack G).p ⋙ inclusionOver h S hS).map α)
      ((changeBigSiteQuotientMap B B' h S hS G).map α) :=
    @Functor.isHomLift_map_of_comp_eq _ _ _ _ _ _ _ _ _
      (changeBigSiteQuotientMap_comp B B' h S hS G) _ _
      (((quotientStack G).p ⋙ inclusionOver h S hS).map α) _ _ α
      (Functor.IsHomLift.map α)
  exact @Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift _ _ _ _ _
    (isFiberedInGroupoids_quotientStack (changeBigSiteGroupoid B B' h S hS G)) _ _ _ _
    (((quotientStack G).p ⋙ inclusionOver h S hS).map α)
    ((changeBigSiteQuotientMap B B' h S hS G).map α) h1

/-- **The canonical comparison `u_p [U/R] ⟶ [f⁻¹U/f⁻¹R]`** over the enlarged localized big fppf
site, the transpose of `changeBigSiteQuotientMap` under the adjunction of Stacks 04WI. On a
presentation `(T', φ : T' ⟶ i T, x)` it is the chosen pullback of the image of `x` along `φ`. -/
def changeBigSiteQuotientComparison :
    Comma.pullbackLocalization (quotientStack G).p (inclusionOver h S hS) ⥤
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).obj :=
  @PullbackAdjunction.leftToRight _ _ _ _ _ _ _ _
    (quotientStack G).p (inclusionOver h S hS)
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
    (isFibered_quotientStack (changeBigSiteGroupoid B B' h S hS G))
    (changeBigSiteQuotientMap B B' h S hS G) (changeBigSiteQuotientMap_comp B B' h S hS G)
    (fun α _ => isStronglyCartesian_changeBigSiteQuotientMap_map B B' h S hS G α)

/-- The comparison is a 1-morphism of fibred categories over the enlarged localized big fppf
site. -/
theorem isFibredOneMorphism_changeBigSiteQuotientComparison :
    (Comma.pullbackProj (quotientStack G).p (inclusionOver h S hS)).IsFibredOneMorphism
      (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
      (changeBigSiteQuotientComparison B B' h S hS G) :=
  @PullbackAdjunction.isFibredOneMorphism_leftToRight _ _ _ _ _ _ _ _
    (quotientStack G).p (inclusionOver h S hS)
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
    (isFibered_quotientStack (changeBigSiteGroupoid B B' h S hS G))
    (changeBigSiteQuotientMap B B' h S hS G) (changeBigSiteQuotientMap_comp B B' h S hS G)
    (isFibered_quotientStack G) (hasNonemptyFiniteLimits_bigFppfOver S hS)
    (inclusionOver_preservesLimitsOfShape_of_nonempty h S hS)
    (fun α _ => isStronglyCartesian_changeBigSiteQuotientMap_map B B' h S hS G α)

/-- **The transport of sections on objects of the pointwise presentation**: the composite to the
quotient stack of the pulled-back groupoid sends the universe-lifted `W`-point `w` of the object
space to the `i W`-point obtained by transporting `w`. -/
theorem changeBigSitePrestackMap_obj (W : BigFppfOver B S hS)
    (w : G.objects.obj.obj (op W)) :
    (changeBigSitePrestackMap B B' h S hS G).obj
        ((quotientPrestackEquivalence G).functor.obj ⟨W, w⟩) =
      (pointwiseToQuotientStack (changeBigSiteGroupoid B B' h S hS G)).obj
        ⟨(inclusionOver h S hS).obj W,
          changeBigSiteSectionEquiv B B' h S hS G.objects W w⟩ := rfl

/-- **The comparison on a presentation.** A presentation `(V, φ : V ⟶ i T, ξ)` of the pullback
goes to the chosen pullback along `φ` of the image of `ξ` under the 1-morphism
`[U/R] ⟶ [f⁻¹U/f⁻¹R]`. This is the formula `(T', φ, x) ↦ φ^*(x)` of Stacks 04WX. -/
theorem changeBigSiteQuotientComparison_obj_localization
    (Z : Comma (𝟭 (BigFppfOver B' S (largerContains h hS)))
      ((quotientStack G).p ⋙ inclusionOver h S hS)) :
    (changeBigSiteQuotientComparison B B' h S hS G).obj
        ((Comma.idBaseStronglyCartesian (quotientStack G).p (inclusionOver h S hS)).Q.obj Z)
      = @PullbackAdjunction.leftToRightObj _ _ _ _ _ _ _ _
          (quotientStack G).p (inclusionOver h S hS)
          (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
          (isFibered_quotientStack (changeBigSiteGroupoid B B' h S hS G))
          (changeBigSiteQuotientMap B B' h S hS G)
          (changeBigSiteQuotientMap_comp B B' h S hS G) Z :=
  Functor.congr_obj (@PullbackAdjunction.leftToRight_fac _ _ _ _ _ _ _ _
    (quotientStack G).p (inclusionOver h S hS)
    (quotientStack (changeBigSiteGroupoid B B' h S hS G)).p
    (isFibered_quotientStack (changeBigSiteGroupoid B B' h S hS G))
    (changeBigSiteQuotientMap B B' h S hS G)
    (changeBigSiteQuotientMap_comp B B' h S hS G)
    (fun α _ => isStronglyCartesian_changeBigSiteQuotientMap_map B B' h S hS G α)) Z

end AlgebraicGeometry.Stack

end
