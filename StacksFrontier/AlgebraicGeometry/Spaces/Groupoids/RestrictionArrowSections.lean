module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RestrictionArrowsDerealization
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSections

/-!
# Generalized arrows of a restriction, read in the restricted realization

`Stacks.Groupoids.GroupoidScheme.restrictionArrowsIsoOfIso` identifies the arrow space of the
restriction of the realization of a groupoid scheme with the space represented by the arrow
scheme of the restriction of the groupoid scheme.  This file reads that identification on
*sections*: a morphism of schemes over `S` from an object of the site into the arrow scheme of
the restriction becomes a section of the arrow space of the restricted realization, and its
source, its target and its underlying arrow of the ambient groupoid are the expected ones.

It also transports an open subspace of that arrow space to an open subscheme of the arrow scheme
of the restriction, and says when a generalized arrow is a section of the subspace: exactly when
it lands pointwise in the open subscheme.

Together these turn a statement about an open finite subgroupoid of the restricted realization
into statements about an open subscheme of the arrow scheme of the restriction which are
conditions on points, which is the form
`Stacks.Groupoids.GroupoidScheme.IsArrowSubgroupoid` consumes.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.arrowSection`: the section of the arrow space of the
  restricted realization determined by a generalized arrow of the restriction.
* `Stacks.Groupoids.GroupoidScheme.arrowOpens`: the open subscheme of the arrow scheme of the
  restriction cut out by an open subspace of the arrow space of the restricted realization.

## Main results

* `Stacks.Groupoids.GroupoidScheme.arrowSection_arrowsToArrows`,
  `arrowSection_source` and `arrowSection_target`: the underlying ambient arrow, the source and
  the target of such a section are those of the generalized arrow it came from, the last two up
  to the comparison isomorphism.
* `Stacks.Groupoids.GroupoidScheme.mem_iff_forall_mem_arrowOpens`: a generalized arrow is a
  section of the open subspace exactly when it lands pointwise in the open subscheme.

## Implementation notes

A section of a presheaf represented by a scheme over `S` which the site contains is a morphism of
schemes over `S` out of the test object, by
`AlgebraicGeometry.Space.yonedaSchemePointEquiv`; the three compatibility statements are the
three projections of `restrictionArrowsIsoOfIso` read through that equivalence and
`AlgebraicGeometry.Space.yonedaSchemePointEquiv_map`.

The open subscheme is obtained by pulling the open subspace back along the identification — an
open subspace of a represented space, by
`AlgebraicGeometry.Space.isOpenSubspace_preimage` — and then applying
`AlgebraicGeometry.Space.opensOfOpenSubspace`, which is the open of the representing scheme
attached to an open subspace of a chart.  The membership criterion is
`AlgebraicGeometry.Space.mem_iff_of_isOpenSubspace`.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left) {X : Over S}
  (hX : C.Contains X.left) (p : X ⟶ G.objects) (U' : AlgebraicSpaces C S hS)
  (g : U' ⟶ (G.realization C hS hU hR hP).objects)
  (e : yoneda.obj (schemeSiteObject C hS hX) ≅ U'.obj)
  (he : e.hom ≫ g.hom = yoneda.map (schemeSiteMap C hS hX hU p))
  (hA : C.Contains (pullback p G.target).left)
  (hB : C.Contains (pullback G.source p).left)
  (hRA : C.Contains (AlgebraicGeometry.restrictionArrows G p).left)

/-! ### Sections -/

/-- The underlying morphism of schemes of the section of a represented presheaf attached to a
morphism of schemes over `S`. -/
theorem toScheme_map_yonedaSchemePointEquiv_symm {Y : Over S} (hY : C.Contains Y.left)
    (T : (BigFppfOver C S hS)ᵒᵖ) (a : (siteToOver C hS).obj T.unop ⟶ Y) :
    (BigFppfOver.toScheme C S hS).map ((yonedaSchemePointEquiv C hS hY T).symm a) = a.left :=
  congrArg (fun m : (siteToOver C hS).obj T.unop ⟶ Y => m.left)
    ((siteToOver C hS).map_preimage (Y := schemeSiteObject C hS hY) a)

/-- Acting on a section of a represented presheaf by the Yoneda image of a morphism of schemes
over `S` composes the morphism of schemes it is with that morphism. -/
theorem yonedaSchemePointEquiv_symm_comp {Y Z : Over S} (hY : C.Contains Y.left)
    (hZ : C.Contains Z.left) (f : Y ⟶ Z) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (siteToOver C hS).obj T.unop ⟶ Y) :
    (yoneda.map (schemeSiteMap C hS hY hZ f)).app T
        ((yonedaSchemePointEquiv C hS hY T).symm a) =
      (yonedaSchemePointEquiv C hS hZ T).symm (a ≫ f) := by
  refine (yonedaSchemePointEquiv C hS hZ T).injective ?_
  rw [Equiv.apply_symm_apply, yonedaSchemePointEquiv_map, Equiv.apply_symm_apply]

include he in
/-- **The generalized arrow of the restricted realization attached to a generalized arrow of the
restriction of the groupoid scheme.** -/
noncomputable def arrowSection (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (siteToOver C hS).obj T.unop ⟶ AlgebraicGeometry.restrictionArrows G p) :
    (GroupoidInAlgebraicSpaces.restrictionArrows (G.realization C hS hU hR hP) g).obj.obj T :=
  (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom.app T
    ((yonedaSchemePointEquiv C hS hRA T).symm a)

/-- Evaluating both sides of an equation `f ≫ g = h` of morphisms of presheaves of types at a
section. -/
private theorem app_comp_eq_of_comp_eq {D : Type*} [Category D] {F G H : Dᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {g : G ⟶ H} {h : F ⟶ H} (w : f ≫ g = h) (T : Dᵒᵖ) (x : F.obj T) :
    g.app T (f.app T x) = h.app T x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app w T) x

include he in
/-- The underlying arrow of the ambient groupoid of
`Stacks.Groupoids.GroupoidScheme.arrowSection` is the underlying arrow of the generalized arrow
it came from. -/
theorem arrowSection_arrowsToArrows (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (siteToOver C hS).obj T.unop ⟶ AlgebraicGeometry.restrictionArrows G p) :
    yonedaSchemePointEquiv C hS hR T
        ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows (G.realization C hS hU hR hP)
          g).hom.app T (arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA T a)) =
      a ≫ AlgebraicGeometry.restrictionArrowsToArrows G p := by
  refine (congrArg _ (app_comp_eq_of_comp_eq
    (restrictionArrowsIsoOfIso_hom_comp_arrowsToArrows G C hS hU hR hP hX p U' g e he hA hB hRA)
    T ((yonedaSchemePointEquiv C hS hRA T).symm a))).trans ?_
  erw [yonedaSchemePointEquiv_map, Equiv.apply_symm_apply]

include he in
/-- The source of `Stacks.Groupoids.GroupoidScheme.arrowSection` is the source of the
generalized arrow it came from, read through the comparison isomorphism. -/
theorem arrowSection_source (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (siteToOver C hS).obj T.unop ⟶ AlgebraicGeometry.restrictionArrows G p) :
    (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP) g).hom.app T
        (arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA T a) =
      e.hom.app T ((yonedaSchemePointEquiv C hS hX T).symm
        (a ≫ AlgebraicGeometry.restrictionSource G p)) := by
  refine (app_comp_eq_of_comp_eq
    (restrictionArrowsIsoOfIso_hom_comp_source G C hS hU hR hP hX p U' g e he hA hB hRA)
    T ((yonedaSchemePointEquiv C hS hRA T).symm a)).trans ?_
  erw [NatTrans.comp_app_apply, yonedaSchemePointEquiv_symm_comp]

include he in
/-- The target of `Stacks.Groupoids.GroupoidScheme.arrowSection` is the target of the
generalized arrow it came from, read through the comparison isomorphism. -/
theorem arrowSection_target (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (siteToOver C hS).obj T.unop ⟶ AlgebraicGeometry.restrictionArrows G p) :
    (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP) g).hom.app T
        (arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA T a) =
      e.hom.app T ((yonedaSchemePointEquiv C hS hX T).symm
        (a ≫ AlgebraicGeometry.restrictionTarget G p)) := by
  refine (app_comp_eq_of_comp_eq
    (restrictionArrowsIsoOfIso_hom_comp_target G C hS hU hR hP hX p U' g e he hA hB hRA)
    T ((yonedaSchemePointEquiv C hS hRA T).symm a)).trans ?_
  erw [NatTrans.comp_app_apply, yonedaSchemePointEquiv_symm_comp]

/-! ### The open subscheme cut out by an open subspace -/

variable (A : Subfunctor
    (GroupoidInAlgebraicSpaces.restrictionArrows (G.realization C hS hU hR hP) g).obj)
  (hAo : Space.IsOpenSubspace C S hS A)

include he hAo in
/-- The open subspace pulled back along the identification of the arrow space with a represented
space is an open subspace of that represented space. -/
theorem isOpenSubspace_arrowsPreimage :
    Space.IsOpenSubspace C S hS
      (A.preimage (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom) :=
  Space.isOpenSubspace_preimage C S hS _ A
    (GroupoidInAlgebraicSpaces.restrictionArrows (G.realization C hS hU hR hP) g).property
    (isAlgebraicSpace_yoneda C S hS _) hAo

include he hAo in
/-- **The open subscheme of the arrow scheme of the restriction cut out by an open subspace of
the arrow space of the restricted realization.** -/
noncomputable def arrowOpens : (AlgebraicGeometry.restrictionArrows G p).left.Opens :=
  Space.opensOfOpenSubspace C S hS (schemeSiteObject C hS hRA)
    (A.preimage (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom)
    (isOpenSubspace_arrowsPreimage G C hS hU hR hP hX p U' g e he hA hB hRA A hAo)

include he hAo in
/-- **A generalized arrow of the restriction is a section of the open subspace exactly when it
lands pointwise in the open subscheme it cuts out.** -/
theorem mem_iff_forall_mem_arrowOpens (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (siteToOver C hS).obj T.unop ⟶ AlgebraicGeometry.restrictionArrows G p) :
    arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA T a ∈ A.obj T ↔
      ∀ y, a.left.base y ∈ arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA A hAo := by
  have hmem : arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA T a ∈ A.obj T ↔
      (yonedaSchemePointEquiv C hS hRA T).symm a ∈
        (A.preimage
          (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom).obj
          (Opposite.op T.unop) := Iff.rfl
  have hdict := Space.mem_iff_of_isOpenSubspace C S hS (schemeSiteObject C hS hRA)
    (A.preimage (restrictionArrowsIsoOfIso G C hS hU hR hP hX p U' g e he hA hB hRA).hom)
    (isOpenSubspace_arrowsPreimage G C hS hU hR hP hX p U' g e he hA hB hRA A hAo)
    ((yonedaSchemePointEquiv C hS hRA T).symm a)
  refine hmem.trans (hdict.trans ?_)
  rw [toScheme_map_yonedaSchemePointEquiv_symm]
  exact Iff.rfl

end Stacks.Groupoids.GroupoidScheme

end
