module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSpacesDerealization

/-!
# The realization of a groupoid scheme is functorial, and inverse to the de-realization

`Stacks.Groupoids.GroupoidScheme.realization` turns a groupoid scheme over `S` into a groupoid
in algebraic spaces over a big fppf site, and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.derealization` turns a groupoid in algebraic spaces
whose two structure spaces are representable back into a groupoid scheme.  Both were available
on objects only: the realization of a *morphism* of groupoid schemes, and the sense in which the
two constructions are mutually inverse, were stated nowhere.  This file supplies both.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.realizationHom`: **the realization of a morphism of groupoid
  schemes**, a morphism of the two realizations whose maps on objects and on arrows are the
  Yoneda images of the two maps of the given morphism.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.realizationHom` and
  `…realizationIso`: **a groupoid in algebraic spaces presented by schemes of the site is
  isomorphic to the realization of its de-realization**, by the two identifications the
  presentation carries.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.realizationIso`: the same for a groupoid whose
  object and arrow spaces are merely representable, with no further datum.

## Main results

* `Stacks.Groupoids.GroupoidScheme.realization_compose`: the composite of a composable pair of
  generalized points of the realization is the composite of the two generalized arrows of the
  groupoid scheme they name.  This is
  `Stacks.Groupoids.GroupoidScheme.realizationComp_app` read in the vocabulary of
  `Deformation.GroupoidInFunctors.compose`, which is the vocabulary each clause of a morphism of
  groupoids is phrased in.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.derealization_comp`: the
  composition of the groupoid scheme a presentation de-realizes is the de-realized composition.
  The other four structure morphisms are already identified by
  `…derealization_source` and its companions, which hold by definition; the composition does
  not, because `Stacks.Groupoids.GroupoidScheme.ofGroupoidObject` pre-composes with the
  comparison of the chosen fibre product of the source and target with the object of composable
  pairs, and here that comparison is the identity only by the universal property.
* `…SchemePresentation.yonedaSchemePullbackIso_hom_comp_yoneda_comp`: **the de-realized
  composition, read on presheaves, is the comparison of fibre products followed by the
  composition of the groupoid itself.**

## Implementation notes

Both constructions are assembled by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mk'`, so neither has to discharge the identity
clause of `Deformation.GroupoidInFunctors.Hom`: identities in a groupoid are determined by the
composition, and that constructor derives the identity clause from the composition clause.  For
the same reason the comparison is produced as an
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Iso` by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Iso.mk'`, which asks only for the forward morphism
together with inverses of its two maps — here the inverses of the two identifications the
presentation carries.

For the realization of a morphism every clause is an equation between sections of represented
presheaves, and `AlgebraicGeometry.Space.yonedaSchemePointEquiv` turns each into an equation
between morphisms of schemes over `S`, where it is the corresponding clause of the morphism of
groupoid schemes.

For the comparison the composition clause is the only one with content.  Its substance is that
the composition of the realization of the de-realization is, as a morphism of presheaves, the
comparison of fibre products
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.pairComparison` followed by the
composition of the original groupoid: the realization reads a composition through
`AlgebraicGeometry.Space.yonedaSchemePullbackIso`, and the de-realization built its composition
by pre-composing with the inverse of that same identification, so the two cancel.  The clause
then follows from `AlgebraicGeometry.GroupoidInAlgebraicSpaces.comp_app_pair`, because the
composable pair of the realization determined by a composable pair of the groupoid has, under
the comparison, that very pair as its two projections.

The morphism and the isomorphism take the three containment hypotheses of the realization as
arguments rather than reading them off the presentation, which is the form in which a caller has
them — for instance from
`AlgebraicGeometry.Space.Division.contains_descended_objects` and its companions.  They are
propositions, so no generality is gained or lost and nothing has to be transported.

The dictionary leading up to them, by contrast, is stated throughout on the morphisms of
presheaves `yoneda.map (AlgebraicGeometry.Space.schemeSiteMap …)` that the structure morphisms of
the realization unfold to, and never on the realization itself.  The reason is mechanical:
`rw` requires its target to remain type-correct at `implicit` transparency, and the object and
arrow schemes of the de-realization reduce to those of the presentation only at `default`
transparency, so a goal mentioning the realization cannot be rewritten at all.  The bridge to
the realization is therefore made in term mode, where `default` transparency is available —
which is also why `…derealization_comp` is applied through `congrArg` rather than by `rw`.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high)
    AlgebraicGeometry.GroupoidInAlgebraicSpaces.hasPullback_presheaf_groupoidSchemeRealizationComparison
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

section Compose

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left)

/-- **The composite of a composable pair of generalized points of the realization is the
composite of the two generalized arrows of the groupoid scheme they name.**  This is
`Stacks.Groupoids.GroupoidScheme.realizationComp_app` phrased with
`Deformation.GroupoidInFunctors.compose`, which is how each clause of a morphism of groupoids in
algebraic spaces reads its two sides. -/
theorem realization_compose (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (G.realization C hS hU hR hP).arrows.obj.obj T)
    (h : (G.realization C hS hU hR hP).source.hom.app T a =
      (G.realization C hS hU hR hP).target.hom.app T b)
    (w : yonedaSchemePointEquiv C hS hR T a ≫ G.source =
      yonedaSchemePointEquiv C hS hR T b ≫ G.target) :
    yonedaSchemePointEquiv C hS hR T
        ((G.realization C hS hU hR hP).toGroupoidInFunctors.compose T a b h) =
      G.compose (yonedaSchemePointEquiv C hS hR T a) (yonedaSchemePointEquiv C hS hR T b) w :=
  realizationComp_app G C hS hU hR hP T ⟨(a, b), h⟩ w

end Compose

section Functoriality

variable {S : Scheme.{u}} {G H : GroupoidScheme S} (f : Hom G H) (C : BigFppfSite.{u})
  (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left)
  (hU' : C.Contains H.objects.left) (hR' : C.Contains H.arrows.left)
  (hP' : C.Contains (pullback H.source H.target).left)

/-- The Yoneda images of the maps of a morphism of groupoid schemes commute with the Yoneda images
of any two structure morphisms that the morphism intertwines. -/
private theorem yoneda_map_mapArrows_comm (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (yoneda.obj (schemeSiteObject C hS hR)).obj T)
    (g : G.arrows ⟶ G.objects) (g' : H.arrows ⟶ H.objects)
    (hg : f.mapArrows ≫ g' = g ≫ f.mapObjects) :
    (yoneda.map (schemeSiteMap C hS hR' hU' g')).app T
        ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T a) =
      (yoneda.map (schemeSiteMap C hS hU hU' f.mapObjects)).app T
        ((yoneda.map (schemeSiteMap C hS hR hU g)).app T a) := by
  refine (yonedaSchemePointEquiv C hS hU' T).injective ?_
  rw [yonedaSchemePointEquiv_map C hS hR' hU' g' T,
    yonedaSchemePointEquiv_map C hS hR hR' f.mapArrows T a,
    yonedaSchemePointEquiv_map C hS hU hU' f.mapObjects T,
    yonedaSchemePointEquiv_map C hS hR hU g T a, Category.assoc, Category.assoc, hg]

/-- The Yoneda images of the two maps of a morphism of groupoid schemes are compatible with the
sources of the two realizations. -/
theorem realizationHom_map_source (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (G.realization C hS hU hR hP).arrows.obj.obj T) :
    (H.realization C hS hU' hR' hP').source.hom.app T
        ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T a) =
      (yoneda.map (schemeSiteMap C hS hU hU' f.mapObjects)).app T
        ((G.realization C hS hU hR hP).source.hom.app T a) :=
  yoneda_map_mapArrows_comm f C hS hU hR hU' hR' T a G.source H.source f.map_source

/-- The Yoneda images of the two maps of a morphism of groupoid schemes are compatible with the
targets of the two realizations. -/
theorem realizationHom_map_target (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (G.realization C hS hU hR hP).arrows.obj.obj T) :
    (H.realization C hS hU' hR' hP').target.hom.app T
        ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T a) =
      (yoneda.map (schemeSiteMap C hS hU hU' f.mapObjects)).app T
        ((G.realization C hS hU hR hP).target.hom.app T a) :=
  yoneda_map_mapArrows_comm f C hS hU hR hU' hR' T a G.target H.target f.map_target

/-- **The Yoneda image of the map on arrows of a morphism of groupoid schemes is compatible with
the compositions of the two realizations.**  Both sides are read as generalized arrows of the
target groupoid scheme by `Stacks.Groupoids.GroupoidScheme.realization_compose`, where the
equation is the composition clause of the morphism of groupoid schemes. -/
theorem realizationHom_map_comp (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : (G.realization C hS hU hR hP).arrows.obj.obj T)
    (h : (G.realization C hS hU hR hP).source.hom.app T a =
      (G.realization C hS hU hR hP).target.hom.app T b)
    (h' : (H.realization C hS hU' hR' hP').source.hom.app T
        ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T a) =
      (H.realization C hS hU' hR' hP').target.hom.app T
        ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T b)) :
    (H.realization C hS hU' hR' hP').toGroupoidInFunctors.compose T
        ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T a)
        ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T b) h' =
      (yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T
        ((G.realization C hS hU hR hP).toGroupoidInFunctors.compose T a b h) := by
  refine (yonedaSchemePointEquiv C hS hR' T).injective ?_
  have e₁ : yonedaSchemePointEquiv C hS hR' T
        ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T a) =
      yonedaSchemePointEquiv C hS hR T a ≫ f.mapArrows :=
    yonedaSchemePointEquiv_map C hS hR hR' f.mapArrows T a
  have e₂ : yonedaSchemePointEquiv C hS hR' T
        ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T b) =
      yonedaSchemePointEquiv C hS hR T b ≫ f.mapArrows :=
    yonedaSchemePointEquiv_map C hS hR hR' f.mapArrows T b
  have w₀ : yonedaSchemePointEquiv C hS hR T a ≫ G.source =
      yonedaSchemePointEquiv C hS hR T b ≫ G.target := by
    rw [← yonedaSchemePointEquiv_map C hS hR hU G.source T a,
      ← yonedaSchemePointEquiv_map C hS hR hU G.target T b]
    exact congrArg (yonedaSchemePointEquiv C hS hU T) h
  have w₁ : (yonedaSchemePointEquiv C hS hR T a ≫ f.mapArrows) ≫ H.source =
      (yonedaSchemePointEquiv C hS hR T b ≫ f.mapArrows) ≫ H.target := by
    simp only [Category.assoc]
    rw [f.map_source, f.map_target, ← Category.assoc, ← Category.assoc, w₀]
  have w₁' : yonedaSchemePointEquiv C hS hR' T
        ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T a) ≫ H.source =
      yonedaSchemePointEquiv C hS hR' T
        ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T b) ≫ H.target := by
    rw [e₁, e₂]
    exact w₁
  have hcongr : ∀ (x₁ x₂ y₁ y₂ : (siteToOver C hS).obj T.unop ⟶ H.arrows)
      (p : x₁ ≫ H.source = y₁ ≫ H.target) (q : x₂ ≫ H.source = y₂ ≫ H.target),
      x₁ = x₂ → y₁ = y₂ → H.compose x₁ y₁ p = H.compose x₂ y₂ q := by
    intro x₁ x₂ y₁ y₂ p q ex ey
    subst ex
    subst ey
    rfl
  calc yonedaSchemePointEquiv C hS hR' T
        ((H.realization C hS hU' hR' hP').toGroupoidInFunctors.compose T
          ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T a)
          ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T b) h')
      = H.compose
          (yonedaSchemePointEquiv C hS hR' T
            ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T a))
          (yonedaSchemePointEquiv C hS hR' T
            ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T b)) w₁' :=
        realization_compose H C hS hU' hR' hP' T _ _ h' w₁'
    _ = H.compose (yonedaSchemePointEquiv C hS hR T a ≫ f.mapArrows)
          (yonedaSchemePointEquiv C hS hR T b ≫ f.mapArrows) w₁ :=
        hcongr _ _ _ _ w₁' w₁ e₁ e₂
    _ = G.compose (yonedaSchemePointEquiv C hS hR T a)
          (yonedaSchemePointEquiv C hS hR T b) w₀ ≫ f.mapArrows :=
        (f.map_comp ((siteToOver C hS).obj T.unop) _ _ w₀ w₁).symm
    _ = yonedaSchemePointEquiv C hS hR T
          ((G.realization C hS hU hR hP).toGroupoidInFunctors.compose T a b h) ≫ f.mapArrows :=
        congrArg (fun k => k ≫ f.mapArrows)
          (realization_compose G C hS hU hR hP T a b h w₀).symm
    _ = yonedaSchemePointEquiv C hS hR' T
          ((yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows)).app T
            ((G.realization C hS hU hR hP).toGroupoidInFunctors.compose T a b h)) :=
        (yonedaSchemePointEquiv_map C hS hR hR' f.mapArrows T _).symm

/-- **The realization of a morphism of groupoid schemes.**  A morphism of the two realizations
whose map on objects and map on arrows are the Yoneda images of the map on objects and the map on
arrows of the given morphism.

Both realizations are groupoids over the terminal algebraic space of the site over `S`, so being
a morphism over the base is the compatibility of
`AlgebraicGeometry.Space.schemeSiteMapToBase` with composition; and the identity clause is not
asked for at all by `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mk'`. -/
noncomputable def realizationHom :
    AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom (G.realization C hS hU hR hP)
      (H.realization C hS hU' hR' hP') :=
  AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mk'
    (yoneda.map (schemeSiteMap C hS hU hU' f.mapObjects))
    (yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows))
    (realizationHom_map_source f C hS hU hR hP hU' hR' hP')
    (realizationHom_map_target f C hS hU hR hP hU' hR' hP')
    (fun T a b h => realizationHom_map_comp f C hS hU hR hP hU' hR' hP' T a b h _)
    (by
      change yoneda.map (schemeSiteMap C hS hU hU' f.mapObjects) ≫
          yoneda.map (schemeSiteMapToBase C hS hU') = yoneda.map (schemeSiteMapToBase C hS hU)
      rw [← yoneda.map_comp, schemeSiteMap_toBase])
    (by
      change yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows) ≫
          yoneda.map (schemeSiteMapToBase C hS hR') = yoneda.map (schemeSiteMapToBase C hS hR)
      rw [← yoneda.map_comp, schemeSiteMap_toBase])

/-- The map on object spaces of the realization of a morphism of groupoid schemes is the Yoneda
image of its map on objects. -/
@[simp] theorem realizationHom_mapObjects :
    (realizationHom f C hS hU hR hP hU' hR' hP').toGroupoidHom.mapObjects =
      yoneda.map (schemeSiteMap C hS hU hU' f.mapObjects) := rfl

/-- The map on arrow spaces of the realization of a morphism of groupoid schemes is the Yoneda
image of its map on arrows. -/
@[simp] theorem realizationHom_mapArrows :
    (realizationHom f C hS hU hR hP hU' hR' hP').toGroupoidHom.mapArrows =
      yoneda.map (schemeSiteMap C hS hR hR' f.mapArrows) := rfl

end Functoriality

end Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open AlgebraicGeometry.Space

namespace SchemePresentation

section Dictionary

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}
  (P : SchemePresentation G)

/-- **The composition of the groupoid scheme a presentation de-realizes is the de-realized
composition.**  `Stacks.Groupoids.GroupoidScheme.ofGroupoidObject` pre-composes the composition
of a groupoid object with the comparison of the chosen fibre product of its source and target
with its object of composable pairs; here that object *is* the chosen fibre product, and the
comparison is the identity because it commutes with both projections. -/
theorem derealization_comp : P.derealization.comp = P.comp :=
  have hid : (IsPullback.of_hasPullback P.source P.target).isoPullback.inv =
      𝟙 (pullback P.source P.target) :=
    pullback.hom_ext
      (((IsPullback.of_hasPullback P.source P.target).isoPullback_inv_fst).trans
        (Category.id_comp _).symm)
      (((IsPullback.of_hasPullback P.source P.target).isoPullback_inv_snd).trans
        (Category.id_comp _).symm)
  (congrArg (fun k => k ≫ P.comp) hid).trans (Category.id_comp P.comp)

/-- The source of the realization of the de-realization is the source of the groupoid, read
through the two identifications of the presentation. -/
theorem realization_derealization_source_hom :
    (P.derealization.realization C hS P.containsObjects P.containsArrows
        P.containsPairs).source.hom =
      P.arrowsIso.inv ≫ G.source.hom ≫ P.objectsIso.hom :=
  P.yoneda_source

/-- The target of the realization of the de-realization is the target of the groupoid, read
through the two identifications of the presentation. -/
theorem realization_derealization_target_hom :
    (P.derealization.realization C hS P.containsObjects P.containsArrows
        P.containsPairs).target.hom =
      P.arrowsIso.inv ≫ G.target.hom ≫ P.objectsIso.hom :=
  P.yoneda_target

/-- **The composition of the realization of the de-realization, as a morphism of presheaves.**
It is the composition of the groupoid scheme the presentation de-realizes, read on the presheaf
fibre product through `AlgebraicGeometry.Space.yonedaSchemePullbackIso` — the de-realized
composition rather than the composition of the groupoid object underlying it, which is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.derealization_comp`. -/
theorem realization_derealization_comp_hom :
    (P.derealization.realization C hS P.containsObjects P.containsArrows
        P.containsPairs).comp.hom =
      (yonedaSchemePullbackIso C hS P.containsArrows P.containsArrows P.containsObjects
          P.source P.target P.containsPairs).hom ≫
        yoneda.map (schemeSiteMap C hS P.containsPairs P.containsArrows P.comp) :=
  congrArg
    (fun k => (yonedaSchemePullbackIso C hS P.containsArrows P.containsArrows P.containsObjects
        P.source P.target P.containsPairs).hom ≫
      yoneda.map (schemeSiteMap C hS P.containsPairs P.containsArrows k))
    P.derealization_comp

/-- The identification of the arrow space carries the source of the groupoid to the source of the
de-realization, read on presheaves. -/
theorem arrowsIso_hom_comp_yoneda_source :
    P.arrowsIso.hom ≫
        yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.source) =
      G.source.hom ≫ P.objectsIso.hom := by
  rw [P.yoneda_source, Iso.hom_inv_id_assoc]

/-- The identification of the arrow space carries the target of the groupoid to the target of the
de-realization, read on presheaves. -/
theorem arrowsIso_hom_comp_yoneda_target :
    P.arrowsIso.hom ≫
        yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.target) =
      G.target.hom ≫ P.objectsIso.hom := by
  rw [P.yoneda_target, Iso.hom_inv_id_assoc]

/-- **The de-realized composition cancels the identification of the presheaf of the scheme of
composable pairs with the presheaf fibre product.**  The de-realized composition was built by
pre-composing with the inverse of that identification, so what is left is the comparison of
fibre products followed by the composition of the groupoid itself. -/
theorem yonedaSchemePullbackIso_hom_comp_yoneda_comp :
    (yonedaSchemePullbackIso C hS P.containsArrows P.containsArrows P.containsObjects
          P.source P.target P.containsPairs).hom ≫
        yoneda.map (schemeSiteMap C hS P.containsPairs P.containsArrows P.comp) =
      P.pairComparison ≫ compOnPairs G ≫ P.arrowsIso.hom := by
  rw [P.yoneda_comp, Iso.hom_inv_id_assoc]

/-- **A generalized composable pair of the de-realization whose two projections are known is
composed by composing those projections in the groupoid itself.**  The comparison of fibre
products carries the pair to the pair of its projections read through the inverse of the
identification of the arrow space, so
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.comp_app_pair` applies. -/
theorem yoneda_comp_app_of_projections (T : (BigFppfOver C S hS)ᵒᵖ)
    (q : (pullback (yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.source))
      (yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.target))).obj T)
    (a b : G.arrows.obj.obj T)
    (ha : (pullback.fst
        (yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.source))
        (yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.target))).app T q =
      P.arrowsIso.hom.app T a)
    (hb : (pullback.snd
        (yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.source))
        (yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.target))).app T q =
      P.arrowsIso.hom.app T b)
    (h : G.source.hom.app T a = G.target.hom.app T b) :
    ((yonedaSchemePullbackIso C hS P.containsArrows P.containsArrows P.containsObjects
            P.source P.target P.containsPairs).hom ≫
          yoneda.map (schemeSiteMap C hS P.containsPairs P.containsArrows P.comp)).app T q =
      P.arrowsIso.hom.app T (G.toGroupoidInFunctors.compose T a b h) := by
  rw [P.yonedaSchemePullbackIso_hom_comp_yoneda_comp]
  refine congrArg (P.arrowsIso.hom.app T) (comp_app_pair G P.pairComparison T q a b ?_ ?_ h)
  · have hc : (pullback.fst G.source.hom G.target.hom).app T (P.pairComparison.app T q) =
        P.arrowsIso.inv.app T ((pullback.fst
          (yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.source))
          (yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.target))).app T q) :=
      congrArg (fun m => m.app T q) P.pairComparison_comp_fst
    rw [hc, ha]
    exact congrArg (fun m => m.app T a) P.arrowsIso.hom_inv_id
  · have hc : (pullback.snd G.source.hom G.target.hom).app T (P.pairComparison.app T q) =
        P.arrowsIso.inv.app T ((pullback.snd
          (yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.source))
          (yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.target))).app T q) :=
      congrArg (fun m => m.app T q) P.pairComparison_comp_snd
    rw [hc, hb]
    exact congrArg (fun m => m.app T b) P.arrowsIso.hom_inv_id

/-- **The identification of the arrow space carries the composition of the groupoid to the
composition of the realization of the de-realization.**  This is the one clause of the comparison
with content. -/
theorem arrowsIso_hom_realization_compose (T : (BigFppfOver C S hS)ᵒᵖ)
    (a b : G.arrows.obj.obj T) (h : G.source.hom.app T a = G.target.hom.app T b)
    (h' : (yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.source)).app T
        (P.arrowsIso.hom.app T a) =
      (yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.target)).app T
        (P.arrowsIso.hom.app T b)) :
    (P.derealization.realization C hS P.containsObjects P.containsArrows
          P.containsPairs).toGroupoidInFunctors.compose T
        (P.arrowsIso.hom.app T a) (P.arrowsIso.hom.app T b) h' =
      P.arrowsIso.hom.app T (G.toGroupoidInFunctors.compose T a b h) :=
  Eq.trans
    (congrArg (fun m => m.app T
        ((composableToPullback
            (yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.source))
            (yoneda.map (schemeSiteMap C hS P.containsArrows P.containsObjects P.target))).app T
          ⟨(P.arrowsIso.hom.app T a, P.arrowsIso.hom.app T b), h'⟩))
      P.realization_derealization_comp_hom)
    (P.yoneda_comp_app_of_projections T _ a b
      (composableToPullback_fst_app C hS _ _ T _)
      (composableToPullback_snd_app C hS _ _ T _) h)

end Dictionary

section Comparison

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {G : GroupoidInAlgebraicSpaces C S hS (Space.terminalSpace C S hS)}
  (P : SchemePresentation G)
  (hU : C.Contains P.derealization.objects.left)
  (hR : C.Contains P.derealization.arrows.left)
  (hP : C.Contains (pullback P.derealization.source P.derealization.target).left)

/-- **The morphism from a groupoid in algebraic spaces presented by schemes of the site to the
realization of its de-realization.**  Its maps on the object and on the arrow space are the two
identifications the presentation carries; being a morphism over the base is no condition, the
base being the terminal algebraic space of the site over `S`. -/
noncomputable def realizationHom : Hom G (P.derealization.realization C hS hU hR hP) :=
  Hom.mk' P.objectsIso.hom P.arrowsIso.hom
    (fun T a => congrArg (fun m => m.app T a) P.arrowsIso_hom_comp_yoneda_source)
    (fun T a => congrArg (fun m => m.app T a) P.arrowsIso_hom_comp_yoneda_target)
    (fun T a b h => P.arrowsIso_hom_realization_compose T a b h _)
    ((baseTerminal_yonedaIsTerminal C S hS).hom_ext _ _)
    ((baseTerminal_yonedaIsTerminal C S hS).hom_ext _ _)

/-- **A groupoid in algebraic spaces presented by schemes of the site is isomorphic to the
realization of its de-realization.**  This is the precise sense — missing until now — in which
`Stacks.Groupoids.GroupoidScheme.realization` and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.SchemePresentation.derealization` are mutually
inverse.  Only the forward morphism has to be built:
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Iso.mk'` reconstructs the backward one from the
inverses of the two identifications. -/
noncomputable def realizationIso : Iso G (P.derealization.realization C hS hU hR hP) :=
  Iso.mk' (P.realizationHom hU hR hP) P.objectsIso.inv P.arrowsIso.inv
    P.objectsIso.hom_inv_id P.objectsIso.inv_hom_id
    P.arrowsIso.hom_inv_id P.arrowsIso.inv_hom_id

end Comparison

end SchemePresentation

section Representable

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **A groupoid in algebraic spaces whose object and arrow spaces are representable is
isomorphic to the realization of its de-realization.**  No datum beyond representability of the
two structure spaces is needed: the presentation is the one representability supplies, and the
isomorphism on each space is the identification of that space with the presheaf its chosen
representing scheme represents. -/
noncomputable def realizationIso
    (G : GroupoidInAlgebraicSpaces C S hS (Space.terminalSpace C S hS))
    [G.objects.obj.IsRepresentable] [G.arrows.obj.IsRepresentable]
    (hU : C.Contains (derealization G).objects.left)
    (hR : C.Contains (derealization G).arrows.left)
    (hP : C.Contains (pullback (derealization G).source (derealization G).target).left) :
    Iso G ((derealization G).realization C hS hU hR hP) :=
  (SchemePresentation.ofIsRepresentable G).realizationIso hU hR hP

end Representable

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
