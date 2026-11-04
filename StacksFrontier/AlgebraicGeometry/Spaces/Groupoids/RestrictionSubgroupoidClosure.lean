module

public import StacksFrontier.AlgebraicGeometry.Groupoids.More.IteratedRestriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.OpenArrowSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RealizationInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RestrictionArrowSections
public import StacksFrontier.Deformation.Groupoid.HomInverse

/-!
# An open finite subgroupoid of a restricted realization is a subgroupoid of the restriction

Let `(U, R, s, t, c)` be a groupoid scheme over `S`, let `g : U' ⟶ U` be a morphism to its object
scheme and let `R'` be a groupoid scheme realizing the restriction `R|_{U'}`.  Restricting the
*realization* of the groupoid scheme along the corresponding morphism of algebraic spaces produces
a groupoid in algebraic spaces whose arrow space is identified with the space represented by the
arrow scheme of `R'`, and an open finite subgroupoid of it therefore cuts out an open subscheme of
that arrow scheme, by `Stacks.Groupoids.GroupoidScheme.arrowOpens`.  This file proves that the
open subscheme so obtained is a subgroupoid of `R'` in the sense of
`Stacks.Groupoids.GroupoidScheme.IsArrowSubgroupoid`: it contains every identity arrow, it is
stable under the inverse, and it is stable under the composition of its own composable pairs.

Together with `Stacks.Groupoids.GroupoidScheme.openFiniteSubgroupoidOfOpens` this turns an open
finite subgroupoid of the restriction of a realization — the form in which Stacks 04RY produces
one — into an open finite subgroupoid of a groupoid scheme realizing the restriction, which is the
form in which Stacks 04S0 consumes one.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.subgroupoidOpens`: the open subscheme of the arrow scheme of
  the restriction cut out by an open finite subgroupoid of the restricted realization.

## Main results

* `Stacks.Groupoids.GroupoidScheme.mem_identity_subgroupoidOpens`,
  `mem_inverse_subgroupoidOpens` and `mem_comp_subgroupoidOpens`: the three stability conditions,
  each as a condition on points.
* `Stacks.Groupoids.GroupoidScheme.isArrowSubgroupoid_subgroupoidOpens`: the open, transported to
  the arrow scheme of a groupoid scheme realizing the restriction, is a subgroupoid.

## Implementation notes

Each condition is a condition on the points of a scheme which the site contains — the object
scheme, the open subscheme of arrows, or the scheme of composable pairs of the latter — so by
`Stacks.Groupoids.GroupoidScheme.mem_iff_forall_mem_arrowOpens` it is equivalent to the
corresponding generalized arrow of the restriction being a section of the subgroupoid.  The work
is therefore the identification of the section attached to a structure morphism of `R'` with the
corresponding operation of the restricted realization.

That identification is made on the three data which determine a section of the arrow space of a
restriction: its source, its target and its underlying arrow of the ambient groupoid.  On the
space side a section is determined by them, by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowDataEquiv` and
`RestrictionArrowData.ext`; the three data of the identity arrow, of the inverse and of a
composite are read off from the pointwise groupoid laws and from the fact that the canonical
morphism to the realization preserves the groupoid operations, the realization's own operations
being the Yoneda images of those of the groupoid scheme by
`Stacks.Groupoids.GroupoidScheme.realization_identity_yonedaMap`, `realization_inverse` and
`realizationComp_app`.  On the scheme side the same three data are computed from the fields of
`AlgebraicGeometry.GroupoidScheme.Restriction`, which express the source, the target and the
projection to the ambient arrow scheme of a realization of the restriction in terms of the chosen
iterated fibre product.

That an open finite subgroupoid of a groupoid in algebraic spaces contains the identity arrows and
is stable under the inverse and the composition is not part of its definition: it is a groupoid
only pointwise, through `AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid`'s
field `pointwiseGroupoid`, and its composition is required merely to be the restriction of the
ambient one.  What is used is that the inclusion of the subspace of arrows is then a morphism of
groupoids in presheaves: identities go to identities because an idempotent endo-arrow of the
ambient groupoid is an identity arrow, by
`Deformation.GroupoidInFunctors.identity_eq_of_idempotent`, and inverses go to inverses by
`Deformation.GroupoidInFunctors.Hom.mapArrows_inverseArrow`.

## References

* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
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

/-! ### Identity arrows in a groupoid in presheaves -/

section Identity

universe v

variable {J : Type u} [Category.{v} J] (K : Deformation.GroupoidInFunctors J)

/-- The source of an identity arrow of a groupoid in presheaves is the object it sits at. -/
private theorem identity_source (T : J) (x : K.Evaluation T) :
    K.source.app T (K.identity T x) = x := (K.evaluationArrowEquiv T x x (𝟙 x)).2.1

/-- The target of an identity arrow of a groupoid in presheaves is the object it sits at. -/
private theorem identity_target (T : J) (x : K.Evaluation T) :
    K.target.app T (K.identity T x) = x := (K.evaluationArrowEquiv T x x (𝟙 x)).2.2

/-- The source of a composite in a groupoid in presheaves is the source of its second arrow. -/
private theorem compose_source (T : J) (a b : K.arrows.obj T)
    (h : K.source.app T a = K.target.app T b) :
    K.source.app T (K.compose T a b h) = K.source.app T b :=
  (K.pointwiseData T).source_comp a b h

/-- The target of a composite in a groupoid in presheaves is the target of its first arrow. -/
private theorem compose_target (T : J) (a b : K.arrows.obj T)
    (h : K.source.app T a = K.target.app T b) :
    K.target.app T (K.compose T a b h) = K.target.app T a :=
  (K.pointwiseData T).target_comp a b h

end Identity

/-! ### The subgroupoid as a groupoid in presheaves -/

section Subgroupoid

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
  {H : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B}

/-- An open finite subgroupoid of a groupoid in algebraic spaces, read as a groupoid in
presheaves on the site: the ambient objects, the subspace of arrows, the restricted source and
target and the subgroupoid's own composition. -/
private noncomputable def subgroupoidFunctors
    (P : AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid H) :
    Deformation.GroupoidInFunctors ((BigFppfOver C S hS)ᵒᵖ) where
  objects := H.objects.obj
  arrows := P.arrows.toFunctor
  source := P.arrows.ι ≫ H.source.hom
  target := P.arrows.ι ≫ H.target.hom
  comp := P.comp
  pointwiseGroupoid := P.pointwiseGroupoid

/-- The identity arrow of an open finite subgroupoid at a generalized object is the ambient
identity arrow there: it is an arrow with both endpoints at that object which composes with
itself to itself. -/
private theorem subgroupoid_identity_eq
    (P : AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid H)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : H.objects.obj.obj T) :
    H.toGroupoidInFunctors.identity T x =
      ((subgroupoidFunctors P).identity T x).1 := by
  let F := subgroupoidFunctors P
  let y : F.Evaluation T := x
  let a := F.identity T y
  have hs : H.source.hom.app T a.1 = x := identity_source F T y
  have ht : H.target.hom.app T a.1 = x := identity_target F T y
  have haa : F.compose T a a (hs.trans ht.symm) = a := by
    have hh := F.evaluationArrowEquiv_comp T (𝟙 y) (𝟙 y)
    rw [Category.id_comp] at hh
    exact hh.symm
  exact Deformation.GroupoidInFunctors.identity_eq_of_idempotent H.toGroupoidInFunctors T x a.1
    hs ht ((P.comp_restricts T ⟨(a, a), hs.trans ht.symm⟩).symm.trans
      (congrArg Subtype.val haa))

/-- The inclusion of an open finite subgroupoid into the ambient groupoid, as a morphism of
groupoids in presheaves. -/
private noncomputable def subgroupoidHom
    (P : AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid H) :
    Deformation.GroupoidInFunctors.Hom (subgroupoidFunctors P) H.toGroupoidInFunctors where
  mapObjects := 𝟙 H.objects.obj
  mapArrows := P.arrows.ι
  map_source _ _ := rfl
  map_target _ _ := rfl
  map_id T x := (subgroupoid_identity_eq P T x).symm
  map_comp T a b h := (P.comp_restricts T ⟨(a, b), h⟩).symm

/-- **An open finite subgroupoid contains every identity arrow of the ambient groupoid.** -/
private theorem mem_identity_of_openFiniteSubgroupoid
    (P : AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid H)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : H.objects.obj.obj T) :
    H.toGroupoidInFunctors.identity T x ∈ P.arrows.obj T := by
  rw [subgroupoid_identity_eq P T x]
  exact ((subgroupoidFunctors P).identity T x).2

/-- **An open finite subgroupoid is stable under the inverse of the ambient groupoid.** -/
private theorem mem_inverseArrow_of_openFiniteSubgroupoid
    (P : AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid H)
    (T : (BigFppfOver C S hS)ᵒᵖ) (z : H.arrows.obj.obj T) (hz : z ∈ P.arrows.obj T) :
    Deformation.inverseArrow H.toGroupoidInFunctors T z ∈ P.arrows.obj T := by
  have key : Deformation.inverseArrow H.toGroupoidInFunctors T z =
      (Deformation.inverseArrow (subgroupoidFunctors P) T ⟨z, hz⟩).1 :=
    ((subgroupoidHom P).mapArrows_inverseArrow T ⟨z, hz⟩).symm
  rw [key]
  exact (Deformation.inverseArrow (subgroupoidFunctors P) T ⟨z, hz⟩).2

/-- **An open finite subgroupoid is stable under the composition of the ambient groupoid.** -/
private theorem mem_compose_of_openFiniteSubgroupoid
    (P : AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid H)
    (T : (BigFppfOver C S hS)ᵒᵖ) (z₁ z₂ : H.arrows.obj.obj T)
    (hz₁ : z₁ ∈ P.arrows.obj T) (hz₂ : z₂ ∈ P.arrows.obj T)
    (h : H.source.hom.app T z₁ = H.target.hom.app T z₂) :
    H.toGroupoidInFunctors.compose T z₁ z₂ h ∈ P.arrows.obj T := by
  have key : H.toGroupoidInFunctors.compose T z₁ z₂ h =
      ((subgroupoidFunctors P).compose T ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩ h).1 :=
    (subgroupoidHom P).map_comp T ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩ h
  rw [key]
  exact ((subgroupoidFunctors P).compose T ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩ h).2

end Subgroupoid

/-! ### Generalized arrows of a restricted space-level groupoid -/

section RestrictionExt

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
  {K : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B}
  {V : AlgebraicGeometry.AlgebraicSpaces C S hS}

/-- A section of the arrow space of a restriction is determined by its source, its underlying
arrow of the ambient groupoid and its target. -/
private theorem restrictionArrows_ext (q : V ⟶ K.objects) (T : (BigFppfOver C S hS)ᵒᵖ)
    {z z' : (restrictionArrows K q).obj.obj T}
    (hs : (restrictionSource K q).hom.app T z = (restrictionSource K q).hom.app T z')
    (ha : (restrictionArrowsToArrows K q).hom.app T z =
      (restrictionArrowsToArrows K q).hom.app T z')
    (ht : (restrictionTarget K q).hom.app T z = (restrictionTarget K q).hom.app T z') :
    z = z' := by
  refine (restrictionArrowDataEquiv K q T).injective (RestrictionArrowData.ext ?_ ?_ ?_)
  · rwa [restrictionArrowDataEquiv_source, restrictionArrowDataEquiv_source]
  · rwa [restrictionArrowDataEquiv_arrow, restrictionArrowDataEquiv_arrow]
  · rwa [restrictionArrowDataEquiv_target, restrictionArrowDataEquiv_target]

end RestrictionExt

section RestrictFacts

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
  {K : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B}
  {V : AlgebraicGeometry.AlgebraicSpaces C S hS}

/-- The arrow space of the canonical restriction is the chosen iterated fibre product. -/
private theorem restrict_arrows (q : V ⟶ K.objects) :
    (restrict K q).groupoid.arrows = restrictionArrows K q := rfl

/-- The source of the canonical restriction is the projection to the lift of the source. -/
private theorem restrict_source (q : V ⟶ K.objects) :
    (restrict K q).groupoid.source = restrictionSource K q := rfl

/-- The target of the canonical restriction is the projection to the lift of the target. -/
private theorem restrict_target (q : V ⟶ K.objects) :
    (restrict K q).groupoid.target = restrictionTarget K q := rfl

/-- The map on arrows of the canonical morphism out of the canonical restriction is the
projection to the ambient arrow space. -/
private theorem restrict_mapArrows (q : V ⟶ K.objects) :
    (restrict K q).hom.toGroupoidHom.mapArrows = (restrictionArrowsToArrows K q).hom :=
  (restrict K q).mapArrows_eq

/-- The map on objects of the canonical morphism out of the canonical restriction is the
restricting morphism. -/
private theorem restrict_mapObjects (q : V ⟶ K.objects) :
    (restrict K q).hom.toGroupoidHom.mapObjects = q.hom := (restrict K q).mapObjects_eq

/-- Composition in the canonical restriction is the composition law supplied by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionCompositionData`. -/
private theorem restrict_compose (q : V ⟶ K.objects) (T : (BigFppfOver C S hS)ᵒᵖ)
    (z₁ z₂ : (restrictionArrows K q).obj.obj T)
    (h : (restrictionSource K q).hom.app T z₁ = (restrictionTarget K q).hom.app T z₂) :
    (restrict K q).groupoid.toGroupoidInFunctors.compose T z₁ z₂ h =
      (restrictionCompositionData K q).hom.hom.app T
        ((composableToPullback (restrictionSource K q).hom
          (restrictionTarget K q).hom).app T ⟨(z₁, z₂), h⟩) := rfl

end RestrictFacts

/-! ### The open cut out by a subgroupoid of the restricted realization -/

include he in
/-- **The open subscheme of the arrow scheme of the restriction cut out by an open finite
subgroupoid of the restriction of the realization.**  The subgroupoid's space of arrows is an
open subspace of the arrow space of the restricted realization, which
`Stacks.Groupoids.GroupoidScheme.arrowOpens` reads as an open of the arrow scheme of the
restriction. -/
noncomputable abbrev subgroupoidOpens
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid) :
    (AlgebraicGeometry.restrictionArrows G p).left.Opens :=
  arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA P.arrows P.arrows_open

/-! ### The sections of the subgroupoid -/

include he in
/-- **A generalized arrow of the restriction is a section of the open finite subgroupoid
exactly when it lands pointwise in the open subscheme the subgroupoid cuts out.** -/
private theorem mem_arrows_iff_forall_mem_subgroupoidOpens
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid)
    {Y : Over S} (hY : C.Contains Y.left)
    (a : Y ⟶ AlgebraicGeometry.restrictionArrows G p) :
    arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
        (Opposite.op (schemeSiteObject C hS hY)) a ∈
      P.arrows.obj (Opposite.op (schemeSiteObject C hS hY)) ↔
      ∀ y, a.left.base y ∈ subgroupoidOpens G C hS hU hR hP hX p U' g e he hA hB hRA P :=
  mem_iff_forall_mem_arrowOpens G C hS hU hR hP hX p U' g e he hA hB hRA
    P.arrows P.arrows_open (Opposite.op (schemeSiteObject C hS hY)) a

include he in
/-- The generalized object of the object space of the restricted realization underlying the
source of `Stacks.Groupoids.GroupoidScheme.arrowSection`. -/
private theorem yonedaSchemePointEquiv_objectSection {Y : Over S} (hY : C.Contains Y.left)
    (q : Y ⟶ X) :
    yonedaSchemePointEquiv C hS hU (Opposite.op (schemeSiteObject C hS hY))
        (g.hom.app (Opposite.op (schemeSiteObject C hS hY))
          (e.hom.app (Opposite.op (schemeSiteObject C hS hY))
            ((yonedaSchemePointEquiv C hS hX
              (Opposite.op (schemeSiteObject C hS hY))).symm q))) =
      q ≫ p := by
  have key : g.hom.app (Opposite.op (schemeSiteObject C hS hY))
        (e.hom.app (Opposite.op (schemeSiteObject C hS hY))
          ((yonedaSchemePointEquiv C hS hX
            (Opposite.op (schemeSiteObject C hS hY))).symm q)) =
      (yoneda.map (schemeSiteMap C hS hX hU p)).app
        (Opposite.op (schemeSiteObject C hS hY))
        ((yonedaSchemePointEquiv C hS hX
          (Opposite.op (schemeSiteObject C hS hY))).symm q) :=
    congrArg (fun k : yoneda.obj (schemeSiteObject C hS hX) ⟶
      yoneda.obj (schemeSiteObject C hS hU) =>
      k.app (Opposite.op (schemeSiteObject C hS hY))
        ((yonedaSchemePointEquiv C hS hX
          (Opposite.op (schemeSiteObject C hS hY))).symm q)) he
  rw [key, yonedaSchemePointEquiv_map]
  exact (yonedaSchemePointEquiv C hS hX
    (Opposite.op (schemeSiteObject C hS hY))).apply_symm_apply q =≫ p

/-! ### The ambient arrow underlying the operations of the restricted realization -/

/-- The ambient arrow underlying an identity arrow of the restricted realization is the
identity arrow of the groupoid scheme at the image of the object. -/
private theorem yonedaSchemePointEquiv_arrowsToArrows_identity
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : U'.obj.obj T) :
    yonedaSchemePointEquiv C hS hR T
        ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
            (G.realization C hS hU hR hP) g).hom.app T
          ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            g).groupoid.toGroupoidInFunctors.identity T x)) =
      yonedaSchemePointEquiv C hS hU T (g.hom.app T x) ≫ G.identity := by
  have h1 : (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
          (G.realization C hS hU hR hP) g).hom.app T
        ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
          g).groupoid.toGroupoidInFunctors.identity T x) =
      (yoneda.map (schemeSiteMap C hS hU hR G.identity)).app T (g.hom.app T x) :=
    ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
      g).hom.toGroupoidHom.map_id T x).trans
      (realization_identity_yonedaMap G C hS hU hR hP T _)
  rw [h1]
  exact yonedaSchemePointEquiv_map C hS hU hR G.identity T (g.hom.app T x)

/-- The ambient arrow underlying the inverse of a section of the arrow space of the restricted
realization is the inverse of the ambient arrow underlying that section. -/
private theorem yonedaSchemePointEquiv_arrowsToArrows_inverseArrow
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (z : (GroupoidInAlgebraicSpaces.restrictionArrows
      (G.realization C hS hU hR hP) g).obj.obj T) :
    yonedaSchemePointEquiv C hS hR T
        ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
            (G.realization C hS hU hR hP) g).hom.app T
          (Deformation.inverseArrow (GroupoidInAlgebraicSpaces.restrict
            (G.realization C hS hU hR hP) g).groupoid.toGroupoidInFunctors T z)) =
      yonedaSchemePointEquiv C hS hR T
          ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
            (G.realization C hS hU hR hP) g).hom.app T z) ≫ G.inverse := by
  have h1 : (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
          (G.realization C hS hU hR hP) g).hom.app T
        (Deformation.inverseArrow (GroupoidInAlgebraicSpaces.restrict
          (G.realization C hS hU hR hP) g).groupoid.toGroupoidInFunctors T z) =
      (yoneda.map (schemeSiteMap C hS hR hR G.inverse)).app T
        ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
          (G.realization C hS hU hR hP) g).hom.app T z) :=
    ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
      g).hom.toGroupoidHom.mapArrows_inverseArrow T z).trans
      (realization_inverse G C hS hU hR hP T _)
  rw [h1]
  exact yonedaSchemePointEquiv_map C hS hR hR G.inverse T
    ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
      (G.realization C hS hU hR hP) g).hom.app T z)

/-- Two sections of the arrow space of the restricted realization composable for the restricted
source and target have composable ambient arrows, read as generalized arrows of the groupoid
scheme. -/
private theorem realization_composable
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (z₁ z₂ : (GroupoidInAlgebraicSpaces.restrictionArrows
      (G.realization C hS hU hR hP) g).obj.obj T)
    (w : yonedaSchemePointEquiv C hS hR T
        ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
          (G.realization C hS hU hR hP) g).hom.app T z₁) ≫ G.source =
      yonedaSchemePointEquiv C hS hR T
        ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
          (G.realization C hS hU hR hP) g).hom.app T z₂) ≫ G.target) :
    (G.realization C hS hU hR hP).source.hom.app T
        ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
          (G.realization C hS hU hR hP) g).hom.app T z₁) =
      (G.realization C hS hU hR hP).target.hom.app T
        ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
          (G.realization C hS hU hR hP) g).hom.app T z₂) := by
  refine (yonedaSchemePointEquiv C hS hU T).injective ?_
  exact (yonedaSchemePointEquiv_map C hS hR hU G.source T _).trans
    (w.trans (yonedaSchemePointEquiv_map C hS hR hU G.target T _).symm)

/-- The ambient arrow underlying a composite in the restricted realization is the composite of
the two ambient arrows underlying its factors. -/
private theorem yonedaSchemePointEquiv_arrowsToArrows_compose
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (z₁ z₂ : (GroupoidInAlgebraicSpaces.restrictionArrows
      (G.realization C hS hU hR hP) g).obj.obj T)
    (h : (GroupoidInAlgebraicSpaces.restrictionSource
        (G.realization C hS hU hR hP) g).hom.app T z₁ =
      (GroupoidInAlgebraicSpaces.restrictionTarget
        (G.realization C hS hU hR hP) g).hom.app T z₂)
    (w : yonedaSchemePointEquiv C hS hR T
        ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
          (G.realization C hS hU hR hP) g).hom.app T z₁) ≫ G.source =
      yonedaSchemePointEquiv C hS hR T
        ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
          (G.realization C hS hU hR hP) g).hom.app T z₂) ≫ G.target) :
    yonedaSchemePointEquiv C hS hR T
        ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
            (G.realization C hS hU hR hP) g).hom.app T
          ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
            g).groupoid.toGroupoidInFunctors.compose T z₁ z₂ h)) =
      G.compose
        (yonedaSchemePointEquiv C hS hR T
          ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
            (G.realization C hS hU hR hP) g).hom.app T z₁))
        (yonedaSchemePointEquiv C hS hR T
          ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
            (G.realization C hS hU hR hP) g).hom.app T z₂)) w := by
  have h1 : (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
          (G.realization C hS hU hR hP) g).hom.app T
        ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
          g).groupoid.toGroupoidInFunctors.compose T z₁ z₂ h) =
      (composableToPullback (realizationSource G C hS hU hR).hom
            (realizationTarget G C hS hU hR).hom ≫
          (realizationComp G C hS hU hR hP).hom).app T
        ⟨((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
            (G.realization C hS hU hR hP) g).hom.app T z₁,
          (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
            (G.realization C hS hU hR hP) g).hom.app T z₂),
          realization_composable G C hS hU hR hP U' g T z₁ z₂ w⟩ :=
    ((GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
      g).hom.toGroupoidHom.map_comp T z₁ z₂ h).symm
  rw [h1]
  exact realizationComp_app G C hS hU hR hP T
    ⟨((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
        (G.realization C hS hU hR hP) g).hom.app T z₁,
      (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
        (G.realization C hS hU hR hP) g).hom.app T z₂),
      realization_composable G C hS hU hR hP U' g T z₁ z₂ w⟩ w

/-- A section of the arrow space of the restricted realization is the section of a generalized
arrow of the restriction as soon as it has the right source, target and underlying ambient
arrow. -/
private theorem arrowSection_eq (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (siteToOver C hS).obj T.unop ⟶ AlgebraicGeometry.restrictionArrows G p)
    (z : (GroupoidInAlgebraicSpaces.restrictionArrows (G.realization C hS hU hR hP) g).obj.obj T)
    {q q' : _ ⟶ X} (hq : a ≫ AlgebraicGeometry.restrictionSource G p = q)
    (hq' : a ≫ AlgebraicGeometry.restrictionTarget G p = q')
    (hs : (GroupoidInAlgebraicSpaces.restrictionSource (G.realization C hS hU hR hP) g).hom.app
        T z = e.hom.app T ((yonedaSchemePointEquiv C hS hX T).symm q))
    (ht : (GroupoidInAlgebraicSpaces.restrictionTarget (G.realization C hS hU hR hP) g).hom.app
        T z = e.hom.app T ((yonedaSchemePointEquiv C hS hX T).symm q'))
    (har : yonedaSchemePointEquiv C hS hR T
        ((GroupoidInAlgebraicSpaces.restrictionArrowsToArrows
          (G.realization C hS hU hR hP) g).hom.app T z) =
      a ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) :
    arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA T a = z := by
  subst hq hq'
  exact restrictionArrows_ext g T
    ((arrowSection_source G C hS hU hR hP hX p U' g e he hA hB hRA T a).trans hs.symm)
    ((yonedaSchemePointEquiv C hS hR T).injective
      ((arrowSection_arrowsToArrows G C hS hU hR hP hX p U' g e he hA hB hRA T a).trans
        har.symm))
    ((arrowSection_target G C hS hU hR hP hX p U' g e he hA hB hRA T a).trans ht.symm)

/-! ### The identity -/

include he in
/-- **A generalized arrow of the restriction whose source and target agree and whose underlying
ambient arrow is the identity arrow there is a section of every open finite subgroupoid of the
restricted realization.**  It is the identity arrow of the restricted realization at the
generalized object its source names, and a subgroupoid contains every identity arrow. -/
private theorem mem_arrows_of_identity
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid)
    {Y : Over S} (hY : C.Contains Y.left) (q : Y ⟶ X)
    (a : Y ⟶ AlgebraicGeometry.restrictionArrows G p)
    (hs : a ≫ AlgebraicGeometry.restrictionSource G p = q)
    (ht : a ≫ AlgebraicGeometry.restrictionTarget G p = q)
    (har : a ≫ AlgebraicGeometry.restrictionArrowsToArrows G p = q ≫ p ≫ G.identity) :
    arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
        (Opposite.op (schemeSiteObject C hS hY)) a ∈
      P.arrows.obj (Opposite.op (schemeSiteObject C hS hY)) := by
  have heq : arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
        (Opposite.op (schemeSiteObject C hS hY)) a =
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
        g).groupoid.toGroupoidInFunctors.identity (Opposite.op (schemeSiteObject C hS hY))
        (e.hom.app (Opposite.op (schemeSiteObject C hS hY))
          ((yonedaSchemePointEquiv C hS hX
            (Opposite.op (schemeSiteObject C hS hY))).symm q)) := by
    refine arrowSection_eq G C hS hU hR hP hX p U' g e he hA hB hRA
      (Opposite.op (schemeSiteObject C hS hY)) a _ hs ht ?_ ?_ ?_
    · exact identity_source (GroupoidInAlgebraicSpaces.restrict
        (G.realization C hS hU hR hP) g).groupoid.toGroupoidInFunctors _ _
    · exact identity_target (GroupoidInAlgebraicSpaces.restrict
        (G.realization C hS hU hR hP) g).groupoid.toGroupoidInFunctors _ _
    · refine (yonedaSchemePointEquiv_arrowsToArrows_identity G C hS hU hR hP
        U' g _ _).trans ?_
      rw [yonedaSchemePointEquiv_objectSection G C hS hU hR hP hX p U' g e he hY q]
      exact (Category.assoc _ _ _).trans har.symm
  rw [heq]
  exact mem_identity_of_openFiniteSubgroupoid P _ _

/-! ### The inverse -/

include he in
/-- **A generalized arrow of the restriction whose endpoints are those of a section of an open
finite subgroupoid of the restricted realization exchanged, and whose underlying ambient arrow is
the inverse of that section's, is again a section of the subgroupoid.**  It is the inverse of
that section in the restricted realization, and a subgroupoid is stable under the inverse. -/
private theorem mem_arrows_of_inverse
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid)
    {Y : Over S} (hY : C.Contains Y.left)
    (a b : Y ⟶ AlgebraicGeometry.restrictionArrows G p)
    (hs : a ≫ AlgebraicGeometry.restrictionSource G p =
      b ≫ AlgebraicGeometry.restrictionTarget G p)
    (ht : a ≫ AlgebraicGeometry.restrictionTarget G p =
      b ≫ AlgebraicGeometry.restrictionSource G p)
    (har : a ≫ AlgebraicGeometry.restrictionArrowsToArrows G p =
      (b ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.inverse)
    (hb : arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
        (Opposite.op (schemeSiteObject C hS hY)) b ∈
      P.arrows.obj (Opposite.op (schemeSiteObject C hS hY))) :
    arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
        (Opposite.op (schemeSiteObject C hS hY)) a ∈
      P.arrows.obj (Opposite.op (schemeSiteObject C hS hY)) := by
  have heq : arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
        (Opposite.op (schemeSiteObject C hS hY)) a =
      Deformation.inverseArrow (GroupoidInAlgebraicSpaces.restrict
          (G.realization C hS hU hR hP) g).groupoid.toGroupoidInFunctors
        (Opposite.op (schemeSiteObject C hS hY))
        (arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
          (Opposite.op (schemeSiteObject C hS hY)) b) := by
    refine arrowSection_eq G C hS hU hR hP hX p U' g e he hA hB hRA
      (Opposite.op (schemeSiteObject C hS hY)) a _ hs ht ?_ ?_ ?_
    · exact (Deformation.inverseArrow_source (GroupoidInAlgebraicSpaces.restrict
        (G.realization C hS hU hR hP) g).groupoid.toGroupoidInFunctors _ _).trans
        (arrowSection_target G C hS hU hR hP hX p U' g e he hA hB hRA
          (Opposite.op (schemeSiteObject C hS hY)) b)
    · exact (Deformation.inverseArrow_target (GroupoidInAlgebraicSpaces.restrict
        (G.realization C hS hU hR hP) g).groupoid.toGroupoidInFunctors _ _).trans
        (arrowSection_source G C hS hU hR hP hX p U' g e he hA hB hRA
          (Opposite.op (schemeSiteObject C hS hY)) b)
    · exact (yonedaSchemePointEquiv_arrowsToArrows_inverseArrow G C hS hU hR hP U' g _ _).trans
        ((arrowSection_arrowsToArrows G C hS hU hR hP hX p U' g e he hA hB hRA
          (Opposite.op (schemeSiteObject C hS hY)) b =≫
          G.inverse).trans har.symm)
  rw [heq]
  exact mem_inverseArrow_of_openFiniteSubgroupoid P _ _ hb

/-! ### The composition -/

include he in
/-- **A generalized arrow of the restriction which is the composite of two sections of an open
finite subgroupoid of the restricted realization is again a section of the subgroupoid.** -/
private theorem mem_arrows_of_compose
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid)
    {Y : Over S} (hY : C.Contains Y.left)
    (a b₁ b₂ : Y ⟶ AlgebraicGeometry.restrictionArrows G p)
    (hw : b₁ ≫ AlgebraicGeometry.restrictionSource G p =
      b₂ ≫ AlgebraicGeometry.restrictionTarget G p)
    (w : (b₁ ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.source =
      (b₂ ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.target)
    (hs : a ≫ AlgebraicGeometry.restrictionSource G p =
      b₂ ≫ AlgebraicGeometry.restrictionSource G p)
    (ht : a ≫ AlgebraicGeometry.restrictionTarget G p =
      b₁ ≫ AlgebraicGeometry.restrictionTarget G p)
    (har : a ≫ AlgebraicGeometry.restrictionArrowsToArrows G p =
      G.compose (b₁ ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)
        (b₂ ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) w)
    (hb₁ : arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
        (Opposite.op (schemeSiteObject C hS hY)) b₁ ∈
      P.arrows.obj (Opposite.op (schemeSiteObject C hS hY)))
    (hb₂ : arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
        (Opposite.op (schemeSiteObject C hS hY)) b₂ ∈
      P.arrows.obj (Opposite.op (schemeSiteObject C hS hY))) :
    arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
        (Opposite.op (schemeSiteObject C hS hY)) a ∈
      P.arrows.obj (Opposite.op (schemeSiteObject C hS hY)) := by
  have h₁ := arrowSection_arrowsToArrows G C hS hU hR hP hX p U' g e he hA hB hRA
    (Opposite.op (schemeSiteObject C hS hY)) b₁
  have h₂ := arrowSection_arrowsToArrows G C hS hU hR hP hX p U' g e he hA hB hRA
    (Opposite.op (schemeSiteObject C hS hY)) b₂
  have hcs : (GroupoidInAlgebraicSpaces.restrictionSource
          (G.realization C hS hU hR hP) g).hom.app
        (Opposite.op (schemeSiteObject C hS hY))
        (arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
          (Opposite.op (schemeSiteObject C hS hY)) b₁) =
      (GroupoidInAlgebraicSpaces.restrictionTarget
          (G.realization C hS hU hR hP) g).hom.app
        (Opposite.op (schemeSiteObject C hS hY))
        (arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
          (Opposite.op (schemeSiteObject C hS hY)) b₂) :=
    (arrowSection_source G C hS hU hR hP hX p U' g e he hA hB hRA
          (Opposite.op (schemeSiteObject C hS hY)) b₁).trans
      ((congrArg (fun r => e.hom.app _ ((yonedaSchemePointEquiv C hS hX _).symm r)) hw).trans
        (arrowSection_target G C hS hU hR hP hX p U' g e he hA hB hRA
          (Opposite.op (schemeSiteObject C hS hY)) b₂).symm)
  have hwa := (h₁ =≫ G.source).trans (w.trans (h₂ =≫ G.target).symm)
  have heq : arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
        (Opposite.op (schemeSiteObject C hS hY)) a =
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP)
          g).groupoid.toGroupoidInFunctors.compose
        (Opposite.op (schemeSiteObject C hS hY))
        (arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
          (Opposite.op (schemeSiteObject C hS hY)) b₁)
        (arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
          (Opposite.op (schemeSiteObject C hS hY)) b₂) hcs := by
    refine arrowSection_eq G C hS hU hR hP hX p U' g e he hA hB hRA
      (Opposite.op (schemeSiteObject C hS hY)) a _ hs ht ?_ ?_ ?_
    · exact (compose_source (GroupoidInAlgebraicSpaces.restrict
        (G.realization C hS hU hR hP) g).groupoid.toGroupoidInFunctors _ _ _ hcs).trans
        (arrowSection_source G C hS hU hR hP hX p U' g e he hA hB hRA
          (Opposite.op (schemeSiteObject C hS hY)) b₂)
    · exact (compose_target (GroupoidInAlgebraicSpaces.restrict
        (G.realization C hS hU hR hP) g).groupoid.toGroupoidInFunctors _ _ _ hcs).trans
        (arrowSection_target G C hS hU hR hP hX p U' g e he hA hB hRA
          (Opposite.op (schemeSiteObject C hS hY)) b₁)
    · exact (yonedaSchemePointEquiv_arrowsToArrows_compose G C hS hU hR hP U' g _ _ _ hcs
        hwa).trans ((AlgebraicGeometry.groupoidCompose_arrow_eq _ _ _ _ hwa w h₁ h₂).trans
          har.symm)
  rw [heq]
  exact mem_compose_of_openFiniteSubgroupoid P _ _ _ hb₁ hb₂ hcs

/-! ### The groupoid-scheme side of the comparison -/

variable (R' : AlgebraicGeometry.GroupoidScheme.Restriction G p)

/-- Transporting an arrow of a groupoid scheme realizing the restriction to the chosen iterated
fibre product and taking its source is taking its source in the realization. -/
private theorem eqToHom_comp_restrictionSource :
    eqToHom R'.arrows_eq ≫ AlgebraicGeometry.restrictionSource G p =
      R'.groupoid.source ≫ eqToHom R'.objects_eq := by
  simp only [R'.source_eq, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- Transporting an arrow of a groupoid scheme realizing the restriction to the chosen iterated
fibre product and taking its target is taking its target in the realization. -/
private theorem eqToHom_comp_restrictionTarget :
    eqToHom R'.arrows_eq ≫ AlgebraicGeometry.restrictionTarget G p =
      R'.groupoid.target ≫ eqToHom R'.objects_eq := by
  simp only [R'.target_eq, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- Transporting an arrow of a groupoid scheme realizing the restriction to the chosen iterated
fibre product and projecting to the ambient arrow scheme is the canonical morphism. -/
private theorem eqToHom_comp_restrictionArrowsToArrows :
    eqToHom R'.arrows_eq ≫ AlgebraicGeometry.restrictionArrowsToArrows G p =
      R'.hom.mapArrows := R'.mapArrows_eq.symm

/-- The previous identity, with a further morphism appended. -/
private theorem eqToHom_comp_restrictionArrowsToArrows_comp {Z : Over S} (m : G.arrows ⟶ Z) :
    eqToHom R'.arrows_eq ≫ AlgebraicGeometry.restrictionArrowsToArrows G p ≫ m =
      R'.hom.mapArrows ≫ m := by
  rw [← Category.assoc, eqToHom_comp_restrictionArrowsToArrows]

/-! ### Composable pairs of arrows of an open -/

/-- The two arrows of a composable pair of arrows of an open are composable in the groupoid. -/
private theorem openArrowComposables_condition (W : R'.groupoid.arrows.left.Opens) :
    pullback.fst (openArrowSource W) (openArrowTarget W) ≫
        openOverι R'.groupoid.arrows W ≫ R'.groupoid.source =
      pullback.snd (openArrowSource W) (openArrowTarget W) ≫
        openOverι R'.groupoid.arrows W ≫ R'.groupoid.target := pullback.condition

/-- The first arrow of a composable pair of arrows of an open. -/
private theorem openArrowComposables_fst (W : R'.groupoid.arrows.left.Opens) :
    openArrowComposables W ≫ pullback.fst R'.groupoid.source R'.groupoid.target =
      pullback.fst (openArrowSource W) (openArrowTarget W) ≫ openOverι R'.groupoid.arrows W :=
  pullback.lift_fst _ _ _

/-- The second arrow of a composable pair of arrows of an open. -/
private theorem openArrowComposables_snd (W : R'.groupoid.arrows.left.Opens) :
    openArrowComposables W ≫ pullback.snd R'.groupoid.source R'.groupoid.target =
      pullback.snd (openArrowSource W) (openArrowTarget W) ≫ openOverι R'.groupoid.arrows W :=
  pullback.lift_snd _ _ _

/-- A composable pair of arrows of an open, read in the chosen iterated fibre product, is
composable for the restricted source and target. -/
private theorem openArrowComposables_source_eq_target (W : R'.groupoid.arrows.left.Opens) :
    ((pullback.fst (openArrowSource W) (openArrowTarget W) ≫
        openOverι R'.groupoid.arrows W) ≫ eqToHom R'.arrows_eq) ≫
        AlgebraicGeometry.restrictionSource G p =
      ((pullback.snd (openArrowSource W) (openArrowTarget W) ≫
        openOverι R'.groupoid.arrows W) ≫ eqToHom R'.arrows_eq) ≫
        AlgebraicGeometry.restrictionTarget G p := by
  simp only [Category.assoc, eqToHom_comp_restrictionSource G p R',
    eqToHom_comp_restrictionTarget G p R']
  simpa only [Category.assoc] using
    openArrowComposables_condition G p R' W =≫ eqToHom R'.objects_eq

/-- The ambient arrows underlying a composable pair of arrows of an open are composable. -/
private theorem openArrowComposables_arrows_source_eq_target
    (W : R'.groupoid.arrows.left.Opens) :
    (((pullback.fst (openArrowSource W) (openArrowTarget W) ≫
          openOverι R'.groupoid.arrows W) ≫ eqToHom R'.arrows_eq) ≫
        AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.source =
      (((pullback.snd (openArrowSource W) (openArrowTarget W) ≫
          openOverι R'.groupoid.arrows W) ≫ eqToHom R'.arrows_eq) ≫
        AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.target := by
  simp only [Category.assoc, eqToHom_comp_restrictionArrowsToArrows G p R', R'.hom.map_source,
    R'.hom.map_target]
  simpa only [Category.assoc] using
    openArrowComposables_condition G p R' W =≫ R'.hom.mapObjects

/-- The source of the composite of a composable pair of arrows of an open is the source of the
second arrow. -/
private theorem openArrowComposables_comp_source (W : R'.groupoid.arrows.left.Opens) :
    ((openArrowComposables W ≫ R'.groupoid.comp) ≫ eqToHom R'.arrows_eq) ≫
        AlgebraicGeometry.restrictionSource G p =
      ((pullback.snd (openArrowSource W) (openArrowTarget W) ≫
        openOverι R'.groupoid.arrows W) ≫ eqToHom R'.arrows_eq) ≫
        AlgebraicGeometry.restrictionSource G p := by
  simp only [Category.assoc, eqToHom_comp_restrictionSource G p R']
  rw [← Category.assoc R'.groupoid.comp R'.groupoid.source, R'.groupoid.source_comp,
    Category.assoc, ← Category.assoc (openArrowComposables W),
    openArrowComposables_snd G p R' W, Category.assoc]

/-- The target of the composite of a composable pair of arrows of an open is the target of the
first arrow. -/
private theorem openArrowComposables_comp_target (W : R'.groupoid.arrows.left.Opens) :
    ((openArrowComposables W ≫ R'.groupoid.comp) ≫ eqToHom R'.arrows_eq) ≫
        AlgebraicGeometry.restrictionTarget G p =
      ((pullback.fst (openArrowSource W) (openArrowTarget W) ≫
        openOverι R'.groupoid.arrows W) ≫ eqToHom R'.arrows_eq) ≫
        AlgebraicGeometry.restrictionTarget G p := by
  simp only [Category.assoc, eqToHom_comp_restrictionTarget G p R']
  rw [← Category.assoc R'.groupoid.comp R'.groupoid.target, R'.groupoid.target_comp,
    Category.assoc, ← Category.assoc (openArrowComposables W),
    openArrowComposables_fst G p R' W, Category.assoc]

/-- The two projections of the composable pairs of arrows of an open are composable in the
groupoid. -/
private theorem openArrowComposables_fst_source (W : R'.groupoid.arrows.left.Opens) :
    (openArrowComposables W ≫ pullback.fst R'.groupoid.source R'.groupoid.target) ≫
        R'.groupoid.source =
      (openArrowComposables W ≫ pullback.snd R'.groupoid.source R'.groupoid.target) ≫
        R'.groupoid.target := by
  rw [Category.assoc, Category.assoc, pullback.condition]

/-- The ambient arrows underlying the two projections of the composable pairs of arrows of an
open are composable. -/
private theorem openArrowComposables_mapArrows_source (W : R'.groupoid.arrows.left.Opens) :
    ((openArrowComposables W ≫ pullback.fst R'.groupoid.source R'.groupoid.target) ≫
        R'.hom.mapArrows) ≫ G.source =
      ((openArrowComposables W ≫ pullback.snd R'.groupoid.source R'.groupoid.target) ≫
        R'.hom.mapArrows) ≫ G.target := by
  simp only [Category.assoc, R'.hom.map_source, R'.hom.map_target]
  simpa only [Category.assoc] using
    openArrowComposables_fst_source G p R' W =≫ R'.hom.mapObjects

/-- The ambient arrow underlying the composite of a composable pair of arrows of an open is the
composite of the two underlying ambient arrows. -/
private theorem openArrowComposables_comp_arrowsToArrows (W : R'.groupoid.arrows.left.Opens) :
    ((openArrowComposables W ≫ R'.groupoid.comp) ≫ eqToHom R'.arrows_eq) ≫
        AlgebraicGeometry.restrictionArrowsToArrows G p =
      G.compose
        (((pullback.fst (openArrowSource W) (openArrowTarget W) ≫
            openOverι R'.groupoid.arrows W) ≫ eqToHom R'.arrows_eq) ≫
          AlgebraicGeometry.restrictionArrowsToArrows G p)
        (((pullback.snd (openArrowSource W) (openArrowTarget W) ≫
            openOverι R'.groupoid.arrows W) ≫ eqToHom R'.arrows_eq) ≫
          AlgebraicGeometry.restrictionArrowsToArrows G p)
        (openArrowComposables_arrows_source_eq_target G p R' W) := by
  have wfg := openArrowComposables_fst_source G p R' W
  have hlift : pullback.lift
      (openArrowComposables W ≫ pullback.fst R'.groupoid.source R'.groupoid.target)
      (openArrowComposables W ≫ pullback.snd R'.groupoid.source R'.groupoid.target) wfg =
      openArrowComposables W :=
    pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hmc := R'.hom.map_comp (pullback (openArrowSource W) (openArrowTarget W))
    (openArrowComposables W ≫ pullback.fst R'.groupoid.source R'.groupoid.target)
    (openArrowComposables W ≫ pullback.snd R'.groupoid.source R'.groupoid.target) wfg
    (openArrowComposables_mapArrows_source G p R' W)
  have hcompose : R'.groupoid.compose
      (openArrowComposables W ≫ pullback.fst R'.groupoid.source R'.groupoid.target)
      (openArrowComposables W ≫ pullback.snd R'.groupoid.source R'.groupoid.target) wfg =
      openArrowComposables W ≫ R'.groupoid.comp :=
    hlift =≫ R'.groupoid.comp
  rw [hcompose] at hmc
  have hb₁ : (openArrowComposables W ≫
        pullback.fst R'.groupoid.source R'.groupoid.target) ≫ R'.hom.mapArrows =
      ((pullback.fst (openArrowSource W) (openArrowTarget W) ≫
        openOverι R'.groupoid.arrows W) ≫ eqToHom R'.arrows_eq) ≫
        AlgebraicGeometry.restrictionArrowsToArrows G p := by
    rw [openArrowComposables_fst G p R' W]
    simp only [Category.assoc, eqToHom_comp_restrictionArrowsToArrows G p R']
  have hb₂ : (openArrowComposables W ≫
        pullback.snd R'.groupoid.source R'.groupoid.target) ≫ R'.hom.mapArrows =
      ((pullback.snd (openArrowSource W) (openArrowTarget W) ≫
        openOverι R'.groupoid.arrows W) ≫ eqToHom R'.arrows_eq) ≫
        AlgebraicGeometry.restrictionArrowsToArrows G p := by
    rw [openArrowComposables_snd G p R' W]
    simp only [Category.assoc, eqToHom_comp_restrictionArrowsToArrows G p R']
  refine Eq.trans ?_ (AlgebraicGeometry.groupoidCompose_arrow_eq _ _ _ _
    (openArrowComposables_mapArrows_source G p R' W)
    (openArrowComposables_arrows_source_eq_target G p R' W) hb₁ hb₂)
  rwa [Category.assoc, eqToHom_comp_restrictionArrowsToArrows]

/-! ### Sections of the subgroupoid and points of the open -/

/-- A generalized arrow of the restriction factoring through the open, transported from a
groupoid scheme realizing the restriction, is a section of the subgroupoid. -/
private theorem mem_arrows_of_factors_openOverι
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid)
    (W : R'.groupoid.arrows.left.Opens)
    (hW : ∀ x, x ∈ W ↔ (eqToHom R'.arrows_eq).left.base x ∈
      subgroupoidOpens G C hS hU hR hP hX p U' g e he hA hB hRA P)
    {Y : Over S} (hY : C.Contains Y.left) (k : Y ⟶ openOver R'.groupoid.arrows W) :
    arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
        (Opposite.op (schemeSiteObject C hS hY))
        ((k ≫ openOverι R'.groupoid.arrows W) ≫ eqToHom R'.arrows_eq) ∈
      P.arrows.obj (Opposite.op (schemeSiteObject C hS hY)) := by
  refine (mem_arrows_iff_forall_mem_subgroupoidOpens G C hS hU hR hP hX p U' g e he
    hA hB hRA P hY ((k ≫ openOverι R'.groupoid.arrows W) ≫ eqToHom R'.arrows_eq)).2 fun y => ?_
  have hy : (k ≫ openOverι R'.groupoid.arrows W).left.base y ∈ W :=
    mem_of_eq_comp_ι k.left (by rw [Over.comp_left, openOverι_left]) y
  simpa only [Over.comp_left, Scheme.Hom.comp_apply] using (hW _).1 hy

/-- A generalized arrow of a groupoid scheme realizing the restriction whose transport is a
section of the subgroupoid lands pointwise in the open. -/
private theorem forall_mem_of_mem_arrows
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid)
    (W : R'.groupoid.arrows.left.Opens)
    (hW : ∀ x, x ∈ W ↔ (eqToHom R'.arrows_eq).left.base x ∈
      subgroupoidOpens G C hS hU hR hP hX p U' g e he hA hB hRA P)
    {Y : Over S} (hY : C.Contains Y.left) (f : Y ⟶ R'.groupoid.arrows)
    (hf : arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
        (Opposite.op (schemeSiteObject C hS hY)) (f ≫ eqToHom R'.arrows_eq) ∈
      P.arrows.obj (Opposite.op (schemeSiteObject C hS hY))) :
    ∀ y, f.left.base y ∈ W := fun y => (hW _).2 <| by
  simpa only [Over.comp_left, Scheme.Hom.comp_apply] using
    (mem_arrows_iff_forall_mem_subgroupoidOpens G C hS hU hR hP hX p U' g e he
      hA hB hRA P hY (f ≫ eqToHom R'.arrows_eq)).1 hf y

/-! ### The three conditions -/

include he in
/-- **The first condition: the open contains every identity arrow.**  The identity arrow of the
restriction, read as a generalized arrow of the chosen iterated fibre product, has equal source
and target and underlying ambient arrow the identity arrow of the groupoid scheme there, so it
is the identity arrow of the restricted realization and lies in every open finite subgroupoid. -/
theorem mem_identity_subgroupoidOpens
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid)
    (W : R'.groupoid.arrows.left.Opens)
    (hW : ∀ x, x ∈ W ↔ (eqToHom R'.arrows_eq).left.base x ∈
      subgroupoidOpens G C hS hU hR hP hX p U' g e he hA hB hRA P) :
    ∀ y : R'.groupoid.objects.left, R'.groupoid.identity.left.base y ∈ W := by
  have hY : C.Contains R'.groupoid.objects.left := by rwa [R'.objects_eq]
  have hs : (R'.groupoid.identity ≫ eqToHom R'.arrows_eq) ≫
      AlgebraicGeometry.restrictionSource G p = eqToHom R'.objects_eq := by
    rw [Category.assoc, eqToHom_comp_restrictionSource, ← Category.assoc,
      R'.groupoid.source_identity, Category.id_comp]
  have ht : (R'.groupoid.identity ≫ eqToHom R'.arrows_eq) ≫
      AlgebraicGeometry.restrictionTarget G p = eqToHom R'.objects_eq := by
    rw [Category.assoc, eqToHom_comp_restrictionTarget, ← Category.assoc,
      R'.groupoid.target_identity, Category.id_comp]
  have har : (R'.groupoid.identity ≫ eqToHom R'.arrows_eq) ≫
      AlgebraicGeometry.restrictionArrowsToArrows G p =
      eqToHom R'.objects_eq ≫ p ≫ G.identity := by
    rw [Category.assoc, eqToHom_comp_restrictionArrowsToArrows, ← R'.hom.map_identity,
      R'.mapObjects_eq, Category.assoc]
  exact forall_mem_of_mem_arrows G C hS hU hR hP hX p U' g e he hA hB hRA R' P W hW hY
    R'.groupoid.identity (mem_arrows_of_identity G C hS hU hR hP hX p U' g e he hA hB hRA P hY
      (eqToHom R'.objects_eq) (R'.groupoid.identity ≫ eqToHom R'.arrows_eq) hs ht har)

include he in
/-- **The second condition: the open is stable under the inverse.**  The inverse of an arrow of
the open, read as a generalized arrow of the chosen iterated fibre product, has the endpoints of
that arrow exchanged and underlying ambient arrow the inverse of its, so it is the inverse of
the corresponding section in the restricted realization. -/
theorem mem_inverse_subgroupoidOpens
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid)
    (W : R'.groupoid.arrows.left.Opens)
    (hW : ∀ x, x ∈ W ↔ (eqToHom R'.arrows_eq).left.base x ∈
      subgroupoidOpens G C hS hU hR hP hX p U' g e he hA hB hRA P) :
    ∀ x, (openOverι R'.groupoid.arrows W ≫ R'.groupoid.inverse).left.base x ∈ W := by
  have hYw : C.Contains (openOver R'.groupoid.arrows W).left :=
    AlgebraicGeometry.BigFppfOver.contains_opens C (by rwa [R'.arrows_eq]) W
  have hb : arrowSection G C hS hU hR hP hX p U' g e he hA hB hRA
        (Opposite.op (schemeSiteObject C hS hYw))
        (openOverι R'.groupoid.arrows W ≫ eqToHom R'.arrows_eq) ∈
      P.arrows.obj (Opposite.op (schemeSiteObject C hS hYw)) := by
    convert mem_arrows_of_factors_openOverι G C hS hU hR hP hX p U' g e he hA hB hRA R' P W hW
      hYw (𝟙 _) using 3
    exact (Category.id_comp _).symm
  have hs : ((openOverι R'.groupoid.arrows W ≫ R'.groupoid.inverse) ≫
        eqToHom R'.arrows_eq) ≫ AlgebraicGeometry.restrictionSource G p =
      (openOverι R'.groupoid.arrows W ≫ eqToHom R'.arrows_eq) ≫
        AlgebraicGeometry.restrictionTarget G p := by
    simp only [Category.assoc, eqToHom_comp_restrictionSource G p R',
      eqToHom_comp_restrictionTarget G p R']
    rw [← Category.assoc R'.groupoid.inverse R'.groupoid.source, R'.groupoid.source_inverse]
  have ht : ((openOverι R'.groupoid.arrows W ≫ R'.groupoid.inverse) ≫
        eqToHom R'.arrows_eq) ≫ AlgebraicGeometry.restrictionTarget G p =
      (openOverι R'.groupoid.arrows W ≫ eqToHom R'.arrows_eq) ≫
        AlgebraicGeometry.restrictionSource G p := by
    simp only [Category.assoc, eqToHom_comp_restrictionSource G p R',
      eqToHom_comp_restrictionTarget G p R']
    rw [← Category.assoc R'.groupoid.inverse R'.groupoid.target, R'.groupoid.target_inverse]
  have har : ((openOverι R'.groupoid.arrows W ≫ R'.groupoid.inverse) ≫
        eqToHom R'.arrows_eq) ≫ AlgebraicGeometry.restrictionArrowsToArrows G p =
      ((openOverι R'.groupoid.arrows W ≫ eqToHom R'.arrows_eq) ≫
        AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.inverse := by
    simp only [Category.assoc, eqToHom_comp_restrictionArrowsToArrows G p R']
    rw [AlgebraicGeometry.groupoidHom_map_inverse]
  exact forall_mem_of_mem_arrows G C hS hU hR hP hX p U' g e he hA hB hRA R' P W hW hYw
    (openOverι R'.groupoid.arrows W ≫ R'.groupoid.inverse)
    (mem_arrows_of_inverse G C hS hU hR hP hX p U' g e he hA hB hRA P hYw
      ((openOverι R'.groupoid.arrows W ≫ R'.groupoid.inverse) ≫ eqToHom R'.arrows_eq)
      (openOverι R'.groupoid.arrows W ≫ eqToHom R'.arrows_eq) hs ht har hb)

include he in
/-- **The third condition: the open is stable under the composition of its own composable
pairs.**  The composite of a composable pair of arrows of the open, read as a generalized arrow
of the chosen iterated fibre product, has the source of the second, the target of the first and
underlying ambient arrow the composite of the two underlying ambient arrows, so it is the
composite of the two corresponding sections in the restricted realization. -/
theorem mem_comp_subgroupoidOpens
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid)
    (W : R'.groupoid.arrows.left.Opens)
    (hW : ∀ x, x ∈ W ↔ (eqToHom R'.arrows_eq).left.base x ∈
      subgroupoidOpens G C hS hU hR hP hX p U' g e he hA hB hRA P) :
    ∀ z, (openArrowComposables W ≫ R'.groupoid.comp).left.base z ∈ W := by
  have hYw : C.Contains (openOver R'.groupoid.arrows W).left :=
    AlgebraicGeometry.BigFppfOver.contains_opens C (by rwa [R'.arrows_eq]) W
  have hZ : C.Contains (pullback (openArrowSource W) (openArrowTarget W)).left :=
    C.contains_pullback_left (openArrowSource W) (openArrowTarget W) hYw hYw
  exact forall_mem_of_mem_arrows G C hS hU hR hP hX p U' g e he hA hB hRA R' P W hW hZ
    (openArrowComposables W ≫ R'.groupoid.comp)
    (mem_arrows_of_compose G C hS hU hR hP hX p U' g e he hA hB hRA P hZ
      ((openArrowComposables W ≫ R'.groupoid.comp) ≫ eqToHom R'.arrows_eq)
      ((pullback.fst (openArrowSource W) (openArrowTarget W) ≫
        openOverι R'.groupoid.arrows W) ≫ eqToHom R'.arrows_eq)
      ((pullback.snd (openArrowSource W) (openArrowTarget W) ≫
        openOverι R'.groupoid.arrows W) ≫ eqToHom R'.arrows_eq)
      (openArrowComposables_source_eq_target G p R' W)
      (openArrowComposables_arrows_source_eq_target G p R' W)
      (openArrowComposables_comp_source G p R' W) (openArrowComposables_comp_target G p R' W)
      (openArrowComposables_comp_arrowsToArrows G p R' W)
      (mem_arrows_of_factors_openOverι G C hS hU hR hP hX p U' g e he hA hB hRA R' P W hW hZ _)
      (mem_arrows_of_factors_openOverι G C hS hU hR hP hX p U' g e he hA hB hRA R' P W hW hZ _))

/-! ### The subgroupoid condition -/

include he in
/-- **The open subscheme of the arrow scheme of the restriction cut out by an open finite
subgroupoid of the restriction of the realization is a subgroupoid.**  Transported to the arrow
scheme of a groupoid scheme realizing the restriction, it contains every identity arrow and is
stable under the inverse and under the composition of its own composable pairs. -/
theorem isArrowSubgroupoid_subgroupoidOpens
    (R' : AlgebraicGeometry.GroupoidScheme.Restriction G p)
    (P : GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (GroupoidInAlgebraicSpaces.restrict (G.realization C hS hU hR hP) g).groupoid) :
    Stacks.Groupoids.GroupoidScheme.IsArrowSubgroupoid
      ((eqToHom R'.arrows_eq).left ⁻¹ᵁ
        subgroupoidOpens G C hS hU hR hP hX p U' g e he hA hB hRA P) where
  mem_identity := mem_identity_subgroupoidOpens G C hS hU hR hP hX p U' g e he hA hB hRA R' P
    _ (fun _ => Iff.rfl)
  mem_inverse := mem_inverse_subgroupoidOpens G C hS hU hR hP hX p U' g e he hA hB hRA R' P
    _ (fun _ => Iff.rfl)
  mem_comp := mem_comp_subgroupoidOpens G C hS hU hR hP hX p U' g e he hA hB hRA R' P
    _ (fun _ => Iff.rfl)

end Stacks.Groupoids.GroupoidScheme

end
