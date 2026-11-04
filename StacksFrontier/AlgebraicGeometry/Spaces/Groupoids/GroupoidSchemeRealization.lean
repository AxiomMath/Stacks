module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces

/-!
# Realizing a groupoid scheme as a groupoid in algebraic spaces

A groupoid scheme over `S` in the sense of Stacks 0231 is a groupoid object in the category of
schemes over `S`; a groupoid in algebraic spaces in the sense of Stacks 043W is a groupoid object
in the category of algebraic spaces over a big fppf site. If a big fppf site contains the object
scheme, the arrow scheme and the scheme of composable pairs of a groupoid scheme, then the
presheaves represented by those three schemes assemble into a groupoid in algebraic spaces over
the terminal algebraic space, whose source, target and composition are the images under Yoneda
of the source, target and composition of the groupoid scheme.

## Main definitions

* `AlgebraicGeometry.Space.siteToOver`: the comparison functor from the big fppf site over `S`
  to schemes over `S`, which is fully faithful.
* `AlgebraicGeometry.Space.schemeSiteObject` and `AlgebraicGeometry.Space.schemeSiteMap`: a
  scheme over `S`, respectively a morphism of such, regarded in the site.
* `AlgebraicGeometry.Space.yonedaSchemePointEquiv`: a section of the presheaf represented by a
  scheme over `S` is the same thing as a morphism of schemes over `S`.
* `AlgebraicGeometry.Space.yonedaSchemePullbackIso`: Yoneda carries a fibre product of schemes
  over `S` that the site contains to the fibre product of presheaves.
* `Deformation.PointwiseGroupoid.ofEquiv`: transport of a pointwise groupoid along bijections
  of the sets of objects and of arrows.
* `Stacks.Groupoids.GroupoidScheme.pointwiseGroupoidEvaluation`: the groupoid of generalized
  points of a groupoid scheme, in the pointwise vocabulary of Stacks 06K3.
* `Stacks.Groupoids.GroupoidScheme.realization`: the groupoid in algebraic spaces represented
  by a groupoid scheme.

## Main results

* `Stacks.Groupoids.GroupoidScheme.realization_objects`,
  `Stacks.Groupoids.GroupoidScheme.realization_arrows`,
  `Stacks.Groupoids.GroupoidScheme.realization_source`,
  `Stacks.Groupoids.GroupoidScheme.realization_target` and
  `Stacks.Groupoids.GroupoidScheme.realization_comp` identify the structure spaces and the
  structure morphisms of the realization with the Yoneda images of those of the groupoid
  scheme.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w u

namespace Deformation.PointwiseGroupoid

/-- Transport a pointwise groupoid along a bijection of the set of objects and a bijection of
the set of arrows which together carry the source, target and composition maps to the given
ones. -/
noncomputable def ofEquiv {U R U' R' : Type w}
    {source target : R → U} {comp : {p : R × R // source p.1 = target p.2} → R}
    {source' target' : R' → U'}
    {comp' : {p : R' × R' // source' p.1 = target' p.2} → R'}
    (H : Deformation.PointwiseGroupoid source target comp)
    (eU : U' ≃ U) (eR : R' ≃ R)
    (hs : ∀ a, eU (source' a) = source (eR a))
    (ht : ∀ a, eU (target' a) = target (eR a))
    (hc : ∀ p : {p : R' × R' // source' p.1 = target' p.2},
      eR (comp' p) = comp ⟨(eR p.1.1, eR p.1.2), by rw [← hs, ← ht, p.2]⟩) :
    Deformation.PointwiseGroupoid source' target' comp' := by
  letI : Groupoid.{w} U := H.groupoid
  refine
    { groupoid :=
      { Hom := fun x y => (eU x ⟶ eU y)
        id := fun x => 𝟙 (eU x)
        comp := fun f g => f ≫ g
        id_comp := fun f => Category.id_comp f
        comp_id := fun f => Category.comp_id f
        assoc := fun f g h => Category.assoc f g h
        inv := fun f => Groupoid.inv f
        inv_comp := fun f => Groupoid.inv_comp f
        comp_inv := fun f => Groupoid.comp_inv f }
      arrowEquiv := fun x y => (H.arrowEquiv (eU x) (eU y)).trans
        { toFun := fun a => ⟨eR.symm a.1, eU.injective (by rw [hs, Equiv.apply_symm_apply, a.2.1]),
            eU.injective (by rw [ht, Equiv.apply_symm_apply, a.2.2])⟩
          invFun := fun a => ⟨eR a.1, by rw [← hs, a.2.1], by rw [← ht, a.2.2]⟩
          left_inv := fun a => Subtype.ext (eR.apply_symm_apply a.1)
          right_inv := fun a => Subtype.ext (eR.symm_apply_apply a.1) }
      comp_eq := ?_ }
  intro x y z g f
  apply eR.injective
  rw [hc]
  refine Eq.trans ?_ ((H.comp_eq g f).trans (congrArg comp (Subtype.ext (Prod.ext ?_ ?_))))
  · exact Equiv.apply_symm_apply eR _
  · exact (Equiv.apply_symm_apply eR _).symm
  · exact (Equiv.apply_symm_apply eR _).symm

end Deformation.PointwiseGroupoid

namespace Stacks.Groupoids.GroupoidScheme

/-- The groupoid of generalized points of a groupoid scheme over a test scheme, written in the
pointwise vocabulary of Stacks 06K3: the arrows with prescribed source and target are the
morphisms of `Stacks.Groupoids.GroupoidScheme.evaluationGroupoid`, and the composition is
`Stacks.Groupoids.GroupoidScheme.compose`. -/
noncomputable def pointwiseGroupoidEvaluation {S : Scheme.{u}} (G : GroupoidScheme S)
    (T : Over S) :
    Deformation.PointwiseGroupoid
      (fun a : T ⟶ G.arrows => a ≫ G.source)
      (fun a : T ⟶ G.arrows => a ≫ G.target)
      (fun p => G.compose p.1.1 p.1.2 p.2) where
  groupoid := G.evaluationGroupoid T
  arrowEquiv _x _y :=
    { toFun := fun f => ⟨f.arrow, f.source_eq, f.target_eq⟩
      invFun := fun a => ⟨a.1, a.2.1, a.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  comp_eq _ _ := rfl

end Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) {S : Scheme.{u}} (hS : C.Contains S)

/-- The big fppf site over `S`, regarded in schemes over `S`: an object of the site is a scheme
of the site with a morphism to `S`, and is sent to that scheme with that morphism. -/
def siteToOver : BigFppfOver C S hS ⥤ Over S where
  obj T := Over.mk (C.inclusion.map T.hom)
  map f := Over.homMk (C.inclusion.map f.left) (congrArg C.inclusion.map f.w)
  map_id T := by
    apply Over.OverMorphism.ext
    simp
  map_comp f g := by
    apply Over.OverMorphism.ext
    simp

/-- The comparison functor from the big fppf site over `S` to schemes over `S` is full. -/
instance : (siteToOver C hS).Full where
  map_surjective f := by
    dsimp [siteToOver] at f
    refine ⟨Over.homMk (C.inclusion.preimage f.left) (C.inclusion.map_injective ?_),
      Over.OverMorphism.ext (C.inclusion.map_preimage f.left)⟩
    rw [Functor.map_comp, Functor.map_preimage]
    exact f.w

/-- The comparison functor from the big fppf site over `S` to schemes over `S` is faithful. -/
instance : (siteToOver C hS).Faithful where
  map_injective h := Over.OverMorphism.ext (C.inclusion.map_injective (congrArg Over.Hom.left h))

/-- A scheme over `S` which the site contains, regarded as an object of the site over `S`. -/
def schemeSiteObject {X : Over S} (hX : C.Contains X.left) : BigFppfOver C S hS :=
  Over.mk (⟨X.hom⟩ : C.obj hX ⟶ C.obj hS)

/-- A morphism of schemes over `S` between two schemes which the site contains, regarded as a
morphism of the site over `S`. -/
def schemeSiteMap {X Y : Over S} (hX : C.Contains X.left) (hY : C.Contains Y.left)
    (f : X ⟶ Y) : schemeSiteObject C hS hX ⟶ schemeSiteObject C hS hY :=
  Over.homMk (⟨f.left⟩ : C.obj hX ⟶ C.obj hY) (by ext; exact f.w)

/-- The comparison functor returns a scheme over `S` regarded in the site unchanged. -/
theorem siteToOver_obj_schemeSiteObject {X : Over S} (hX : C.Contains X.left) :
    (siteToOver C hS).obj (schemeSiteObject C hS hX) = X := rfl

/-- The comparison functor returns a morphism of schemes over `S` regarded in the site
unchanged. -/
theorem siteToOver_map_schemeSiteMap {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (f : X ⟶ Y) :
    (siteToOver C hS).map (schemeSiteMap C hS hX hY f) = f :=
  Over.OverMorphism.ext rfl

/-- Regarding morphisms of schemes over `S` in the site is compatible with composition. -/
theorem schemeSiteMap_comp {X Y Z : Over S} (hX : C.Contains X.left) (hY : C.Contains Y.left)
    (hZ : C.Contains Z.left) (f : X ⟶ Y) (g : Y ⟶ Z) :
    schemeSiteMap C hS hX hZ (f ≫ g) =
      schemeSiteMap C hS hX hY f ≫ schemeSiteMap C hS hY hZ g :=
  Over.OverMorphism.ext rfl

/-- The structure morphism of a scheme over `S` which the site contains, as a morphism of the
site to its terminal object. -/
def schemeSiteMapToBase {X : Over S} (hX : C.Contains X.left) :
    schemeSiteObject C hS hX ⟶ Over.mk (𝟙 (C.obj hS)) :=
  Over.homMk (⟨X.hom⟩ : C.obj hX ⟶ C.obj hS) (by simp [schemeSiteObject])

/-- Every morphism of the site coming from a morphism of schemes over `S` is a morphism over
the terminal object. -/
theorem schemeSiteMap_toBase {X Y : Over S} (hX : C.Contains X.left) (hY : C.Contains Y.left)
    (f : X ⟶ Y) :
    schemeSiteMap C hS hX hY f ≫ schemeSiteMapToBase C hS hY = schemeSiteMapToBase C hS hX :=
  Over.OverMorphism.ext (C.inclusion.map_injective f.w)

/-- A section over a test object of the presheaf represented by a scheme over `S` is the same
thing as a morphism of schemes over `S` from the test object. -/
noncomputable def yonedaSchemePointEquiv {X : Over S} (hX : C.Contains X.left)
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    (yoneda.obj (schemeSiteObject C hS hX)).obj T ≃ ((siteToOver C hS).obj T.unop ⟶ X) where
  toFun a := (siteToOver C hS).map a
  invFun g := (siteToOver C hS).preimage g
  left_inv a := (siteToOver C hS).map_injective (by rw [Functor.map_preimage])
  right_inv g := (siteToOver C hS).map_preimage (Y := schemeSiteObject C hS hX) g

/-- Under `AlgebraicGeometry.Space.yonedaSchemePointEquiv`, acting by the Yoneda image of a
morphism of schemes over `S` is composing with that morphism. -/
theorem yonedaSchemePointEquiv_map {X Y : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (f : X ⟶ Y) (T : (BigFppfOver C S hS)ᵒᵖ)
    (a : (yoneda.obj (schemeSiteObject C hS hX)).obj T) :
    yonedaSchemePointEquiv C hS hY T ((yoneda.map (schemeSiteMap C hS hX hY f)).app T a) =
      yonedaSchemePointEquiv C hS hX T a ≫ f := by
  change (siteToOver C hS).map (a ≫ schemeSiteMap C hS hX hY f) = (siteToOver C hS).map a ≫ f
  rw [Functor.map_comp, siteToOver_map_schemeSiteMap]
  rfl

/-- A fibre product of schemes over `S` which the site contains, regarded in the site, with its
two projections. -/
noncomputable def schemeSitePullbackCone {X Y Z : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (hZ : C.Contains Z.left) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hP : C.Contains (pullback f g).left) :
    PullbackCone (schemeSiteMap C hS hX hZ f) (schemeSiteMap C hS hY hZ g) :=
  PullbackCone.mk (schemeSiteMap C hS hP hX (pullback.fst f g))
    (schemeSiteMap C hS hP hY (pullback.snd f g))
    (by rw [← schemeSiteMap_comp, ← schemeSiteMap_comp, pullback.condition])

/-- The square `AlgebraicGeometry.Space.schemeSitePullbackCone` is a pullback square in the
site. -/
noncomputable def schemeSitePullbackCone_isLimit {X Y Z : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (hZ : C.Contains Z.left) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hP : C.Contains (pullback f g).left) :
    IsLimit (schemeSitePullbackCone C hS hX hY hZ f g hP) := by
  let F := siteToOver C hS
  let c := schemeSitePullbackCone C hS hX hY hZ f g hP
  have hpm : F.map c.fst = pullback.fst f g :=
    siteToOver_map_schemeSiteMap C hS hP hX (pullback.fst f g)
  have hqm : F.map c.snd = pullback.snd f g :=
    siteToOver_map_schemeSiteMap C hS hP hY (pullback.snd f g)
  refine PullbackCone.isLimitAux' c fun s => ?_
  have h : F.map s.fst ≫ f = F.map s.snd ≫ g := by
    simpa only [F, F.map_comp, siteToOver_map_schemeSiteMap, siteToOver_obj_schemeSiteObject] using
      congrArg F.map s.condition
  let q := pullback.lift (F.map s.fst) (F.map s.snd) h
  have hobj : F.obj c.pt = pullback f g :=
    siteToOver_obj_schemeSiteObject C hS (X := pullback f g) hP
  cases hobj
  let l := F.preimage (X := s.pt) (Y := c.pt) q
  have hmapl : F.map l = q := F.map_preimage (X := s.pt) (Y := c.pt) q
  have facL : l ≫ c.fst = s.fst :=
    F.map_injective (by rw [F.map_comp, hmapl, hpm]; exact pullback.lift_fst _ _ _)
  have facR : l ≫ c.snd = s.snd :=
    F.map_injective (by rw [F.map_comp, hmapl, hqm]; exact pullback.lift_snd _ _ _)
  refine ⟨l, facL, facR, fun hmL hmR => ?_⟩
  apply F.map_injective
  apply pullback.hom_ext
  · have h := congrArg F.map (hmL.trans facL.symm)
    rwa [F.map_comp, F.map_comp, hpm] at h
  · have h := congrArg F.map (hmR.trans facR.symm)
    rwa [F.map_comp, F.map_comp, hqm] at h

/-- Yoneda carries a fibre product of schemes over `S` which the site contains to the fibre
product of the represented presheaves. -/
noncomputable def yonedaSchemePullbackIso {X Y Z : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (hZ : C.Contains Z.left) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hP : C.Contains (pullback f g).left) :
    pullback (yoneda.map (schemeSiteMap C hS hX hZ f))
        (yoneda.map (schemeSiteMap C hS hY hZ g)) ≅
      yoneda.obj (schemeSiteObject C hS hP) :=
  let c := schemeSitePullbackCone C hS hX hY hZ f g hP
  let hc := (c.isLimitMapConeEquiv yoneda).1
    (isLimitOfPreserves yoneda (schemeSitePullbackCone_isLimit C hS hX hY hZ f g hP))
  (pullback.isLimit _ _).conePointUniqueUpToIso hc

/-- The identification of `AlgebraicGeometry.Space.yonedaSchemePullbackIso` is compatible with
the first projection. -/
theorem yonedaSchemePullbackIso_hom_fst {X Y Z : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (hZ : C.Contains Z.left) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hP : C.Contains (pullback f g).left) :
    (yonedaSchemePullbackIso C hS hX hY hZ f g hP).hom ≫
        yoneda.map (schemeSiteMap C hS hP hX (pullback.fst f g)) =
      pullback.fst (yoneda.map (schemeSiteMap C hS hX hZ f))
        (yoneda.map (schemeSiteMap C hS hY hZ g)) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (pullback.isLimit _ _) _ WalkingCospan.left

/-- The identification of `AlgebraicGeometry.Space.yonedaSchemePullbackIso` is compatible with
the second projection. -/
theorem yonedaSchemePullbackIso_hom_snd {X Y Z : Over S} (hX : C.Contains X.left)
    (hY : C.Contains Y.left) (hZ : C.Contains Z.left) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hP : C.Contains (pullback f g).left) :
    (yonedaSchemePullbackIso C hS hX hY hZ f g hP).hom ≫
        yoneda.map (schemeSiteMap C hS hP hY (pullback.snd f g)) =
      pullback.snd (yoneda.map (schemeSiteMap C hS hX hZ f))
        (yoneda.map (schemeSiteMap C hS hY hZ g)) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (pullback.isLimit _ _) _ WalkingCospan.right

/-- The first component of a composable pair of arrows, read through the comparison with the
presheaf fibre product. -/
theorem composableToPullback_fst_app
    {U R : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (s t : R ⟶ U) (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows U R s t).obj T) :
    (pullback.fst s t).app T ((composableToPullback s t).app T p) = p.1.1 := by
  change ((composableToPullback s t ≫ pullback.fst s t).app T) p = _
  simp only [composableToPullback, pullback.lift_fst]
  rfl

/-- The second component of a composable pair of arrows, read through the comparison with the
presheaf fibre product. -/
theorem composableToPullback_snd_app
    {U R : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (s t : R ⟶ U) (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows U R s t).obj T) :
    (pullback.snd s t).app T ((composableToPullback s t).app T p) = p.1.2 := by
  change ((composableToPullback s t ≫ pullback.snd s t).app T) p = _
  simp only [composableToPullback, pullback.lift_snd]
  rfl

end AlgebraicGeometry.Space

namespace Stacks.Groupoids.GroupoidScheme

open AlgebraicGeometry.Space

variable {S : Scheme.{u}} (G : GroupoidScheme S) (C : BigFppfSite.{u}) (hS : C.Contains S)
  (hU : C.Contains G.objects.left) (hR : C.Contains G.arrows.left)
  (hP : C.Contains (pullback G.source G.target).left)

/-- The terminal algebraic space of the site over `S`, which is the base of the realization of
a groupoid scheme. -/
noncomputable abbrev realizationBase : AlgebraicSpaces C S hS :=
  ⟨yoneda.obj (Over.mk (𝟙 (C.obj hS))), isAlgebraicSpace_yoneda C S hS _⟩

/-- The object space of the realization of a groupoid scheme. -/
noncomputable abbrev realizationObjects : AlgebraicSpaces C S hS :=
  ⟨yoneda.obj (schemeSiteObject C hS hU), isAlgebraicSpace_yoneda C S hS _⟩

/-- The arrow space of the realization of a groupoid scheme. -/
noncomputable abbrev realizationArrows : AlgebraicSpaces C S hS :=
  ⟨yoneda.obj (schemeSiteObject C hS hR), isAlgebraicSpace_yoneda C S hS _⟩

/-- The source morphism of the realization of a groupoid scheme. -/
noncomputable abbrev realizationSource :
    realizationArrows G C hS hR ⟶ realizationObjects G C hS hU :=
  ObjectProperty.homMk (yoneda.map (schemeSiteMap C hS hR hU G.source))

/-- The target morphism of the realization of a groupoid scheme. -/
noncomputable abbrev realizationTarget :
    realizationArrows G C hS hR ⟶ realizationObjects G C hS hU :=
  ObjectProperty.homMk (yoneda.map (schemeSiteMap C hS hR hU G.target))

/-- The composition morphism of the realization of a groupoid scheme: the Yoneda image of the
composition of the groupoid scheme, read on the presheaf fibre product through
`AlgebraicGeometry.Space.yonedaSchemePullbackIso`. -/
noncomputable abbrev realizationComp :
    AlgebraicSpaces.fiberProduct C S hS (realizationSource G C hS hU hR)
        (realizationTarget G C hS hU hR) ⟶
      realizationArrows G C hS hR :=
  ObjectProperty.homMk
    ((yonedaSchemePullbackIso C hS hR hR hU G.source G.target hP).hom ≫
      yoneda.map (schemeSiteMap C hS hP hR G.comp))

/-- On sections over a test object, the composition of the realization is the composition of
generalized points of the groupoid scheme. -/
theorem realizationComp_app (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows (realizationObjects G C hS hU).obj
      (realizationArrows G C hS hR).obj (realizationSource G C hS hU hR).hom
      (realizationTarget G C hS hU hR).hom).obj T)
    (w : yonedaSchemePointEquiv C hS hR T p.1.1 ≫ G.source =
      yonedaSchemePointEquiv C hS hR T p.1.2 ≫ G.target) :
    yonedaSchemePointEquiv C hS hR T
        ((composableToPullback (realizationSource G C hS hU hR).hom
          (realizationTarget G C hS hU hR).hom ≫
            (realizationComp G C hS hU hR hP).hom).app T p) =
      G.compose (yonedaSchemePointEquiv C hS hR T p.1.1)
        (yonedaSchemePointEquiv C hS hR T p.1.2) w := by
  have hstep : ((composableToPullback (realizationSource G C hS hU hR).hom
          (realizationTarget G C hS hU hR).hom ≫
          (realizationComp G C hS hU hR hP).hom).app T) p =
      (yoneda.map (schemeSiteMap C hS hP hR G.comp)).app T
        ((yonedaSchemePullbackIso C hS hR hR hU G.source G.target hP).hom.app T
          ((composableToPullback (realizationSource G C hS hU hR).hom
            (realizationTarget G C hS hU hR).hom).app T p)) := rfl
  rw [hstep, yonedaSchemePointEquiv_map]
  refine congrArg (fun k => k ≫ G.comp) ?_
  have key : ∀ (pr : pullback G.source G.target ⟶ G.arrows)
      (π : pullback (yoneda.map (schemeSiteMap C hS hR hU G.source))
        (yoneda.map (schemeSiteMap C hS hR hU G.target)) ⟶
        yoneda.obj (schemeSiteObject C hS hR)) (a : (yoneda.obj (schemeSiteObject C hS hR)).obj T),
      (yonedaSchemePullbackIso C hS hR hR hU G.source G.target hP).hom ≫
        yoneda.map (schemeSiteMap C hS hP hR pr) = π →
      π.app T ((composableToPullback (realizationSource G C hS hU hR).hom
        (realizationTarget G C hS hU hR).hom).app T p) = a →
      yonedaSchemePointEquiv C hS hP T
        ((yonedaSchemePullbackIso C hS hR hR hU G.source G.target hP).hom.app T
          ((composableToPullback (realizationSource G C hS hU hR).hom
            (realizationTarget G C hS hU hR).hom).app T p)) ≫ pr =
      yonedaSchemePointEquiv C hS hR T a := by
    rintro pr π a rfl rfl
    exact (yonedaSchemePointEquiv_map C hS hP hR pr T _).symm
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    exact key _ _ _ (yonedaSchemePullbackIso_hom_fst C hS hR hR hU G.source G.target hP)
      (composableToPullback_fst_app C hS _ _ T p)
  · rw [pullback.lift_snd]
    exact key _ _ _ (yonedaSchemePullbackIso_hom_snd C hS hR hR hU G.source G.target hP)
      (composableToPullback_snd_app C hS _ _ T p)

/-- The sections of the realization over a test object form the groupoid of generalized points
of the groupoid scheme. -/
noncomputable def realizationPointwiseGroupoid (T : (BigFppfOver C S hS)ᵒᵖ) :
    Deformation.PointwiseGroupoid
      ((realizationSource G C hS hU hR).hom.app T)
      ((realizationTarget G C hS hU hR).hom.app T)
      (fun p => (composableToPullback (realizationSource G C hS hU hR).hom
        (realizationTarget G C hS hU hR).hom ≫
          (realizationComp G C hS hU hR hP).hom).app T p) :=
  Deformation.PointwiseGroupoid.ofEquiv
    (G.pointwiseGroupoidEvaluation ((siteToOver C hS).obj T.unop))
    (yonedaSchemePointEquiv C hS hU T) (yonedaSchemePointEquiv C hS hR T)
    (fun a => yonedaSchemePointEquiv_map C hS hR hU G.source T a)
    (fun a => yonedaSchemePointEquiv_map C hS hR hU G.target T a)
    (fun p => realizationComp_app G C hS hU hR hP T p _)

/-- A groupoid scheme over `S`, realized as a groupoid in algebraic spaces over the terminal
algebraic space of a big fppf site over `S` which contains its object scheme, its arrow scheme
and its scheme of composable pairs. -/
noncomputable def realization :
    AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS (realizationBase C hS) where
  objects := realizationObjects G C hS hU
  arrows := realizationArrows G C hS hR
  objectsToBase := ObjectProperty.homMk (yoneda.map (schemeSiteMapToBase C hS hU))
  arrowsToBase := ObjectProperty.homMk (yoneda.map (schemeSiteMapToBase C hS hR))
  source := realizationSource G C hS hU hR
  target := realizationTarget G C hS hU hR
  source_over := by
    apply ObjectProperty.hom_ext
    change yoneda.map (schemeSiteMap C hS hR hU G.source) ≫
      yoneda.map (schemeSiteMapToBase C hS hU) = yoneda.map (schemeSiteMapToBase C hS hR)
    rw [← yoneda.map_comp, schemeSiteMap_toBase]
  target_over := by
    apply ObjectProperty.hom_ext
    change yoneda.map (schemeSiteMap C hS hR hU G.target) ≫
      yoneda.map (schemeSiteMapToBase C hS hU) = yoneda.map (schemeSiteMapToBase C hS hR)
    rw [← yoneda.map_comp, schemeSiteMap_toBase]
  comp := realizationComp G C hS hU hR hP
  comp_over := by
    apply ObjectProperty.hom_ext
    change ((yonedaSchemePullbackIso C hS hR hR hU G.source G.target hP).hom ≫
        yoneda.map (schemeSiteMap C hS hP hR G.comp)) ≫
        yoneda.map (schemeSiteMapToBase C hS hR) =
      pullback.fst (yoneda.map (schemeSiteMap C hS hR hU G.source))
          (yoneda.map (schemeSiteMap C hS hR hU G.target)) ≫
        yoneda.map (schemeSiteMapToBase C hS hR)
    rw [← yonedaSchemePullbackIso_hom_fst C hS hR hR hU G.source G.target hP,
      Category.assoc, Category.assoc, ← yoneda.map_comp, ← yoneda.map_comp,
      schemeSiteMap_toBase, schemeSiteMap_toBase]
  pointwiseGroupoid := fun T => ⟨realizationPointwiseGroupoid G C hS hU hR hP T⟩

/-- The object space of the realization is the presheaf represented by the object scheme. -/
theorem realization_objects :
    (realization G C hS hU hR hP).objects = realizationObjects G C hS hU := rfl

/-- The arrow space of the realization is the presheaf represented by the arrow scheme. -/
theorem realization_arrows :
    (realization G C hS hU hR hP).arrows = realizationArrows G C hS hR := rfl

/-- The source of the realization is the Yoneda image of the source of the groupoid scheme. -/
theorem realization_source :
    (realization G C hS hU hR hP).source.hom =
      yoneda.map (schemeSiteMap C hS hR hU G.source) := rfl

/-- The target of the realization is the Yoneda image of the target of the groupoid scheme. -/
theorem realization_target :
    (realization G C hS hU hR hP).target.hom =
      yoneda.map (schemeSiteMap C hS hR hU G.target) := rfl

/-- The composition of the realization is the Yoneda image of the composition of the groupoid
scheme, read on the presheaf fibre product. -/
theorem realization_comp :
    (realization G C hS hU hR hP).comp.hom =
      (yonedaSchemePullbackIso C hS hR hR hU G.source G.target hP).hom ≫
        yoneda.map (schemeSiteMap C hS hP hR G.comp) := rfl

end Stacks.Groupoids.GroupoidScheme

end
