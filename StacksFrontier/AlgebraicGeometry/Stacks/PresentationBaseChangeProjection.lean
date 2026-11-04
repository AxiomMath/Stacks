module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationAtlasRelationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationBaseChangePresentation
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The projection of the base-changed presentation, and the induced morphism of quotient stacks

Let `S` be a scheme of a big fppf site, let `g : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks over
`S` representable by algebraic spaces and let `P = ((U, R, s, t, c), [U/R] ≃ 𝒳)` be a presentation
of `𝒳`. `StacksFrontier/AlgebraicGeometry/Stacks/PresentationBaseChangePresentation.lean` builds the
base-changed groupoid `(U', R', s', t', c')` on `U' = U ×_𝒳 𝒳'` and `R' = U' ×_{𝒳'} U'`, together
with the presentation `[U'/R'] ⟶ 𝒳'`. This module builds **Stacks 04Y6, assertion (3)**: the
morphism of groupoids

    pr : (U', R', s', t', c') ⟶ (U, R, s, t, c)

and the 1-morphism `[pr] : [U'/R'] ⟶ [U/R]` of quotient stacks it induces through Stacks 046Q.

## The mathematical content

On objects `pr` is the projection `U' ⟶ U`; on arrows it is the map `R' ⟶ R` that the source
calls "the projection morphism", and which has to be *built*, `R'` being the self-intersection of
the base-changed atlas rather than a fibre product over `U`. An arrow of `R'` over a test object
is a triple `(z₁, z₂, φ)` with `zᵢ` points of `U' = U ×_𝒳 𝒳'`, say `zᵢ = (uᵢ, xᵢ, ψᵢ)` with
`ψᵢ : f(uᵢ) ≅ g(xᵢ)`, and `φ : x₁ ≅ x₂`; its image is the arrow

    (u₁, u₂, ψ₁ ≫ g(φ) ≫ ψ₂⁻¹)

of `R = U ×_𝒳 U`. That assignment is a composite of two 1-morphisms already in the library —
`CategoryTheory.TwoFibreProductOver.precomposeSnd` along the exchange of the two factors of `U'`,
followed by the outer projection `CategoryTheory.TwoFibreProductOver.outerProjection` of
Stacks 04S7 — and the three clauses of a morphism of groupoids are then read off the
section-naming calculus of Stacks 04SW. The composition clause is the one with content: after
unfolding both composition laws through
`AlgebraicGeometry.Stack.SelfIntersection.sectionOfObj_composition_eq_compositionValue` the
residue is the compatibility square of the middle isomorphism of a composable pair, which is one
field of a morphism of a 2-fibre product.

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidPresentation.bcRelationFunctor`: the 1-morphism
  `U' ×_{𝒳'} U' ⟶ U ×_𝒳 U` of self-intersections underlying the arrow part of `pr`.
* `AlgebraicGeometry.Stack.GroupoidPresentation.prObjects` and `...prArrows`: the two maps of
  algebraic spaces, named through Stacks 04SW.
* `AlgebraicGeometry.Stack.GroupoidPresentation.pr`: **Stacks 04Y6, assertion (3)** — the morphism
  of groupoids in algebraic spaces.
* `AlgebraicGeometry.Stack.GroupoidPresentation.quotientStackPr`: **Stacks 04Y6, assertion (3)** —
  the induced 1-morphism `[pr] : [U'/R'] ⟶ [U/R]` of Stacks 046Q.

## Main results

* `AlgebraicGeometry.Stack.GroupoidPresentation.composition_obj_prComposable`: the arrow part of
  `pr` respects the composition of Stacks 04T4 (3).
* `AlgebraicGeometry.Stack.GroupoidPresentation.prArrows_source`,
  `...prArrows_target` and `...prArrows_compositionLaw`: the three clauses of
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mk'`.

## Implementation notes

The two categories of the intermediate 2-fibre products need their `CategoryTheory.Category`
instances named: matching the legs forces the apex of the base-changed atlas square against an
unfolding of `AlgebraicGeometry.Stack.GroupoidPresentation.baseChangedAtlasSquare`, which is
invisible at the reducible transparency instance search uses. This is the same provision
`StacksFrontier/AlgebraicGeometry/Stacks/SelfIntersection.lean` makes for the three-fold product and
for the category of composable pairs.

`AlgebraicGeometry.Stack.GroupoidPresentation.comp_regroup_middle` is stated in an abstract
category on purpose: the composites it regroups live in `𝒳`, where a goal naming them is not
type-correct at `implicit` transparency — the coercion of a category fibred in groupoids to a
based category is not unfolded there — and `CategoryTheory.Category.assoc` therefore refuses to
rewrite. In an abstract category the ordinary simp set applies.

## References

* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04S7](https://stacks.math.columbia.edu/tag/04S7)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
* [Stacks Project, Tag 04Y6](https://stacks.math.columbia.edu/tag/04Y6)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack.GroupoidPresentation

universe u w u₁ v₁

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 𝒳' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

attribute [local implicit_reducible] liftedObjectSpace liftedSpace liftedFibredCategory

/-- A seven-factor composite regrouped so that its middle three factors are bracketed together.
Stated in an abstract category: see the implementation notes. -/
theorem comp_regroup_middle {𝒞 : Type u₁} [Category.{v₁} 𝒞] {X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ : 𝒞}
    (a : X₁ ⟶ X₂) (m : X₂ ⟶ X₃) (i : X₃ ⟶ X₄) (v : X₄ ⟶ X₅) (h : X₅ ⟶ X₆) (n : X₆ ⟶ X₇)
    (j : X₇ ⟶ X₈) :
    (a ≫ m ≫ i) ≫ v ≫ (h ≫ n ≫ j) = a ≫ (m ≫ (i ≫ v ≫ h) ≫ n) ≫ j := by
  simp

variable (P : GroupoidPresentation B S hS 𝒳.val) (g : 𝒳' ⟶ 𝒳)

/-- The exchange of the two factors of `U' = U ×_𝒳 𝒳'`. -/
noncomputable abbrev bcSwap :
    (baseChangedAtlasSquare P g).pt.val.obj ⥤
      TwoFibreProductOver 𝒳'.val.p (objectStack P).val.p 𝒳.val.p
        g.hom.toFunctor (atlasMap P).hom.toFunctor :=
  TwoFibreProductOver.swap (p𝒳 := (objectStack P).val.p) (p𝒴 := 𝒳'.val.p)
    (p𝒮 := 𝒳.val.p) (F := (atlasMap P).hom.toFunctor) (G := g.hom.toFunctor)

/-- The category structure of the exchanged base-changed atlas; see the implementation notes. -/
noncomputable local instance instCategoryBcSwapped :
    Category.{u, u + 1}
      (TwoFibreProductOver 𝒳'.val.p (objectStack P).val.p 𝒳.val.p
        g.hom.toFunctor (atlasMap P).hom.toFunctor) :=
  TwoFibreProductOver.instCategory

/-- The category structure of the pairs of points of `U'` composable over `𝒳'`; see the
implementation notes. -/
noncomputable local instance instCategoryBcComposable :
    Category.{u, u + 1}
      (TwoFibreProductOver (baseChangedAtlasSquare P g).pt.val.p
        (TwoFibreProductOver.structureFunctor 𝒳'.val.p (objectStack P).val.p 𝒳.val.p
          g.hom.toFunctor (atlasMap P).hom.toFunctor)
        𝒳'.val.p
        (TwoFibreProductOver.snd (objectStack P).val.p 𝒳'.val.p 𝒳.val.p
          (atlasMap P).hom.toFunctor g.hom.toFunctor)
        (TwoFibreProductOver.fst 𝒳'.val.p (objectStack P).val.p 𝒳.val.p
          g.hom.toFunctor (atlasMap P).hom.toFunctor)) :=
  TwoFibreProductOver.instCategory

/-- **The 1-morphism `U' ×_{𝒳'} U' ⟶ U ×_𝒳 U` of self-intersections underlying the arrow part of
`pr`.** On a triple `(z₁, z₂, φ)` with `zᵢ = (uᵢ, xᵢ, ψᵢ)` it is `(u₁, u₂, ψ₁ ≫ g(φ) ≫ ψ₂⁻¹)`:
the exchange of the two factors of `U'` followed by the outer projection of Stacks 04S7. -/
noncomputable def bcRelationFunctor :
    (SelfIntersection.relation B S hS (baseChangedAtlasSquare P g).pt 𝒳'
        (baseChangedAtlas P g).hom).val.obj ⥤
      (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.obj :=
  TwoFibreProductOver.precomposeSnd
      (pT := (baseChangedAtlasSquare P g).pt.val.p) (pℬ := 𝒳'.val.p)
      (TwoFibreProductOver.snd (objectStack P).val.p 𝒳'.val.p 𝒳.val.p
        (atlasMap P).hom.toFunctor g.hom.toFunctor)
      (TwoFibreProductOver.fst 𝒳'.val.p (objectStack P).val.p 𝒳.val.p
        g.hom.toFunctor (atlasMap P).hom.toFunctor)
      (bcSwap P g) rfl ⋙
    TwoFibreProductOver.outerProjection (F := (atlasMap P).hom.toFunctor)
      (G := g.hom.toFunctor) (H := (atlasMap P).hom.toFunctor) g.hom.w

/-- The arrow part of `pr` is a 1-morphism over the big fppf site of `S`. -/
theorem bcRelationFunctor_comp :
    bcRelationFunctor P g ⋙
        (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.p =
      (SelfIntersection.relation B S hS (baseChangedAtlasSquare P g).pt 𝒳'
        (baseChangedAtlas P g).hom).val.p := rfl

/-- The target of the image of an arrow of `R'` is the image of its target. -/
theorem bcRelationFunctor_obj_x
    (z : (SelfIntersection.relation B S hS (baseChangedAtlasSquare P g).pt 𝒳'
      (baseChangedAtlas P g).hom).val.obj) :
    ((bcRelationFunctor P g).obj z).x =
      (baseChangedAtlasSquare P g).fst.hom.toFunctor.obj z.x := rfl

/-- The source of the image of an arrow of `R'` is the image of its source. -/
theorem bcRelationFunctor_obj_y
    (z : (SelfIntersection.relation B S hS (baseChangedAtlasSquare P g).pt 𝒳'
      (baseChangedAtlas P g).hom).val.obj) :
    ((bcRelationFunctor P g).obj z).y =
      (baseChangedAtlasSquare P g).fst.hom.toFunctor.obj z.y := rfl

/-- The comparison isomorphism of the image of an arrow of `R'` is `ψ₁ ≫ g(φ) ≫ ψ₂⁻¹`. -/
theorem bcRelationFunctor_obj_iso
    (z : (SelfIntersection.relation B S hS (baseChangedAtlasSquare P g).pt 𝒳'
      (baseChangedAtlas P g).hom).val.obj) :
    ((bcRelationFunctor P g).obj z).iso =
      z.x.iso ≪≫ g.hom.toFunctor.mapIso z.iso ≪≫ z.y.iso.symm := rfl

section Composable

variable (x : SelfIntersection.composable B S hS (baseChangedAtlasSquare P g).pt 𝒳'
  (baseChangedAtlas P g).hom)

/-- The image of the first component of a composable pair lies over the pair's test object. -/
theorem bcRelationFunctor_obj_over_fst :
    (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.p.obj
      ((bcRelationFunctor P g).obj x.x) = x.base :=
  (Functor.congr_obj (bcRelationFunctor_comp P g) x.x).trans x.hx

/-- The image of the second component of a composable pair lies over the pair's test object. -/
theorem bcRelationFunctor_obj_over_snd :
    (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.p.obj
      ((bcRelationFunctor P g).obj x.y) = x.base :=
  (Functor.congr_obj (bcRelationFunctor_comp P g) x.y).trans x.hy

/-- The image under the projection `U' ⟶ U` of the middle isomorphism of a composable pair. -/
noncomputable def bcMiddleIso :
    (Functor.Fiber.mk (SelfIntersection.relation_obj_y (bcRelationFunctor_obj_over_fst P g x)) :
        (objectStack P).val.p.Fiber x.base) ≅
      Functor.Fiber.mk (SelfIntersection.relation_obj_x (bcRelationFunctor_obj_over_snd P g x)) :=
  Functor.Fiber.isoMk
    ((baseChangedAtlasSquare P g).fst.hom.toFunctor.mapIso x.iso)
    (TwoFibreProductOver.isHomLift_a x.iso.hom (𝟙 x.base) x.vertical)

/-- **The image under `pr` of a composable pair of arrows of `R'`**, a composable pair of arrows
of `R`. -/
noncomputable def prComposable :
    SelfIntersection.composable B S hS (objectStack P) 𝒳 (atlasMap P).hom :=
  SelfIntersection.composableMk (bcRelationFunctor_obj_over_fst P g x)
    (bcRelationFunctor_obj_over_snd P g x) (bcMiddleIso P g x)

/-- The first component of the image pair is the image of the first component. -/
theorem prComposable_x : (prComposable P g x).x = (bcRelationFunctor P g).obj x.x := rfl

/-- The second component of the image pair is the image of the second component. -/
theorem prComposable_y : (prComposable P g x).y = (bcRelationFunctor P g).obj x.y := rfl

/-- The image pair lies over the same test object. -/
theorem prComposable_base : (prComposable P g x).base = x.base := rfl

/-- **The arrow part of `pr` respects the composition of Stacks 04T4 (3).** The composite of the
images of a composable pair is the image of its composite: after cancelling the comparison
isomorphisms of the two points of `U'` in the middle, the residue is the compatibility square of
the middle isomorphism of the pair. -/
theorem composition_obj_prComposable :
    (SelfIntersection.composition B S hS (objectStack P) 𝒳 (atlasMap P).hom).toFunctor.obj
        (prComposable P g x) =
      (bcRelationFunctor P g).obj
        ((SelfIntersection.composition B S hS (baseChangedAtlasSquare P g).pt 𝒳'
          (baseChangedAtlas P g).hom).toFunctor.obj x) := by
  refine TwoFibreProductOver.ext_of_heq_iso rfl rfl rfl (heq_of_eq (Iso.ext ?_))
  have hw : (atlasMap P).hom.toFunctor.map x.iso.hom.a ≫ x.y.x.iso.hom =
      x.x.y.iso.hom ≫ g.hom.toFunctor.map x.iso.hom.b := x.iso.hom.w
  have hwkey : x.x.y.iso.inv ≫ (atlasMap P).hom.toFunctor.map x.iso.hom.a ≫ x.y.x.iso.hom =
      g.hom.toFunctor.map x.iso.hom.b :=
    (congrArg (fun m => x.x.y.iso.inv ≫ m) hw).trans
      (Iso.inv_hom_id_assoc x.x.y.iso (g.hom.toFunctor.map x.iso.hom.b))
  have hA : ((SelfIntersection.composition B S hS (objectStack P) 𝒳
          (atlasMap P).hom).toFunctor.obj (prComposable P g x)).iso.hom =
      (x.x.x.iso.hom ≫ g.hom.toFunctor.map x.x.iso.hom ≫ x.x.y.iso.inv) ≫
        (atlasMap P).hom.toFunctor.map x.iso.hom.a ≫
          (x.y.x.iso.hom ≫ g.hom.toFunctor.map x.y.iso.hom ≫ x.y.y.iso.inv) := rfl
  have hB : ((bcRelationFunctor P g).obj
          ((SelfIntersection.composition B S hS (baseChangedAtlasSquare P g).pt 𝒳'
            (baseChangedAtlas P g).hom).toFunctor.obj x)).iso.hom =
      x.x.x.iso.hom ≫
        g.hom.toFunctor.map (x.x.iso.hom ≫ x.iso.hom.b ≫ x.y.iso.hom) ≫
          x.y.y.iso.inv := rfl
  have hmap : g.hom.toFunctor.map (x.x.iso.hom ≫ x.iso.hom.b ≫ x.y.iso.hom) =
      g.hom.toFunctor.map x.x.iso.hom ≫ g.hom.toFunctor.map x.iso.hom.b ≫
        g.hom.toFunctor.map x.y.iso.hom :=
    (g.hom.toFunctor.map_comp _ _).trans
      (congrArg (fun m => g.hom.toFunctor.map x.x.iso.hom ≫ m)
        (g.hom.toFunctor.map_comp _ _))
  exact hA.trans
    ((comp_regroup_middle x.x.x.iso.hom (g.hom.toFunctor.map x.x.iso.hom) x.x.y.iso.inv
        ((atlasMap P).hom.toFunctor.map x.iso.hom.a) x.y.x.iso.hom
        (g.hom.toFunctor.map x.y.iso.hom) x.y.y.iso.inv).trans
      (((congrArg (fun m => x.x.x.iso.hom ≫
            (g.hom.toFunctor.map x.x.iso.hom ≫ m ≫ g.hom.toFunctor.map x.y.iso.hom) ≫
              x.y.y.iso.inv) hwkey).trans
        (congrArg (fun m => x.x.x.iso.hom ≫ m ≫ x.y.y.iso.inv) hmap.symm)).trans hB.symm))

end Composable

section Maps

variable {U' R' : AlgebraicSpaces B S hS}
variable
  (eU' : StacksRepresentableCFG.EquivalenceOver
    (baseChangedAtlasSquare P g).pt.val.p (presheafOfCategories (U'.obj ⋙ typeToCat)).p)
  (eR' : StacksRepresentableCFG.EquivalenceOver
    (SelfIntersection.relation B S hS (baseChangedAtlasSquare P g).pt 𝒳'
      (baseChangedAtlas P g).hom).val.p
    (presheafOfCategories (R'.obj ⋙ typeToCat)).p)

/-- **The map `U' ⟶ U` on object spaces**, named through Stacks 04SW by the projection
`U ×_𝒳 𝒳' ⟶ 𝒮_U`. -/
noncomputable def prObjects : U'.obj ⟶ P.groupoid.objects.obj :=
  morphismSpaceEquiv B S hS (baseChangedAtlasSquare P g).pt (objectStack P)
    U'.obj P.groupoid.objects.obj eU' (atlasObjectEquivalence P)
    (Quotient.mk _ ⟨(baseChangedAtlasSquare P g).fst.hom.toFunctor,
      (baseChangedAtlasSquare P g).fst.hom.w⟩)

/-- **The map `R' ⟶ R` on arrow spaces**, named through Stacks 04SW by
`AlgebraicGeometry.Stack.GroupoidPresentation.bcRelationFunctor`. -/
noncomputable def prArrows : R'.obj ⟶ P.groupoid.arrows.obj :=
  morphismSpaceEquiv B S hS
    (SelfIntersection.relation B S hS (baseChangedAtlasSquare P g).pt 𝒳'
      (baseChangedAtlas P g).hom)
    (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom)
    R'.obj P.groupoid.arrows.obj eR' (atlasRelationEquivalence P)
    (Quotient.mk _ ⟨bcRelationFunctor P g, bcRelationFunctor_comp P g⟩)

/-- The map on object spaces carries the section named by a point of `U ×_𝒳 𝒳'` to the section
named by its projection. -/
theorem prObjects_app_sectionOfObj {W : BigFppfOver B S hS}
    (z : (baseChangedAtlasSquare P g).pt.val.obj)
    (hz : (baseChangedAtlasSquare P g).pt.val.p.obj z = W) :
    (prObjects P g eU').app (op W) (PresheafOfCategories.sectionOfObj eU' z hz) =
      PresheafOfCategories.sectionOfObj (atlasObjectEquivalence P)
        ((baseChangedAtlasSquare P g).fst.hom.toFunctor.obj z)
        ((Functor.congr_obj (baseChangedAtlasSquare P g).fst.hom.w z).trans hz) :=
  morphismSpaceEquiv_app_sectionOfObj B S hS _ _ _ _ eU' (atlasObjectEquivalence P) _ z hz

/-- The map on arrow spaces carries the section named by an arrow of `U' ×_{𝒳'} U'` to the
section named by its image. -/
theorem prArrows_app_sectionOfObj {W : BigFppfOver B S hS}
    (z : (SelfIntersection.relation B S hS (baseChangedAtlasSquare P g).pt 𝒳'
      (baseChangedAtlas P g).hom).val.obj)
    (hz : (SelfIntersection.relation B S hS (baseChangedAtlasSquare P g).pt 𝒳'
      (baseChangedAtlas P g).hom).val.p.obj z = W) :
    (prArrows P g eR').app (op W) (PresheafOfCategories.sectionOfObj eR' z hz) =
      PresheafOfCategories.sectionOfObj (atlasRelationEquivalence P)
        ((bcRelationFunctor P g).obj z)
        ((Functor.congr_obj (bcRelationFunctor_comp P g) z).trans hz) :=
  morphismSpaceEquiv_app_sectionOfObj B S hS _ _ _ _ eR' (atlasRelationEquivalence P) _ z hz

/-- The source of the presenting groupoid carries the section named by an arrow of the
self-intersection of the atlas to the section named by its source. -/
theorem source_hom_sectionOfObj
    (r : (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.obj)
    {W : BigFppfOver B S hS}
    (h : (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.p.obj r = W) :
    P.groupoid.source.hom.app (op W)
        (PresheafOfCategories.sectionOfObj (atlasRelationEquivalence P) r h) =
      PresheafOfCategories.sectionOfObj (atlasObjectEquivalence P) r.y
        (SelfIntersection.relation_obj_y h) := by
  rw [← relationSourceMap_atlasRelationEquivalence P]
  exact SelfIntersection.relationSourceMap_sectionOfObj (atlasObjectEquivalence P)
    (atlasRelationEquivalence P) r h

/-- The target of the presenting groupoid carries the section named by an arrow of the
self-intersection of the atlas to the section named by its target. -/
theorem target_hom_sectionOfObj
    (r : (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.obj)
    {W : BigFppfOver B S hS}
    (h : (SelfIntersection.relation B S hS (objectStack P) 𝒳 (atlasMap P).hom).val.p.obj r = W) :
    P.groupoid.target.hom.app (op W)
        (PresheafOfCategories.sectionOfObj (atlasRelationEquivalence P) r h) =
      PresheafOfCategories.sectionOfObj (atlasObjectEquivalence P) r.x
        (SelfIntersection.relation_obj_x h) := by
  rw [← relationTargetMap_atlasRelationEquivalence P]
  exact SelfIntersection.relationTargetMap_sectionOfObj (atlasObjectEquivalence P)
    (atlasRelationEquivalence P) r h

/-- **`pr` commutes with the source maps.** -/
theorem prArrows_source {W : BigFppfOver B S hS} (a : R'.obj.obj (op W)) :
    P.groupoid.source.hom.app (op W) ((prArrows P g eR').app (op W) a) =
      (prObjects P g eU').app (op W)
        ((SelfIntersection.relationSourceMap eU' eR').app (op W) a) := by
  obtain ⟨z, hz, hzs⟩ := PresheafOfCategories.exists_sectionOfObj eR' a
  subst hzs
  exact ((congrArg (fun y => P.groupoid.source.hom.app (op W) y)
      (prArrows_app_sectionOfObj P g eR' z hz)).trans
    (source_hom_sectionOfObj P ((bcRelationFunctor P g).obj z) _)).trans
      ((prObjects_app_sectionOfObj P g eU' z.y (SelfIntersection.relation_obj_y hz)).symm.trans
        (congrArg (fun y => (prObjects P g eU').app (op W) y)
          (SelfIntersection.relationSourceMap_sectionOfObj eU' eR' z hz).symm))

/-- **`pr` commutes with the target maps.** -/
theorem prArrows_target {W : BigFppfOver B S hS} (a : R'.obj.obj (op W)) :
    P.groupoid.target.hom.app (op W) ((prArrows P g eR').app (op W) a) =
      (prObjects P g eU').app (op W)
        ((SelfIntersection.relationTargetMap eU' eR').app (op W) a) := by
  obtain ⟨z, hz, hzs⟩ := PresheafOfCategories.exists_sectionOfObj eR' a
  subst hzs
  exact ((congrArg (fun y => P.groupoid.target.hom.app (op W) y)
      (prArrows_app_sectionOfObj P g eR' z hz)).trans
    (target_hom_sectionOfObj P ((bcRelationFunctor P g).obj z) _)).trans
      ((prObjects_app_sectionOfObj P g eU' z.x (SelfIntersection.relation_obj_x hz)).symm.trans
        (congrArg (fun y => (prObjects P g eU').app (op W) y)
          (SelfIntersection.relationTargetMap_sectionOfObj eU' eR' z hz).symm))

/-- **`pr` commutes with the composition laws**, in the form of the composition law of
Stacks 04T4 (4) on the base-changed side. -/
theorem prArrows_compositionLaw {W : BigFppfOver B S hS} (a b : R'.obj.obj (op W))
    (h : (SelfIntersection.relationSourceMap eU' eR').app (op W) a =
      (SelfIntersection.relationTargetMap eU' eR').app (op W) b)
    (h₂ : P.groupoid.source.hom.app (op W) ((prArrows P g eR').app (op W) a) =
      P.groupoid.target.hom.app (op W) ((prArrows P g eR').app (op W) b)) :
    P.groupoid.toGroupoidInFunctors.compose (op W)
        ((prArrows P g eR').app (op W) a) ((prArrows P g eR').app (op W) b) h₂ =
      (prArrows P g eR').app (op W)
        ((SelfIntersection.compositionLaw eU' eR'
          (SelfIntersection.isFiberedInSetoids_source eU')).app (op W) ⟨(a, b), h⟩) := by
  obtain ⟨x, hb, e₁, e₂⟩ := SelfIntersection.exists_composable eU' eR' a b h
  subst hb
  have h' : (SelfIntersection.relationSourceMap (atlasObjectEquivalence P)
          (atlasRelationEquivalence P)).app (op x.base) ((prArrows P g eR').app (op x.base) a) =
      (SelfIntersection.relationTargetMap (atlasObjectEquivalence P)
          (atlasRelationEquivalence P)).app (op x.base)
        ((prArrows P g eR').app (op x.base) b) := by
    rw [relationSourceMap_atlasRelationEquivalence P,
      relationTargetMap_atlasRelationEquivalence P]
    exact h₂
  have keyA := SelfIntersection.sectionOfObj_composition_eq_compositionValue
    (atlasObjectEquivalence P) (atlasRelationEquivalence P) (isFiberedInSetoids_objectStack P)
    ⟨((prArrows P g eR').app (op x.base) a, (prArrows P g eR').app (op x.base) b), h'⟩
    (prComposable P g x) rfl
    ((prArrows_app_sectionOfObj P g eR' x.x (x.hx.trans rfl)).symm.trans (congrArg _ e₁))
    ((prArrows_app_sectionOfObj P g eR' x.y (x.hy.trans rfl)).symm.trans (congrArg _ e₂))
  have keyB := SelfIntersection.sectionOfObj_composition_eq_compositionValue eU' eR'
    (SelfIntersection.isFiberedInSetoids_source eU') ⟨(a, b), h⟩ x rfl e₁ e₂
  have hLHS : P.groupoid.toGroupoidInFunctors.compose (op x.base)
        ((prArrows P g eR').app (op x.base) a) ((prArrows P g eR').app (op x.base) b) h₂ =
      PresheafOfCategories.sectionOfObj (atlasRelationEquivalence P)
        ((SelfIntersection.composition B S hS (objectStack P) 𝒳
          (atlasMap P).hom).toFunctor.obj (prComposable P g x))
        (SelfIntersection.composition_obj_over rfl) :=
    (compositionLaw_app_atlasRelationEquivalence P ((prArrows P g eR').app (op x.base) a)
      ((prArrows P g eR').app (op x.base) b) h₂ h').symm.trans keyA.symm
  refine hLHS.trans ?_
  refine Eq.trans ?_ (congrArg (fun y => (prArrows P g eR').app (op x.base) y) keyB)
  refine Eq.trans ?_ (prArrows_app_sectionOfObj P g eR'
    ((SelfIntersection.composition B S hS (baseChangedAtlasSquare P g).pt 𝒳'
      (baseChangedAtlas P g).hom).toFunctor.obj x)
    (SelfIntersection.composition_obj_over rfl)).symm
  congr 1
  exact composition_obj_prComposable P g x

variable (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
variable (h𝒳' : IsAlgebraicStack.{u, w} B S hS 𝒳'.val)

/-- The composition law of the base-changed presentation is the composition law of
Stacks 04T4 (4). -/
theorem compose_baseChangedPresentation {W : BigFppfOver B S hS} (a b : R'.obj.obj (op W))
    (h : (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid.source.hom.app (op W) a =
      (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid.target.hom.app (op W) b) :
    (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid.toGroupoidInFunctors.compose
        (op W) a b h =
      (SelfIntersection.compositionLaw eU' eR'
        (SelfIntersection.isFiberedInSetoids_source eU')).app (op W) ⟨(a, b), h⟩ :=
  compose_ofComposable U' R'
    (ObjectProperty.homMk (SelfIntersection.relationSourceMap eU' eR'))
    (ObjectProperty.homMk (SelfIntersection.relationTargetMap eU' eR'))
    (SelfIntersection.compositionLaw eU' eR' (SelfIntersection.isFiberedInSetoids_source eU'))
    (SelfIntersection.nonempty_pointwiseGroupoid eU' eR'
      (SelfIntersection.isFiberedInSetoids_source eU'))
    (op W) a b h

/-- **Stacks 04Y6, assertion (3).** The morphism of groupoids in algebraic spaces
`pr : (U', R', s', t', c') ⟶ (U, R, s, t, c)`: on objects the projection `U' = U ×_𝒳 𝒳' ⟶ U`, on
arrows the map carrying `(u₁, x₁, ψ₁), (u₂, x₂, ψ₂), φ` to `(u₁, u₂, ψ₁ ≫ g(φ) ≫ ψ₂⁻¹)`. The
identity clause is not a hypothesis of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.mk'`, and the two clauses over the base are free,
the base being final. -/
@[stacks 04Y6 "assertion (3): the morphism of groupoids pr : (U', R', s', t', c') ⟶ (U, R, s, t, c)"]
noncomputable def pr : GroupoidInAlgebraicSpaces.Hom
    (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid P.groupoid :=
  GroupoidInAlgebraicSpaces.Hom.mk' (prObjects P g eU') (prArrows P g eR')
    (fun _ a => prArrows_source P g eU' eR' a)
    (fun _ a => prArrows_target P g eU' eR' a)
    (fun _ a b h =>
      (prArrows_compositionLaw P g eU' eR' a b h _).trans
        (congrArg (fun y => (prArrows P g eR').app _ y)
          (compose_baseChangedPresentation P g eU' eR' h𝒳 h𝒳' a b h).symm))
    (congrArg (fun m : U' ⟶ baseSpace B S hS => m.hom)
      ((isTerminal_baseSpace B S hS).hom_ext
        (ObjectProperty.homMk (prObjects P g eU') ≫ P.groupoid.objectsToBase)
        (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid.objectsToBase))
    (congrArg (fun m : R' ⟶ baseSpace B S hS => m.hom)
      ((isTerminal_baseSpace B S hS).hom_ext
        (ObjectProperty.homMk (prArrows P g eR') ≫ P.groupoid.arrowsToBase)
        (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid.arrowsToBase))

/-- **Stacks 04Y6, assertion (3).** The 1-morphism `[pr] : [U'/R'] ⟶ [U/R]` of quotient stacks
induced by `pr` through Stacks 046Q. -/
@[stacks 04Y6 "assertion (3): the induced morphism [pr] of quotient stacks"]
noncomputable def quotientStackPr :
    BasedFunctor (quotientStack (baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid)
      (quotientStack P.groupoid) :=
  quotientStackMap (pr P g eU' eR' h𝒳 h𝒳')

end Maps

end AlgebraicGeometry.Stack.GroupoidPresentation

end
