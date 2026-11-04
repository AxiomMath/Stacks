module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpacesOfComposable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceIsoClass
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersection
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso

/-!
# The self-intersection groupoid and its composition law

Let `S` be a scheme contained in a big fppf site `B`, let `𝒰` and `𝒳` be categories fibred in
groupoids over the big fppf site of `S`, let `f : 𝒰 ⟶ 𝒳` be a 1-morphism and let
`ℛ = 𝒰 ×_{f, 𝒳, f} 𝒰` be its self-intersection
(`AlgebraicGeometry.Stack.SelfIntersection.relation`). Suppose `𝒰` and `ℛ` are represented by
algebraic spaces `U` and `R` over `S` through chosen equivalences `eU` and `eR` over the site.

Stacks 04T4 (4) asserts that `U` and `R` carry a groupoid in algebraic spaces, whose source and
target are the morphisms `R ⟶ U` induced by the two projections `pr₁`, `pr₀` of `ℛ` and whose
composition is the morphism induced by the outer projection `pr₀₂` of Stacks 04T4 (3). An arrow of
the relation over a scheme `T` is a triple `(a, b, α : f a ≅ f b)`, read as an arrow from the
isomorphism class of `b` to that of `a`. This file builds that composition law, as a morphism of
presheaves

```text
c : R ×_{s, U, t} R ⟶ R
```

on the presheaf of composable pairs of arrows (`Deformation.composableArrows`, Stacks 06K3), and
proves the identity that characterises it: on the pair of sections named by the two components of
a composable pair of `ℛ ×_{pr₁, 𝒰, pr₀} ℛ`, it is the section named by the composite.

## Main definitions

* `AlgebraicGeometry.Stack.SelfIntersection.relationSourceMap` and
  `AlgebraicGeometry.Stack.SelfIntersection.relationTargetMap`: the two structure morphisms
  `R.obj ⟶ U.obj` of representing presheaves, the images of the projections `pr₁` and `pr₀`
  under the bijection of Stacks 04SW.
* `AlgebraicGeometry.Stack.SelfIntersection.relationSource` and
  `AlgebraicGeometry.Stack.SelfIntersection.relationTarget`: those same two morphisms read in the
  category of algebraic spaces over `S` of Stacks 02X2, which is where the source `s : R ⟶ U` and
  the target `t : R ⟶ U` of the groupoid live.
* `AlgebraicGeometry.Stack.SelfIntersection.composableMk`: a composable pair of arrows of `ℛ`
  from two arrows over one object of the site together with a vertical identification of the
  target of the first with the source of the second.
* `AlgebraicGeometry.Stack.SelfIntersection.compositionLaw`: the composition law.
* `AlgebraicGeometry.Stack.SelfIntersection.representingObj`: the chosen representative of a
  section of the object space — the source's chosen quasi-inverse of `𝒰 ⟶ 𝒮_U`.
* `AlgebraicGeometry.Stack.SelfIntersection.arrowEquivOfSection`: the hom-set bijection of the
  pointwise groupoid.
* `AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionGroupoid`: the groupoid in algebraic
  spaces of Stacks 04T4 (4).

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.relationSourceMap_sectionOfObj` and
  `AlgebraicGeometry.Stack.SelfIntersection.relationTargetMap_sectionOfObj`: the two structure
  morphisms carry the section named by an arrow of `ℛ` to the sections named by its two
  endpoints.
* `AlgebraicGeometry.Stack.SelfIntersection.exists_composable`: a composable pair of *sections*
  comes from a composable pair of *arrows*.
* `AlgebraicGeometry.Stack.SelfIntersection.sectionOfObj_composition_congr`: the section named by
  the composite depends only on the sections named by the two factors.
* `AlgebraicGeometry.Stack.SelfIntersection.compositionLaw_app_sectionOfObj`: the characterising
  identity of the composition law.
* `AlgebraicGeometry.Stack.SelfIntersection.exists_comp_compatible`: the compatibility clause of
  the presentation data of Stacks 04T4 (4) and (5), for the groupoid built from this composition
  law.
* `AlgebraicGeometry.Stack.SelfIntersection.sourcePresentation_pointwise`: the clause of that
  same data saying that the chosen presentation of `𝒰` agrees on objects with the canonical
  projection to the quotient stack.
* `AlgebraicGeometry.Stack.SelfIntersection.nonempty_pointwiseGroupoid`: the pointwise groupoid
  condition of Stacks 04T4 (4).
* `AlgebraicGeometry.Stack.SelfIntersection.exists_comp_compatible_groupoid` and
  `AlgebraicGeometry.Stack.SelfIntersection.sourcePresentation_pointwise_groupoid`: the two
  clauses above for the groupoid itself, with no hypothesis left over.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.SelfIntersection

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
variable {f : 𝒰.val ⥤ᵇ 𝒳.val}

attribute [local instance] instCategoryComposable

/-- The category of composable pairs of arrows of the relation is fibred in groupoids over the
big fppf site of `S`. -/
theorem isFiberedInGroupoids_composableProjection :
    (composableProjection B S hS 𝒰 𝒳 f).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
    (relation B S hS 𝒰 𝒳 f).isFiberedInGroupoids
    (relation B S hS 𝒰 𝒳 f).isFiberedInGroupoids 𝒰.isFiberedInGroupoids
    TwoFibreProductOver.snd_comp_eq TwoFibreProductOver.fst_comp_eq

/-- The target of an arrow of the relation lies over the same object of the site as the arrow. -/
theorem relation_obj_x {r : (relation B S hS 𝒰 𝒳 f).val.obj}
    {W : BigFppfOver B S hS} (h : (relation B S hS 𝒰 𝒳 f).val.p.obj r = W) :
    𝒰.val.p.obj r.x = W := r.hx.trans h

/-- The source of an arrow of the relation lies over the same object of the site as the arrow. -/
theorem relation_obj_y {r : (relation B S hS 𝒰 𝒳 f).val.obj}
    {W : BigFppfOver B S hS} (h : (relation B S hS 𝒰 𝒳 f).val.p.obj r = W) :
    𝒰.val.p.obj r.y = W := r.hy.trans h

/-- The composite of a composable pair of arrows lies over the same object of the site as the
pair. -/
theorem composition_obj_over {x : composable B S hS 𝒰 𝒳 f} {W : BigFppfOver B S hS}
    (hb : x.base = W) :
    (relation B S hS 𝒰 𝒳 f).val.p.obj
      ((composition B S hS 𝒰 𝒳 f).toFunctor.obj x) = W :=
  (Functor.congr_obj (composition B S hS 𝒰 𝒳 f).w x).trans hb

variable {U R : AlgebraicSpaces B S hS}
variable
  (eU : StacksRepresentableCFG.EquivalenceOver
    𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS 𝒰 𝒳 f).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

include eU in
/-- A category fibred in groupoids equivalent over the site to the category of elements of a
presheaf of sets is fibred in setoids. -/
theorem isFiberedInSetoids_source : 𝒰.val.p.IsFiberedInSetoids :=
  StacksRepresentableCFG.isFiberedInSetoids_of_equivalenceOver eU
    (PresheafOfCategories.isFiberedInSetoids_discreteProjection U.obj)

/-- The target morphism `R ⟶ U` of the self-intersection groupoid: the morphism of
representing presheaves which the first projection `pr₀ : ℛ ⟶ 𝒰` induces through the bijection of
Stacks 04SW. -/
noncomputable def relationTargetMap : R.obj ⟶ U.obj :=
  morphismSpaceEquiv B S hS (relation B S hS 𝒰 𝒳 f) 𝒰 R.obj U.obj eR eU
    (Quotient.mk _
      ⟨TwoFibreProductOver.fst 𝒰.val.p 𝒰.val.p 𝒳.val.p f.toFunctor f.toFunctor,
        by exact TwoFibreProductOver.fst_comp_eq⟩)

/-- The source morphism `R ⟶ U` of the self-intersection groupoid: the morphism of
representing presheaves which the second projection `pr₁ : ℛ ⟶ 𝒰` induces through the bijection
of Stacks 04SW. -/
noncomputable def relationSourceMap : R.obj ⟶ U.obj :=
  morphismSpaceEquiv B S hS (relation B S hS 𝒰 𝒳 f) 𝒰 R.obj U.obj eR eU
    (Quotient.mk _
      ⟨TwoFibreProductOver.snd 𝒰.val.p 𝒰.val.p 𝒳.val.p f.toFunctor f.toFunctor,
        by exact TwoFibreProductOver.snd_comp_eq⟩)

/-- The target morphism `t : R ⟶ U` of the self-intersection groupoid, read in the category of
algebraic spaces over `S` of Stacks 02X2: the morphism of algebraic spaces named, through Stacks
04SW, by the first projection `pr₀ : ℛ ⟶ 𝒰` of the 2-fibre product.

On a test scheme `T` it sends the isomorphism class of a triple `(a, b, α)` to that of `a`. -/
@[stacks 04T4 "part (4): target morphism of the groupoid"]
noncomputable def relationTarget : R ⟶ U :=
  ObjectProperty.homMk (relationTargetMap eU eR)

/-- The source morphism `s : R ⟶ U` of the self-intersection groupoid, read in the category of
algebraic spaces over `S` of Stacks 02X2: the morphism of algebraic spaces named, through Stacks
04SW, by the second projection `pr₁ : ℛ ⟶ 𝒰` of the 2-fibre product.

On a test scheme `T` it sends the isomorphism class of a triple `(a, b, α)` to that of `b`. -/
@[stacks 04T4 "part (4): source morphism of the groupoid"]
noncomputable def relationSource : R ⟶ U :=
  ObjectProperty.homMk (relationSourceMap eU eR)

/-- The target morphism carries the section named by an arrow of the relation to the section
named by the target of that arrow. -/
theorem relationTargetMap_sectionOfObj
    (r : (relation B S hS 𝒰 𝒳 f).val.obj) {W : BigFppfOver B S hS}
    (h : (relation B S hS 𝒰 𝒳 f).val.p.obj r = W) :
    (relationTargetMap eU eR).app (op W)
        (PresheafOfCategories.sectionOfObj eR r h) =
      PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x h) :=
  morphismSpaceEquiv_app_sectionOfObj B S hS _ _ _ _ eR eU _ r h

/-- The source morphism carries the section named by an arrow of the relation to the section
named by the source of that arrow. -/
theorem relationSourceMap_sectionOfObj
    (r : (relation B S hS 𝒰 𝒳 f).val.obj) {W : BigFppfOver B S hS}
    (h : (relation B S hS 𝒰 𝒳 f).val.p.obj r = W) :
    (relationSourceMap eU eR).app (op W)
        (PresheafOfCategories.sectionOfObj eR r h) =
      PresheafOfCategories.sectionOfObj eU r.y (relation_obj_y h) :=
  morphismSpaceEquiv_app_sectionOfObj B S hS _ _ _ _ eR eU _ r h

/-- A composable pair of arrows of the relation, from two arrows lying over one object `W` of the
site together with an isomorphism, in the fibre of `𝒰` over `W`, of the source of the first with
the target of the second. -/
noncomputable def composableMk
    {γ ϱ : (relation B S hS 𝒰 𝒳 f).val.obj} {W : BigFppfOver B S hS}
    (hγ : (relation B S hS 𝒰 𝒳 f).val.p.obj γ = W)
    (hϱ : (relation B S hS 𝒰 𝒳 f).val.p.obj ϱ = W)
    (i : (Functor.Fiber.mk (relation_obj_y hγ) : 𝒰.val.p.Fiber W) ≅
      Functor.Fiber.mk (relation_obj_x hϱ)) :
    composable B S hS 𝒰 𝒳 f where
  base := W
  x := γ
  y := ϱ
  hx := hγ
  hy := hϱ
  iso := Functor.Fiber.fiberInclusion.mapIso i
  vertical := i.hom.2

/-- Two sections of `R` over `W` whose images under the source and the target morphisms agree
are named by the two components of a composable pair of arrows of the relation over `W`. -/
theorem exists_composable
    {W : BigFppfOver B S hS} (g r : R.obj.obj (op W))
    (h : (relationSourceMap eU eR).app (op W) g = (relationTargetMap eU eR).app (op W) r) :
    ∃ (x : composable B S hS 𝒰 𝒳 f) (hb : x.base = W),
      PresheafOfCategories.sectionOfObj eR x.x (x.hx.trans hb) = g ∧
        PresheafOfCategories.sectionOfObj eR x.y (x.hy.trans hb) = r := by
  obtain ⟨γ, hγ, hγs⟩ := PresheafOfCategories.exists_sectionOfObj eR g
  obtain ⟨ϱ, hϱ, hϱs⟩ := PresheafOfCategories.exists_sectionOfObj eR r
  subst hγs hϱs
  rw [relationSourceMap_sectionOfObj eU eR γ hγ,
    relationTargetMap_sectionOfObj eU eR ϱ hϱ] at h
  exact ⟨composableMk hγ hϱ
    (PresheafOfCategories.fiberIsoOfSectionOfObj_eq eU _ _ h), rfl, rfl, rfl⟩

/-- Two composable pairs of arrows over one object of the site whose components name the same
sections of `R` have composites naming the same section of `R`. -/
theorem sectionOfObj_composition_congr
    (hset : 𝒰.val.p.IsFiberedInSetoids)
    {x x' : composable B S hS 𝒰 𝒳 f} {W : BigFppfOver B S hS}
    (hb : x.base = W) (hb' : x'.base = W)
    (h1 : PresheafOfCategories.sectionOfObj eR x.x (x.hx.trans hb) =
      PresheafOfCategories.sectionOfObj eR x'.x (x'.hx.trans hb'))
    (h2 : PresheafOfCategories.sectionOfObj eR x.y (x.hy.trans hb) =
      PresheafOfCategories.sectionOfObj eR x'.y (x'.hy.trans hb')) :
    PresheafOfCategories.sectionOfObj eR
        ((composition B S hS 𝒰 𝒳 f).toFunctor.obj x) (composition_obj_over hb) =
      PresheafOfCategories.sectionOfObj eR
        ((composition B S hS 𝒰 𝒳 f).toFunctor.obj x') (composition_obj_over hb') := by
  have : 𝒰.val.p.IsFiberedInSetoids := hset
  let ia := PresheafOfCategories.fiberIsoOfSectionOfObj_eq eR
    (x.hx.trans hb) (x'.hx.trans hb') h1
  let ib := PresheafOfCategories.fiberIsoOfSectionOfObj_eq eR
    (x.hy.trans hb) (x'.hy.trans hb') h2
  let i : x.x ≅ x'.x := Functor.Fiber.fiberInclusion.mapIso ia
  let j : x.y ≅ x'.y := Functor.Fiber.fiberInclusion.mapIso ib
  have hi : (relation B S hS 𝒰 𝒳 f).val.p.IsHomLift (𝟙 W) i.hom := ia.hom.2
  have hj : (relation B S hS 𝒰 𝒳 f).val.p.IsHomLift (𝟙 W) j.hom := ib.hom.2
  have hv : ∀ (y : composable B S hS 𝒰 𝒳 f), y.base = W →
      𝒰.val.p.IsHomLift (𝟙 W) y.iso.hom := fun y hy => by
    have := y.vertical; rwa [hy] at this
  have hib : 𝒰.val.p.IsHomLift (𝟙 W) i.hom.b :=
    TwoFibreProductOver.isHomLift_b i.hom (𝟙 W) hi
  have hja : 𝒰.val.p.IsHomLift (𝟙 W) j.hom.a :=
    TwoFibreProductOver.isHomLift_a j.hom (𝟙 W) hj
  have hw : (TwoFibreProductOver.snd 𝒰.val.p 𝒰.val.p 𝒳.val.p f.toFunctor
        f.toFunctor).map i.hom ≫ x'.iso.hom =
      x.iso.hom ≫ (TwoFibreProductOver.fst 𝒰.val.p 𝒰.val.p 𝒳.val.p f.toFunctor
        f.toFunctor).map j.hom :=
    Functor.hom_unique_of_fiber_isThin 𝒰.val.p (𝟙 W) (hset.fiber_isThin W) _ _
      (Functor.isHomLift_comp_of_isHomLift_id 𝒰.val.p _ _ (𝟙 W) hib (hv x' hb'))
      (Functor.isHomLift_comp_of_isHomLift_id 𝒰.val.p _ _ (𝟙 W) (hv x hb) hja)
  let e : x ≅ x' := TwoFibreProductOver.isoMkVertical i j hi hj hw
  exact PresheafOfCategories.sectionOfObj_eq_of_hom eR _ _
    ((composition B S hS 𝒰 𝒳 f).toFunctor.map e.hom)
    (Functor.isHomLift_map_of_comp_eq' (composition B S hS 𝒰 𝒳 f).w (𝟙 W) e.hom
      (TwoFibreProductOver.structureFunctor_isHomLift e.hom (𝟙 W) hi))

/-- The value of the composition law at a composable pair of sections exists: some composable
pair of arrows names that pair of sections, and the section named by its composite is independent
of the choice. -/
theorem exists_compositionValue
    (hset : 𝒰.val.p.IsFiberedInSetoids) {W : BigFppfOver B S hS}
    (q : (Deformation.composableArrows U.obj R.obj
      (relationSourceMap eU eR) (relationTargetMap eU eR)).obj (op W)) :
    ∃ z : R.obj.obj (op W), ∀ (x : composable B S hS 𝒰 𝒳 f) (hb : x.base = W),
      PresheafOfCategories.sectionOfObj eR x.x (x.hx.trans hb) = q.1.1 →
      PresheafOfCategories.sectionOfObj eR x.y (x.hy.trans hb) = q.1.2 →
      PresheafOfCategories.sectionOfObj eR
        ((composition B S hS 𝒰 𝒳 f).toFunctor.obj x) (composition_obj_over hb) = z := by
  obtain ⟨x₀, hb₀, h₁, h₂⟩ := exists_composable eU eR q.1.1 q.1.2 q.2
  refine ⟨PresheafOfCategories.sectionOfObj eR _ (composition_obj_over hb₀), ?_⟩
  intro x hb e₁ e₂
  exact sectionOfObj_composition_congr eR hset hb hb₀ (e₁.trans h₁.symm) (e₂.trans h₂.symm)

/-- The value of the composition law at a composable pair of sections. -/
noncomputable def compositionValue
    (hset : 𝒰.val.p.IsFiberedInSetoids) {W : BigFppfOver B S hS}
    (q : (Deformation.composableArrows U.obj R.obj
      (relationSourceMap eU eR) (relationTargetMap eU eR)).obj (op W)) :
    R.obj.obj (op W) :=
  (exists_compositionValue eU eR hset q).choose

/-- The defining property of the value of the composition law: on the pair of sections named by
the two components of a composable pair of arrows, it is the section named by the composite. -/
theorem sectionOfObj_composition_eq_compositionValue
    (hset : 𝒰.val.p.IsFiberedInSetoids) {W : BigFppfOver B S hS}
    (q : (Deformation.composableArrows U.obj R.obj
      (relationSourceMap eU eR) (relationTargetMap eU eR)).obj (op W))
    (x : composable B S hS 𝒰 𝒳 f) (hb : x.base = W)
    (e₁ : PresheafOfCategories.sectionOfObj eR x.x (x.hx.trans hb) = q.1.1)
    (e₂ : PresheafOfCategories.sectionOfObj eR x.y (x.hy.trans hb) = q.1.2) :
    PresheafOfCategories.sectionOfObj eR
        ((composition B S hS 𝒰 𝒳 f).toFunctor.obj x) (composition_obj_over hb) =
      compositionValue eU eR hset q :=
  (exists_compositionValue eU eR hset q).choose_spec x hb e₁ e₂

/-- The composition law of the self-intersection groupoid: the morphism of presheaves
`R ×_{s, U, t} R ⟶ R` induced by the outer projection of Stacks 04T4 (3). -/
noncomputable def compositionLaw (hset : 𝒰.val.p.IsFiberedInSetoids) :
    Deformation.composableArrows U.obj R.obj
      (relationSourceMap eU eR) (relationTargetMap eU eR) ⟶ R.obj where
  app T := ↾ fun q => compositionValue eU eR hset (W := T.unop) q
  naturality := by
    intro X Y g
    ext q
    change compositionValue eU eR hset (W := Y.unop) _ =
      R.obj.map g (compositionValue eU eR hset (W := X.unop) q)
    obtain ⟨x, hb, h₁, h₂⟩ := exists_composable eU eR q.1.1 q.1.2 q.2
    obtain ⟨x', φ, hφ⟩ :=
      (isFiberedInGroupoids_composableProjection (𝒰 := 𝒰) (𝒳 := 𝒳) (f := f)).exists_lift
        g.unop x hb
    have hb' : x'.base = Y.unop :=
      CategoryTheory.IsHomLift.domain_eq (composableProjection B S hS 𝒰 𝒳 f) g.unop φ
    have hφa : (relation B S hS 𝒰 𝒳 f).val.p.IsHomLift g.unop φ.a :=
      TwoFibreProductOver.isHomLift_a φ g.unop hφ
    have hφb : (relation B S hS 𝒰 𝒳 f).val.p.IsHomLift g.unop φ.b :=
      TwoFibreProductOver.isHomLift_b φ g.unop hφ
    have e₁ : PresheafOfCategories.sectionOfObj eR x'.x (x'.hx.trans hb') =
        R.obj.map g q.1.1 := by
      rw [← h₁]
      exact PresheafOfCategories.sectionOfObj_map eR (x.hx.trans hb) (x'.hx.trans hb')
        g.unop φ.a hφa
    have e₂ : PresheafOfCategories.sectionOfObj eR x'.y (x'.hy.trans hb') =
        R.obj.map g q.1.2 := by
      rw [← h₂]
      exact PresheafOfCategories.sectionOfObj_map eR (x.hy.trans hb) (x'.hy.trans hb')
        g.unop φ.b hφb
    have hcomp : PresheafOfCategories.sectionOfObj eR
          ((composition B S hS 𝒰 𝒳 f).toFunctor.obj x') (composition_obj_over hb') =
        R.obj.map g (PresheafOfCategories.sectionOfObj eR
          ((composition B S hS 𝒰 𝒳 f).toFunctor.obj x) (composition_obj_over hb)) :=
      PresheafOfCategories.sectionOfObj_map eR (composition_obj_over hb)
        (composition_obj_over hb') g.unop ((composition B S hS 𝒰 𝒳 f).toFunctor.map φ)
        (Functor.isHomLift_map_of_comp_eq' (composition B S hS 𝒰 𝒳 f).w g.unop φ hφ)
    rw [← sectionOfObj_composition_eq_compositionValue eU eR hset q x hb h₁ h₂, ← hcomp]
    exact (sectionOfObj_composition_eq_compositionValue eU eR hset _ x' hb' e₁ e₂).symm

/-- The two sections named by the components of a composable pair of arrows are
composable. -/
theorem composable_sectionOfObj_compatible (x : composable B S hS 𝒰 𝒳 f) :
    (relationSourceMap eU eR).app (op x.base)
        (PresheafOfCategories.sectionOfObj eR x.x x.hx) =
      (relationTargetMap eU eR).app (op x.base)
        (PresheafOfCategories.sectionOfObj eR x.y x.hy) := by
  rw [relationSourceMap_sectionOfObj eU eR x.x x.hx,
    relationTargetMap_sectionOfObj eU eR x.y x.hy]
  exact PresheafOfCategories.sectionOfObj_eq_of_hom eU _ _ x.iso.hom x.vertical

/-- On the pair of sections named by the two components of a composable pair of arrows of the
relation, the composition law is the section named by the composite of that pair. -/
theorem compositionLaw_app_sectionOfObj
    (hset : 𝒰.val.p.IsFiberedInSetoids) (x : composable B S hS 𝒰 𝒳 f) :
    (compositionLaw eU eR hset).app (op x.base)
        ⟨(PresheafOfCategories.sectionOfObj eR x.x x.hx,
          PresheafOfCategories.sectionOfObj eR x.y x.hy),
          composable_sectionOfObj_compatible eU eR x⟩ =
      PresheafOfCategories.sectionOfObj eR
        ((composition B S hS 𝒰 𝒳 f).toFunctor.obj x) (composition_obj_over rfl) :=
  (sectionOfObj_composition_eq_compositionValue eU eR hset _ x rfl rfl rfl).symm

/-- The section named by an object is, up to the identification of the two base objects, the
element named by the image of that object in the category of elements. -/
theorem heq_sectionOfObj {𝒮 : Type (u + 1)} [Category.{u} 𝒮] {q : 𝒮 ⥤ BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : StacksRepresentableCFG.EquivalenceOver q
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (z : 𝒮) {W : BigFppfOver B S hS} (h : q.obj z = W) :
    HEq (PresheafOfCategories.sectionOfObj e z h)
      (Discrete.as (e.hom.functor.obj z).fiber) :=
  cast_heq _ _

/-- For the groupoid in algebraic spaces built from the composition law, every composable pair
of arrows of the relation is matched by a point of the algebraic-space fibre product of the source
and the target whose two projections name the two components of the pair and whose image under
the composition of the groupoid names the composite. -/
theorem exists_comp_compatible
    (hset : 𝒰.val.p.IsFiberedInSetoids)
    (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid
      ((ObjectProperty.homMk (relationSourceMap eU eR) : R ⟶ U).hom.app T)
      ((ObjectProperty.homMk (relationTargetMap eU eR) : R ⟶ U).hom.app T)
      (fun q => (compositionLaw eU eR hset).app T q)))
    (x : composable B S hS 𝒰 𝒳 f) :
    ∃ p : (AlgebraicSpaces.fiberProduct B S hS
        (GroupoidInAlgebraicSpaces.ofComposable U R
          (ObjectProperty.homMk (relationSourceMap eU eR))
          (ObjectProperty.homMk (relationTargetMap eU eR))
          (compositionLaw eU eR hset) hG).source
        (GroupoidInAlgebraicSpaces.ofComposable U R
          (ObjectProperty.homMk (relationSourceMap eU eR))
          (ObjectProperty.homMk (relationTargetMap eU eR))
          (compositionLaw eU eR hset) hG).target).obj.obj (op x.base),
      HEq ((pullback.fst (relationSourceMap eU eR) (relationTargetMap eU eR)).app
            (op x.base) p)
          (Discrete.as (eR.hom.functor.obj x.x).fiber) ∧
        HEq ((pullback.snd (relationSourceMap eU eR) (relationTargetMap eU eR)).app
            (op x.base) p)
          (Discrete.as (eR.hom.functor.obj x.y).fiber) ∧
        HEq ((GroupoidInAlgebraicSpaces.ofComposable U R
            (ObjectProperty.homMk (relationSourceMap eU eR))
            (ObjectProperty.homMk (relationTargetMap eU eR))
            (compositionLaw eU eR hset) hG).comp.hom.app (op x.base) p)
          (Discrete.as (eR.hom.functor.obj
            ((composition B S hS 𝒰 𝒳 f).toFunctor.obj x)).fiber) := by
  refine ⟨(composableToPullback (relationSourceMap eU eR) (relationTargetMap eU eR)).app
    (op x.base) ⟨(PresheafOfCategories.sectionOfObj eR x.x x.hx,
      PresheafOfCategories.sectionOfObj eR x.y x.hy),
      composable_sectionOfObj_compatible eU eR x⟩, ?_, ?_, ?_⟩
  · rw [pullbackFst_app_composableToPullback]
    exact heq_sectionOfObj eR x.x x.hx
  · rw [pullbackSnd_app_composableToPullback]
    exact heq_sectionOfObj eR x.y x.hy
  · exact (heq_of_eq ((compOfComposable_app_composableToPullback _ _
      (compositionLaw eU eR hset) _ _).trans (compositionLaw_app_sectionOfObj eU eR hset x))).trans
      (heq_sectionOfObj eR _ (composition_obj_over rfl))

/-- The chosen equivalence of `𝒰` with the category of elements of `U` agrees on objects with
the canonical projection of Stacks 044R from the object space to the quotient stack, composed with
the canonical map of Stacks 044Q from the pointwise groupoid fibration. -/
theorem sourcePresentation_pointwise
    (hset : 𝒰.val.p.IsFiberedInSetoids)
    (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid
      ((ObjectProperty.homMk (relationSourceMap eU eR) : R ⟶ U).hom.app T)
      ((ObjectProperty.homMk (relationTargetMap eU eR) : R ⟶ U).hom.app T)
      (fun q => (compositionLaw eU eR hset).app T q)))
    (z : 𝒰.val.obj) :
    (pointwiseToQuotientStack (GroupoidInAlgebraicSpaces.ofComposable U R
          (ObjectProperty.homMk (relationSourceMap eU eR))
          (ObjectProperty.homMk (relationTargetMap eU eR))
          (compositionLaw eU eR hset) hG)).obj
        ⟨(eU.hom.functor.obj z).base, Discrete.as (eU.hom.functor.obj z).fiber⟩ =
      (quotientStackProjection (GroupoidInAlgebraicSpaces.ofComposable U R
          (ObjectProperty.homMk (relationSourceMap eU eR))
          (ObjectProperty.homMk (relationTargetMap eU eR))
          (compositionLaw eU eR hset) hG)).obj (eU.hom.functor.obj z) :=
  (quotientStackProjection_obj _ _).symm

/-! ### The pointwise groupoid, and the groupoid in algebraic spaces itself

At every object `W` of the site the sections of `U` over `W` form a groupoid whose arrows from `x`
to `y` are the sections of `R` over `W` with source `x` and target `y`, composed by the
composition law above. It is the groupoid induced by indexing a section `a` by the object
`f (j⁻¹ a)` of the opposite of the fibre of `𝒳` over `W`, where `j⁻¹ a` is the chosen
representative `AlgebraicGeometry.Stack.SelfIntersection.representingObj` of `a`.
-/

/-- The chosen representative of a section of the object space: the object of `𝒰` that the
backward 1-morphism of the chosen equivalence attaches to it. -/
noncomputable def representingObj {W : BigFppfOver B S hS} (a : U.obj.obj (op W)) : 𝒰.val.obj :=
  eU.inv.functor.obj ⟨W, Discrete.mk a⟩

/-- The chosen representative of a section over `W` lies over `W`. -/
theorem representingObj_over {W : BigFppfOver B S hS} (a : U.obj.obj (op W)) :
    𝒰.val.p.obj (representingObj eU a) = W :=
  Functor.congr_obj eU.inv.w
    (⟨W, Discrete.mk a⟩ : (presheafOfCategories (U.obj ⋙ typeToCat)).obj)

/-- The chosen representative of a section names that section back. -/
theorem sectionOfObj_representingObj {W : BigFppfOver B S hS} (a : U.obj.obj (op W)) :
    PresheafOfCategories.sectionOfObj eU (representingObj eU a) (representingObj_over eU a) = a :=
  PresheafOfCategories.sectionOfObj_inv_obj eU ⟨W, Discrete.mk a⟩

/-- The image under `f` of the chosen representative of a section over `W` lies over `W`. -/
theorem fObj_over {W : BigFppfOver B S hS} (a : U.obj.obj (op W)) :
    𝒳.val.p.obj (f.toFunctor.obj (representingObj eU a)) = W :=
  (Functor.congr_obj f.w (representingObj eU a)).trans (representingObj_over eU a)

/-- The fibres of the target are groupoids. -/
theorem isGroupoid_targetFiber (W : BigFppfOver B S hS) : IsGroupoid (𝒳.val.p.Fiber W) :=
  ⟨fun g => (𝒳.isFiberedInGroupoids.fiber_isGroupoid W).all_isIso g⟩

/-- The groupoid structure on the opposite of a fibre of the target. -/
@[instance_reducible]
noncomputable def groupoidTargetFiberOp (W : BigFppfOver B S hS) :
    Groupoid.{u} ((𝒳.val.p.Fiber W)ᵒᵖ) :=
  Groupoid.ofIsIso (C := (𝒳.val.p.Fiber W)ᵒᵖ) (fun {X Y} g => by
    have := isGroupoid_targetFiber (𝒳 := 𝒳) W
    have : IsIso g.unop := IsGroupoid.all_isIso g.unop
    exact (isIso_op_iff g.unop).2 inferInstance)

/-- A morphism between two fibre objects of the target, read in the total category as an
isomorphism: the fibre is a groupoid. -/
noncomputable def fiberHomIso {W : BigFppfOver B S hS} (a b : U.obj.obj (op W))
    (α : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU a)) :
    f.toFunctor.obj (representingObj eU b) ≅ f.toFunctor.obj (representingObj eU a) :=
  have := isGroupoid_targetFiber (𝒳 := 𝒳) W
  have : IsIso α := IsGroupoid.all_isIso α
  Functor.Fiber.fiberInclusion.mapIso (asIso α)

/-- The underlying morphism of `AlgebraicGeometry.Stack.SelfIntersection.fiberHomIso` is the given
one. -/
@[simp] theorem fiberHomIso_hom {W : BigFppfOver B S hS} (a b : U.obj.obj (op W))
    (α : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU a)) :
    (fiberHomIso eU a b α).hom = Functor.Fiber.fiberInclusion.map α := rfl

/-- The arrow of the relation attached to a morphism `f (j⁻¹ b) ⟶ f (j⁻¹ a)` of a fibre of the
target: the triple `(j⁻¹ b, j⁻¹ a, α)`, read as an arrow from the class of `a` to the class
of `b`. -/
noncomputable def relationOfFiberHom {W : BigFppfOver B S hS} (a b : U.obj.obj (op W))
    (α : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU a)) :
    (relation B S hS 𝒰 𝒳 f).val.obj where
  base := W
  x := representingObj eU b
  y := representingObj eU a
  hx := representingObj_over eU b
  hy := representingObj_over eU a
  iso := fiberHomIso eU a b α
  vertical := α.2

/-- The section of the arrow space named by
`AlgebraicGeometry.Stack.SelfIntersection.relationOfFiberHom`. -/
noncomputable def arrowOfFiberHom {W : BigFppfOver B S hS} (a b : U.obj.obj (op W))
    (α : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU a)) :
    R.obj.obj (op W) :=
  PresheafOfCategories.sectionOfObj eR (relationOfFiberHom eU a b α) rfl

/-- The source of the section attached to a fibre morphism is the section it starts at. -/
theorem relationSourceMap_arrowOfFiberHom {W : BigFppfOver B S hS} (a b : U.obj.obj (op W))
    (α : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU a)) :
    (relationSourceMap eU eR).app (op W) (arrowOfFiberHom eU eR a b α) = a :=
  (relationSourceMap_sectionOfObj eU eR (relationOfFiberHom eU a b α) rfl).trans
    (sectionOfObj_representingObj eU a)

/-- The target of the section attached to a fibre morphism is the section it ends at. -/
theorem relationTargetMap_arrowOfFiberHom {W : BigFppfOver B S hS} (a b : U.obj.obj (op W))
    (α : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU a)) :
    (relationTargetMap eU eR).app (op W) (arrowOfFiberHom eU eR a b α) = b :=
  (relationTargetMap_sectionOfObj eU eR (relationOfFiberHom eU a b α) rfl).trans
    (sectionOfObj_representingObj eU b)

/-- Two fibre morphisms with the same endpoints naming the same section are equal. -/
theorem arrowOfFiberHom_injective (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {W : BigFppfOver B S hS} (a b : U.obj.obj (op W))
    (α α' : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU a))
    (h : arrowOfFiberHom eU eR a b α = arrowOfFiberHom eU eR a b α') : α = α' := by
  have : 𝒰.val.p.IsFiberedInSetoids := hsetU
  have i := PresheafOfCategories.fiberIsoOfSectionOfObj_eq eR
    (z := relationOfFiberHom eU a b α) (z' := relationOfFiberHom eU a b α') rfl rfl h
  have hlift : (relation B S hS 𝒰 𝒳 f).val.p.IsHomLift (𝟙 W)
      (Functor.Fiber.fiberInclusion.map i.hom) := i.hom.2
  have ha : 𝒰.val.p.IsHomLift (𝟙 W)
      (Functor.Fiber.fiberInclusion.map i.hom).a :=
    TwoFibreProductOver.isHomLift_a _ (𝟙 W) hlift
  have hb : 𝒰.val.p.IsHomLift (𝟙 W)
      (Functor.Fiber.fiberInclusion.map i.hom).b :=
    TwoFibreProductOver.isHomLift_b _ (𝟙 W) hlift
  have hid : ∀ {c : 𝒰.val.obj}, 𝒰.val.p.obj c = W → ∀ m : c ⟶ c,
      𝒰.val.p.IsHomLift (𝟙 W) m → m = 𝟙 c := fun hc m hm =>
    Functor.hom_unique_of_fiber_isThin 𝒰.val.p (𝟙 W) (hsetU.fiber_isThin W) _ _ hm
      (CategoryTheory.IsHomLift.id hc)
  have hw := (Functor.Fiber.fiberInclusion.map i.hom).w
  rw [hid (representingObj_over eU b) _ ha, hid (representingObj_over eU a) _ hb] at hw
  erw [f.toFunctor.map_id, f.toFunctor.map_id, Category.id_comp, Category.comp_id] at hw
  exact Functor.Fiber.hom_ext hw.symm

/-- Every section of the arrow space with prescribed source and target comes from a fibre
morphism. -/
theorem exists_fiberHom_of_arrow
    {W : BigFppfOver B S hS} (a b : U.obj.obj (op W)) (r : R.obj.obj (op W))
    (hs : (relationSourceMap eU eR).app (op W) r = a)
    (ht : (relationTargetMap eU eR).app (op W) r = b) :
    ∃ α : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU a),
      arrowOfFiberHom eU eR a b α = r := by
  obtain ⟨ρ, hρ, hρs⟩ := PresheafOfCategories.exists_sectionOfObj eR r
  have hxb : PresheafOfCategories.sectionOfObj eU ρ.x (relation_obj_x hρ) =
      PresheafOfCategories.sectionOfObj eU (representingObj eU b) (representingObj_over eU b) := by
    rw [sectionOfObj_representingObj eU b, ← ht, ← hρs,
      relationTargetMap_sectionOfObj eU eR ρ hρ]
  have hya : PresheafOfCategories.sectionOfObj eU ρ.y (relation_obj_y hρ) =
      PresheafOfCategories.sectionOfObj eU (representingObj eU a) (representingObj_over eU a) := by
    rw [sectionOfObj_representingObj eU a, ← hs, ← hρs,
      relationSourceMap_sectionOfObj eU eR ρ hρ]
  let ix := PresheafOfCategories.fiberIsoOfSectionOfObj_eq eU
    (relation_obj_x hρ) (representingObj_over eU b) hxb
  let iy := PresheafOfCategories.fiberIsoOfSectionOfObj_eq eU
    (relation_obj_y hρ) (representingObj_over eU a) hya
  have hρb : ρ.base = W := hρ
  have hρiso : 𝒳.val.p.IsHomLift (𝟙 W) ρ.iso.hom := by
    have := ρ.vertical; rwa [hρb] at this
  have h1 : 𝒳.val.p.IsHomLift (𝟙 W)
      (f.toFunctor.map (Functor.Fiber.fiberInclusion.map ix.inv)) :=
    Functor.isHomLift_map_of_comp_eq' f.w (𝟙 W) _ ix.inv.2
  have h2 : 𝒳.val.p.IsHomLift (𝟙 W)
      (f.toFunctor.map (Functor.Fiber.fiberInclusion.map iy.hom)) :=
    Functor.isHomLift_map_of_comp_eq' f.w (𝟙 W) _ iy.hom.2
  let αmor : f.toFunctor.obj (representingObj eU b) ⟶ f.toFunctor.obj (representingObj eU a) :=
    f.toFunctor.map (Functor.Fiber.fiberInclusion.map ix.inv) ≫ ρ.iso.hom ≫
      f.toFunctor.map (Functor.Fiber.fiberInclusion.map iy.hom)
  have hαlift : 𝒳.val.p.IsHomLift (𝟙 W) αmor :=
    Functor.isHomLift_comp_of_isHomLift_id 𝒳.val.p _ _ (𝟙 W) h1
      (Functor.isHomLift_comp_of_isHomLift_id 𝒳.val.p _ _ (𝟙 W) hρiso h2)
  refine ⟨⟨αmor, hαlift⟩, ?_⟩
  have hcancel : Functor.Fiber.fiberInclusion.map iy.hom ≫
      Functor.Fiber.fiberInclusion.map iy.inv = 𝟙 ρ.y :=
    (Functor.Fiber.fiberInclusion.map_comp iy.hom iy.inv).symm.trans
      ((congrArg Functor.Fiber.fiberInclusion.map iy.hom_inv_id).trans
        (Functor.Fiber.fiberInclusion.map_id _))
  have hCD : f.toFunctor.map (Functor.Fiber.fiberInclusion.map iy.hom) ≫
      f.toFunctor.map (Functor.Fiber.fiberInclusion.map iy.inv) = 𝟙 _ :=
    (f.toFunctor.map_comp _ _).symm.trans
      ((congrArg f.toFunctor.map hcancel).trans (f.toFunctor.map_id _))
  have hinner : (ρ.iso.hom ≫
        f.toFunctor.map (Functor.Fiber.fiberInclusion.map iy.hom)) ≫
      f.toFunctor.map (Functor.Fiber.fiberInclusion.map iy.inv) = ρ.iso.hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => ρ.iso.hom ≫ m) hCD).trans (Category.comp_id _))
  have hw : f.toFunctor.map (Functor.Fiber.fiberInclusion.map ix.inv) ≫ ρ.iso.hom =
      αmor ≫ f.toFunctor.map (Functor.Fiber.fiberInclusion.map iy.inv) :=
    ((Category.assoc _ _ _).trans
      (congrArg (fun m => f.toFunctor.map
        (Functor.Fiber.fiberInclusion.map ix.inv) ≫ m) hinner)).symm
  let e : relationOfFiberHom eU a b ⟨αmor, hαlift⟩ ≅ ρ :=
    TwoFibreProductOver.isoMkVertical (U := W)
      (Functor.Fiber.fiberInclusion.mapIso ix.symm)
      (Functor.Fiber.fiberInclusion.mapIso iy.symm) ix.inv.2 iy.inv.2 hw
  exact (PresheafOfCategories.sectionOfObj_eq_of_fiberIso eR rfl hρ (Functor.Fiber.isoMk e
    (TwoFibreProductOver.structureFunctor_isHomLift e.hom (𝟙 W) ix.inv.2))).trans hρs

/-- The hom-set bijection of the pointwise groupoid: morphisms `f (j⁻¹ b) ⟶ f (j⁻¹ a)` of the
fibre of `𝒳` over `W`, equivalently morphisms from the index of `a` to the index of `b` in the
opposite of that fibre, are exactly the sections of the arrow space over `W` with source `a` and
target `b`. -/
noncomputable def arrowEquivOfSection (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {W : BigFppfOver B S hS} (a b : U.obj.obj (op W)) :
    ((op (Functor.Fiber.mk (fObj_over (f := f) eU a)) : (𝒳.val.p.Fiber W)ᵒᵖ) ⟶
        op (Functor.Fiber.mk (fObj_over (f := f) eU b))) ≃
      { r : R.obj.obj (op W) //
        (relationSourceMap eU eR).app (op W) r = a ∧
          (relationTargetMap eU eR).app (op W) r = b } where
  toFun g := ⟨arrowOfFiberHom eU eR a b g.unop,
    relationSourceMap_arrowOfFiberHom eU eR a b g.unop,
    relationTargetMap_arrowOfFiberHom eU eR a b g.unop⟩
  invFun r :=
    (Classical.choose (exists_fiberHom_of_arrow eU eR a b r.1 r.2.1 r.2.2)).op
  left_inv g := by
    refine Quiver.Hom.unop_inj ?_
    refine arrowOfFiberHom_injective eU eR hsetU a b _ _ ?_
    exact Classical.choose_spec (exists_fiberHom_of_arrow eU eR a b
      (arrowOfFiberHom eU eR a b g.unop)
      (relationSourceMap_arrowOfFiberHom eU eR a b g.unop)
      (relationTargetMap_arrowOfFiberHom eU eR a b g.unop))
  right_inv r :=
    Subtype.ext (Classical.choose_spec
      (exists_fiberHom_of_arrow eU eR a b r.1 r.2.1 r.2.2))

/-- The composable pair of arrows of the relation attached to two composable fibre morphisms: its
comparison isomorphism is the identity of the chosen representative of the middle section. -/
noncomputable def composableOfFiberHoms {W : BigFppfOver B S hS} (x y z : U.obj.obj (op W))
    (g : (Functor.Fiber.mk (fObj_over (f := f) eU y) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU x))
    (fh : (Functor.Fiber.mk (fObj_over (f := f) eU z) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU y)) :
    composable B S hS 𝒰 𝒳 f where
  base := W
  x := relationOfFiberHom eU y z fh
  y := relationOfFiberHom eU x y g
  hx := rfl
  hy := rfl
  iso := Iso.refl (representingObj eU y)
  vertical := CategoryTheory.IsHomLift.id (representingObj_over eU y)

/-- The section named by the composite of the composable pair of arrows attached to two
composable fibre morphisms is the section attached to the composed fibre morphism. -/
theorem sectionOfObj_composition_composableOfFiberHoms
    {W : BigFppfOver B S hS} (x y z : U.obj.obj (op W))
    (g : (Functor.Fiber.mk (fObj_over (f := f) eU y) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU x))
    (fh : (Functor.Fiber.mk (fObj_over (f := f) eU z) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU y)) :
    PresheafOfCategories.sectionOfObj eR
        ((composition B S hS 𝒰 𝒳 f).toFunctor.obj (composableOfFiberHoms eU x y z g fh))
        (composition_obj_over rfl) =
      arrowOfFiberHom eU eR x z (fh ≫ g) := by
  have hL : f.toFunctor.map (𝟙 (representingObj eU z)) ≫
      Functor.Fiber.fiberInclusion.map (fh ≫ g) =
        Functor.Fiber.fiberInclusion.map fh ≫ Functor.Fiber.fiberInclusion.map g :=
    (congrArg (fun m => m ≫ Functor.Fiber.fiberInclusion.map (fh ≫ g))
        (f.toFunctor.map_id (representingObj eU z))).trans
      ((Category.id_comp _).trans (Functor.Fiber.fiberInclusion.map_comp fh g))
  have hR : (Functor.Fiber.fiberInclusion.map fh ≫
        (f.toFunctor.map (𝟙 (representingObj eU y)) ≫
          Functor.Fiber.fiberInclusion.map g)) ≫
      f.toFunctor.map (𝟙 (representingObj eU x)) =
        Functor.Fiber.fiberInclusion.map fh ≫ Functor.Fiber.fiberInclusion.map g :=
    (congrArg (fun m => (Functor.Fiber.fiberInclusion.map fh ≫
          (f.toFunctor.map (𝟙 (representingObj eU y)) ≫
            Functor.Fiber.fiberInclusion.map g)) ≫ m)
        (f.toFunctor.map_id (representingObj eU x))).trans
      ((Category.comp_id _).trans
        ((congrArg (fun m => Functor.Fiber.fiberInclusion.map fh ≫
            (m ≫ Functor.Fiber.fiberInclusion.map g))
              (f.toFunctor.map_id (representingObj eU y))).trans
          (congrArg (fun m => Functor.Fiber.fiberInclusion.map fh ≫ m)
            (Category.id_comp _))))
  let e : (composition B S hS 𝒰 𝒳 f).toFunctor.obj (composableOfFiberHoms eU x y z g fh) ≅
      relationOfFiberHom eU x z (fh ≫ g) :=
    TwoFibreProductOver.isoMkVertical (U := W)
      (Iso.refl (representingObj eU z)) (Iso.refl (representingObj eU x))
      (CategoryTheory.IsHomLift.id (representingObj_over eU z))
      (CategoryTheory.IsHomLift.id (representingObj_over eU x)) (hL.trans hR.symm)
  exact PresheafOfCategories.sectionOfObj_eq_of_fiberIso eR (composition_obj_over rfl) rfl
    (Functor.Fiber.isoMk e (TwoFibreProductOver.structureFunctor_isHomLift e.hom (𝟙 W)
      (CategoryTheory.IsHomLift.id (representingObj_over eU z))))

/-- At every object of the site the source, target and composition law of the self-intersection
make the sections of the object space into a groupoid whose arrows are the sections of the arrow
space. -/
theorem nonempty_pointwiseGroupoid (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (T : (BigFppfOver B S hS)ᵒᵖ) :
    Nonempty (Deformation.PointwiseGroupoid
      ((ObjectProperty.homMk (relationSourceMap eU eR) : R ⟶ U).hom.app T)
      ((ObjectProperty.homMk (relationTargetMap eU eR) : R ⟶ U).hom.app T)
      (fun q => (compositionLaw eU eR hsetU).app T q)) := by
  let _ := groupoidTargetFiberOp (𝒳 := 𝒳) T.unop
  refine ⟨Deformation.PointwiseGroupoid.ofIndexing
    (fun a => (op (Functor.Fiber.mk (fObj_over (f := f) eU a)) :
      (𝒳.val.p.Fiber T.unop)ᵒᵖ))
    _ _ _ (fun a b => arrowEquivOfSection eU eR hsetU a b) ?_⟩
  intro x y z g fh
  exact ((compositionLaw_app_sectionOfObj eU eR hsetU
      (composableOfFiberHoms eU x y z g.unop fh.unop)).trans
    (sectionOfObj_composition_composableOfFiberHoms eU eR x y z g.unop fh.unop)).symm

/-- The groupoid in algebraic spaces of Stacks 04T4 (4): the chosen representing spaces of `𝒰`
and of its self-intersection, with the two projections as source and target and the composition
law above, form a groupoid in algebraic spaces over the final algebraic space. -/
noncomputable def selfIntersectionGroupoid (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    GroupoidInAlgebraicSpaces B S hS (Space.terminalSpace B S hS) :=
  GroupoidInAlgebraicSpaces.ofComposable U R
    (ObjectProperty.homMk (relationSourceMap eU eR))
    (ObjectProperty.homMk (relationTargetMap eU eR))
    (compositionLaw eU eR hsetU) (nonempty_pointwiseGroupoid eU eR hsetU)

/-- The object space of the self-intersection groupoid is the chosen representing space of `𝒰`. -/
@[simp] theorem selfIntersectionGroupoid_objects (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    (selfIntersectionGroupoid eU eR hsetU).objects = U := rfl

/-- The arrow space of the self-intersection groupoid is the chosen representing space of the
relation. -/
@[simp] theorem selfIntersectionGroupoid_arrows (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    (selfIntersectionGroupoid eU eR hsetU).arrows = R := rfl

/-- The source of the self-intersection groupoid is the morphism induced by the second
projection. -/
@[simp] theorem selfIntersectionGroupoid_source (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    (selfIntersectionGroupoid eU eR hsetU).source =
      ObjectProperty.homMk (relationSourceMap eU eR) := rfl

/-- The target of the self-intersection groupoid is the morphism induced by the first
projection. -/
@[simp] theorem selfIntersectionGroupoid_target (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    (selfIntersectionGroupoid eU eR hsetU).target =
      ObjectProperty.homMk (relationTargetMap eU eR) := rfl

/-- For the self-intersection groupoid, every composable pair of arrows of the relation is
matched by a point of the fibre product of the source and the target whose two projections name
the two components of the pair and whose image under the composition names the composite. -/
theorem exists_comp_compatible_groupoid (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (x : composable B S hS 𝒰 𝒳 f) :
    ∃ p : (AlgebraicSpaces.fiberProduct B S hS
        (selfIntersectionGroupoid eU eR hsetU).source
        (selfIntersectionGroupoid eU eR hsetU).target).obj.obj (op x.base),
      HEq ((pullback.fst (relationSourceMap eU eR) (relationTargetMap eU eR)).app
            (op x.base) p)
          (Discrete.as (eR.hom.functor.obj x.x).fiber) ∧
        HEq ((pullback.snd (relationSourceMap eU eR) (relationTargetMap eU eR)).app
            (op x.base) p)
          (Discrete.as (eR.hom.functor.obj x.y).fiber) ∧
        HEq ((selfIntersectionGroupoid eU eR hsetU).comp.hom.app (op x.base) p)
          (Discrete.as (eR.hom.functor.obj
            ((composition B S hS 𝒰 𝒳 f).toFunctor.obj x)).fiber) :=
  exists_comp_compatible eU eR hsetU (nonempty_pointwiseGroupoid eU eR hsetU) x

/-- For the self-intersection groupoid, the chosen equivalence of `𝒰` with the category of
elements of `U` agrees on objects with the canonical projection to the quotient stack, composed
with the canonical map from the pointwise groupoid fibration. -/
theorem sourcePresentation_pointwise_groupoid (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (z : 𝒰.val.obj) :
    (pointwiseToQuotientStack (selfIntersectionGroupoid eU eR hsetU)).obj
        ⟨(eU.hom.functor.obj z).base, Discrete.as (eU.hom.functor.obj z).fiber⟩ =
      (quotientStackProjection (selfIntersectionGroupoid eU eR hsetU)).obj
        (eU.hom.functor.obj z) :=
  sourcePresentation_pointwise eU eR hsetU (nonempty_pointwiseGroupoid eU eR hsetU) z

end AlgebraicGeometry.Stack.SelfIntersection

end
