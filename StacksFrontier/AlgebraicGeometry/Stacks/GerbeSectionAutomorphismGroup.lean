module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.TrivialActionComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionIsomProjection
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionQuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeAutomorphismGroupAlgebraicSpace

/-!
# The automorphism group of a section is the stabilizer of its self-intersection groupoid

Let `𝒳` be an algebraic stack over `S`, let `Z` be an algebraic space over `S` with algebraic stack
`𝒰`, let `π : 𝒳 ⟶ 𝒰` be a 1-morphism and let `x : 𝒰 ⟶ 𝒳` be a section of `π`, a 1-morphism
together with a 2-isomorphism `x ≫ π ≅ 𝟙 𝒰`. Write `G = Isom_𝒳(x, x)` with its group law of
**Stacks 06PP**, composition of automorphisms
(`AlgebraicGeometry.Stack.relativeAutomorphismGroupAlgebraicSpace` at `π`: since `𝒰` is an
algebraic space, every vertical automorphism of a point of `𝒳` is killed by `π`, so the relative
automorphisms of `x` over `𝒰` are all its automorphisms). Let `R ⇉ Z` be the self-intersection
groupoid of Stacks 04T4 (4), whose arrow space represents `𝒰 ×_{x, 𝒳, x} 𝒰`. Its source and target
agree, so its stabilizer group of Stacks 0447 is all of `R`.

The proof of **Stacks 06QG** identifies `R` with `G` and asserts that the composition law of `R`
"agrees with the group law on `G` (proof omitted)". This file supplies that proof: the
identification `G ≅ R` over `Z` sends an automorphism `φ` of `x(z)` to the arrow `(z, z, φ)`, and
composition in the groupoid composes the underlying isomorphisms in the diagrammatic order, so
`(z, z, φ) ∘ (z, z, ψ) = (z, z, φ ≫ ψ)`, while the group law of `G` is `φ * ψ = ψ ≫ φ`. The
identification is therefore an anti-isomorphism, and composing it with inversion in `G` gives an
isomorphism of group objects over `Z`, `AlgebraicGeometry.Stack.sectionAutomorphismStabilizerIso`.

## Main definitions

* `AlgebraicGeometry.Stack.relativeAutomorphismToIsomSpace`: the comparison of the presheaf
  `Isom_{𝒳/𝒰}(x, x)` of relative automorphisms with the presheaf `Isom_𝒳(x, x)` of all
  automorphisms, the identity on sections.
* `AlgebraicGeometry.Stack.relativeAutomorphismToArrows`: the composite comparison
  `Isom_𝒳(x, x) ⟶ R`, `φ ↦ (z, z, φ)`.
* `AlgebraicGeometry.Stack.sectionAutomorphismStabilizerIso`: the isomorphism of group objects
  over `Z` between `Isom_𝒳(x, x)` with the group law of Stacks 06PP and the stabilizer of the
  self-intersection groupoid with the group law of Stacks 0447.

## Main results

* `AlgebraicGeometry.Stack.isIso_relativeAutomorphismToIsomSpace`: for `𝒰` an algebraic space,
  `Isom_{𝒳/𝒰}(x, x) = Isom_𝒳(x, x)`.
* `AlgebraicGeometry.Stack.compositionLaw_isomSpaceToRelationSpace`: the composite of the arrows
  `(z, z, φ)` and `(z, z, ψ)` of the self-intersection groupoid is `(z, z, φ ≫ ψ)`.
* `AlgebraicGeometry.Stack.isMonHom_sectionAutomorphismStabilizerIso`: the isomorphism above is a
  homomorphism of group objects.

## References

* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open CategoryTheory.TwoFibreProductOver.DiagonalFibre

namespace AlgebraicGeometry.Stack

universe u w

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 : AlgebraicStacks.{u, w} B S hS}
variable (π : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Z hZ)
  (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)

/-! ### `Isom_{𝒳/𝒰}(x, x) = Isom_𝒳(x, x)` -/

/-- **Every vertical endomorphism of a point of `𝒳` is killed by a 1-morphism to an algebraic
space**: the fibres of the category of elements of `Z` are discrete. -/
theorem map_eq_id_of_isHomLift_id_algebraicSpaceStack
    {a : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj}
    (φ : x.hom.hom.toFunctor.obj a ⟶ x.hom.hom.toFunctor.obj a)
    (hφ : 𝒳.val.val.p.IsHomLift
      (𝟙 ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.obj a)) φ) :
    π.hom.hom.toFunctor.map φ = 𝟙 _ := by
  have hset : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.IsFiberedInSetoids :=
    SelfIntersection.isFiberedInSetoids_source
      (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ)
  have h₁ : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.IsHomLift
      (𝟙 ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.obj a))
      (π.hom.hom.toFunctor.map φ) :=
    Functor.isHomLift_map_of_comp_eq' π.hom.hom.w
      (𝟙 ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.obj a)) φ hφ
  have h₂ : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.IsHomLift
      (𝟙 ((algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.obj a))
      (𝟙 (π.hom.hom.toFunctor.obj (x.hom.hom.toFunctor.obj a))) :=
    IsHomLift.id ((Functor.congr_obj π.hom.hom.w _).trans (Functor.congr_obj x.hom.hom.w a))
  exact Functor.hom_unique_of_fiber_isThin _ _ (hset.fiber_isThin _) _ _ h₁ h₂

/-- The comparison on sections: a relative automorphism of `x` at a point `z` of `Z` is an
automorphism of `x(z)` in the fibre of `𝒳`. -/
def relativeAutomorphismToIsomSection (W : (BigFppfOver B S hS)ᵒᵖ)
    (s : (relativeAutomorphismTotalPresheaf B S hS Z hZ π x).obj W) :
    isomSection B S hS Z hZ x x W :=
  ⟨s.1, ⟨⟨s.2.1.1, s.2.1.2⟩, isIso_fiberHom B S hS 𝒳 _⟩⟩

/-- **The comparison `Isom_{𝒳/𝒰}(x, x) ⟶ Isom_𝒳(x, x)`**, the identity on sections. It is
natural because the restriction of a relative automorphism and the restriction of an
isomorphism are characterised by the same universal property. -/
noncomputable def relativeAutomorphismToIsomSpace :
    relativeAutomorphismTotalPresheaf B S hS Z hZ π x ⟶ isomSpaceOverSpace B S hS Z hZ x x where
  app W := ↾ relativeAutomorphismToIsomSection B S hS Z hZ π x W
  naturality W W' g := by
    ext s
    obtain ⟨z, φ⟩ := s
    refine congrArg (fun ψ => (⟨Z.map g z, ⟨ψ, isIso_fiberHom B S hS 𝒳 ψ⟩⟩ :
      isomSection B S hS Z hZ x x W')) ?_
    exact pointRestrict_uniq B S hS Z hZ x x g z (Z.map g z) rfl ⟨φ.1.1, φ.1.2⟩ _
      (VertHom.restrict_fac 𝒳.val.isFiberedInGroupoids x.hom.hom.w x.hom.hom.w _ φ.1)

/-- The comparison is over `Z`. -/
theorem relativeAutomorphismToIsomSpace_comp_proj :
    relativeAutomorphismToIsomSpace B S hS Z hZ π x ≫ isomSpaceOverSpaceProj B S hS Z hZ x x =
      PresheafOfCategories.elementsTotalProj Z (relativeAutomorphismPresheaf B S hS Z hZ π x) :=
  rfl

/-- **`Isom_{𝒳/𝒰}(x, x) = Isom_𝒳(x, x)` for `𝒰` an algebraic space**: the comparison is an
isomorphism of presheaves, every automorphism of a point of `𝒳` being killed by `π`
(`AlgebraicGeometry.Stack.map_eq_id_of_isHomLift_id_algebraicSpaceStack`). -/
theorem isIso_relativeAutomorphismToIsomSpace :
    IsIso (relativeAutomorphismToIsomSpace B S hS Z hZ π x) := by
  have (V : (BigFppfOver B S hS)ᵒᵖ) :
      IsIso ((relativeAutomorphismToIsomSpace B S hS Z hZ π x).app V) := by
    refine (isIso_iff_bijective _).2 (Function.bijective_iff_has_inverse.2
      ⟨fun t => ⟨t.1, ⟨⟨t.2.1.1, t.2.1.2⟩,
        map_eq_id_of_isHomLift_id_algebraicSpaceStack B S hS Z hZ π x t.2.1.1 t.2.1.2⟩⟩,
        fun _ => rfl, fun _ => rfl⟩)
  exact NatIso.isIso_of_isIso_app _

/-! ### Composition in the self-intersection groupoid of a section -/

variable {R : AlgebraicSpaces B S hS}
variable (eR : StacksRepresentableCFG.EquivalenceOver
  (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
    𝒳.val x.hom.hom).val.p
  (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- **Composition of the arrows named by two automorphisms.** In the self-intersection groupoid
of Stacks 04T4 (4), the composite of the arrows `(z, z, φ)` and `(z, z, ψ)` named by two
automorphisms of `x(z)` is the arrow `(z, z, φ ≫ ψ)`: the composite of Stacks 04T4 (3) composes
the underlying isomorphisms, with the identity of the middle point in between. This is the
computation the source omits when it asserts that the composition law of `R` agrees with the
group law of `G`. -/
theorem compositionLaw_isomSpaceToRelationSpace (W : BigFppfOver B S hS)
    (z : Z.obj (op W))
    (φ ψ : pointFiber B S hS Z hZ x W z ⟶ pointFiber B S hS Z hZ x W z) (h) :
    (SelfIntersection.compositionLaw
        (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR
        (SelfIntersection.isFiberedInSetoids_source
          (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ))).app (op W)
      ⟨((isomSpaceToRelationSpace B S hS Z hZ x eR).app (op W)
          ⟨z, ⟨φ, isIso_fiberHom B S hS 𝒳 φ⟩⟩,
        (isomSpaceToRelationSpace B S hS Z hZ x eR).app (op W)
          ⟨z, ⟨ψ, isIso_fiberHom B S hS 𝒳 ψ⟩⟩), h⟩ =
      (isomSpaceToRelationSpace B S hS Z hZ x eR).app (op W)
        ⟨z, ⟨φ ≫ ψ, isIso_fiberHom B S hS 𝒳 _⟩⟩ := by
  set eU := algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ
  let r : isomSection B S hS Z hZ x x (op W) →
      (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
        𝒳.val x.hom.hom).val.obj :=
    fun s => (isomToRelation B S hS Z hZ x).toFunctor.obj ⟨W, Discrete.mk s⟩
  let s₁ : isomSection B S hS Z hZ x x (op W) := ⟨z, ⟨φ, isIso_fiberHom B S hS 𝒳 φ⟩⟩
  let s₂ : isomSection B S hS Z hZ x x (op W) := ⟨z, ⟨ψ, isIso_fiberHom B S hS 𝒳 ψ⟩⟩
  let s₃ : isomSection B S hS Z hZ x x (op W) := ⟨z, ⟨φ ≫ ψ, isIso_fiberHom B S hS 𝒳 _⟩⟩
  let c : SelfIntersection.composable B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
      𝒳.val x.hom.hom :=
    SelfIntersection.composableMk (W := W)
      (rfl : (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
        𝒳.val x.hom.hom).val.p.obj (r s₁) = W)
      (rfl : (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
        𝒳.val x.hom.hom).val.p.obj (r s₂) = W) (Iso.refl _)
  have hU : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.IsHomLift (𝟙 W)
      (𝟙 (spacePoint.{u, w} B S hS Z hZ W z)) :=
    IsHomLift.id rfl
  have hw : x.hom.hom.toFunctor.map (𝟙 (spacePoint.{u, w} B S hS Z hZ W z)) ≫
        (r s₃).iso.hom =
      ((SelfIntersection.composition B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
        𝒳.val x.hom.hom).toFunctor.obj c).iso.hom ≫
        x.hom.hom.toFunctor.map (𝟙 (spacePoint.{u, w} B S hS Z hZ W z)) := by
    have h₁ : (r s₃).iso.hom =
        Functor.Fiber.fiberInclusion.map φ ≫ Functor.Fiber.fiberInclusion.map ψ := rfl
    have h₂ : ((SelfIntersection.composition B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
          𝒳.val x.hom.hom).toFunctor.obj c).iso.hom =
        Functor.Fiber.fiberInclusion.map φ ≫
          x.hom.hom.toFunctor.map (𝟙 (spacePoint.{u, w} B S hS Z hZ W z)) ≫
            Functor.Fiber.fiberInclusion.map ψ := rfl
    have hI : x.hom.hom.toFunctor.map (𝟙 (spacePoint.{u, w} B S hS Z hZ W z)) = 𝟙 _ :=
      x.hom.hom.toFunctor.map_id _
    have e₁ : x.hom.hom.toFunctor.map (𝟙 (spacePoint.{u, w} B S hS Z hZ W z)) ≫
        (Functor.Fiber.fiberInclusion.map φ ≫ Functor.Fiber.fiberInclusion.map ψ) =
        Functor.Fiber.fiberInclusion.map φ ≫ Functor.Fiber.fiberInclusion.map ψ :=
      (congrArg (· ≫ (Functor.Fiber.fiberInclusion.map φ ≫
        Functor.Fiber.fiberInclusion.map ψ)) hI).trans (Category.id_comp _)
    have e₂ : (Functor.Fiber.fiberInclusion.map φ ≫
          x.hom.hom.toFunctor.map (𝟙 (spacePoint.{u, w} B S hS Z hZ W z)) ≫
            Functor.Fiber.fiberInclusion.map ψ) ≫
          x.hom.hom.toFunctor.map (𝟙 (spacePoint.{u, w} B S hS Z hZ W z)) =
        Functor.Fiber.fiberInclusion.map φ ≫ Functor.Fiber.fiberInclusion.map ψ :=
      (congrArg (fun m => (Functor.Fiber.fiberInclusion.map φ ≫ m ≫
          Functor.Fiber.fiberInclusion.map ψ) ≫ m) hI).trans
        ((Category.comp_id _).trans
          (congrArg (Functor.Fiber.fiberInclusion.map φ ≫ ·) (Category.id_comp _)))
    exact (congrArg (_ ≫ ·) h₁).trans (e₁.trans (e₂.symm.trans (congrArg (· ≫ _) h₂.symm)))
  let e := TwoFibreProductOver.isoMkVertical (U := W)
    (P := (SelfIntersection.composition B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
        𝒳.val x.hom.hom).toFunctor.obj c) (Q := r s₃)
    (Iso.refl (spacePoint.{u, w} B S hS Z hZ W z)) (Iso.refl (spacePoint.{u, w} B S hS Z hZ W z))
    hU hU hw
  have hpair : (⟨((isomSpaceToRelationSpace B S hS Z hZ x eR).app (op W) s₁,
        (isomSpaceToRelationSpace B S hS Z hZ x eR).app (op W) s₂), h⟩ :
        (Deformation.composableArrows _ R.obj _ _).obj (op W)) =
      ⟨(PresheafOfCategories.sectionOfObj eR c.x c.hx,
        PresheafOfCategories.sectionOfObj eR c.y c.hy),
        SelfIntersection.composable_sectionOfObj_compatible eU eR c⟩ :=
    Subtype.ext (Prod.ext (isomSpaceToRelationSpace_app B S hS Z hZ x eR W s₁)
      (isomSpaceToRelationSpace_app B S hS Z hZ x eR W s₂))
  refine (congrArg _ hpair).trans ?_
  refine (SelfIntersection.compositionLaw_app_sectionOfObj eU eR _ c).trans ?_
  refine Eq.trans ?_ (isomSpaceToRelationSpace_app B S hS Z hZ x eR W s₃).symm
  exact PresheafOfCategories.sectionOfObj_eq_of_fiberIso eR
    (SelfIntersection.composition_obj_over rfl) rfl
    (Functor.Fiber.isoMk e (TwoFibreProductOver.structureFunctor_isHomLift e.hom (𝟙 W) hU))

/-! ### The comparison with the arrow space and the group law -/

/-- **The comparison `Isom_𝒳(x, x) ⟶ R`**: an automorphism `φ` of `x(z)` goes to the section of
the arrow space `R` named by the arrow `(z, z, φ)` of the self-intersection. -/
noncomputable def relativeAutomorphismToArrows :
    relativeAutomorphismTotalPresheaf B S hS Z hZ π x ⟶ R.obj :=
  relativeAutomorphismToIsomSpace B S hS Z hZ π x ≫ isomSpaceToRelationSpace B S hS Z hZ x eR

/-- The comparison `Isom_𝒳(x, x) ⟶ R` followed by the source morphism `R ⟶ Z` is the structure
morphism of `Isom_𝒳(x, x)`. -/
theorem relativeAutomorphismToArrows_comp_relationSourceMap :
    relativeAutomorphismToArrows B S hS Z hZ π x eR ≫
        SelfIntersection.relationSourceMap
          (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR =
      PresheafOfCategories.elementsTotalProj Z (relativeAutomorphismPresheaf B S hS Z hZ π x) :=
  (Category.assoc _ _ _).trans
    (congrArg (relativeAutomorphismToIsomSpace B S hS Z hZ π x ≫ ·)
      (isomSpaceToRelationSpace_comp_relationSourceMap B S hS Z hZ x eR))

/-- The self-intersection groupoid `R ⇉ Z` of Stacks 04T4 (4) of the 1-morphism `x`, at the
tautological presentation of `𝒰` by `Z` and at the presentation `eR` of `𝒰 ×_{x, 𝒳, x} 𝒰`. -/
noncomputable abbrev sectionSelfIntersectionGroupoid :=
  (SelfIntersection.selfIntersectionPresentation
    (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR 𝒳.property).groupoid

/-- For a section, the source and the target of the self-intersection groupoid agree. -/
theorem sectionSelfIntersectionGroupoid_source_eq_target
    (hx : x ≫ π ≅ 𝟙 (algebraicSpaceStack.{u, w} B S hS Z hZ)) :
    (sectionSelfIntersectionGroupoid B S hS Z hZ x eR).source =
      (sectionSelfIntersectionGroupoid B S hS Z hZ x eR).target :=
  SelfIntersection.source_eq_target_selfIntersectionPresentation
    (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR 𝒳.property π.hom
    (Bicategory.InducedBicategory.isoHom (f := x ≫ π)
      (g := 𝟙 (algebraicSpaceStack.{u, w} B S hS Z hZ)) hx)

/-- The stabilizer group of Stacks 0447 of the self-intersection groupoid, read as an object of
the slice over `Z`: the object space of that groupoid is `Z` itself. -/
noncomputable def sectionStabilizer : Over Z :=
  GroupoidInAlgebraicSpaces.stabilizer (sectionSelfIntersectionGroupoid B S hS Z hZ x eR)

/-- The stabilizer of the self-intersection groupoid is an algebraic space. -/
theorem isAlgebraicSpace_sectionStabilizer :
    IsAlgebraicSpace B S hS (sectionStabilizer B S hS Z hZ x eR).left :=
  GroupoidInAlgebraicSpaces.isAlgebraicSpace_stabilizer _

/-- The group law of **Stacks 0447** on the stabilizer of the self-intersection groupoid:
groupoid composition (`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizer_mul_comp_arrow`). -/
noncomputable instance instGrpObjSectionStabilizer :
    GrpObj (sectionStabilizer B S hS Z hZ x eR) :=
  (GroupoidInAlgebraicSpaces.stabilizerGroupStructure _).1

/-- **`Isom_𝒳(x, x)` is the stabilizer of the self-intersection groupoid, as an object over `Z`**:
the comparison `φ ↦ (z, z, φ)` is an isomorphism onto the arrow space, which for a section is the
whole stabilizer. As a map of group objects it reverses the order of multiplication
(`AlgebraicGeometry.Stack.relativeAutomorphismStabilizerIso_mul`). -/
noncomputable def relativeAutomorphismStabilizerIso
    (hx : x ≫ π ≅ 𝟙 (algebraicSpaceStack.{u, w} B S hS Z hZ)) :
    (relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X ≅
      sectionStabilizer B S hS Z hZ x eR :=
  Over.isoMk
    (@asIso _ _ _ _ (relativeAutomorphismToIsomSpace B S hS Z hZ π x)
        (isIso_relativeAutomorphismToIsomSpace B S hS Z hZ π x) ≪≫
      @asIso _ _ _ _ (isomSpaceToRelationSpace B S hS Z hZ x eR)
        (isIso_isomSpaceToRelationSpace B S hS Z hZ x eR π hx) ≪≫
      (GroupoidInAlgebraicSpaces.stabilizerArrowIso _
        (sectionSelfIntersectionGroupoid_source_eq_target B S hS Z hZ π x eR hx)).symm) (by
    have h1 : (GroupoidInAlgebraicSpaces.stabilizerArrowIso _
          (sectionSelfIntersectionGroupoid_source_eq_target B S hS Z hZ π x eR hx)).inv ≫
        (GroupoidInAlgebraicSpaces.stabilizer
          (sectionSelfIntersectionGroupoid B S hS Z hZ x eR)).hom =
        (sectionSelfIntersectionGroupoid B S hS Z hZ x eR).source.hom :=
      pullback.lift_snd _ _ _
    exact (congrArg (fun k => relativeAutomorphismToIsomSpace B S hS Z hZ π x ≫
        isomSpaceToRelationSpace B S hS Z hZ x eR ≫ k) h1).trans
      (relativeAutomorphismToArrows_comp_relationSourceMap B S hS Z hZ π x eR))

/-- The arrow underlying the image of an automorphism under
`AlgebraicGeometry.Stack.relativeAutomorphismStabilizerIso` is the comparison
`AlgebraicGeometry.Stack.relativeAutomorphismToArrows`. -/
theorem relativeAutomorphismStabilizerIso_hom_left_comp_stabilizerArrow
    (hx : x ≫ π ≅ 𝟙 (algebraicSpaceStack.{u, w} B S hS Z hZ)) :
    (relativeAutomorphismStabilizerIso B S hS Z hZ π x eR hx).hom.left ≫
        GroupoidInAlgebraicSpaces.stabilizerArrow
          (sectionSelfIntersectionGroupoid B S hS Z hZ x eR) =
      relativeAutomorphismToArrows B S hS Z hZ π x eR :=
  congrArg (fun k => relativeAutomorphismToIsomSpace B S hS Z hZ π x ≫
      isomSpaceToRelationSpace B S hS Z hZ x eR ≫ k)
    (GroupoidInAlgebraicSpaces.stabilizerArrowIso _
      (sectionSelfIntersectionGroupoid_source_eq_target B S hS Z hZ π x eR hx)).inv_hom_id

/-- The multiplication of `Isom_𝒳(x, x)` over `Z` is the lax monoidal comparison of the total
presheaf functor followed by the image of the multiplication of the presheaf of groups of
relative automorphisms. -/
theorem relativeAutomorphismGroupAlgebraicSpace_mul :
    letI := PresheafOfCategories.elementsTotalFunctorMonoidal Z
    letI := relativeAutomorphismPresheafGrpObj B S hS Z hZ π x
    (μ : (relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X ⊗
      (relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X ⟶ _) =
    Functor.LaxMonoidal.μ (PresheafOfCategories.elementsTotalFunctor Z)
      (relativeAutomorphismPresheaf B S hS Z hZ π x)
      (relativeAutomorphismPresheaf B S hS Z hZ π x) ≫
      (PresheafOfCategories.elementsTotalFunctor Z).map
        μ[relativeAutomorphismPresheaf B S hS Z hZ π x] :=
  rfl

/-- **The comparison reverses multiplication.** For two generalized points `a, b` of
`Isom_𝒳(x, x)`, the image of `a * b` (which is `b` followed by `a`) is the product, in the
stabilizer, of the image of `b` and the image of `a`: the arrow `(z, z, ψ ≫ φ)` is the composite of
`(z, z, ψ)` and `(z, z, φ)` (`AlgebraicGeometry.Stack.compositionLaw_isomSpaceToRelationSpace`). -/
theorem relativeAutomorphismStabilizerIso_mul
    (hx : x ≫ π ≅ 𝟙 (algebraicSpaceStack.{u, w} B S hS Z hZ)) (T : Over Z)
    (a b : T ⟶ (relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X) :
    (a * b) ≫ (relativeAutomorphismStabilizerIso B S hS Z hZ π x eR hx).hom =
      (b ≫ (relativeAutomorphismStabilizerIso B S hS Z hZ π x eR hx).hom) *
        (a ≫ (relativeAutomorphismStabilizerIso B S hS Z hZ π x eR hx).hom) := by
  let _ := PresheafOfCategories.elementsTotalFunctorMonoidal Z
  let _ := relativeAutomorphismPresheafGrpObj B S hS Z hZ π x
  set 𝒢 := sectionSelfIntersectionGroupoid B S hS Z hZ x eR
  set hst := sectionSelfIntersectionGroupoid_source_eq_target B S hS Z hZ π x eR hx
  set Φ := relativeAutomorphismStabilizerIso B S hS Z hZ π x eR hx
  set J := relativeAutomorphismToArrows B S hS Z hZ π x eR
  have hΦJ : Φ.hom.left ≫ GroupoidInAlgebraicSpaces.stabilizerArrow 𝒢 = J :=
    relativeAutomorphismStabilizerIso_hom_left_comp_stabilizerArrow B S hS Z hZ π x eR hx
  let m : T ⟶ (PresheafOfCategories.elementsTotalFunctor Z).obj
      (relativeAutomorphismPresheaf B S hS Z hZ π x ⊗
        relativeAutomorphismPresheaf B S hS Z hZ π x) :=
    lift a b ≫ Functor.LaxMonoidal.μ (PresheafOfCategories.elementsTotalFunctor Z)
      (relativeAutomorphismPresheaf B S hS Z hZ π x) (relativeAutomorphismPresheaf B S hS Z hZ π x)
  have hma : m ≫ (PresheafOfCategories.elementsTotalFunctor Z).map
      (fst (relativeAutomorphismPresheaf B S hS Z hZ π x)
        (relativeAutomorphismPresheaf B S hS Z hZ π x)) = a :=
    (Category.assoc _ _ _).trans ((congrArg (lift a b ≫ ·)
      (Functor.Monoidal.μ_fst (PresheafOfCategories.elementsTotalFunctor Z)
        (relativeAutomorphismPresheaf B S hS Z hZ π x)
        (relativeAutomorphismPresheaf B S hS Z hZ π x))).trans (lift_fst a b))
  have hmb : m ≫ (PresheafOfCategories.elementsTotalFunctor Z).map
      (snd (relativeAutomorphismPresheaf B S hS Z hZ π x)
        (relativeAutomorphismPresheaf B S hS Z hZ π x)) = b :=
    (Category.assoc _ _ _).trans ((congrArg (lift a b ≫ ·)
      (Functor.Monoidal.μ_snd (PresheafOfCategories.elementsTotalFunctor Z)
        (relativeAutomorphismPresheaf B S hS Z hZ π x)
        (relativeAutomorphismPresheaf B S hS Z hZ π x))).trans (lift_snd a b))
  have hab : a * b = m ≫ (PresheafOfCategories.elementsTotalFunctor Z).map
      μ[relativeAutomorphismPresheaf B S hS Z hZ π x] :=
    (Hom.mul_def a b).trans ((congrArg (lift a b ≫ ·)
      (relativeAutomorphismGroupAlgebraicSpace_mul B S hS Z hZ π x)).trans
        (Category.assoc _ _ _).symm)
  obtain ⟨w, hw⟩ :=
    GroupoidInAlgebraicSpaces.stabilizer_mul_comp_arrow 𝒢 T (b ≫ Φ.hom) (a ≫ Φ.hom)
  have hb' : (b ≫ Φ.hom).left ≫ GroupoidInAlgebraicSpaces.stabilizerArrow 𝒢 =
      (m ≫ (PresheafOfCategories.elementsTotalFunctor Z).map
        (snd (relativeAutomorphismPresheaf B S hS Z hZ π x)
          (relativeAutomorphismPresheaf B S hS Z hZ π x))).left ≫ J :=
    (congrArg (b.left ≫ ·) hΦJ).trans (congrArg (fun k : T ⟶ _ => k.left ≫ J) hmb.symm)
  have ha' : (a ≫ Φ.hom).left ≫ GroupoidInAlgebraicSpaces.stabilizerArrow 𝒢 =
      (m ≫ (PresheafOfCategories.elementsTotalFunctor Z).map
        (fst (relativeAutomorphismPresheaf B S hS Z hZ π x)
          (relativeAutomorphismPresheaf B S hS Z hZ π x))).left ≫ J :=
    (congrArg (a.left ≫ ·) hΦJ).trans (congrArg (fun k : T ⟶ _ => k.left ≫ J) hma.symm)
  have hw' : ((m ≫ (PresheafOfCategories.elementsTotalFunctor Z).map
        (snd (relativeAutomorphismPresheaf B S hS Z hZ π x)
          (relativeAutomorphismPresheaf B S hS Z hZ π x))).left ≫ J) ≫ 𝒢.source.hom =
      ((m ≫ (PresheafOfCategories.elementsTotalFunctor Z).map
        (fst (relativeAutomorphismPresheaf B S hS Z hZ π x)
          (relativeAutomorphismPresheaf B S hS Z hZ π x))).left ≫ J) ≫ 𝒢.target.hom :=
    (congrArg (· ≫ 𝒢.source.hom) hb'.symm).trans (w.trans (congrArg (· ≫ 𝒢.target.hom) ha'))
  have key : ∀ (V : BigFppfOver B S hS)
      (q : ((PresheafOfCategories.elementsTotalFunctor Z).obj
        (relativeAutomorphismPresheaf B S hS Z hZ π x ⊗
          relativeAutomorphismPresheaf B S hS Z hZ π x)).left.obj (op V)) (h),
      J.app (op V) (((PresheafOfCategories.elementsTotalFunctor Z).map
          μ[relativeAutomorphismPresheaf B S hS Z hZ π x]).left.app (op V) q) =
        𝒢.toGroupoidInFunctors.compose (op V)
          (J.app (op V) (((PresheafOfCategories.elementsTotalFunctor Z).map
            (snd (relativeAutomorphismPresheaf B S hS Z hZ π x)
              (relativeAutomorphismPresheaf B S hS Z hZ π x))).left.app (op V) q))
          (J.app (op V) (((PresheafOfCategories.elementsTotalFunctor Z).map
            (fst (relativeAutomorphismPresheaf B S hS Z hZ π x)
              (relativeAutomorphismPresheaf B S hS Z hZ π x))).left.app (op V) q)) h := by
    rintro V ⟨z, p₁, p₂⟩ h
    refine Eq.symm ((compose_ofComposable ⟨Z, hZ⟩ R
      (ObjectProperty.homMk (SelfIntersection.relationSourceMap
        (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR))
      (ObjectProperty.homMk (SelfIntersection.relationTargetMap
        (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR))
      (SelfIntersection.compositionLaw
        (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR
        (SelfIntersection.isFiberedInSetoids_source
          (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ)))
      (SelfIntersection.nonempty_pointwiseGroupoid
        (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR
        (SelfIntersection.isFiberedInSetoids_source
          (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ)))
      (op V) _ _ h).trans ?_)
    exact compositionLaw_isomSpaceToRelationSpace B S hS Z hZ x eR V z
      ⟨p₂.1.1, p₂.1.2⟩ ⟨p₁.1.1, p₁.1.2⟩ _
  apply Over.OverMorphism.ext
  refine (Iso.cancel_iso_hom_right _ _ (GroupoidInAlgebraicSpaces.stabilizerArrowIso 𝒢 hst)).1 ?_
  change ((a * b) ≫ Φ.hom).left ≫ GroupoidInAlgebraicSpaces.stabilizerArrow 𝒢 =
    (lift (b ≫ Φ.hom) (a ≫ Φ.hom) ≫ μ).left ≫ GroupoidInAlgebraicSpaces.stabilizerArrow 𝒢
  refine Eq.trans ?_ hw.symm
  calc ((a * b) ≫ Φ.hom).left ≫ GroupoidInAlgebraicSpaces.stabilizerArrow 𝒢
      = ((m ≫ (PresheafOfCategories.elementsTotalFunctor Z).map
          μ[relativeAutomorphismPresheaf B S hS Z hZ π x]).left ≫ J :
            T.left ⟶ 𝒢.arrows.obj) :=
        (congrArg ((a * b).left ≫ ·) hΦJ).trans (congrArg (fun k : T ⟶ _ => k.left ≫ J) hab)
    _ = (GroupoidInAlgebraicSpaces.groupoidCompose 𝒢
          ((m ≫ (PresheafOfCategories.elementsTotalFunctor Z).map
            (snd (relativeAutomorphismPresheaf B S hS Z hZ π x)
              (relativeAutomorphismPresheaf B S hS Z hZ π x))).left ≫ J)
          ((m ≫ (PresheafOfCategories.elementsTotalFunctor Z).map
            (fst (relativeAutomorphismPresheaf B S hS Z hZ π x)
              (relativeAutomorphismPresheaf B S hS Z hZ π x))).left ≫ J) hw' :
            T.left ⟶ 𝒢.arrows.obj) := by
        refine Functor.presheafHom_ext fun V t => ?_
        obtain ⟨V⟩ := V
        rw [GroupoidInAlgebraicSpaces.groupoidCompose_eval]
        exact key V (m.left.app (op V) t) _
    _ = GroupoidInAlgebraicSpaces.groupoidCompose 𝒢
          ((b ≫ Φ.hom).left ≫ GroupoidInAlgebraicSpaces.stabilizerArrow 𝒢)
          ((a ≫ Φ.hom).left ≫ GroupoidInAlgebraicSpaces.stabilizerArrow 𝒢) w :=
        GroupoidInAlgebraicSpaces.groupoidCompose_congr 𝒢 hw' w hb'.symm ha'.symm

/-- **`Isom_𝒳(x, x)` with the group law of Stacks 06PP is the stabilizer of the self-intersection
groupoid with the group law of Stacks 0447**, as group objects over `Z`: inversion in
`Isom_𝒳(x, x)` followed by `φ ↦ (z, z, φ)`, so that `φ` goes to the arrow `(z, z, φ⁻¹)`. -/
noncomputable def sectionAutomorphismStabilizerIso
    (hx : x ≫ π ≅ 𝟙 (algebraicSpaceStack.{u, w} B S hS Z hZ)) :
    (relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X ≅
      sectionStabilizer B S hS Z hZ x eR :=
  asIso ι[(relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X] ≪≫
    relativeAutomorphismStabilizerIso B S hS Z hZ π x eR hx

/-- **The isomorphism `Isom_𝒳(x, x) ≅ G/U` is a homomorphism of group objects** over `Z`, for the
group law of Stacks 06PP on the source and the group law of Stacks 0447 on the target. -/
theorem isMonHom_sectionAutomorphismStabilizerIso
    (hx : x ≫ π ≅ 𝟙 (algebraicSpaceStack.{u, w} B S hS Z hZ)) :
    IsMonHom (sectionAutomorphismStabilizerIso B S hS Z hZ π x eR hx).hom := by
  set H := (relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X
  set Φ := relativeAutomorphismStabilizerIso B S hS Z hZ π x eR hx
  have hmul := relativeAutomorphismStabilizerIso_mul B S hS Z hZ π x eR hx
  have hone : (1 : 𝟙_ (Over Z) ⟶ H) ≫ Φ.hom = 1 := by
    have h := hmul (𝟙_ _) 1 1
    rw [mul_one] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  refine ⟨?_, ?_⟩
  · change η ≫ ι[H] ≫ Φ.hom = η
    have hH : (η : 𝟙_ (Over Z) ⟶ H) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over Z))) (𝟙 _), Category.id_comp]
    have hS : (η : 𝟙_ (Over Z) ⟶ sectionStabilizer B S hS Z hZ x eR) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit (𝟙_ (Over Z))) (𝟙 _), Category.id_comp]
    rw [hH, hS, ← Category.assoc, ← Hom.inv_def, inv_one, hone]
  · change μ ≫ ι[H] ≫ Φ.hom = ((ι[H] ≫ Φ.hom) ⊗ₘ (ι[H] ≫ Φ.hom)) ≫ μ
    have h1 : (μ : H ⊗ H ⟶ H) = fst H H * snd H H := by
      rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    rw [h1, ← Category.assoc, ← Hom.inv_def, mul_inv_rev, hmul, Hom.inv_def, Hom.inv_def,
      Category.assoc, Category.assoc, Hom.mul_def, lift_fst_comp_snd_comp]

end AlgebraicGeometry.Stack

end
