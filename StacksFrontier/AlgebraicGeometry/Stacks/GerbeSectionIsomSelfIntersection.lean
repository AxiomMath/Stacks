module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceOverAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersection
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The self-intersection of a section is its automorphism sheaf (`ℛ = Isom_𝒳(x, x)`)

Let `𝒳` be an algebraic stack over `S`, let `Z` be an algebraic space over `S` and write
`𝒰 = 𝒮_Z` for the algebraic stack of `Z`. Let `x : 𝒰 ⟶ 𝒳` be an algebraic-space-valued point of
`𝒳` which is a **section** of a 1-morphism `π : 𝒳 ⟶ 𝒰`, that is a `x ≫ π ≅ 𝟙 𝒰`. There are two
descriptions of one and the same object attached to these data:

```text
ℛ = 𝒰 ×_{x, 𝒳, x} 𝒰          the self-intersection of Stacks 04T4
G = Isom_𝒳(x, x)             the automorphism sheaf of Stacks 06PP
```

The first paragraph of the proof of **Stacks 06QG** identifies them: the morphism
`ℛ ⟶ 𝒰 × 𝒰` factors through the diagonal, so `ℛ = 𝒰 ×_{𝒰 × 𝒰} ℛ = Isom_𝒳(x, x)`. **This file
proves that identification**, over the big fppf site of `S`, with `Isom_𝒳(x, x)` taken in its
explicit presheaf form `AlgebraicGeometry.Stack.isomSpaceOverSpace` — the sheaf whose sections
over `W` are the pairs of a point `z` of `Z` over `W` and an automorphism of `x(z)` in the fibre
of `𝒳` over `W`.

## Main definitions

* `AlgebraicGeometry.Stack.isomProjFunctor`: the projection of the category of elements of
  `Isom_𝒳(x, x)` to the category of elements of `Z`, which forgets the automorphism.
* `AlgebraicGeometry.Stack.isomTautologicalIso`: the tautological automorphism of `x` over that
  category of elements.
* `AlgebraicGeometry.Stack.isomToRelation`: **the comparison 1-morphism**
  `𝒮_{Isom_𝒳(x, x)} ⟶ ℛ`, sending an automorphism `φ` of `x(z)` to the arrow `(z, z, φ)` of the
  self-intersection. It is the 1-morphism into the 2-fibre product induced by the projection to
  `Z` on both legs and by the tautological automorphism as comparison 2-morphism, so it is a
  1-morphism over the site by construction.

## Main results

* `AlgebraicGeometry.Stack.isomToRelation_faithful` and
  `AlgebraicGeometry.Stack.isomToRelation_full`: the comparison is fully faithful. **No
  hypothesis on `x` is used**: a morphism of a category of elements of a presheaf of sets is
  determined by its base, which gives faithfulness and pins both components of a morphism of
  `ℛ` down, and the comparison square of such a morphism then says, by the uniqueness half of
  `AlgebraicGeometry.Stack.pointRestrict_uniq`, exactly that one automorphism restricts to the
  other.
* `AlgebraicGeometry.Stack.relation_x_eq_y_of_section`: **the trivial action of Stacks 06QG
  part (1), at the level of objects.** For a section the two ends of an arrow of `ℛ` are *equal*,
  not merely isomorphic: applying `π` to the comparison isomorphism and conjugating by the
  2-isomorphism of the section gives a vertical morphism between them, and the fibres of a
  category of elements of a presheaf of sets are discrete. Only the section is used; no gerbe
  hypothesis enters, exactly as for
  `AlgebraicGeometry.Stack.SelfIntersection.relationSourceMap_eq_relationTargetMap`, of which
  this is the object-level form.
* `AlgebraicGeometry.Stack.exists_eq_isomToRelation_obj` and
  `AlgebraicGeometry.Stack.essSurj_isomToRelation`: hence every object of `ℛ` *is* an
  automorphism of `x` at a point of `Z`, so the comparison is essentially surjective.
* `AlgebraicGeometry.Stack.isEquivalence_isomToRelation` and
  `AlgebraicGeometry.Stack.nonempty_equivalenceOver_relation_isomSpaceOverSpace`: **the
  identification `ℛ = Isom_𝒳(x, x)`**, as an equivalence of the underlying categories and as an
  equivalence over the big fppf site of `S`.

## What this gives

The equivalence over the site is stated in exactly the shape
`AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpace` and the presentation data of
Stacks 04T4 (4) and (5) consume — an `StacksRepresentableCFG.EquivalenceOver` of the structure
functor of `ℛ` with that of a category of elements of a presheaf on the site — so it is the
`eR` of `AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionPresentation` once the presheaf
`Isom_𝒳(x, x)` is known to be an algebraic space. It *is*:
`AlgebraicGeometry.Stack.AlgebraicStacks.isAlgebraicSpace_isomSpaceOverSpace_of_section` of
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionClassifyingStack` reads the equivalence proved
here against the representability of `ℛ` by **Stacks 04T4** part (1) and concludes it, since the
category of elements of a presheaf of sets determines the presheaf
(`CategoryTheory.PresheafOfCategories.pointwiseEquivOfEquivalenceOver`).

The group law is not here: this is an identification of objects over the site, not of group
algebraic spaces. The group structure on `Isom_𝒳(x, x)` over an algebraic space base is the one
**Stacks 0447** puts on the stabilizer of the self-intersection groupoid of Stacks 04T4 (4),
which is all of its arrow space because the source and the target of that groupoid agree for a
section; that is how `GerbeSectionClassifyingStack` supplies the group algebraic space of
**Stacks 06QG** part (1), with `AlgebraicGeometry.Stack.isomSpaceOverGrpObj` of Stacks 04YP — the
group law over a *scheme* of the site — playing no part in it.

No Stacks tag is registered here: the identification is the first step of the proof of
Stacks 06QG, not the statement of a tag.

## References

* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04WY](https://stacks.math.columbia.edu/tag/04WY)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-! ### Reading the sections of `Isom_𝒳(x, x)` off its category of elements -/

/-- The section of `Isom_𝒳(x, x)` named by an object of its category of elements. -/
def isomObjSection (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (P : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj) :
    isomSection B S hS Z hZ x x (Opposite.op P.base) :=
  (show Discrete ((isomSpaceOverSpace B S hS Z hZ x x).obj (Opposite.op P.base))
    from P.fiber).as

/-- A morphism of the category of elements of `Isom_𝒳(x, x)` identifies the section named by its
source with the restriction of the section named by its target. -/
lemma isomObjSection_map (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {P Q : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj} (f : P ⟶ Q) :
    isomObjSection B S hS Z hZ x P =
      (isomSpaceOverSpace B S hS Z hZ x x).map f.base.op
        (isomObjSection B S hS Z hZ x Q) :=
  Discrete.eq_of_hom f.fiber

/-- The underlying point of `Z` of the section named by the source of a morphism is the
restriction of the one named by its target. -/
lemma isomObjSection_fst_map (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {P Q : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj} (f : P ⟶ Q) :
    (isomObjSection B S hS Z hZ x P).1 =
      Z.map f.base.op (isomObjSection B S hS Z hZ x Q).1 :=
  congrArg Sigma.fst (isomObjSection_map B S hS Z hZ x f)

/-! ### The structure 1-morphism to `Z` and the tautological automorphism -/

/-- The projection of the category of elements of `Isom_𝒳(x, x)` to the category of elements of
`Z`: forget the automorphism and keep the point. -/
def isomProjFunctor (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj ⥤
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj where
  obj P := spacePoint.{u, w} B S hS Z hZ P.base (isomObjSection B S hS Z hZ x P).1
  map {P Q} f :=
    spacePointHom.{u, w} B S hS Z hZ f.base.op (isomObjSection B S hS Z hZ x Q).1
      (isomObjSection B S hS Z hZ x P).1 (isomObjSection_fst_map B S hS Z hZ x f)
  map_id _ := spacePointHom_id.{u, w} B S hS Z hZ _ _
  map_comp f g :=
    (spacePointHom_comp.{u, w} B S hS Z hZ g.base.op f.base.op _ _ _ _ _ _).symm

/-- The projection sends an object of the category of elements of `Isom_𝒳(x, x)` to the point
of `Z` it names, over the same base. -/
@[simp] lemma isomProjFunctor_obj (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (P : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj) :
    (isomProjFunctor B S hS Z hZ x).obj P =
      spacePoint.{u, w} B S hS Z hZ P.base (isomObjSection B S hS Z hZ x P).1 := rfl

/-- The projection to the category of elements of `Z` is a 1-morphism over the big fppf site of
`S`. -/
lemma isomProjFunctor_comp_p (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    isomProjFunctor B S hS Z hZ x ⋙ (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p =
      (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.p := rfl

/-- **The naturality of the tautological automorphism.** For a morphism of the category of
elements of `Isom_𝒳(x, x)` over `g`, the automorphism named by the target and the one named by
the source are intertwined by the image under `x` of the morphism of the category of elements of
`Z`: this is the defining equation of `AlgebraicGeometry.Stack.pointRestrict`. -/
lemma isomSection_tautological_naturality
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) {W' W : BigFppfOver B S hS} (g : W' ⟶ W)
    (s : isomSection B S hS Z hZ x x (Opposite.op W))
    (s' : isomSection B S hS Z hZ x x (Opposite.op W'))
    (h : s' = (isomSpaceOverSpace B S hS Z hZ x x).map g.op s)
    (h1 : s'.1 = Z.map g.op s.1) :
    x.hom.hom.toFunctor.map
          (spacePointHom.{u, w} B S hS Z hZ g.op s.1 s'.1 h1) ≫
        Functor.Fiber.fiberInclusion.map s.2.1 =
      Functor.Fiber.fiberInclusion.map s'.2.1 ≫
        x.hom.hom.toFunctor.map (spacePointHom.{u, w} B S hS Z hZ g.op s.1 s'.1 h1) := by
  subst h
  exact (pointRestrict_fac B S hS Z hZ x x g.op s.1 _ h1 s.2.1).symm

/-- The tautological automorphism of `x` over the category of elements of `Isom_𝒳(x, x)`: at an
object naming the automorphism `φ` of `x(z)`, the automorphism `φ` itself. -/
noncomputable def isomTautologicalIso (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    isomProjFunctor B S hS Z hZ x ⋙ x.hom.hom.toFunctor ≅
      isomProjFunctor B S hS Z hZ x ⋙ x.hom.hom.toFunctor :=
  NatIso.ofComponents
    (fun P => Functor.Fiber.fiberInclusion.mapIso
      (@asIso _ _ _ _ (isomObjSection B S hS Z hZ x P).2.1
        (isomObjSection B S hS Z hZ x P).2.2))
    (fun {P Q} f => isomSection_tautological_naturality B S hS Z hZ x f.base
      (isomObjSection B S hS Z hZ x Q) (isomObjSection B S hS Z hZ x P)
      (isomObjSection_map B S hS Z hZ x f) (isomObjSection_fst_map B S hS Z hZ x f))

/-- The component of the tautological automorphism at an object is the automorphism it names. -/
@[simp] lemma isomTautologicalIso_hom_app (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (P : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj) :
    (isomTautologicalIso B S hS Z hZ x).hom.app P =
      Functor.Fiber.fiberInclusion.map (isomObjSection B S hS Z hZ x P).2.1 := rfl

/-! ### The comparison 1-morphism -/

/-- **The comparison 1-morphism `Isom_𝒳(x, x) ⟶ 𝒰 ×_{x, 𝒳, x} 𝒰`.** An automorphism `φ` of
`x(z)` over `W` is sent to the arrow `(z, z, φ)` of the self-intersection; it is the 1-morphism
to the 2-fibre product induced by the projection to `Z` on both legs and by the tautological
automorphism as the comparison 2-morphism. -/
noncomputable def isomToRelation (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val ⥤ᵇ
      (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
        𝒳.val x.hom.hom).val where
  toFunctor :=
    TwoFibreProductOver.lift (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p 𝒳.val.val.p
      x.hom.hom.toFunctor x.hom.hom.toFunctor
      (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.p
      (isomProjFunctor B S hS Z hZ x) (isomProjFunctor B S hS Z hZ x)
      (isomProjFunctor_comp_p B S hS Z hZ x) (isomProjFunctor_comp_p B S hS Z hZ x)
      (isomTautologicalIso B S hS Z hZ x)
      (fun P => (isomObjSection B S hS Z hZ x P).2.1.2)
  w := TwoFibreProductOver.lift_comp_structureFunctor ..

/-- The comparison preserves the base of an object. -/
@[simp] lemma isomToRelation_obj_base (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (P : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj) :
    ((isomToRelation B S hS Z hZ x).toFunctor.obj P).base = P.base := rfl

/-- The first leg of the image of an object under the comparison is the point of `Z` it names. -/
@[simp] lemma isomToRelation_obj_x (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (P : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj) :
    ((isomToRelation B S hS Z hZ x).toFunctor.obj P).x =
      spacePoint.{u, w} B S hS Z hZ P.base (isomObjSection B S hS Z hZ x P).1 := rfl

/-- The second leg of the image of an object under the comparison is the point of `Z` it names. -/
@[simp] lemma isomToRelation_obj_y (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (P : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj) :
    ((isomToRelation B S hS Z hZ x).toFunctor.obj P).y =
      spacePoint.{u, w} B S hS Z hZ P.base (isomObjSection B S hS Z hZ x P).1 := rfl

/-- The comparison isomorphism of the image of an object under the comparison is the automorphism
it names. -/
@[simp] lemma isomToRelation_obj_iso_hom (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (P : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj) :
    ((isomToRelation B S hS Z hZ x).toFunctor.obj P).iso.hom =
      Functor.Fiber.fiberInclusion.map (isomObjSection B S hS Z hZ x P).2.1 := rfl

/-- The first component of the image of a morphism under the comparison is its projection to the
category of elements of `Z`. -/
@[simp] lemma isomToRelation_map_a (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {P Q : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj} (f : P ⟶ Q) :
    ((isomToRelation B S hS Z hZ x).toFunctor.map f).a =
      (isomProjFunctor B S hS Z hZ x).map f := rfl

/-- The second component of the image of a morphism under the comparison is its projection to the
category of elements of `Z`. -/
@[simp] lemma isomToRelation_map_b (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {P Q : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj} (f : P ⟶ Q) :
    ((isomToRelation B S hS Z hZ x).toFunctor.map f).b =
      (isomProjFunctor B S hS Z hZ x).map f := rfl

/-- The comparison preserves the base of a morphism. -/
@[simp] lemma isomToRelation_map_hbase (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {P Q : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj} (f : P ⟶ Q) :
    ((isomToRelation B S hS Z hZ x).toFunctor.map f).hbase = f.base := rfl

/-- The image of an object under the comparison, written out: the point `z` of `Z` on both legs
and the automorphism as the comparison isomorphism. -/
lemma isomToRelation_obj_eq_mk (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (P : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj) :
    (isomToRelation B S hS Z hZ x).toFunctor.obj P =
      ({ base := P.base
         x := spacePoint.{u, w} B S hS Z hZ P.base (isomObjSection B S hS Z hZ x P).1
         y := spacePoint.{u, w} B S hS Z hZ P.base (isomObjSection B S hS Z hZ x P).1
         hx := rfl
         hy := rfl
         iso := Functor.Fiber.fiberInclusion.mapIso
           (@asIso _ _ _ _ (isomObjSection B S hS Z hZ x P).2.1
             (isomObjSection B S hS Z hZ x P).2.2)
         vertical := (isomObjSection B S hS Z hZ x P).2.1.2 } :
        (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
          𝒳.val x.hom.hom).val.obj) := rfl

/-! ### The comparison is fully faithful -/

/-- A section of `Isom_𝒳(x, x)` over `W'` is the restriction of one over `W` as soon as its
point is the restriction of the point and its automorphism is intertwined with the
automorphism: that is the universal property `AlgebraicGeometry.Stack.pointRestrict_uniq`. -/
lemma isomSection_mk_eq_map (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {W' W : BigFppfOver B S hS} (g : W' ⟶ W)
    (s : isomSection B S hS Z hZ x x (Opposite.op W))
    (z' : Z.obj (Opposite.op W')) (h1 : z' = Z.map g.op s.1)
    (φ : pointFiber B S hS Z hZ x W' z' ⟶ pointFiber B S hS Z hZ x W' z') (hφ : IsIso φ)
    (hfac : Functor.Fiber.fiberInclusion.map φ ≫
          x.hom.hom.toFunctor.map (spacePointHom.{u, w} B S hS Z hZ g.op s.1 z' h1) =
        x.hom.hom.toFunctor.map (spacePointHom.{u, w} B S hS Z hZ g.op s.1 z' h1) ≫
          Functor.Fiber.fiberInclusion.map s.2.1) :
    (⟨z', ⟨φ, hφ⟩⟩ : isomSection B S hS Z hZ x x (Opposite.op W')) =
      (isomSpaceOverSpace B S hS Z hZ x x).map g.op s := by
  subst h1
  have hp := pointRestrict_uniq B S hS Z hZ x x g.op s.1 _ rfl s.2.1 φ hfac
  subst hp
  rfl

/-- The point of `Z` named by the source of a morphism out of the image of the comparison is the
restriction of the one named by its target. -/
lemma isomToRelation_hom_fst (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {P Q : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj}
    (m : (isomToRelation B S hS Z hZ x).toFunctor.obj P ⟶
      (isomToRelation B S hS Z hZ x).toFunctor.obj Q) :
    (isomObjSection B S hS Z hZ x P).1 =
      Z.map m.a.base.op (isomObjSection B S hS Z hZ x Q).1 :=
  PresheafOfCategories.elementOf_eq_map (P := Z) rfl rfl m.a.base m.a
    (PresheafOfCategories.isHomLift_base m.a)

/-- The two components of a morphism out of the image of the comparison lie over the same
morphism of the site, since both lie over its base morphism. -/
lemma isomToRelation_hom_b_base (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {P Q : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj}
    (m : (isomToRelation B S hS Z hZ x).toFunctor.obj P ⟶
      (isomToRelation B S hS Z hZ x).toFunctor.obj Q) :
    m.b.base = m.a.base :=
  ((@IsHomLift.eq_of_isHomLift _ _ _ _ (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p
      ((isomToRelation B S hS Z hZ x).toFunctor.obj P).y
      ((isomToRelation B S hS Z hZ x).toFunctor.obj Q).y m.hbase m.b m.hb).symm.trans
    (@IsHomLift.eq_of_isHomLift _ _ _ _ (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p
      ((isomToRelation B S hS Z hZ x).toFunctor.obj P).x
      ((isomToRelation B S hS Z hZ x).toFunctor.obj Q).x m.hbase m.a m.ha))

/-- The first component of a morphism out of the image of the comparison is *the* morphism of the
category of elements of `Z` over its base: the fibres of a category of elements are discrete, so
a morphism of it is determined by its base. -/
lemma isomToRelation_hom_a (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {P Q : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj}
    (m : (isomToRelation B S hS Z hZ x).toFunctor.obj P ⟶
      (isomToRelation B S hS Z hZ x).toFunctor.obj Q) :
    m.a = spacePointHom.{u, w} B S hS Z hZ m.a.base.op
      (isomObjSection B S hS Z hZ x Q).1 (isomObjSection B S hS Z hZ x P).1
      (isomToRelation_hom_fst B S hS Z hZ x m) :=
  PresheafOfCategories.elements_hom_ext _ _ rfl

/-- The second component of a morphism out of the image of the comparison is *the* morphism of
the category of elements of `Z` over the base of its first component. -/
lemma isomToRelation_hom_b (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    {P Q : (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).val.obj}
    (m : (isomToRelation B S hS Z hZ x).toFunctor.obj P ⟶
      (isomToRelation B S hS Z hZ x).toFunctor.obj Q) :
    m.b = spacePointHom.{u, w} B S hS Z hZ m.a.base.op
      (isomObjSection B S hS Z hZ x Q).1 (isomObjSection B S hS Z hZ x P).1
      (isomToRelation_hom_fst B S hS Z hZ x m) :=
  PresheafOfCategories.elements_hom_ext _ _ (isomToRelation_hom_b_base B S hS Z hZ x m)

/-- **The comparison is faithful.** A morphism of the category of elements of `Isom_𝒳(x, x)` is
determined by its base, and the comparison keeps the base. -/
instance isomToRelation_faithful (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (isomToRelation B S hS Z hZ x).toFunctor.Faithful where
  map_injective {_ _} f g h :=
    PresheafOfCategories.elements_hom_ext f g
      (congrArg TwoFibreProductOver.Hom.hbase h)

/-- **The comparison is full.** A morphism `(z, z, φ) ⟶ (z', z', φ')` of the self-intersection
has both components equal to the morphism of the category of elements of `Z` over its base, and
its comparison square then says exactly, by the uniqueness half of the universal property
`AlgebraicGeometry.Stack.pointRestrict_uniq`, that `φ` is the restriction of `φ'` — which is
what a morphism of the category of elements of `Isom_𝒳(x, x)` is. -/
instance isomToRelation_full (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (isomToRelation B S hS Z hZ x).toFunctor.Full where
  map_surjective {P Q} m := by
    have hw := m.w
    rw [isomToRelation_hom_a B S hS Z hZ x m, isomToRelation_hom_b B S hS Z hZ x m] at hw
    have hsec : isomObjSection B S hS Z hZ x P =
        (isomSpaceOverSpace B S hS Z hZ x x).map (m.a.base : P.base ⟶ Q.base).op
          (isomObjSection B S hS Z hZ x Q) :=
      isomSection_mk_eq_map B S hS Z hZ x (m.a.base : P.base ⟶ Q.base)
        (isomObjSection B S hS Z hZ x Q) (isomObjSection B S hS Z hZ x P).1
        (isomToRelation_hom_fst B S hS Z hZ x m)
        (isomObjSection B S hS Z hZ x P).2.1 (isomObjSection B S hS Z hZ x P).2.2 hw.symm
    refine ⟨{ base := (m.a.base : P.base ⟶ Q.base), fiber := Discrete.eqToHom hsec }, ?_⟩
    refine TwoFibreProductOver.Hom.ext'
      (PresheafOfCategories.elements_hom_ext _ _ ?_)
      (PresheafOfCategories.elements_hom_ext _ _ ?_)
    · exact rfl
    · exact (isomToRelation_hom_b_base B S hS Z hZ x m).symm

/-! ### The trivial action: an arrow of the self-intersection of a section has equal ends -/

/-- **Stacks 06QG, part (1), at the level of objects: the action is trivial.** For a section
`x : 𝒰 ⟶ 𝒳` of a 1-morphism `π : 𝒳 ⟶ 𝒰` with `𝒰` the stack of an algebraic space `Z`, the two
ends of an arrow of the self-intersection `𝒰 ×_{x, 𝒳, x} 𝒰` are *equal*: applying `π` to the
comparison isomorphism and conjugating by the 2-isomorphism of the section gives a vertical
morphism between the two ends, and the fibres of the category of elements of a presheaf of sets
are discrete.

Only the section is used; no gerbe hypothesis enters. This is the object-level form of
`AlgebraicGeometry.Stack.SelfIntersection.relationSourceMap_eq_relationTargetMap`, which says
the same of the two structure morphisms of the presentation groupoid. -/
theorem relation_x_eq_y_of_section (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (π : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (algebraicSpaceStack.{u, w} B S hS Z hZ))
    (P : (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
      𝒳.val x.hom.hom).val.obj) :
    P.x = P.y := by
  have hπ (a) (h : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.obj a = P.base) :=
    (BasedFunctor.w_obj π.hom.hom (x.hom.hom.toFunctor.obj a)).trans
      ((BasedFunctor.w_obj x.hom.hom a).trans h)
  have h1 : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.IsHomLift (𝟙 P.base)
      (hx.inv.hom.hom.toNatTrans.app P.x) :=
    P.hx ▸ CatFiberedInGroupoids.isHomLift_app hx.inv.hom P.x
  have h3 : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.IsHomLift (𝟙 P.base)
      (hx.hom.hom.hom.toNatTrans.app P.y) :=
    P.hy ▸ CatFiberedInGroupoids.isHomLift_app hx.hom.hom P.y
  have h2 : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.IsHomLift (𝟙 P.base)
      (π.hom.hom.toFunctor.map P.iso.hom) := by
    have := P.vertical
    exact Functor.isHomLift_map_of_comp_eq π.hom.hom.w (𝟙 P.base) P.iso.hom
  -- The three vertical morphisms, composed in the fibre of the stack of `Z` over `P.base`.
  let m1 : (Functor.Fiber.mk P.hx :
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.Fiber P.base) ⟶
      Functor.Fiber.mk (hπ _ P.hx) := ⟨hx.inv.hom.hom.toNatTrans.app P.x, h1⟩
  let m2 : (Functor.Fiber.mk (hπ _ P.hx) :
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.Fiber P.base) ⟶
      Functor.Fiber.mk (hπ _ P.hy) := ⟨π.hom.hom.toFunctor.map P.iso.hom, h2⟩
  let m3 : (Functor.Fiber.mk (hπ _ P.hy) :
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p.Fiber P.base) ⟶
      Functor.Fiber.mk P.hy := ⟨hx.hom.hom.hom.toNatTrans.app P.y, h3⟩
  refine PresheafOfCategories.obj_eq_of_elementOf_eq (P := Z) P.hx P.hy ?_
  refine (PresheafOfCategories.elementOf_eq_map (P := Z) P.hx P.hy (𝟙 P.base)
    (m1 ≫ m2 ≫ m3).1 (m1 ≫ m2 ≫ m3).2).trans ?_
  simp

/-! ### The comparison is an equivalence -/

/-- **Every arrow of the self-intersection of a section is an automorphism of `x`.** Given the
equality of the two ends, an object of `𝒰 ×_{x, 𝒳, x} 𝒰` *is* a point `z` of `Z` together with
an automorphism of `x(z)`, that is an object of the category of elements of `Isom_𝒳(x, x)`. -/
theorem exists_eq_isomToRelation_obj (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (π : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (algebraicSpaceStack.{u, w} B S hS Z hZ))
    (P : (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
      𝒳.val x.hom.hom).val.obj) :
    ∃ Q, (isomToRelation B S hS Z hZ x).toFunctor.obj Q = P := by
  obtain ⟨V, a, b, hxa, hyb, iso, vert⟩ := P
  have heq : a = b := relation_x_eq_y_of_section B S hS Z hZ x π hx
    (⟨V, a, b, hxa, hyb, iso, vert⟩ :
      (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
        𝒳.val x.hom.hom).val.obj)
  subst heq
  subst hxa
  refine ⟨⟨_, Discrete.mk ⟨(show Discrete (Z.obj (Opposite.op a.base)) from a.fiber).as,
      ⟨⟨iso.hom, vert⟩, isIso_fiberHom B S hS 𝒳 _⟩⟩⟩,
    (isomToRelation_obj_eq_mk B S hS Z hZ x _).trans (TwoFibreProductOver.obj_ext ?_)⟩
  exact Iso.ext rfl

/-- **The comparison is essentially surjective**, for a section: every object of the
self-intersection is in its image. -/
theorem essSurj_isomToRelation (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (π : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (algebraicSpaceStack.{u, w} B S hS Z hZ)) :
    (isomToRelation B S hS Z hZ x).toFunctor.EssSurj where
  mem_essImage P := by
    obtain ⟨Q, hQ⟩ := exists_eq_isomToRelation_obj B S hS Z hZ x π hx P
    exact ⟨Q, ⟨eqToIso hQ⟩⟩

/-- **`𝒰 ×_{x, 𝒳, x} 𝒰 = Isom_𝒳(x, x)` for a section `x`.** The comparison 1-morphism
`AlgebraicGeometry.Stack.isomToRelation` is an equivalence of categories: it is fully faithful
with no hypothesis, and essentially surjective because the two ends of an arrow of the
self-intersection of a section agree. -/
theorem isEquivalence_isomToRelation (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (π : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (algebraicSpaceStack.{u, w} B S hS Z hZ)) :
    (isomToRelation B S hS Z hZ x).toFunctor.IsEquivalence :=
  have := essSurj_isomToRelation B S hS Z hZ x π hx
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- **The self-intersection of a section of a gerbe is represented by its automorphism sheaf.**
For a section `x : 𝒰 ⟶ 𝒳` of `π : 𝒳 ⟶ 𝒰`, with `𝒰` the stack of an algebraic space `Z`, the
self-intersection `ℛ = 𝒰 ×_{x, 𝒳, x} 𝒰` is equivalent, over the big fppf site of `S`, to the
category of elements of the presheaf `Isom_𝒳(x, x)`.

This is the identification `R = G` which is the first step of the proof of Stacks 06QG: it is
what makes the arrow space of the self-intersection groupoid of Stacks 04T4 (4) the automorphism
sheaf of Stacks 06PP. -/
theorem nonempty_equivalenceOver_relation_isomSpaceOverSpace
    (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (π : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (algebraicSpaceStack.{u, w} B S hS Z hZ)) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
        𝒳.val x.hom.hom).val.p
      (presheafOfCategories (isomSpaceOverSpace B S hS Z hZ x x ⋙ typeToCat)).p) := by
  obtain ⟨e⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x)).isFiberedInGroupoids
    (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
      𝒳.val x.hom.hom).isFiberedInGroupoids
    (isomToRelation B S hS Z hZ x).toFunctor (isomToRelation B S hS Z hZ x).w
    (isEquivalence_isomToRelation B S hS Z hZ x π hx)
  exact ⟨e.symm⟩

end AlgebraicGeometry.Stack

end
