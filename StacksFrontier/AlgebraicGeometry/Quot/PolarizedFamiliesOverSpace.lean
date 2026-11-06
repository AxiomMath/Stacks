module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamilies

/-!
# Polarized proper schemes over a fixed algebraic space (Stacks 0D1N)

Fix an algebraic space `A` over the base of a big fppf site, presented as a presheaf on the
schemes of that site over the base. A *polarized family over* `A` is a polarized family
`(X ⟶ S, L)` of Stacks 0D1M together with a point of `A` over the base scheme `S`, and a morphism
of such is a morphism of polarized families whose base map carries the point of the target to the
point of the source.

Forgetting the point and forgetting the polarization exhibit this category as the 2-fibre product
of the category of polarized families with the category of schemes carrying a point of `A`, over
the big fppf site of schemes: that is the base-change square of Stacks 0D1N, by which statements
about the absolute category of polarized families transfer to families over a fixed base algebraic
space.

## Main definitions

* `AlgebraicGeometry.PolarizedFamilyOver`: **Stacks 0D1N**, the objects.
* `AlgebraicGeometry.PolarizedFamilyOver.Hom`: **Stacks 0D1N**, the morphisms.
* `AlgebraicGeometry.PolarizedFamilyOver.instCategory`: **Stacks 0D1N**, the category.
* `AlgebraicGeometry.pointedSchemesProjection` is the projection taking a scheme carrying a point
  of `A` to the underlying scheme of the site.
* `AlgebraicGeometry.PolarizedFamilyOver.toCategoricalPullback` is the canonical comparison with
  the 2-fibre product.

## Main results

* `AlgebraicGeometry.PolarizedFamilyOver.isEquivalence_toCategoricalPullback`: **Stacks 0D1N**,
  the displayed square is a 2-fibre product square.

## Implementation notes

The algebraic space is taken to be an arbitrary presheaf: neither the sheaf condition nor the
existence of an étale atlas is used anywhere in this identification, which is purely categorical,
so no algebraicity hypothesis is imposed. A point of the presheaf over a scheme `S` of the site is
by the Yoneda lemma exactly a morphism `S ⟶ A` of presheaves, so the data carried by an object
below is the triple `(X ⟶ S, L, h : S ⟶ A)` of the source. The base scheme of an object is written
through the field `AlgebraicGeometry.PolarizedFamily.base` rather than through
`AlgebraicGeometry.polarizedProjection`, which computes it; the two are the same object, and the
former keeps the types of the structure morphisms in normal form.

The category of schemes carrying a point of `A` is the *opposite* of
`CategoryTheory.Functor.Elements`, so that its morphisms run in the direction of morphisms of
schemes rather than against them; `AlgebraicGeometry.pointedSchemesProjection` then forgets both
the point and the structure morphism to the base.

The 2-fibre product is Mathlib's `CategoryTheory.Limits.CategoricalPullback`, whose objects are
triples consisting of an object of each factor and an isomorphism between their images. The
comparison functor below sends an object to its polarized family, its pointed base scheme, and the
*identity* isomorphism of their common base scheme; an inverse is built by transporting a point of
`A` along the comparison isomorphism of an arbitrary object of the 2-fibre product, and the
transported structure morphism is an isomorphism over the base, so the result is isomorphic to the
object it came from.

## References

* [Stacks Project, Tag 0D1N](https://stacks.math.columbia.edu/tag/0D1N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 0D1N.** A *polarized family over the space* `A`: a polarized family together with a
structure morphism of its base scheme over the base of the site and a point of `A` there. -/
@[stacks 0D1N "objects"]
structure PolarizedFamilyOver where
  /-- The underlying polarized family. -/
  polarized : PolarizedFamily B
  /-- The structure morphism of the base scheme over the base of the site. -/
  toBase : polarized.base ⟶ B.obj hS
  /-- The point of `A` over the base scheme. -/
  point : A.obj (Opposite.op (Over.mk toBase))

/-- The projection taking a scheme over the base of the site carrying a point of `A` to the
underlying scheme of the site. -/
def pointedSchemesProjection : A.Elementsᵒᵖ ⥤ B.Schemes :=
  (Functor.Elements.π A).op ⋙ unopUnop _ ⋙ Over.forget (B.obj hS)

namespace PolarizedFamilyOver

variable {B S hS A}

/-- **Stacks 0D1N.** A morphism of polarized families over `A`: a morphism of the underlying
polarized families whose base map lies over the base of the site and carries the point of the
target to the point of the source. -/
@[stacks 0D1N "morphisms"]
structure Hom (X Y : PolarizedFamilyOver B S hS A) where
  /-- The underlying morphism of polarized families. -/
  polarizedHom : X.polarized ⟶ Y.polarized
  /-- The base map lies over the base of the site. -/
  base_comm : PolarizedFamily.Hom.baseMap polarizedHom ≫ Y.toBase = X.toBase
  /-- The base map carries the point of the target to the point of the source. -/
  point_comm :
    A.map (Quiver.Hom.op
      (Over.homMk (PolarizedFamily.Hom.baseMap polarizedHom) base_comm)) Y.point = X.point

/-- The morphism of schemes over the base of the site underlying a morphism of polarized families
over `A`. -/
def Hom.over {X Y : PolarizedFamilyOver B S hS A} (f : Hom X Y) :
    Over.mk X.toBase ⟶ Over.mk Y.toBase :=
  Over.homMk (PolarizedFamily.Hom.baseMap f.polarizedHom) f.base_comm

/-- The base map underlying a morphism of polarized families over `A`. -/
@[simp]
theorem Hom.over_left {X Y : PolarizedFamilyOver B S hS A} (f : Hom X Y) :
    (Hom.over f).left = PolarizedFamily.Hom.baseMap f.polarizedHom := rfl

/-- Two morphisms of polarized families over `A` agree as soon as their underlying morphisms of
polarized families agree: the two remaining fields are propositions. -/
theorem Hom.ext {X Y : PolarizedFamilyOver B S hS A} {f g : Hom X Y}
    (h : f.polarizedHom = g.polarizedHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- **Stacks 0D1N.** Polarized families over `A` and the morphisms compatible with their points
form a category, with the identities and composition of the underlying polarized families. -/
@[stacks 0D1N "category"]
instance instCategory : Category.{u} (PolarizedFamilyOver B S hS A) where
  Hom X Y := Hom X Y
  id X :=
    have hb : PolarizedFamily.Hom.baseMap (𝟙 X.polarized) ≫ X.toBase = X.toBase := by
      simp
    { polarizedHom := 𝟙 X.polarized
      base_comm := hb
      point_comm := by
        have h : (Over.homMk (PolarizedFamily.Hom.baseMap (𝟙 X.polarized)) hb :
            Over.mk X.toBase ⟶ Over.mk X.toBase) = 𝟙 _ :=
          Over.OverMorphism.ext (PolarizedFamily.id_baseMap X.polarized)
        rw [h]
        simp }
  comp {X Y Z} f g :=
    have hb : PolarizedFamily.Hom.baseMap (f.polarizedHom ≫ g.polarizedHom) ≫ Z.toBase =
        X.toBase := by
      rw [PolarizedFamily.comp_baseMap, Category.assoc, g.base_comm, f.base_comm]
    { polarizedHom := f.polarizedHom ≫ g.polarizedHom
      base_comm := hb
      point_comm := by
        have hcomp : (Over.homMk (PolarizedFamily.Hom.baseMap
              (f.polarizedHom ≫ g.polarizedHom)) hb :
            Over.mk X.toBase ⟶ Over.mk Z.toBase) = Hom.over f ≫ Hom.over g :=
          Over.OverMorphism.ext (by simp)
        have hg : A.map (Quiver.Hom.op (Hom.over g)) Z.point = Y.point := g.point_comm
        have hf : A.map (Quiver.Hom.op (Hom.over f)) Y.point = X.point := f.point_comm
        rw [hcomp, CategoryTheory.op_comp, Functor.map_comp_apply, hg, hf] }
  id_comp f := Hom.ext (Category.id_comp f.polarizedHom)
  comp_id f := Hom.ext (Category.comp_id f.polarizedHom)
  assoc f g h := Hom.ext (Category.assoc f.polarizedHom g.polarizedHom h.polarizedHom)

/-- The underlying morphism of polarized families of an identity morphism is the identity. -/
@[simp]
theorem id_polarizedHom (X : PolarizedFamilyOver B S hS A) :
    Hom.polarizedHom (𝟙 X) = 𝟙 X.polarized := rfl

/-- The underlying morphism of polarized families of a composite is the composite. -/
@[simp]
theorem comp_polarizedHom {X Y Z : PolarizedFamilyOver B S hS A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Hom.polarizedHom (f ≫ g) = Hom.polarizedHom f ≫ Hom.polarizedHom g := rfl

variable (B S hS A)

/-- Forget the point of `A`, retaining the polarized family. -/
def forgetPoint : PolarizedFamilyOver B S hS A ⥤ PolarizedFamily B where
  obj X := X.polarized
  map f := Hom.polarizedHom f

/-- Forget the polarization, retaining the base scheme with its point of `A`. -/
def toElements : PolarizedFamilyOver B S hS A ⥤ A.Elementsᵒᵖ where
  obj X := Opposite.op (A.elementsMk (Opposite.op (Over.mk X.toBase)) X.point)
  map f := Quiver.Hom.op (Functor.Elements.homMk (Hom.over f).op (Hom.point_comm f))
  map_id X := by
    apply Quiver.Hom.unop_inj
    simp only [unop_id]
    apply Functor.Elements.hom_ext
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    change PolarizedFamily.Hom.baseMap (Hom.polarizedHom (𝟙 X)) = 𝟙 X.polarized.base
    simp
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    simp only [unop_comp]
    apply Functor.Elements.hom_ext
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    change PolarizedFamily.Hom.baseMap (Hom.polarizedHom (f ≫ g)) =
      PolarizedFamily.Hom.baseMap (Hom.polarizedHom f) ≫
        PolarizedFamily.Hom.baseMap (Hom.polarizedHom g)
    simp

/-- The canonical comparison of polarized families over `A` with the 2-fibre product of polarized
families and schemes carrying a point of `A`: an object goes to its polarized family, its pointed
base scheme, and the identity isomorphism of their common base scheme. -/
def toCategoricalPullback :
    PolarizedFamilyOver B S hS A ⥤
      (polarizedProjection B) ⊡ (pointedSchemesProjection B S hS A) where
  obj X := ⟨X.polarized, (toElements B S hS A).obj X, Iso.refl _⟩
  map f := ⟨Hom.polarizedHom f, (toElements B S hS A).map f, rfl⟩

variable {B S hS A}

/-- The scheme over the base of the site underlying an object of the 2-fibre product. -/
private def elementOver
    (q : (polarizedProjection B) ⊡ (pointedSchemesProjection B S hS A)) :
    BigFppfOver B S hS := Opposite.unop (Opposite.unop q.snd).1

/-- The point of `A` carried by an object of the 2-fibre product. -/
private def elementPoint
    (q : (polarizedProjection B) ⊡ (pointedSchemesProjection B S hS A)) :
    A.obj (Opposite.op (elementOver q)) := (Opposite.unop q.snd).2

/-- An object of the 2-fibre product gives a polarized family over `A`, by transporting its point
of `A` along its comparison isomorphism. -/
private def ofCategoricalPullback
    (q : (polarizedProjection B) ⊡ (pointedSchemesProjection B S hS A)) :
    PolarizedFamilyOver B S hS A :=
  ⟨q.fst, q.iso.hom ≫ (elementOver q).hom,
    A.map (Quiver.Hom.op (Over.homMk q.iso.hom rfl)) (elementPoint q)⟩

/-- The comparison functor sends the polarized family built from an object of the 2-fibre product
back to an object isomorphic to it. -/
private def ofCategoricalPullbackIso
    (q : (polarizedProjection B) ⊡ (pointedSchemesProjection B S hS A)) :
    (toCategoricalPullback B S hS A).obj (ofCategoricalPullback q) ≅ q := by
  have hiso : IsIso (show Over.mk (q.iso.hom ≫ (elementOver q).hom) ⟶ elementOver q from
      Over.homMk q.iso.hom rfl) := by
    have : IsIso ((Over.forget (B.obj hS)).map
        (show Over.mk (q.iso.hom ≫ (elementOver q).hom) ⟶ elementOver q from
          Over.homMk q.iso.hom rfl)) := by
      change IsIso q.iso.hom
      infer_instance
    exact Functor.ReflectsIsomorphisms.reflects (Over.forget (B.obj hS)) _
  refine CategoricalPullback.mkIso (Iso.refl q.fst)
    (Functor.Elements.isoMk (x := Opposite.unop q.snd)
      (y := Opposite.unop ((toCategoricalPullback B S hS A).obj (ofCategoricalPullback q)).snd)
      (@asIso _ _ _ _ _ hiso).op rfl).op ?_
  change (polarizedProjection B).map (𝟙 q.fst) ≫ q.iso.hom = q.iso.hom
  simp

/-- The base map underlying a morphism between images of the comparison functor is the base map
of its pointed-scheme component. -/
private theorem baseMap_fst_eq_left {X Y : PolarizedFamilyOver B S hS A}
    (f : (toCategoricalPullback B S hS A).obj X ⟶ (toCategoricalPullback B S hS A).obj Y) :
    PolarizedFamily.Hom.baseMap f.fst = (Opposite.unop (Opposite.unop f.snd).hom).left := by
  calc _ = (pointedSchemesProjection B S hS A).map f.snd := by
        simpa [toCategoricalPullback, pointedSchemesProjection, toElements] using f.w
    _ = _ := rfl

/-- A morphism between images of the comparison functor comes from a morphism of polarized
families over `A`. -/
private def homOfCategoricalPullbackHom {X Y : PolarizedFamilyOver B S hS A}
    (f : (toCategoricalPullback B S hS A).obj X ⟶ (toCategoricalPullback B S hS A).obj Y) :
    X ⟶ Y := by
  have hw := baseMap_fst_eq_left f
  have hbase : PolarizedFamily.Hom.baseMap f.fst ≫ Y.toBase = X.toBase := by
    rw [hw]
    exact (Opposite.unop (Opposite.unop f.snd).hom).w
  refine ⟨f.fst, hbase, ?_⟩
  have hover : (Over.homMk (PolarizedFamily.Hom.baseMap f.fst) hbase :
      Over.mk X.toBase ⟶ Over.mk Y.toBase) = Opposite.unop (Opposite.unop f.snd).hom :=
    Over.OverMorphism.ext hw
  rw [hover]
  exact (Opposite.unop f.snd).map_val

/-- The comparison functor takes the morphism built from a morphism between images back to it. -/
private theorem map_homOfCategoricalPullbackHom {X Y : PolarizedFamilyOver B S hS A}
    (f : (toCategoricalPullback B S hS A).obj X ⟶ (toCategoricalPullback B S hS A).obj Y) :
    (toCategoricalPullback B S hS A).map (homOfCategoricalPullbackHom f) = f :=
  CategoricalPullback.hom_ext rfl <| Quiver.Hom.unop_inj <| Functor.Elements.hom_ext <|
    Quiver.Hom.unop_inj <| Over.OverMorphism.ext <| baseMap_fst_eq_left f

variable (B S hS A)

/-- **Stacks 0D1N.** The canonical comparison from polarized families over `A` to the 2-fibre
product of polarized families and schemes carrying a point of `A`, over the big fppf site of
schemes, is an equivalence: the displayed square is a 2-fibre product square. -/
@[stacks 0D1N "the 2-fibre product square"]
theorem isEquivalence_toCategoricalPullback :
    (toCategoricalPullback B S hS A).IsEquivalence where
  faithful := ⟨fun h => Hom.ext (congrArg (·.fst) h)⟩
  full := ⟨fun f => ⟨homOfCategoricalPullbackHom f, map_homOfCategoricalPullbackHom f⟩⟩
  essSurj := ⟨fun q => ⟨ofCategoricalPullback q, ⟨ofCategoricalPullbackIso q⟩⟩⟩

end PolarizedFamilyOver

end AlgebraicGeometry

end
