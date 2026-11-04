module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# The iso-fibre of a functor over an object

For a functor `F : C ⥤ D` and an object `x` of `D`, the *iso-fibre* of `F` over `x` is the
full subcategory of `CategoryTheory.CostructuredArrow F x` on those arrows `F c ⟶ x` which
are isomorphisms. It is the category of objects of `C` equipped with an identification of
their image with `x`.

Unlike the strict fibre `CategoryTheory.Functor.Fiber`, the iso-fibre is insensitive to
replacing `F` by a naturally isomorphic functor.

The two structural facts proved here express that the iso-fibre turns a categorical
pullback of a diagram over a groupoid into a product. Writing `P` for the functor sending a
point of `CategoryTheory.Limits.CategoricalPullback F G` to the image of its first
component, the arrows into `x` over `P` are the same as pairs of arrows into `x` over `F`
and over `G`, because the comparison isomorphism carried by a point of the categorical
pullback converts one leg into the other.

## Main definitions

* `CategoryTheory.Functor.IsIsoCostructuredArrow` — the property of an object of
  `CostructuredArrow F x` that its structure arrow is an isomorphism.
* `CategoryTheory.Functor.IsoFiber` — the iso-fibre of `F` over `x`.
* `CategoryTheory.Functor.categoricalPullbackFst` — the functor taking a point of a
  categorical pullback to the image of its first component.

## Main results

* `CategoryTheory.Functor.costructuredArrowCategoricalPullbackEquiv` — over a groupoid, the
  arrows into `x` above `categoricalPullbackFst F G` are pairs of arrows into `x` above `F`
  and above `G`.
* `CategoryTheory.Functor.isoFiberProdEquivalence` — the iso-fibre of a product diagram is
  the product of the two iso-fibres.

## Implementation notes

`CategoryTheory.Functor.costructuredArrowCategoricalPullbackEquiv` is produced by exhibiting
the evident functor as full, faithful and essentially surjective; its inverse on objects
assembles a point of the categorical pullback from a pair of arrows into `x` by composing
one isomorphism with the inverse of the other, which is why the target is required to be a
groupoid.

The second leg of the equivalence is the structure arrow of the second component *read
through* the comparison isomorphism, so that both legs of the resulting pair land on the
same object `x`.
-/

@[expose] public section

universe v v₁ v₂ u u₁ u₂

namespace CategoryTheory.Functor

open CategoryTheory.Limits

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- The objects of `CostructuredArrow F x` whose structure arrow is an isomorphism. -/
public abbrev IsIsoCostructuredArrow (F : C ⥤ D) (x : D) :
    ObjectProperty (CostructuredArrow F x) := fun t => IsIso t.hom

/-- The *iso-fibre* of `F` over `x`: objects of `C` together with an isomorphism from their
image to `x`. -/
public abbrev IsoFiber (F : C ⥤ D) (x : D) :=
  (IsIsoCostructuredArrow F x).FullSubcategory

/-- Two objects of an iso-fibre agree as soon as their underlying objects of
`CostructuredArrow F x` have the same source and the same structure arrow. -/
public theorem IsoFiber.ext {F : C ⥤ D} {x : D} {a b : IsoFiber F x}
    (hleft : a.obj.left = b.obj.left) (hhom : HEq a.obj.hom b.obj.hom) : a = b := by
  obtain ⟨⟨al, ar, ah⟩, ha⟩ := a
  obtain ⟨⟨bl, br, bh⟩, hb⟩ := b
  dsimp at hleft hhom
  cases hleft
  cases Subsingleton.elim ar br
  cases eq_of_heq hhom
  rfl

/-- Being an isomorphism is invariant under isomorphism of costructured arrows. -/
public instance IsIsoCostructuredArrow.isClosedUnderIsomorphisms (F : C ⥤ D) (x : D) :
    (IsIsoCostructuredArrow F x).IsClosedUnderIsomorphisms where
  of_iso {t t'} e ht := by
    have : IsIso t.hom := ht
    change IsIso t'.hom
    rw [← CostructuredArrow.w e.inv]
    infer_instance

/-! ### The iso-fibre of a categorical pullback -/

section Pullback

variable {E : Type u} [Category.{v} E]

/-- The functor taking a point of a categorical pullback to the image of its first
component. -/
@[implicit_reducible]
public def categoricalPullbackFst (F : C ⥤ E) (G : D ⥤ E) :
    CategoricalPullback F G ⥤ E where
  obj z := F.obj z.fst
  map m := F.map m.fst

/-- The property, on a pair of costructured arrows into one and the same object, that both
structure arrows are isomorphisms. -/
public abbrev IsIsoCostructuredArrowPair (F : C ⥤ E) (G : D ⥤ E) (x : E) :
    ObjectProperty (CostructuredArrow F x × CostructuredArrow G x) :=
  fun y => IsIso y.1.hom ∧ IsIso y.2.hom

/-- Being a pair of isomorphisms is invariant under isomorphism of pairs of costructured
arrows. -/
public instance IsIsoCostructuredArrowPair.isClosedUnderIsomorphisms
    (F : C ⥤ E) (G : D ⥤ E) (x : E) :
    (IsIsoCostructuredArrowPair F G x).IsClosedUnderIsomorphisms where
  of_iso e ht :=
    ⟨ObjectProperty.prop_of_iso (IsIsoCostructuredArrow F x)
        ((CategoryTheory.Prod.fst _ _).mapIso e) ht.1,
      ObjectProperty.prop_of_iso (IsIsoCostructuredArrow G x)
        ((CategoryTheory.Prod.snd _ _).mapIso e) ht.2⟩

/-- The arrows into `x` above `categoricalPullbackFst F G` are the same as pairs of an arrow
into `x` above `F` and an arrow into `x` above `G`. The second component of the pair is the
structure arrow of the second component of the point, read through the comparison
isomorphism; recovering a point of the categorical pullback from a pair uses that every
arrow of the target is invertible. -/
@[implicit_reducible]
public noncomputable def costructuredArrowCategoricalPullbackEquiv
    (F : C ⥤ E) (G : D ⥤ E) (x : E) (hE : IsGroupoid E) :
    CostructuredArrow (categoricalPullbackFst F G) x ≌
      (CostructuredArrow F x × CostructuredArrow G x) := by
  let := hE
  let P := categoricalPullbackFst F G
  let Q : CostructuredArrow P x ⥤ (CostructuredArrow F x × CostructuredArrow G x) :=
    { obj t :=
        (CostructuredArrow.mk (S := F) (T := x) t.hom,
          CostructuredArrow.mk (S := G) (T := x) (t.left.iso.inv ≫ t.hom))
      map {X Y} m :=
        (CostructuredArrow.homMk m.left.fst (CostructuredArrow.w m),
          CostructuredArrow.homMk m.left.snd
            (((reassoc_of% (CategoricalPullback.Hom.w' m.left)) Y.hom).trans
              (X.left.iso.inv ≫= CostructuredArrow.w m))) }
  let : Q.Faithful := ⟨fun h => CostructuredArrow.ext _ _ (CategoricalPullback.hom_ext
    (congrArg (fun z => z.1.left) h) (congrArg (fun z => z.2.left) h))⟩
  let : Q.Full := by
    refine ⟨fun {a b} m => ?_⟩
    have hm₁ : F.map m.1.left ≫ b.hom = a.hom := CostructuredArrow.w m.1
    have hm₂ : G.map m.2.left ≫ b.left.iso.inv ≫ b.hom = a.left.iso.inv ≫ a.hom :=
      CostructuredArrow.w m.2
    let pbm : a.left ⟶ b.left :=
      { fst := m.1.left
        snd := m.2.left
        w := by
          have haux : G.map m.2.left ≫ b.left.iso.inv = a.left.iso.inv ≫ F.map m.1.left :=
            (cancel_mono b.hom).1 (by simp only [Category.assoc, hm₁, hm₂])
          simpa using (a.left.iso.hom ≫= haux =≫ b.left.iso.hom).symm }
    exact ⟨CostructuredArrow.homMk pbm (by
      simpa [P, categoricalPullbackFst, pbm] using hm₁), by ext <;> rfl⟩
  let : Q.EssSurj := by
    refine ⟨fun y => ⟨⟨⟨y.1.left, y.2.left, asIso y.1.hom ≪≫ (asIso y.2.hom).symm⟩, ⟨⟨⟩⟩,
      y.1.hom⟩, ?_⟩⟩
    refine ⟨eqToIso (Prod.ext (CostructuredArrow.obj_ext _ _ rfl ?_)
      (CostructuredArrow.obj_ext _ _ rfl ?_))⟩ <;>
      simp [Q, P, categoricalPullbackFst, CostructuredArrow.hom]
  let : Q.IsEquivalence := { }
  exact Q.asEquivalence

/-- The first leg of `costructuredArrowCategoricalPullbackEquiv` is the structure arrow of the
point itself. -/
@[simp]
public theorem costructuredArrowCategoricalPullbackEquiv_functor_obj_fst_hom
    (F : C ⥤ E) (G : D ⥤ E) (x : E) (hE : IsGroupoid E)
    (t : CostructuredArrow (categoricalPullbackFst F G) x) :
    ((costructuredArrowCategoricalPullbackEquiv F G x hE).functor.obj t).1.hom = t.hom :=
  rfl

/-- The second leg of `costructuredArrowCategoricalPullbackEquiv` is the structure arrow read
through the comparison isomorphism carried by the point. -/
@[simp]
public theorem costructuredArrowCategoricalPullbackEquiv_functor_obj_snd_hom
    (F : C ⥤ E) (G : D ⥤ E) (x : E) (hE : IsGroupoid E)
    (t : CostructuredArrow (categoricalPullbackFst F G) x) :
    ((costructuredArrowCategoricalPullbackEquiv F G x hE).functor.obj t).2.hom =
      t.left.iso.inv ≫ t.hom :=
  rfl

/-- The full subcategory of pairs of isomorphisms is the product of the two iso-fibres. -/
public def isoFiberProdEquivalence (F : C ⥤ E) (G : D ⥤ E) (x : E) :
    (IsIsoCostructuredArrowPair F G x).FullSubcategory ≌
      (IsoFiber F x × IsoFiber G x) where
  functor :=
    { obj y := (⟨y.1.1, y.2.1⟩, ⟨y.1.2, y.2.2⟩)
      map m := (ObjectProperty.homMk m.hom.1, ObjectProperty.homMk m.hom.2) }
  inverse :=
    { obj y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
      map m := ObjectProperty.homMk (m.1.hom, m.2.hom) }
  unitIso := NatIso.ofComponents Iso.refl
  counitIso := NatIso.ofComponents Iso.refl

end Pullback

end CategoryTheory.Functor
