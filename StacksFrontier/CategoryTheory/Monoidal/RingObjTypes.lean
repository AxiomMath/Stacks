module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
public import Mathlib.CategoryTheory.Monoidal.Ring

/-!
# Ring objects in `Type u` are bundled rings

A ring object in the cartesian monoidal category `Type u` is a type `A` equipped with morphisms
`𝟙_ (Type u) ⟶ A` and `A ⊗ A ⟶ A` for the zero, the addition, the one and the multiplication,
together with a negation `A ⟶ A`. Since `𝟙_ (Type u)` is `PUnit` and `A ⊗ A` is `A × A`, these
morphisms are exactly two elements `0, 1 : A`, two binary operations and a unary operation on `A`,
and the identities required of a ring object say at points precisely that these make `A` a ring.
So a ring object in `Type u` is the same thing as a bundled ring, and this file proves that the
two categories are equivalent.

This is the ring analogue of Mathlib's `CategoryTheory.monTypeEquivalenceMon` and
`CategoryTheory.grpTypeEquivalenceGrp`, and it is built on the former: the multiplicative monoid
of a ring object in `Type u` is the monoid that Mathlib already extracts from the underlying
monoid object.

## Main definitions

* `CategoryTheory.RingTypeEquivalenceRing.ringObjRing` — the ring structure on the underlying
  type of a ring object in `Type u`.
* `CategoryTheory.RingTypeEquivalenceRing.ringObjOfRing` — the ring object structure on the
  underlying type of a bundled ring.
* `CategoryTheory.RingTypeEquivalenceRing.functor` and
  `CategoryTheory.RingTypeEquivalenceRing.inverse` — the two functors between
  `RingObjCat (Type u)` and `RingCat.{u}`.

## Main results

* `CategoryTheory.ringTypeEquivalenceRing` — the category of ring objects in `Type u` is
  equivalent to the category of bundled rings.
* `CategoryTheory.ringTypeEquivalenceRingForget` — that equivalence is compatible with the
  forgetful functors to `Type u`.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
-/

@[expose] public section

universe u

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory

open scoped MonObj AddMonObj

namespace RingTypeEquivalenceRing

/-- The additive commutative group underlying a ring object in `Type u`: the zero is the value of
the zero morphism at the unique point of `𝟙_ (Type u)`, the addition is the addition morphism
read as a function on `A × A`, and the negation is the negation morphism. -/
public instance ringObjAddCommGroup (A : Type u) [RingObj A] : AddCommGroup A :=
  let : Zero A := ⟨ζ[A] PUnit.unit⟩
  let : Add A := ⟨fun x y => σ[A] (x, y)⟩
  let : Neg A := ⟨fun x => AddGrpObj.neg (X := A) x⟩
  { zero := ζ[A] PUnit.unit
    add x y := σ[A] (x, y)
    neg x := AddGrpObj.neg (X := A) x
    nsmul := nsmulRec
    zsmul := zsmulRec
    zero_add x := by
      convert! ConcreteCategory.congr_hom (CC := fun X ↦ X) (AddMonObj.zero_add A) (PUnit.unit, x)
    add_zero x := by
      convert! ConcreteCategory.congr_hom (CC := fun X ↦ X) (AddMonObj.add_zero A) (x, PUnit.unit)
    add_assoc x y z := by
      convert! ConcreteCategory.congr_hom (CC := fun X ↦ X) (AddMonObj.add_assoc A) ((x, y), z)
    neg_add_cancel x := ConcreteCategory.congr_hom (CC := fun X ↦ X) (AddGrpObj.left_neg A) x
    add_comm x y := by
      convert! ConcreteCategory.congr_hom (CC := fun X ↦ X) (IsCommAddMonObj.add_comm A) (y, x) }

/-- **The underlying type of a ring object in `Type u` is a ring.** The multiplicative monoid is
the one carried by the underlying monoid object, the additive commutative group is
`CategoryTheory.RingTypeEquivalenceRing.ringObjAddCommGroup`, and the distributivity laws are the
two distributivity identities of the ring object read off at points. -/
public instance ringObjRing (A : Type u) [RingObj A] : Ring A :=
  { MonTypeEquivalenceMon.monMonoid A, ringObjAddCommGroup A with
    left_distrib a b c :=
      ConcreteCategory.congr_hom (CC := fun X ↦ X) (RingObj.mul_add A) (a, (b, c))
    right_distrib a b c :=
      ConcreteCategory.congr_hom (CC := fun X ↦ X) (RingObj.add_mul A) ((a, b), c)
    zero_mul a := by
      have h : ∀ x y z : A, (x + y) * z = x * z + y * z := fun x y z =>
        ConcreteCategory.congr_hom (CC := fun X ↦ X) (RingObj.add_mul A) ((x, y), z)
      refine add_left_cancel (a := (0 : A) * a) ?_
      rw [add_zero, ← h 0 0 a, zero_add]
    mul_zero a := by
      have h : ∀ x y z : A, x * (y + z) = x * y + x * z := fun x y z =>
        ConcreteCategory.congr_hom (CC := fun X ↦ X) (RingObj.mul_add A) (x, (y, z))
      refine add_left_cancel (a := a * (0 : A)) ?_
      rw [add_zero, ← h a 0 0, zero_add] }

attribute [local simp] types_tensorObj_def types_tensorUnit_def in
/-- **The underlying type of a bundled ring is a ring object in `Type u`**, with the four
structure morphisms the ring operations read as functions on `PUnit` and on `A × A`. -/
@[instance_reducible]
public def ringObjOfRing (A : Type u) [Ring A] : RingObj A where
  one := ↾fun _ => (1 : A)
  mul := ↾fun p => p.1 * p.2
  zero := ↾fun _ => (0 : A)
  add := ↾fun p => p.1 + p.2
  neg := ↾fun x => -x
  one_mul := by cat_disch
  mul_one := by cat_disch
  mul_assoc := by ext ⟨⟨x, y⟩, z⟩; exact _root_.mul_assoc x y z
  zero_add := by cat_disch
  add_zero := by cat_disch
  add_assoc := by ext ⟨⟨x, y⟩, z⟩; exact _root_.add_assoc x y z
  left_neg := by ext x; exact neg_add_cancel x
  right_neg := by ext x; exact add_neg_cancel x
  add_comm := by ext ⟨x, y⟩; exact _root_.add_comm y x
  mul_add := by ext ⟨x, y, z⟩; exact _root_.mul_add x y z
  add_mul := by ext ⟨⟨x, y⟩, z⟩; exact _root_.add_mul x y z

/-- Converting a ring object in `Type u` into a bundled ring. -/
public noncomputable def functor : RingObjCat (Type u) ⥤ RingCat.{u} where
  obj A := RingCat.of A.X
  map f := RingCat.ofHom
    { toFun := f.hom
      map_one' := ConcreteCategory.congr_hom (IsMonHom.one_hom f.hom) PUnit.unit
      map_mul' x y :=
        ConcreteCategory.congr_hom (CC := fun X ↦ X) (IsMonHom.mul_hom f.hom) (x, y)
      map_zero' := ConcreteCategory.congr_hom (IsAddMonHom.zero_hom f.hom) PUnit.unit
      map_add' x y :=
        ConcreteCategory.congr_hom (CC := fun X ↦ X) (IsAddMonHom.add_hom f.hom) (x, y) }

/-- Converting a bundled ring into a ring object in `Type u`. -/
public noncomputable def inverse : RingCat.{u} ⥤ RingObjCat (Type u) where
  obj A := letI := ringObjOfRing (A : Type u); { X := (A : Type u) }
  map {A B} f :=
    letI := ringObjOfRing (A : Type u)
    letI := ringObjOfRing (B : Type u)
    haveI : IsMonHom (↾(f.hom : A → B)) :=
      { one_hom := by ext _; exact map_one f.hom
        mul_hom := by ext ⟨x, y⟩; exact map_mul f.hom x y }
    haveI : IsAddMonHom (↾(f.hom : A → B)) :=
      { zero_hom := by ext _; exact map_zero f.hom
        add_hom := by ext ⟨x, y⟩; exact map_add f.hom x y }
    haveI : IsRingHom (↾(f.hom : A → B)) := ⟨⟩
    { hom := ↾(f.hom : A → B) }

end RingTypeEquivalenceRing

open RingTypeEquivalenceRing

/-- **A ring object in `Type u` is the same thing as a bundled ring:** the category of ring
objects in the cartesian monoidal category `Type u` is equivalent to the category of rings. -/
public noncomputable def ringTypeEquivalenceRing : RingObjCat (Type u) ≌ RingCat.{u} where
  functor := functor
  inverse := inverse
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun A => RingEquiv.toRingCatIso
      { Equiv.refl _ with
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl })
    (by cat_disch)

/-- The equivalence `RingObjCat (Type u) ≌ RingCat.{u}` is naturally compatible with the
forgetful functors to `Type u`. -/
public noncomputable def ringTypeEquivalenceRingForget :
    RingTypeEquivalenceRing.functor ⋙ forget RingCat ≅ RingObjCat.forget (Type u) :=
  Iso.refl _

end CategoryTheory

end
