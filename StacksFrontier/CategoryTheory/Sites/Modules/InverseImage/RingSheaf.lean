module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Ring.MinimalAxioms
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Ring
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
public import Mathlib.RingTheory.FreeRing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import StacksFrontier.CategoryTheory.Monoidal.MapRingObj
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf

/-!
# Sheaves of rings as internal ring objects

A sheaf of rings on a site is the same thing as an internal ring object in the category of
sheaves of sets: the ring operations of a sheaf of rings are a `RingObj` structure on its
underlying sheaf of sets, and conversely the operations of an internal ring can be read
sectionwise as rings of sections. Transporting the geometric inverse image of a morphism of
topoi through this identification gives the inverse image on sheaves of rings.

This is the ring-level companion of
`StacksFrontier/CategoryTheory/Sites/Modules/InverseImage/GrpSheaf.lean` and
`StacksFrontier/CategoryTheory/Sites/Modules/InverseImage/AbelianSheaf.lean`, which do the same for
sheaves of groups and of abelian groups. Internal ring objects are moved along a braided functor
by `CategoryTheory.Functor.mapRing`.

## Main definitions

* `CategoryTheory.Sites.RingSheaf.presheafEquivalence` identifies presheaves of rings with ring
  objects in presheaves of sets.
* `CategoryTheory.Sites.RingSheaf.internalSheaf` turns a sheaf of rings into an internal ring
  object in sheaves of sets.
* `CategoryTheory.Sites.RingSheaf.externalSheaf` is its inverse, reading the operations of an
  internal ring sectionwise.
* `CategoryTheory.Sites.ringInverseImage` is the canonical functor between `Sheaf K RingCat` and
  `Sheaf J RingCat` attached to a morphism of topoi.

## Main results

* `CategoryTheory.Sites.RingSheaf.equivalence` is the equivalence between sheaves of rings and
  internal ring objects in sheaves of sets.
* `CategoryTheory.Sites.ringInverseImage_forgetIso` identifies the underlying sheaf of sets of
  `ringInverseImage` with the geometric inverse image; it is the identity isomorphism.
* `RingCat.forget_isCorepresentable`: the free ring on one generator corepresents the forgetful
  functor, so a sheaf of rings always has an underlying sheaf of sets, with no size condition
  relating the universe of the rings to the universes of the site.

## Implementation notes

Mathlib corepresents the forgetful functor of `GrpCat` and `AddCommGrpCat` but not of `RingCat`,
so the group and abelian files get `GrothendieckTopology.HasSheafCompose (forget _)` for free
where this one does not. `RingCat.coyonedaObjIsoForget` supplies it from
`FreeRing (ULift Unit)`; every statement below is therefore unconditional, exactly as in the
group case, rather than carrying a `HasSheafCompose` hypothesis.

A ring object in `Type w` is turned into an honest `Ring` by `ringObjRing`, through
`Ring.ofMinimalAxioms`: commutativity of the addition and the two annihilation laws are
consequences of the remaining axioms, so only the eight equations that are literally the ring
object's structure morphisms evaluated at elements have to be supplied.

`CategoryTheory.Functor.mapRing` asks for `CategoryTheory.Functor.Braided` rather than
`CategoryTheory.Functor.Monoidal`, so the call sites here fix the braided structure with
`CategoryTheory.Functor.Braided.ofChosenFiniteProducts`. The scoped instances of the `Obj`
namespace are deliberately not opened: they would transport a pulled-back `MonObj X` forward to
`MonObj (F.obj X)` and shadow the ring structure actually given on `F.obj X`.

There is a second construction of the same functor in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposRingImageAdjunction.lean`, namely
`Stacks.Sheaves.ToposPushforward.inverseImageRingFunctor`, obtained by an elementwise transport
of the ring operations along any finite-product-preserving functor of sheaves of sets rather than
through internal ring objects. Both have the geometric inverse image as their underlying sheaf of
sets on the nose.

## References

* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

universe v u v' u' w w'

open CategoryTheory Opposite

/-- The free ring on one generator represents elements: a ring homomorphism out of it is the
same thing as an element of the target. -/
noncomputable def freeRingUnitHomEquiv (R : Type w) [Ring R] :
    (FreeRing (ULift.{w} Unit) →+* R) ≃ R where
  toFun f := f (FreeRing.of (ULift.up ()))
  invFun r := FreeRing.lift fun _ => r
  left_inv f := by ext ⟨⟨⟩⟩; simp
  right_inv r := by simp

/-- The forgetful functor from rings to sets is corepresented by the free ring on one
generator. -/
noncomputable def RingCat.coyonedaObjIsoForget :
    coyoneda.obj (op (RingCat.of (FreeRing (ULift.{w} Unit)))) ≅ forget RingCat.{w} :=
  NatIso.ofComponents fun R ↦
    (ConcreteCategory.homEquiv.trans (freeRingUnitHomEquiv R.carrier)).toIso

/-- The forgetful functor from rings to sets is corepresentable. -/
instance RingCat.forget_isCorepresentable : (forget RingCat.{w}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' RingCat.coyonedaObjIsoForget

namespace CategoryTheory.Sites

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C]

namespace RingSheaf

open scoped MonObj AddMonObj

/-- The sectionwise ring operations of a presheaf of rings. -/
noncomputable abbrev presheafRingObj (R : C ⥤ RingCat.{w}) :
    RingObj (R ⋙ forget RingCat.{w}) where
  zero := { app X := ↾fun _ => (0 : R.obj X)
            naturality X Y f := by ext; exact (map_zero (R.map f).hom).symm }
  add := { app X := ↾fun p => (p.1 + p.2 : R.obj X)
           naturality X Y f := by ext; exact (map_add (R.map f).hom _ _).symm }
  neg := { app X := ↾fun a => (-a : R.obj X)
           naturality X Y f := by ext; exact (map_neg (R.map f).hom _).symm }
  one := { app X := ↾fun _ => (1 : R.obj X)
           naturality X Y f := by ext; exact (map_one (R.map f).hom).symm }
  mul := { app X := ↾fun p => (p.1 * p.2 : R.obj X)
           naturality X Y f := by ext; exact (map_mul (R.map f).hom _ _).symm }
  zero_add := by ext X x; exact zero_add _
  add_zero := by ext X x; exact add_zero _
  add_assoc := by ext X x; exact add_assoc _ _ _
  left_neg := by ext X x; exact neg_add_cancel _
  right_neg := by ext X x; exact add_neg_cancel _
  add_comm := by ext X x; exact add_comm _ _
  one_mul := by ext X x; exact one_mul _
  mul_one := by ext X x; exact mul_one _
  mul_assoc := by ext X x; exact mul_assoc _ _ _
  mul_add := by ext X x; exact mul_add _ _ _
  add_mul := by ext X x; exact add_mul _ _ _

/-- A homomorphism of presheaves of rings, regarded as a homomorphism of internal ring
objects. -/
lemma isRingHom_whiskerRight {R S : C ⥤ RingCat.{w}} (f : R ⟶ S) :
    letI := presheafRingObj R
    letI := presheafRingObj S
    IsRingHom (Functor.whiskerRight f (forget RingCat.{w})) := by
  let := presheafRingObj R
  let := presheafRingObj S
  have : IsMonHom (Functor.whiskerRight f (forget RingCat.{w})) :=
    ⟨by ext X x; exact map_one (f.app X).hom,
      by ext X x; exact map_mul (f.app X).hom _ _⟩
  have : IsAddMonHom (Functor.whiskerRight f (forget RingCat.{w})) :=
    ⟨by ext X x; exact map_zero (f.app X).hom,
      by ext X x; exact map_add (f.app X).hom _ _⟩
  exact ⟨⟩

/-- Internalize the sectionwise operations and homomorphisms of presheaves of rings. -/
noncomputable def presheafRing : (C ⥤ RingCat.{w}) ⥤ RingObjCat (C ⥤ Type w) where
  obj R := letI := presheafRingObj R; { X := R ⋙ forget RingCat.{w} }
  map {R S} f :=
    letI := presheafRingObj R
    letI := presheafRingObj S
    haveI := isRingHom_whiskerRight f
    { hom := Functor.whiskerRight f (forget RingCat.{w}) }
  map_id _ := RingObjCat.hom_ext rfl
  map_comp _ _ := RingObjCat.hom_ext rfl

/-- Evaluate an internal ring object in a functor category at an object. -/
noncomputable abbrev evaluationRingObj (R : C ⥤ Type w) [RingObj R] (X : C) :
    RingObj (R.obj X) where
  zero := ζ[R].app X
  add := σ[R].app X
  neg := (AddGrpObj.neg (X := R)).app X
  one := η[R].app X
  mul := μ[R].app X
  zero_add := congr_app (AddMonObj.zero_add R) X
  add_zero := congr_app (AddMonObj.add_zero R) X
  add_assoc := congr_app (AddMonObj.add_assoc R) X
  left_neg := congr_app (AddGrpObj.left_neg R) X
  right_neg := congr_app (AddGrpObj.right_neg R) X
  add_comm := congr_app (IsCommAddMonObj.add_comm R) X
  one_mul := congr_app (MonObj.one_mul R) X
  mul_one := congr_app (MonObj.mul_one R) X
  mul_assoc := congr_app (MonObj.mul_assoc R) X
  mul_add := congr_app (RingObj.mul_add R) X
  add_mul := congr_app (RingObj.add_mul R) X

/-- The zero of an additive monoid object in `Type w`. -/
noncomputable abbrev addMonObjZero (A : Type w) [AddMonObj A] : Zero A := ⟨ζ[A] PUnit.unit⟩

/-- The addition of an additive monoid object in `Type w`. -/
noncomputable abbrev addMonObjAdd (A : Type w) [AddMonObj A] : Add A := ⟨fun x y => σ[A] (x, y)⟩

/-- The negation of an additive group object in `Type w`. -/
noncomputable abbrev addGrpObjNeg (A : Type w) [AddGrpObj A] : Neg A :=
  ⟨fun x => AddGrpObj.neg (X := A) x⟩

/-- The ring whose operations are those of a ring object in `Type w`. -/
noncomputable abbrev ringObjRing (A : Type w) [RingObj A] : Ring A :=
  letI := MonTypeEquivalenceMon.monMonoid A
  letI := addMonObjZero A
  letI := addMonObjAdd A
  letI := addGrpObjNeg A
  Ring.ofMinimalAxioms
    (fun x y z => by
      convert! ConcreteCategory.congr_hom (CC := fun X : Type w => X)
        (AddMonObj.add_assoc A) ((x, y), z))
    (fun x => by
      convert! ConcreteCategory.congr_hom (CC := fun X : Type w => X)
        (AddMonObj.zero_add A) (PUnit.unit, x))
    (fun x => ConcreteCategory.congr_hom (CC := fun X : Type w => X) (AddGrpObj.left_neg A) x)
    mul_assoc one_mul mul_one
    (fun x y z => ConcreteCategory.congr_hom (CC := fun X : Type w => X)
      (RingObj.mul_add A) (x, (y, z)))
    (fun x y z => ConcreteCategory.congr_hom (CC := fun X : Type w => X)
      (RingObj.add_mul A) ((x, y), z))

/-- Read the internal ring operations of a ring object in presheaves of sets as rings of
sections. -/
noncomputable def ringPresheaf (R : RingObjCat (C ⥤ Type w)) : C ⥤ RingCat.{w} where
  obj X :=
    letI := evaluationRingObj R.X X
    letI := ringObjRing (R.X.obj X)
    RingCat.of (R.X.obj X)
  map {X Y} f := by
    letI := evaluationRingObj R.X X
    letI := evaluationRingObj R.X Y
    letI := ringObjRing (R.X.obj X)
    letI := ringObjRing (R.X.obj Y)
    exact RingCat.ofHom {
      toFun := R.X.map f
      map_one' := (ConcreteCategory.congr_hom (CC := fun X : Type w => X)
        ((MonObj.one (X := R.X)).naturality f) PUnit.unit).symm
      map_mul' a b := (ConcreteCategory.congr_hom (CC := fun X : Type w => X)
        ((MonObj.mul (X := R.X)).naturality f) (a, b)).symm
      map_zero' := (ConcreteCategory.congr_hom (CC := fun X : Type w => X)
        ((AddMonObj.zero (X := R.X)).naturality f) PUnit.unit).symm
      map_add' a b := (ConcreteCategory.congr_hom (CC := fun X : Type w => X)
        ((AddMonObj.add (X := R.X)).naturality f) (a, b)).symm }
  map_id X := (forget RingCat.{w}).map_injective (R.X.map_id X)
  map_comp f g := (forget RingCat.{w}).map_injective (R.X.map_comp f g)

/-- Read internal homomorphisms sectionwise as homomorphisms of presheaves of rings. -/
noncomputable def ringPresheaves : RingObjCat (C ⥤ Type w) ⥤ (C ⥤ RingCat.{w}) where
  obj := ringPresheaf
  map {R S} f := {
    app X := by
      letI := evaluationRingObj R.X X
      letI := evaluationRingObj S.X X
      letI := ringObjRing (R.X.obj X)
      letI := ringObjRing (S.X.obj X)
      exact RingCat.ofHom {
        toFun := f.hom.app X
        map_one' := ConcreteCategory.congr_hom (CC := fun X : Type w => X)
          (congr_app (IsMonHom.one_hom f.hom) X) PUnit.unit
        map_mul' a b := ConcreteCategory.congr_hom (CC := fun X : Type w => X)
          (congr_app (IsMonHom.mul_hom f.hom) X) (a, b)
        map_zero' := ConcreteCategory.congr_hom (CC := fun X : Type w => X)
          (congr_app (IsAddMonHom.zero_hom f.hom) X) PUnit.unit
        map_add' a b := ConcreteCategory.congr_hom (CC := fun X : Type w => X)
          (congr_app (IsAddMonHom.add_hom f.hom) X) (a, b) }
    naturality X Y a := by
      ext x
      exact ConcreteCategory.congr_hom (f.hom.naturality a) x }
  map_id R := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- Presheaves of rings are the same thing as ring objects in presheaves of sets: the
operations of a presheaf of rings are read sectionwise, and conversely. -/
noncomputable def presheafEquivalence (C : Type u) [Category.{v} C] :
    (C ⥤ RingCat.{w}) ≌ RingObjCat (C ⥤ Type w) where
  functor := presheafRing
  inverse := ringPresheaves
  unitIso := NatIso.ofComponents fun A ↦ NatIso.ofComponents fun X ↦
    letI := evaluationRingObj (presheafRing.obj A).X X
    letI := ringObjRing ((presheafRing.obj A).X.obj X)
    RingEquiv.toRingCatIso
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl
        map_add' := fun _ _ ↦ rfl }
  counitIso := NatIso.ofComponents fun R ↦ RingObjCat.mkIso (Iso.refl R.X)
    (by ext X x; rfl) (by ext X x; rfl) (by ext X x; rfl) (by ext X x; rfl)
  functor_unitIso_comp _ := RingObjCat.hom_ext rfl

section Pullback
variable [CartesianMonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} [F.Braided] (hF : F.FullyFaithful)

private lemma map_pull_mul {X : C} [MonObj (F.obj X)] [MonObj X]
    (h : μ[X] = hF.preimage (Functor.OplaxMonoidal.δ F X X ≫ μ[F.obj X]))
    {Y : C} (a b : Y ⟶ X) : F.map (a * b) = F.map a * F.map b := by
  change F.map (lift a b ≫ μ[X]) = lift (F.map a) (F.map b) ≫ μ[F.obj X]
  rw [h, F.map_comp, hF.map_preimage, ← Category.assoc, Functor.OplaxMonoidal.lift_δ]

private lemma map_pull_add {X : C} [AddMonObj (F.obj X)] [AddMonObj X]
    (h : σ[X] = hF.preimage (Functor.OplaxMonoidal.δ F X X ≫ σ[F.obj X]))
    {Y : C} (a b : Y ⟶ X) : F.map (a + b) = F.map a + F.map b := by
  change F.map (lift a b ≫ σ[X]) = lift (F.map a) (F.map b) ≫ σ[F.obj X]
  rw [h, F.map_comp, hF.map_preimage, ← Category.assoc, Functor.OplaxMonoidal.lift_δ]

/-- Pull internal ring operations back along a fully faithful braided functor. -/
noncomputable abbrev pullRingObj (X : C) [RingObj (F.obj X)] : RingObj X :=
  letI : AddGrpObj X := hF.addGrpObj X
  letI : MonObj X := hF.monObj X
  letI : IsCommAddMonObj X :=
    ⟨hF.map_injective (by simp [Functor.map_comp, IsCommAddMonObj.add_comm])⟩
  { __ := (inferInstance : AddGrpObj X)
    __ := (inferInstance : IsCommAddMonObj X)
    __ := (inferInstance : MonObj X)
    mul_add := (mul_add_iff X).mpr fun Y a b c => hF.map_injective (by
      rw [map_pull_mul hF rfl, map_pull_add hF rfl, map_pull_add hF rfl,
        map_pull_mul hF rfl, map_pull_mul hF rfl]
      exact Hom.mul_add _ _ _)
    add_mul := (add_mul_iff X).mpr fun Y a b c => hF.map_injective (by
      rw [map_pull_mul hF rfl, map_pull_add hF rfl, map_pull_add hF rfl,
        map_pull_mul hF rfl, map_pull_mul hF rfl]
      exact Hom.add_mul _ _ _) }

/-- The ring object obtained by pulling internal ring operations back along a fully faithful
braided functor. -/
noncomputable abbrev pullRing (X : C) [RingObj (F.obj X)] : RingObjCat C :=
  letI := pullRingObj hF X
  { X := X }

/-- A morphism preserves pulled-back ring operations when its image preserves the original
ones. -/
lemma isRingHom_pullRingObj {X Y : C} [RingObj (F.obj X)] [RingObj (F.obj Y)]
    (f : X ⟶ Y) [IsRingHom (F.map f)] :
    letI := pullRingObj hF X
    letI := pullRingObj hF Y
    IsRingHom f := by
  have ho := IsMonHom.one_hom (F.map f)
  have hm := IsMonHom.mul_hom (F.map f)
  have hz := IsAddMonHom.zero_hom (F.map f)
  have ha := IsAddMonHom.add_hom (F.map f)
  let : RingObj X := pullRingObj hF X
  let : RingObj Y := pullRingObj hF Y
  have : IsMonHom f :=
    { one_hom := hF.map_injective (by simp [Functor.map_comp, ho])
      mul_hom := hF.map_injective (by
        simp [Functor.map_comp, ← Functor.OplaxMonoidal.δ_natural_assoc, hm]) }
  have : IsAddMonHom f :=
    { zero_hom := hF.map_injective (by simp [Functor.map_comp, hz])
      add_hom := hF.map_injective (by
        simp [Functor.map_comp, ← Functor.OplaxMonoidal.δ_natural_assoc, ha]) }
  exact ⟨⟩

private lemma map_pullRing_mul (X : C) [RingObj (F.obj X)] :
    MonObj.mul (X := (F.mapRing.obj (pullRing hF X)).X) = MonObj.mul (X := F.obj X) := by
  let : RingObj X := pullRingObj hF X
  change Functor.LaxMonoidal.μ F X X ≫ F.map
      (hF.preimage (Functor.OplaxMonoidal.δ F X X ≫ MonObj.mul (X := F.obj X))) =
    MonObj.mul (X := F.obj X)
  rw [hF.map_preimage]
  simp

private lemma map_pullRing_add (X : C) [RingObj (F.obj X)] :
    AddMonObj.add (X := (F.mapRing.obj (pullRing hF X)).X) = AddMonObj.add (X := F.obj X) := by
  let : RingObj X := pullRingObj hF X
  change Functor.LaxMonoidal.μ F X X ≫ F.map
      (hF.preimage (Functor.OplaxMonoidal.δ F X X ≫ AddMonObj.add (X := F.obj X))) =
    AddMonObj.add (X := F.obj X)
  rw [hF.map_preimage]
  simp

end Pullback

variable (J : GrothendieckTopology C)

/-- The internal ring object attached to an ordinary sheaf of rings. -/
noncomputable abbrev internalSheafObj (R : Sheaf J RingCat.{w}) :
    RingObjCat (Sheaf J (Type w)) := by
  letI : RingObj ((sheafToPresheaf J (Type w)).obj
      ((sheafCompose J (forget RingCat.{w})).obj R)) := presheafRingObj R.obj
  exact pullRing (fullyFaithfulSheafToPresheaf J (Type w))
    ((sheafCompose J (forget RingCat.{w})).obj R)

/-- Internalize ordinary sheaves of rings and their homomorphisms. -/
noncomputable def internalSheaf : Sheaf J RingCat.{w} ⥤ RingObjCat (Sheaf J (Type w)) where
  obj := internalSheafObj J
  map {R S} f := by
    letI : RingObj ((sheafToPresheaf J (Type w)).obj
        ((sheafCompose J (forget RingCat.{w})).obj R)) := presheafRingObj R.obj
    letI : RingObj ((sheafToPresheaf J (Type w)).obj
        ((sheafCompose J (forget RingCat.{w})).obj S)) := presheafRingObj S.obj
    haveI : IsRingHom ((sheafToPresheaf J (Type w)).map
        ((sheafCompose J (forget RingCat.{w})).map f)) :=
      isRingHom_whiskerRight f.hom
    haveI := isRingHom_pullRingObj (fullyFaithfulSheafToPresheaf J (Type w))
      ((sheafCompose J (forget RingCat.{w})).map f)
    exact { hom := (sheafCompose J (forget RingCat.{w})).map f }

/-- Read an internal ring object in sheaves of sets as an ordinary sheaf of rings. -/
noncomputable def externalSheaf : RingObjCat (Sheaf J (Type w)) ⥤ Sheaf J RingCat.{w} where
  obj R := ⟨ringPresheaf ((sheafToPresheaf J (Type w)).mapRing.obj R),
    Presheaf.isSheaf_ringCat_of_isSheaf_forget _ (by
      change Presheaf.IsSheaf J R.X.obj
      exact R.X.property)⟩
  map f := ⟨ringPresheaves.map ((sheafToPresheaf J (Type w)).mapRing.map f)⟩

/-- Reading the ring operations of a sheaf of rings sectionwise and then internalizing them
recovers the sheaf, naturally in it. One half of `equivalence`. -/
public noncomputable def internalExternalIso (J : GrothendieckTopology C) :
    internalSheaf J ⋙ externalSheaf J ≅ 𝟭 (Sheaf J RingCat.{w}) := by
  refine NatIso.ofComponents (fun R => ?_) ?_
  · refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun U => ?_) ?_)
    · letI := evaluationRingObj
        ((sheafToPresheaf J (Type w)).mapRing.obj ((internalSheaf J).obj R)).X U
      letI := ringObjRing
        (((sheafToPresheaf J (Type w)).mapRing.obj ((internalSheaf J).obj R)).X.obj U)
      letI : RingObj ((sheafToPresheaf J (Type w)).obj
          ((sheafCompose J (forget RingCat.{w})).obj R)) := presheafRingObj R.obj
      exact RingEquiv.toRingCatIso
        { toFun := fun x => x
          invFun := fun x => x
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := by
            intro x y
            exact congrArg
              (fun m : (sheafToPresheaf J (Type w)).obj
                    ((sheafCompose J (forget RingCat.{w})).obj R) ⊗
                  (sheafToPresheaf J (Type w)).obj
                    ((sheafCompose J (forget RingCat.{w})).obj R) ⟶
                  (sheafToPresheaf J (Type w)).obj
                    ((sheafCompose J (forget RingCat.{w})).obj R) =>
                (ConcreteCategory.hom (m.app U)) (x, y))
              (map_pullRing_mul (fullyFaithfulSheafToPresheaf J (Type w))
                ((sheafCompose J (forget RingCat.{w})).obj R))
          map_add' := by
            intro x y
            exact congrArg
              (fun m : (sheafToPresheaf J (Type w)).obj
                    ((sheafCompose J (forget RingCat.{w})).obj R) ⊗
                  (sheafToPresheaf J (Type w)).obj
                    ((sheafCompose J (forget RingCat.{w})).obj R) ⟶
                  (sheafToPresheaf J (Type w)).obj
                    ((sheafCompose J (forget RingCat.{w})).obj R) =>
                (ConcreteCategory.hom (m.app U)) (x, y))
              (map_pullRing_add (fullyFaithfulSheafToPresheaf J (Type w))
                ((sheafCompose J (forget RingCat.{w})).obj R)) }
    · intro U V f
      ext x
      rfl
  · intro X Y g
    apply (sheafToPresheaf J RingCat.{w}).map_injective
    ext U x
    rfl

/-- Internalizing a sectionwise ring object and then reading its operations back off recovers
the ring object, naturally in it. The other half of `equivalence`. -/
public noncomputable def externalInternalIso (J : GrothendieckTopology C) :
    externalSheaf J ⋙ internalSheaf J ≅ 𝟭 (RingObjCat (Sheaf J (Type w))) := by
  refine NatIso.ofComponents (fun R => RingObjCat.mkIso (Iso.refl _) ?_ ?_ ?_ ?_) ?_
  · let U := sheafToPresheaf J (Type w)
    let : U.Braided := .ofChosenFiniteProducts _
    change (fullyFaithfulSheafToPresheaf J (Type w)).preimage
      (Functor.OplaxMonoidal.η U ≫
        (Functor.LaxMonoidal.ε U ≫ U.map (MonObj.one (X := R.X)))) ≫ 𝟙 _ = _
    apply U.map_injective
    simp only [Category.comp_id, Functor.Monoidal.η_ε_assoc]
    rfl
  · let U := sheafToPresheaf J (Type w)
    let : U.Braided := .ofChosenFiniteProducts _
    change (fullyFaithfulSheafToPresheaf J (Type w)).preimage
      (Functor.OplaxMonoidal.δ U R.X R.X ≫
        (Functor.LaxMonoidal.μ U R.X R.X ≫ U.map (MonObj.mul (X := R.X)))) ≫ 𝟙 _ = _
    apply U.map_injective
    simp only [Category.comp_id, Functor.Monoidal.δ_μ_assoc, Iso.refl_hom]
    change U.map (ObjectProperty.homMk (U.map (MonObj.mul (X := R.X)))) =
      U.map ((𝟙 R.X ⊗ₘ 𝟙 R.X) ≫ MonObj.mul (X := R.X))
    rw [MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rfl
  · let U := sheafToPresheaf J (Type w)
    let : U.Braided := .ofChosenFiniteProducts _
    change (fullyFaithfulSheafToPresheaf J (Type w)).preimage
      (Functor.OplaxMonoidal.η U ≫
        (Functor.LaxMonoidal.ε U ≫ U.map (AddMonObj.zero (X := R.X)))) ≫ 𝟙 _ = _
    apply U.map_injective
    simp only [Category.comp_id, Functor.Monoidal.η_ε_assoc]
    rfl
  · let U := sheafToPresheaf J (Type w)
    let : U.Braided := .ofChosenFiniteProducts _
    change (fullyFaithfulSheafToPresheaf J (Type w)).preimage
      (Functor.OplaxMonoidal.δ U R.X R.X ≫
        (Functor.LaxMonoidal.μ U R.X R.X ≫ U.map (AddMonObj.add (X := R.X)))) ≫ 𝟙 _ = _
    apply U.map_injective
    simp only [Category.comp_id, Functor.Monoidal.δ_μ_assoc, Iso.refl_hom]
    change U.map (ObjectProperty.homMk (U.map (AddMonObj.add (X := R.X)))) =
      U.map ((𝟙 R.X ⊗ₘ 𝟙 R.X) ≫ AddMonObj.add (X := R.X))
    rw [MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rfl
  · intro X Y g
    exact RingObjCat.hom_ext rfl

/-- Sheaves of rings on a site are the same thing as ring objects in its category of sheaves of
types. The two directions are `internalSheaf` and `externalSheaf`, and the unit and counit are
`internalExternalIso` and `externalInternalIso`. -/
public noncomputable def equivalence (J : GrothendieckTopology C) :
    Sheaf J RingCat.{w} ≌ RingObjCat (Sheaf J (Type w)) where
  functor := internalSheaf J
  inverse := externalSheaf J
  unitIso := (internalExternalIso J).symm
  counitIso := externalInternalIso J
  functor_unitIso_comp X := by
    apply (RingObjCat.forget (Sheaf J (Type w))).map_injective
    ext U x
    rfl

end RingSheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- The inverse image functor of `f`, which preserves finite products, is braided for the
cartesian monoidal structures on the categories of sheaves of types. -/
noncomputable local instance inverseImageBraidedRing : f.inverseImage.Braided :=
  .ofChosenFiniteProducts _

/-- The canonical inverse image of ordinary sheaves of rings: apply geometric inverse image to
their ring operations and read the resulting operations as rings of sections. -/
noncomputable def ringInverseImage :
    Sheaf K RingCat.{w'} ⥤ Sheaf J RingCat.{w} :=
  RingSheaf.internalSheaf K ⋙ f.inverseImage.mapRing ⋙ RingSheaf.externalSheaf J

/-- Forgetting the ring operations recovers the geometric inverse image, naturally in the sheaf.
In this construction the underlying sheaves and their maps agree definitionally. -/
noncomputable def ringInverseImage_forgetIso :
    ringInverseImage f ⋙ sheafCompose J (forget RingCat.{w}) ≅
      sheafCompose K (forget RingCat.{w'}) ⋙ f.inverseImage := Iso.refl _

end CategoryTheory.Sites

end
