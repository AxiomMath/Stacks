module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.Algebra.Category.MonCat.ForgetCorepresentable

/-!
# Sheaves of monoids as internal monoid objects

A sheaf of monoids on a site is the same thing as an internal monoid object in the category of
sheaves of sets: the monoid operations of a sheaf of monoids are a `MonObj` structure on its
underlying sheaf of sets, and conversely the operations of an internal monoid can be read
sectionwise as monoids of sections.

This is the monoid companion of
`StacksFrontier/CategoryTheory/Sites/Modules/InverseImage/GrpSheaf.lean`, which does the same for
sheaves of groups and internal group objects, and is built in exactly the same shape.

## Main definitions

* `CategoryTheory.Sites.MonSheaf.evaluationMonObj` evaluates an internal monoid object in a
  functor category at an object.
* `CategoryTheory.Sites.MonSheaf.presheafEquivalence`: presheaves of monoids are the same thing
  as monoid objects in presheaves of sets.
* `CategoryTheory.Sites.MonSheaf.internalSheaf` turns a sheaf of monoids into an internal monoid
  object in sheaves of sets.
* `CategoryTheory.Sites.MonSheaf.externalSheaf` is its inverse, reading the operations of an
  internal monoid sectionwise.
* `CategoryTheory.Sites.MonSheaf.equivalence` is the resulting equivalence.

## Main results

* `CategoryTheory.Sites.MonSheaf.isMonHom_pullMonObj`: a morphism preserves monoid operations
  pulled back along a fully faithful cartesian functor when its image preserves the original
  ones.
* `CategoryTheory.Sites.MonSheaf.isSheaf_of_forget`: a presheaf of monoids is a sheaf when its
  underlying presheaf of sets is.

## Implementation notes

Internal monoid objects in sheaves of sets are taken for the chosen products `⨯`, as in the
group case. Both `MonCat` and `MonObj` are multiplicative, so reading an internal monoid
sectionwise lands on the nose in the monoid of sections: the underlying sheaves of sets of
`internalSheaf` and `externalSheaf` are definitionally those of their arguments, and the
components of `internalExternalIso`, `externalInternalIso` and `presheafEquivalence` are the
identity on sections.

## References

* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

namespace CategoryTheory.Sites

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

universe v u v' u' w

variable {C : Type u} [Category.{v} C]

namespace MonSheaf

/-- The multiplicative operations of a presheaf of monoids, regarded as internal monoid
operations. -/
noncomputable abbrev presheafMonObj (R : C ⥤ MonCat.{w}) :
    MonObj (R ⋙ forget MonCat.{w}) where
  one := { app X := ↾fun _ => (1 : R.obj X)
           naturality X Y f := by ext; exact (map_one (R.map f).hom).symm }
  mul := { app X := ↾fun (p : R.obj X × R.obj X) => p.1 * p.2
           naturality X Y f := by ext; exact (map_mul (R.map f).hom _ _).symm }
  one_mul := by ext X x; exact one_mul (M := R.obj X) _
  mul_one := by ext X x; exact mul_one (M := R.obj X) _
  mul_assoc := by ext X x; exact mul_assoc (G := R.obj X) _ _ _

/-- Internalize the sectionwise operations and homomorphisms of presheaves of monoids. -/
noncomputable def presheafMon : (C ⥤ MonCat.{w}) ⥤ Mon (C ⥤ Type w) where
  obj R := by
    letI := presheafMonObj R
    exact { X := R ⋙ forget MonCat.{w} }
  map {R S} f := by
    letI := presheafMonObj R
    letI := presheafMonObj S
    exact Mon.Hom.mk' (Functor.whiskerRight f (forget MonCat.{w}))
      (by ext X x; exact map_one (f.app X).hom)
      (by ext X x; exact map_mul (f.app X).hom _ _)

/-- Evaluate an internal monoid in a functor category at an object. -/
noncomputable abbrev evaluationMonObj (R : C ⥤ Type w) [MonObj R] (X : C) :
    MonObj (R.obj X) where
  one := (MonObj.one (X := R)).app X
  mul := (MonObj.mul (X := R)).app X
  one_mul := congr_app (MonObj.one_mul R) X
  mul_one := congr_app (MonObj.mul_one R) X
  mul_assoc := congr_app (MonObj.mul_assoc R) X

/-- Read the internal monoid operations as monoids of sections. -/
noncomputable def monPresheaf (R : Mon (C ⥤ Type w)) : C ⥤ MonCat.{w} where
  obj X :=
    letI := evaluationMonObj R.X X
    MonCat.of (R.X.obj X)
  map {X Y} f := by
    letI := evaluationMonObj R.X X
    letI := evaluationMonObj R.X Y
    exact MonCat.ofHom {
      toFun := R.X.map f
      map_one' := (ConcreteCategory.congr_hom (CC := fun X : Type w => X)
        ((MonObj.one (X := R.X)).naturality f) PUnit.unit).symm
      map_mul' a b := (ConcreteCategory.congr_hom (CC := fun X : Type w => X)
        ((MonObj.mul (X := R.X)).naturality f) (a,b)).symm }
  map_id X := (forget MonCat.{w}).map_injective (R.X.map_id X)
  map_comp f g := (forget MonCat.{w}).map_injective (R.X.map_comp f g)

/-- Read internal homomorphisms sectionwise as homomorphisms of presheaves of monoids. -/
noncomputable def monPresheaves : Mon (C ⥤ Type w) ⥤ (C ⥤ MonCat.{w}) where
  obj := monPresheaf
  map {R S} f := {
    app X := by
      letI := evaluationMonObj R.X X
      letI := evaluationMonObj S.X X
      exact MonCat.ofHom {
        toFun := f.hom.app X
        map_one' := ConcreteCategory.congr_hom (CC := fun X : Type w => X)
          (congr_app (IsMonHom.one_hom f.hom) X) PUnit.unit
        map_mul' a b := ConcreteCategory.congr_hom (CC := fun X : Type w => X)
          (congr_app (IsMonHom.mul_hom f.hom) X) (a,b) }
    naturality X Y a := by
      ext x
      exact ConcreteCategory.congr_hom (f.hom.naturality a) x }
  map_id R := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- Presheaves of monoids are the same thing as monoid objects in presheaves of sets: the
operations of a presheaf of monoids are read sectionwise, and conversely. -/
noncomputable def presheafEquivalence (C : Type u) [Category.{v} C] :
    (C ⥤ MonCat.{w}) ≌ Mon (C ⥤ Type w) where
  functor := presheafMon
  inverse := monPresheaves
  unitIso := NatIso.ofComponents fun A ↦ NatIso.ofComponents fun X ↦
    letI := evaluationMonObj (presheafMon.obj A).X X
    MulEquiv.toMonCatIso
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl }
  counitIso := NatIso.ofComponents fun R ↦ Mon.mkIso (Iso.refl R.X)
    (by ext X x; rfl) (by ext X x; rfl)
  functor_unitIso_comp X := by apply Mon.Hom.ext; rfl

section Pullback
variable [CartesianMonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} [F.Braided] (hF : F.FullyFaithful)

/-- Pull internal monoid operations back along a fully faithful cartesian functor. -/
noncomputable abbrev pullMon (X : C) [MonObj (F.obj X)] : Mon C := by
  letI := hF.monObj X
  exact { X := X }

/-- A morphism preserves pulled-back monoid operations when its image preserves the original
ones. -/
lemma isMonHom_pullMonObj {X Y : C} [MonObj (F.obj X)] [MonObj (F.obj Y)]
    (f : X ⟶ Y) [IsMonHom (F.map f)] :
    letI := hF.monObj X
    letI := hF.monObj Y
    IsMonHom f := by
  have ho := IsMonHom.one_hom (F.map f)
  have hm := IsMonHom.mul_hom (F.map f)
  let : MonObj X := hF.monObj X
  let : MonObj Y := hF.monObj Y
  exact {
    one_hom := hF.map_injective (by simp [Functor.map_comp, ho])
    mul_hom := hF.map_injective (by
      simp [Functor.map_comp, ← Functor.OplaxMonoidal.δ_natural_assoc, hm]) }

private lemma map_pullMon_mul (X : C) [MonObj (F.obj X)] :
    MonObj.mul (X := (F.mapMon.obj (pullMon hF X)).X) = MonObj.mul (X := F.obj X) := by
  let : MonObj X := hF.monObj X
  change Functor.LaxMonoidal.μ F X X ≫ F.map
      (hF.preimage (Functor.OplaxMonoidal.δ F X X ≫ MonObj.mul (X := F.obj X))) =
    MonObj.mul (X := F.obj X)
  rw [hF.map_preimage]
  simp

end Pullback

variable (J : GrothendieckTopology C)

/-- The internal monoid attached to an ordinary sheaf of monoids. -/
noncomputable abbrev internalSheafObj (R : Sheaf J MonCat.{w}) :
    Mon (Sheaf J (Type w)) := by
  letI : MonObj ((sheafToPresheaf J (Type w)).obj
      ((sheafCompose J (forget MonCat.{w})).obj R)) := presheafMonObj R.obj
  exact pullMon (fullyFaithfulSheafToPresheaf J (Type w))
    ((sheafCompose J (forget MonCat.{w})).obj R)

/-- Internalize ordinary sheaves of monoids and their homomorphisms. -/
noncomputable def internalSheaf : Sheaf J MonCat.{w} ⥤ Mon (Sheaf J (Type w)) where
  obj := internalSheafObj J
  map {R S} f := by
    letI : MonObj ((sheafToPresheaf J (Type w)).obj
        ((sheafCompose J (forget MonCat.{w})).obj R)) := presheafMonObj R.obj
    letI : MonObj ((sheafToPresheaf J (Type w)).obj
        ((sheafCompose J (forget MonCat.{w})).obj S)) := presheafMonObj S.obj
    haveI : IsMonHom ((sheafToPresheaf J (Type w)).map
        ((sheafCompose J (forget MonCat.{w})).map f)) :=
      (presheafMon.map f.hom).isMonHom_hom
    haveI := isMonHom_pullMonObj (fullyFaithfulSheafToPresheaf J (Type w))
      ((sheafCompose J (forget MonCat.{w})).map f)
    exact Mon.Hom.mk ((sheafCompose J (forget MonCat.{w})).map f)

/-- A presheaf of monoids is a sheaf if its underlying presheaf of sets is a sheaf.
The existing limit of sets supplies the smallness needed even for a larger site. -/
lemma isSheaf_of_forget (P : Cᵒᵖ ⥤ MonCat.{w})
    (h : Presheaf.IsSheaf J (P ⋙ forget MonCat.{w})) : Presheaf.IsSheaf J P := by
  rw [Presheaf.isSheaf_iff_isLimit] at h ⊢
  intro X S hS
  obtain ⟨t⟩ := h S hS
  let D := S.arrows.diagram.op ⋙ P
  have : HasLimit (D ⋙ forget MonCat.{w}) := ⟨_, t⟩
  have : Small.{w} (D ⋙ forget MonCat.{w}).sections :=
    (Types.hasLimit_iff_small_sections _).mp inferInstance
  have : PreservesLimit D (forget MonCat.{w}) :=
    preservesLimit_of_preserves_limit_cone (MonCat.HasLimits.limitConeIsLimit D)
      (Types.Small.limitConeIsLimit _)
  have : ReflectsLimit D (forget MonCat.{w}) :=
    reflectsLimit_of_reflectsIsomorphisms D (forget MonCat.{w})
  exact ⟨isLimitOfReflects (forget MonCat.{w}) t⟩

/-- Read an internal monoid in sheaves as an ordinary sheaf of monoids. -/
noncomputable def externalSheaf : Mon (Sheaf J (Type w)) ⥤ Sheaf J MonCat.{w} where
  obj R := ⟨monPresheaf ((sheafToPresheaf J (Type w)).mapMon.obj R),
    isSheaf_of_forget J _ (by
      change Presheaf.IsSheaf J R.X.obj
      exact R.X.property)⟩
  map f := ⟨monPresheaves.map ((sheafToPresheaf J (Type w)).mapMon.map f)⟩

/-- Reading the monoid operations of a sheaf of monoids sectionwise and then internalizing them
recovers the sheaf, naturally in it. One half of `equivalence`. -/
noncomputable def internalExternalIso (J : GrothendieckTopology C) :
    internalSheaf J ⋙ externalSheaf J ≅ 𝟭 (Sheaf J MonCat.{w}) := by
  refine NatIso.ofComponents (fun R => ?_) ?_
  · exact ObjectProperty.isoMk _ <| NatIso.ofComponents (fun U =>
      letI := evaluationMonObj
        ((sheafToPresheaf J (Type w)).mapMon.obj ((internalSheaf J).obj R)).X U
      MulEquiv.toMonCatIso {
        toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' x y := by
          let : MonObj ((sheafToPresheaf J (Type w)).obj
              ((sheafCompose J (forget MonCat.{w})).obj R)) := presheafMonObj R.obj
          let P := (sheafToPresheaf J (Type w)).obj
            ((sheafCompose J (forget MonCat.{w})).obj R)
          exact congrArg
            (fun m : P ⊗ P ⟶ P => (ConcreteCategory.hom (m.app U)) (x, y))
            (map_pullMon_mul (fullyFaithfulSheafToPresheaf J (Type w))
              ((sheafCompose J (forget MonCat.{w})).obj R)) }) (by
          intro U V f
          ext x
          rfl)
  · intro X Y g
    apply (sheafToPresheaf J MonCat.{w}).map_injective
    ext U x
    rfl

/-- Internalizing a sectionwise monoid object and then reading its operations back off recovers
the monoid object, naturally in it. The other half of `equivalence`. -/
noncomputable def externalInternalIso (J : GrothendieckTopology C) :
    externalSheaf J ⋙ internalSheaf J ≅ 𝟭 (Mon (Sheaf J (Type w))) := by
  refine NatIso.ofComponents (fun R => Mon.mkIso (Iso.refl _) ?_ ?_) ?_
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
  · intro X Y g
    apply Mon.Hom.ext
    rfl

/-- Sheaves of monoids on a site are the same thing as monoid objects in its category of sheaves
of types. The two directions are `internalSheaf` and `externalSheaf`, and the unit and counit
are `internalExternalIso` and `externalInternalIso`. -/
noncomputable def equivalence (J : GrothendieckTopology C) :
    Sheaf J MonCat.{w} ≌ Mon (Sheaf J (Type w)) where
  functor := internalSheaf J
  inverse := externalSheaf J
  unitIso := (internalExternalIso J).symm
  counitIso := externalInternalIso J
  functor_unitIso_comp X := by
    apply (Mon.forget (Sheaf J (Type w))).map_injective
    ext U x
    rfl

end MonSheaf

end CategoryTheory.Sites

end
