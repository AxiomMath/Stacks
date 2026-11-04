module

public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforward
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
public import Mathlib.Algebra.Category.Grp.Limits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves of groups as internal group objects

A sheaf of groups on a site is the same thing as an internal group object in the category of
sheaves of sets: the group operations of a sheaf of groups are a `GrpObj` structure on its
underlying sheaf of sets, and conversely the operations of an internal group can be read
sectionwise as groups of sections. Transporting the geometric inverse image of a morphism of
topoi through this identification gives the inverse image on sheaves of groups.

This is the non-commutative companion of
`StacksFrontier/CategoryTheory/Sites/Modules/InverseImage/AbelianSheaf.lean`, which does the same
for sheaves of abelian groups and internal commutative group objects. Two of its constructions
are not specific to commutativity and are reused rather than repeated:
`CategoryTheory.Sites.AbelianSheaf.evaluationGrpObj`, which evaluates an internal group object
in a functor category at an object, and
`CategoryTheory.Sites.AbelianSheaf.isMonHom_pullGrpObj`, which pulls the homomorphism property
back along a fully faithful cartesian functor.

## Main definitions

* `CategoryTheory.Sites.GrpSheaf.internalSheaf` turns a sheaf of groups into an internal group
  object in sheaves of sets.
* `CategoryTheory.Sites.GrpSheaf.externalSheaf` is its inverse, reading the operations of an
  internal group sectionwise.
* `CategoryTheory.Sites.GrpSheaf.equivalence` is the resulting equivalence.
* `CategoryTheory.Sites.GrpSheaf.presheafEquivalence` is the same statement for presheaves.
* `CategoryTheory.Sites.grpInverseImage` is the canonical functor between `Sheaf K GrpCat` and
  `Sheaf J GrpCat` attached to a morphism of topoi.
* `CategoryTheory.Sites.grpInverseImage_forgetIso` identifies its underlying sheaf of sets with
  the geometric inverse image.

## Implementation notes

Unlike the abelian case there is no `Additive` wrapper anywhere: `GrpCat` and `GrpObj` are both
multiplicative, so reading an internal group object sectionwise lands on the nose in the
multiplicative group of sections, and the components of `internalExternalIso` and of
`presheafEquivalence` are the identity on sections.

## References

* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

namespace CategoryTheory.Sites

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

universe v u v' u' w w'

variable {C : Type u} [Category.{v} C]

namespace GrpSheaf

open AbelianSheaf (evaluationGrpObj isMonHom_pullGrpObj)

/-- The multiplicative operations of a presheaf of groups, regarded as internal group
operations. -/
@[sga "3 I 2.1.1" "partial"]
noncomputable abbrev presheafGrpObj (R : C ⥤ GrpCat.{w}) :
    GrpObj (R ⋙ forget GrpCat.{w}) where
  one := { app X := ↾fun _ => (1 : R.obj X)
           naturality X Y f := by ext; exact (map_one (R.map f).hom).symm }
  mul := { app X := ↾fun p => (p.1 * p.2 : R.obj X)
           naturality X Y f := by ext; exact (map_mul (R.map f).hom _ _).symm }
  inv := { app X := ↾fun a => (a⁻¹ : R.obj X)
           naturality X Y f := by ext; exact (map_inv (R.map f).hom _).symm }
  one_mul := by ext X x; exact one_mul _
  mul_one := by ext X x; exact mul_one _
  mul_assoc := by ext X x; exact mul_assoc _ _ _
  left_inv := by ext X x; exact inv_mul_cancel _
  right_inv := by ext X x; exact mul_inv_cancel _

/-- Internalize the sectionwise operations and homomorphisms of presheaves of groups. -/
@[sga "3 I 2.1.1" "partial"]
noncomputable def presheafGrp : (C ⥤ GrpCat.{w}) ⥤ Grp (C ⥤ Type w) where
  obj R := by
    letI := presheafGrpObj R
    exact { X := R ⋙ forget GrpCat.{w} }
  map {R S} f := by
    letI := presheafGrpObj R
    letI := presheafGrpObj S
    exact Grp.homMk''
      (Functor.whiskerRight f (forget GrpCat.{w}))
      (by ext X x; exact map_one (f.app X).hom)
      (by ext X x; exact map_mul (f.app X).hom _ _)

/-- Read the internal group operations as groups of sections. -/
noncomputable def grpPresheaf (R : Grp (C ⥤ Type w)) : C ⥤ GrpCat.{w} where
  obj X :=
    letI := evaluationGrpObj R.X X
    GrpCat.of (R.X.obj X)
  map {X Y} f := by
    letI := evaluationGrpObj R.X X
    letI := evaluationGrpObj R.X Y
    exact GrpCat.ofHom {
      toFun := R.X.map f
      map_one' := (ConcreteCategory.congr_hom (CC := fun X : Type w => X)
        ((MonObj.one (X := R.X)).naturality f) PUnit.unit).symm
      map_mul' a b := (ConcreteCategory.congr_hom (CC := fun X : Type w => X)
        ((MonObj.mul (X := R.X)).naturality f) (a,b)).symm }
  map_id X := (forget GrpCat.{w}).map_injective (R.X.map_id X)
  map_comp f g := (forget GrpCat.{w}).map_injective (R.X.map_comp f g)

/-- Read internal homomorphisms sectionwise as homomorphisms of presheaves of groups. -/
noncomputable def grpPresheaves : Grp (C ⥤ Type w) ⥤ (C ⥤ GrpCat.{w}) where
  obj := grpPresheaf
  map {R S} f := {
    app X := by
      letI := evaluationGrpObj R.X X
      letI := evaluationGrpObj S.X X
      exact GrpCat.ofHom {
        toFun := f.hom.hom.app X
        map_one' := ConcreteCategory.congr_hom (CC := fun X : Type w => X)
          (congr_app (IsMonHom.one_hom f.hom.hom) X) PUnit.unit
        map_mul' a b := ConcreteCategory.congr_hom (CC := fun X : Type w => X)
          (congr_app (IsMonHom.mul_hom f.hom.hom) X) (a,b) }
    naturality X Y a := by
      ext x
      exact ConcreteCategory.congr_hom (f.hom.hom.naturality a) x }
  map_id R := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- Presheaves of groups are the same thing as group objects in presheaves of sets: the
operations of a presheaf of groups are read sectionwise, and conversely. -/
noncomputable def presheafEquivalence (C : Type u) [Category.{v} C] :
    (C ⥤ GrpCat.{w}) ≌ Grp (C ⥤ Type w) where
  functor := presheafGrp
  inverse := grpPresheaves
  unitIso := NatIso.ofComponents fun A ↦ NatIso.ofComponents fun X ↦
    MulEquiv.toGrpIso
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl }
  counitIso := NatIso.ofComponents fun R ↦ Grp.mkIso (Iso.refl R.X)
    (by ext X x; rfl) (by ext X x; rfl)
  functor_unitIso_comp X := by apply Grp.hom_ext; rfl

section Pullback
variable [CartesianMonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} [F.Braided] (hF : F.FullyFaithful)

/-- Pull internal group operations back along a fully faithful cartesian functor. -/
noncomputable abbrev pullGrp (X : C) [GrpObj (F.obj X)] : Grp C := by
  letI := hF.grpObj X
  exact { X := X }

private lemma map_pullGrp_mul (X : C) [GrpObj (F.obj X)] :
    MonObj.mul (X := (F.mapGrp.obj (pullGrp hF X)).X) = MonObj.mul (X := F.obj X) := by
  let : GrpObj X := hF.grpObj X
  change Functor.LaxMonoidal.μ F X X ≫ F.map
      (hF.preimage (Functor.OplaxMonoidal.δ F X X ≫ MonObj.mul (X := F.obj X))) =
    MonObj.mul (X := F.obj X)
  rw [hF.map_preimage]
  simp

end Pullback

variable (J : GrothendieckTopology C)

/-- The internal group attached to an ordinary sheaf of groups. -/
noncomputable abbrev internalSheafObj (R : Sheaf J GrpCat.{w}) :
    Grp (Sheaf J (Type w)) := by
  letI : GrpObj ((sheafToPresheaf J (Type w)).obj
      ((sheafCompose J (forget GrpCat.{w})).obj R)) := presheafGrpObj R.obj
  exact pullGrp (fullyFaithfulSheafToPresheaf J (Type w))
    ((sheafCompose J (forget GrpCat.{w})).obj R)

/-- Internalize ordinary sheaves of groups and their homomorphisms. -/
noncomputable def internalSheaf : Sheaf J GrpCat.{w} ⥤ Grp (Sheaf J (Type w)) where
  obj := internalSheafObj J
  map {R S} f := by
    letI : GrpObj ((sheafToPresheaf J (Type w)).obj
        ((sheafCompose J (forget GrpCat.{w})).obj R)) := presheafGrpObj R.obj
    letI : GrpObj ((sheafToPresheaf J (Type w)).obj
        ((sheafCompose J (forget GrpCat.{w})).obj S)) := presheafGrpObj S.obj
    haveI : IsMonHom ((sheafToPresheaf J (Type w)).map
        ((sheafCompose J (forget GrpCat.{w})).map f)) :=
      (presheafGrp.map f.hom).hom.isMonHom_hom
    haveI := isMonHom_pullGrpObj (fullyFaithfulSheafToPresheaf J (Type w))
      ((sheafCompose J (forget GrpCat.{w})).map f)
    exact Grp.homMk ((sheafCompose J (forget GrpCat.{w})).map f)

/-- A presheaf of groups is a sheaf if its underlying presheaf of sets is a sheaf.
The existing limit of sets supplies the smallness needed even for a larger site. -/
@[ega "0 3.1.3" "special case", ega "0 3.1.4" "more general"]
lemma isSheaf_of_forget (P : Cᵒᵖ ⥤ GrpCat.{w})
    (h : Presheaf.IsSheaf J (P ⋙ forget GrpCat.{w})) : Presheaf.IsSheaf J P := by
  rw [Presheaf.isSheaf_iff_isLimit] at h ⊢
  intro X S hS
  obtain ⟨t⟩ := h S hS
  let D := S.arrows.diagram.op ⋙ P
  have : HasLimit (D ⋙ forget GrpCat.{w}) := ⟨_, t⟩
  have : Small.{w} (D ⋙ forget GrpCat.{w}).sections :=
    (Types.hasLimit_iff_small_sections _).mp inferInstance
  have : PreservesLimit D (forget GrpCat.{w}) :=
    preservesLimit_of_preserves_limit_cone (GrpCat.limitConeIsLimit D)
      (Types.Small.limitConeIsLimit _)
  have : ReflectsLimit D (forget GrpCat.{w}) :=
    reflectsLimit_of_reflectsIsomorphisms D (forget GrpCat.{w})
  exact ⟨isLimitOfReflects (forget GrpCat.{w}) t⟩

/-- Read an internal group in sheaves as an ordinary sheaf of groups. -/
noncomputable def externalSheaf : Grp (Sheaf J (Type w)) ⥤ Sheaf J GrpCat.{w} where
  obj R := ⟨grpPresheaf ((sheafToPresheaf J (Type w)).mapGrp.obj R),
    isSheaf_of_forget J _ (by
      change Presheaf.IsSheaf J R.X.obj
      exact R.X.property)⟩
  map f := ⟨grpPresheaves.map ((sheafToPresheaf J (Type w)).mapGrp.map f)⟩

/-- Reading the group operations of a sheaf of groups sectionwise and then internalizing them
recovers the sheaf, naturally in it. One half of `equivalence`. -/
public noncomputable def internalExternalIso (J : GrothendieckTopology C) :
    internalSheaf J ⋙ externalSheaf J ≅ 𝟭 (Sheaf J GrpCat.{w}) := by
  refine NatIso.ofComponents (fun R => ?_) ?_
  · exact ObjectProperty.isoMk _ <| NatIso.ofComponents (fun U =>
      MulEquiv.toGrpIso {
        toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' x y := by
          let := evaluationGrpObj
            ((sheafToPresheaf J (Type w)).mapGrp.obj ((internalSheaf J).obj R)).X U
          let : GrpObj ((sheafToPresheaf J (Type w)).obj
              ((sheafCompose J (forget GrpCat.{w})).obj R)) := presheafGrpObj R.obj
          let P := (sheafToPresheaf J (Type w)).obj
            ((sheafCompose J (forget GrpCat.{w})).obj R)
          exact congrArg
            (fun m : P ⊗ P ⟶ P => (ConcreteCategory.hom (m.app U)) (x, y))
            (map_pullGrp_mul (fullyFaithfulSheafToPresheaf J (Type w))
              ((sheafCompose J (forget GrpCat.{w})).obj R)) }) (by
          intro U V f
          ext x
          rfl)
  · intro X Y g
    apply (sheafToPresheaf J GrpCat.{w}).map_injective
    ext U x
    rfl

/-- Internalizing a sectionwise group object and then reading its operations back off recovers
the group object, naturally in it. The other half of `equivalence`. -/
public noncomputable def externalInternalIso (J : GrothendieckTopology C) :
    externalSheaf J ⋙ internalSheaf J ≅ 𝟭 (Grp (Sheaf J (Type w))) := by
  refine NatIso.ofComponents (fun R => Grp.mkIso (Iso.refl _) ?_ ?_) ?_
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
    apply Grp.hom_ext
    rfl

/-- Sheaves of groups on a site are the same thing as group objects in its category of sheaves
of types. The two directions are `internalSheaf` and `externalSheaf`, and the unit and counit
are `internalExternalIso` and `externalInternalIso`. -/
@[sga "3 IV 4.3.18", sga "4 II 6.3.1" "partial"]
public noncomputable def equivalence (J : GrothendieckTopology C) :
    Sheaf J GrpCat.{w} ≌ Grp (Sheaf J (Type w)) where
  functor := internalSheaf J
  inverse := externalSheaf J
  unitIso := (internalExternalIso J).symm
  counitIso := externalInternalIso J
  functor_unitIso_comp X := by
    apply (Grp.forget (Sheaf J (Type w))).map_injective
    ext U x
    rfl

end GrpSheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- The inverse image functor of a morphism of topoi is braided monoidal for the cartesian
monoidal structures, since it preserves finite products. -/
noncomputable local instance inverseImageBraidedGrp : f.inverseImage.Braided :=
  .ofChosenFiniteProducts _

/-- The canonical inverse image of ordinary sheaves of groups: apply geometric inverse image to
their group operations and read the resulting operations as groups of sections. -/
noncomputable def grpInverseImage :
    Sheaf K GrpCat.{w'} ⥤ Sheaf J GrpCat.{w} :=
  GrpSheaf.internalSheaf K ⋙ f.inverseImage.mapGrp ⋙ GrpSheaf.externalSheaf J

/-- Forgetting the group operations recovers the geometric inverse image, naturally in the
sheaf. In this construction the underlying sheaves and their maps agree definitionally. -/
noncomputable def grpInverseImage_forgetIso :
    grpInverseImage f ⋙ sheafCompose J (forget GrpCat.{w}) ≅
      sheafCompose K (forget GrpCat.{w'}) ⋙ f.inverseImage := Iso.refl _

end CategoryTheory.Sites

end
