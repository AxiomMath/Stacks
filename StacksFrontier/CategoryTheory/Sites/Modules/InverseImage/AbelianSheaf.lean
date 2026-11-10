module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.Grp.AB
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi

/-!
# Exactness of inverse image on abelian sheaves

A sheaf of abelian groups on a site is the same thing as an internal commutative group object
in the category of sheaves of sets: the group operations of an abelian sheaf are a
`GrpObj` structure on its underlying sheaf of sets, and conversely the operations of an
internal commutative group can be read sectionwise as abelian groups of sections. Transporting
the geometric inverse image of a morphism of topoi through this identification gives the
inverse image on abelian sheaves, and exactness then follows from exactness of the geometric
inverse image.

## Main definitions

* `CategoryTheory.Sites.AbelianSheaf.internalSheaf` turns an abelian sheaf into an internal
  commutative group object in sheaves of sets.
* `CategoryTheory.Sites.AbelianSheaf.externalSheaf` is its inverse, reading the operations of
  an internal commutative group sectionwise.
* `CategoryTheory.Sites.abelianInverseImage` is the canonical functor between
  `Sheaf K AddCommGrpCat` and `Sheaf J AddCommGrpCat` attached to a morphism of topoi.
* `CategoryTheory.Sites.abelianInverseImage_forgetIso` identifies its underlying sheaf of sets
  with the geometric inverse image.

## Main results

* `CategoryTheory.Sites.abelianInverseImage_exact` gives exactness, with
  `PreservesFiniteLimits` and `PreservesFiniteColimits` instances for downstream use.

## Implementation notes

The construction internalizes the group operations, applies the geometric inverse image,
and reads the operations sectionwise. Its underlying sheaf comparison is definitional.
The two sites and their two sheaf-value universes are independent; no sheafification or
internal/external comparison is required of callers. The ring structure plays no role.

The functor and the adjunction induced on internal commutative groups by a morphism of topoi
are Mathlib's `CategoryTheory.Functor.mapCommGrp` and
`CategoryTheory.Adjunction.mapCommGrp` applied to the inverse image, its right adjoint and
their adjunction; the braidings come from `Functor.Braided.ofChosenFiniteProducts`, which is
supplied for those two functors only, as Mathlib recommends, rather than globally.

## References

* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

namespace CategoryTheory.Sites

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

universe v u v' u' w w'

variable {C : Type u} [Category.{v} C]

namespace AbelianSheaf

/-- The additive operations of an abelian presheaf, regarded as internal group operations. -/
@[sga "3 I 2.1.1" "partial, special case"]
noncomputable abbrev presheafGrpObj (R : C ⥤ AddCommGrpCat.{w}) :
    GrpObj (R ⋙ forget AddCommGrpCat.{w}) where
  one := { app X := ↾fun _ => (0 : R.obj X)
           naturality X Y f := by ext; exact (map_zero (R.map f).hom).symm }
  mul := { app X := ↾fun p => (p.1 + p.2 : R.obj X)
           naturality X Y f := by ext; exact (map_add (R.map f).hom _ _).symm }
  inv := { app X := ↾fun a => (-a : R.obj X)
           naturality X Y f := by ext; exact (map_neg (R.map f).hom _).symm }
  one_mul := by ext X x; exact zero_add _
  mul_one := by ext X x; exact add_zero _
  mul_assoc := by ext X x; exact add_assoc _ _ _
  left_inv := by ext X x; exact neg_add_cancel _
  right_inv := by ext X x; exact add_neg_cancel _

/-- Internalize the sectionwise operations and homomorphisms of abelian presheaves. -/
noncomputable def presheafCommGrp : (C ⥤ AddCommGrpCat.{w}) ⥤ CommGrp (C ⥤ Type w) where
  obj R := by
    letI := presheafGrpObj R
    exact { X := R ⋙ forget AddCommGrpCat
            comm := { mul_comm := by ext X x; exact add_comm _ _ } }
  map {R S} f := by
    letI := presheafGrpObj R
    letI := presheafGrpObj S
    exact InducedCategory.homMk (Grp.homMk''
      (Functor.whiskerRight f (forget AddCommGrpCat.{w}))
      (by ext X x; exact map_zero (f.app X).hom)
      (by ext X x; exact map_add (f.app X).hom _ _))

/-- Evaluate an internal group in a functor category at an object. -/
noncomputable abbrev evaluationGrpObj (R : C ⥤ Type w) [GrpObj R] (X : C) :
    GrpObj (R.obj X) where
  one := (MonObj.one (X := R)).app X
  mul := (MonObj.mul (X := R)).app X
  inv := (GrpObj.inv (X := R)).app X
  one_mul := congr_app (MonObj.one_mul R) X
  mul_one := congr_app (MonObj.mul_one R) X
  mul_assoc := congr_app (MonObj.mul_assoc R) X
  left_inv := congr_app (GrpObj.left_inv R) X
  right_inv := congr_app (GrpObj.right_inv R) X

/-- Read the internal commutative group operations as abelian groups of sections. -/
noncomputable def abelianPresheaf (R : CommGrp (C ⥤ Type w)) : C ⥤ AddCommGrpCat.{w} where
  obj X :=
    letI := evaluationGrpObj R.X X
    letI : IsCommMonObj (R.X.obj X) := ⟨congr_app (IsCommMonObj.mul_comm R.X) X⟩
    AddCommGrpCat.of (Additive (R.X.obj X))
  map {X Y} f := by
    letI := evaluationGrpObj R.X X
    letI := evaluationGrpObj R.X Y
    letI : IsCommMonObj (R.X.obj X) := ⟨congr_app (IsCommMonObj.mul_comm R.X) X⟩
    letI : IsCommMonObj (R.X.obj Y) := ⟨congr_app (IsCommMonObj.mul_comm R.X) Y⟩
    exact AddCommGrpCat.ofHom {
      toFun := R.X.map f
      map_zero' := (ConcreteCategory.congr_hom (CC := fun X : Type w => X)
        ((MonObj.one (X := R.X)).naturality f) PUnit.unit).symm
      map_add' a b := (ConcreteCategory.congr_hom (CC := fun X : Type w => X)
        ((MonObj.mul (X := R.X)).naturality f) (a,b)).symm }
  map_id X := by
    apply (forget AddCommGrpCat.{w}).map_injective
    exact R.X.map_id X
  map_comp f g := by
    apply (forget AddCommGrpCat.{w}).map_injective
    exact R.X.map_comp f g

/-- Read internal homomorphisms sectionwise as homomorphisms of abelian presheaves. -/
noncomputable def abelianPresheaves : CommGrp (C ⥤ Type w) ⥤ (C ⥤ AddCommGrpCat.{w}) where
  obj := abelianPresheaf
  map {R S} f := {
    app X := by
      letI := evaluationGrpObj R.X X
      letI := evaluationGrpObj S.X X
      letI : IsCommMonObj (R.X.obj X) := ⟨congr_app (IsCommMonObj.mul_comm R.X) X⟩
      letI : IsCommMonObj (S.X.obj X) := ⟨congr_app (IsCommMonObj.mul_comm S.X) X⟩
      exact AddCommGrpCat.ofHom {
        toFun := f.hom.hom.hom.app X
        map_zero' := ConcreteCategory.congr_hom (CC := fun X : Type w => X)
          (congr_app (IsMonHom.one_hom f.hom.hom.hom) X) PUnit.unit
        map_add' a b := ConcreteCategory.congr_hom (CC := fun X : Type w => X)
          (congr_app (IsMonHom.mul_hom f.hom.hom.hom) X) (a,b) }
    naturality X Y a := by
      ext x
      exact ConcreteCategory.congr_hom (f.hom.hom.hom.naturality a) x }
  map_id R := by ext X x; rfl
  map_comp f g := by ext X x; rfl

section Pullback
variable [CartesianMonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  {F : C ⥤ D} [F.Braided] (hF : F.FullyFaithful)

/-- Pull internal commutative group operations back along a fully faithful cartesian functor. -/
noncomputable abbrev pullCommGrp (X : C) [GrpObj (F.obj X)] [IsCommMonObj (F.obj X)] :
    CommGrp C := by
  letI := hF.grpObj X
  exact { X := X
          comm := { mul_comm := hF.map_injective (by
            simp [Functor.map_comp, IsCommMonObj.mul_comm] ) } }

/-- A morphism preserves pulled-back operations when its image preserves the original ones. -/
lemma isMonHom_pullGrpObj {X Y : C} [GrpObj (F.obj X)] [GrpObj (F.obj Y)]
    (f : X ⟶ Y) [IsMonHom (F.map f)] :
    letI := hF.grpObj X
    letI := hF.grpObj Y
    IsMonHom f := by
  have ho := IsMonHom.one_hom (F.map f)
  have hm := IsMonHom.mul_hom (F.map f)
  let : GrpObj X := hF.grpObj X
  let : GrpObj Y := hF.grpObj Y
  exact {
    one_hom := hF.map_injective (by simp [Functor.map_comp, ho])
    mul_hom := hF.map_injective (by
      simp [Functor.map_comp, ← Functor.OplaxMonoidal.δ_natural_assoc, hm]) }

private lemma map_pullCommGrp_mul (X : C) [GrpObj (F.obj X)]
    [IsCommMonObj (F.obj X)] :
    MonObj.mul (X := (F.mapCommGrp.obj (pullCommGrp hF X)).X) =
      MonObj.mul (X := F.obj X) := by
  let : GrpObj X := hF.grpObj X
  change Functor.LaxMonoidal.μ F X X ≫ F.map
      (hF.preimage (Functor.OplaxMonoidal.δ F X X ≫ MonObj.mul (X := F.obj X))) =
    MonObj.mul (X := F.obj X)
  rw [hF.map_preimage]
  simp

end Pullback

variable (J : GrothendieckTopology C)

/-- The cartesian monoidal structure on sheaves of types given by finite products. -/
noncomputable local instance : CartesianMonoidalCategory (Sheaf J (Type w)) :=
  .ofHasFiniteProducts
/-- The braiding on sheaves of types induced by the cartesian monoidal structure. -/
noncomputable local instance : BraidedCategory (Sheaf J (Type w)) :=
  .ofCartesianMonoidalCategory
/-- The inclusion of sheaves of types into presheaves of types is braided monoidal. -/
noncomputable local instance : (sheafToPresheaf J (Type w)).Braided :=
  .ofChosenFiniteProducts _

/-- The internal commutative group attached to an ordinary abelian sheaf. -/
noncomputable abbrev internalSheafObj (R : Sheaf J AddCommGrpCat.{w}) :
    CommGrp (Sheaf J (Type w)) := by
  letI : GrpObj ((sheafToPresheaf J (Type w)).obj
      ((sheafCompose J (forget AddCommGrpCat.{w})).obj R)) := presheafGrpObj R.obj
  letI : IsCommMonObj ((sheafToPresheaf J (Type w)).obj
      ((sheafCompose J (forget AddCommGrpCat.{w})).obj R)) :=
    (presheafCommGrp.obj R.obj).comm
  exact pullCommGrp (fullyFaithfulSheafToPresheaf J (Type w))
    ((sheafCompose J (forget AddCommGrpCat.{w})).obj R)

/-- Internalize ordinary abelian sheaves and their homomorphisms. -/
noncomputable def internalSheaf : Sheaf J AddCommGrpCat.{w} ⥤
    CommGrp (Sheaf J (Type w)) where
  obj := internalSheafObj J
  map {R S} f := by
    letI : GrpObj ((sheafToPresheaf J (Type w)).obj
        ((sheafCompose J (forget AddCommGrpCat.{w})).obj R)) := presheafGrpObj R.obj
    letI : GrpObj ((sheafToPresheaf J (Type w)).obj
        ((sheafCompose J (forget AddCommGrpCat.{w})).obj S)) := presheafGrpObj S.obj
    haveI : IsMonHom ((sheafToPresheaf J (Type w)).map
        ((sheafCompose J (forget AddCommGrpCat.{w})).map f)) :=
      (presheafCommGrp.map f.hom).hom.hom.isMonHom_hom
    haveI := isMonHom_pullGrpObj (fullyFaithfulSheafToPresheaf J (Type w))
      ((sheafCompose J (forget AddCommGrpCat.{w})).map f)
    exact InducedCategory.homMk (Grp.homMk
      ((sheafCompose J (forget AddCommGrpCat.{w})).map f))

/-- An abelian presheaf is a sheaf if its underlying presheaf of sets is a sheaf.
The existing limit of sets supplies the smallness needed even for a larger site. -/
lemma isSheaf_of_forget (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (h : Presheaf.IsSheaf J (P ⋙ forget AddCommGrpCat.{w})) : Presheaf.IsSheaf J P := by
  rw [Presheaf.isSheaf_iff_isLimit] at h ⊢
  intro X S hS
  obtain ⟨t⟩ := h S hS
  let D := S.arrows.diagram.op ⋙ P
  have : HasLimit (D ⋙ forget AddCommGrpCat.{w}) := ⟨_, t⟩
  have : Small.{w} (D ⋙ forget AddCommGrpCat.{w}).sections :=
    (Types.hasLimit_iff_small_sections _).mp inferInstance
  have : PreservesLimit D (forget AddCommGrpCat.{w}) :=
    preservesLimit_of_preserves_limit_cone (AddCommGrpCat.limitConeIsLimit D)
      (Types.Small.limitConeIsLimit _)
  have : ReflectsLimit D (forget AddCommGrpCat.{w}) :=
    reflectsLimit_of_reflectsIsomorphisms D (forget AddCommGrpCat.{w})
  exact ⟨isLimitOfReflects (forget AddCommGrpCat.{w}) t⟩

/-- Read an internal commutative group in sheaves as an ordinary abelian sheaf. -/
noncomputable def externalSheaf : CommGrp (Sheaf J (Type w)) ⥤
    Sheaf J AddCommGrpCat.{w} where
  obj R := ⟨abelianPresheaf ((sheafToPresheaf J (Type w)).mapCommGrp.obj R),
    isSheaf_of_forget J _ (by
      change Presheaf.IsSheaf J R.X.obj
      exact R.X.property)⟩
  map f := ⟨abelianPresheaves.map ((sheafToPresheaf J (Type w)).mapCommGrp.map f)⟩

/-- Reading the group operations of an abelian sheaf sectionwise and then internalizing them
recovers the sheaf, naturally in it. One half of `equivalence`. -/
public noncomputable def internalExternalIso
    (J : GrothendieckTopology C) :
    internalSheaf J ⋙ externalSheaf J ≅ 𝟭 (Sheaf J AddCommGrpCat.{w}) := by
  refine NatIso.ofComponents (fun R => ?_) ?_
  · exact ObjectProperty.isoMk _ <| NatIso.ofComponents (fun U =>
      AddEquiv.toAddCommGrpIso {
        toFun := Additive.toMul
        invFun := Additive.ofMul
        left_inv _ := rfl
        right_inv _ := rfl
        map_add' x y := by
          let := evaluationGrpObj
            ((sheafToPresheaf J (Type w)).mapCommGrp.obj
              ((internalSheaf J).obj R)).X U
          let : IsCommMonObj
              (((sheafToPresheaf J (Type w)).mapCommGrp.obj
                ((internalSheaf J).obj R)).X.obj U) :=
            ⟨congr_app (IsCommMonObj.mul_comm
              ((sheafToPresheaf J (Type w)).mapCommGrp.obj
                ((internalSheaf J).obj R)).X) U⟩
          let : CommGroup
              (((sheafToPresheaf J (Type w)).mapCommGrp.obj
                ((internalSheaf J).obj R)).X.obj U) :=
            CommGrpTypeEquivalenceCommGrp.commGrpCommGroup _
          change Additive (((sheafToPresheaf J (Type w)).mapCommGrp.obj
            ((internalSheaf J).obj R)).X.obj U) at x y
          change Additive.toMul (x + y) =
            @Add.add (R.obj.obj U) (inferInstance : Add (R.obj.obj U))
              (Additive.toMul x) (Additive.toMul y)
          rw [toMul_add]
          let : GrpObj ((sheafToPresheaf J (Type w)).obj
              ((sheafCompose J (forget AddCommGrpCat.{w})).obj R)) :=
            AbelianSheaf.presheafGrpObj R.obj
          let : IsCommMonObj ((sheafToPresheaf J (Type w)).obj
              ((sheafCompose J (forget AddCommGrpCat.{w})).obj R)) :=
            (AbelianSheaf.presheafCommGrp.obj R.obj).comm
          exact congrArg
            (fun m => (ConcreteCategory.hom (m.app U))
              (Additive.toMul x, Additive.toMul y))
            (map_pullCommGrp_mul (fullyFaithfulSheafToPresheaf J (Type w))
              ((sheafCompose J (forget AddCommGrpCat.{w})).obj R)) }) (by
          intro U V f
          ext x
          rfl)
  · intro X Y g
    apply (sheafToPresheaf J AddCommGrpCat.{w}).map_injective
    ext U x
    rfl

/-- Internalizing a sectionwise group object and then reading its operations back off recovers
the group object, naturally in it. The other half of `equivalence`. -/
public noncomputable def externalInternalIso
    (J : GrothendieckTopology C) :
    externalSheaf J ⋙ internalSheaf J ≅ 𝟭 (CommGrp (Sheaf J (Type w))) := by
  refine NatIso.ofComponents (fun R => CommGrp.mkIso (Iso.refl _) ?_ ?_) ?_
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
    apply CommGrp.hom_ext
    rfl

/-- Abelian sheaves on a site are the same thing as commutative group objects in its category of
sheaves of types. The two directions are `internalSheaf` and `externalSheaf`, and the unit and
counit are `internalExternalIso` and `externalInternalIso`. -/
@[sga "3 IV 4.3.18"]
public noncomputable def equivalence
    (J : GrothendieckTopology C) :
    Sheaf J AddCommGrpCat.{w} ≌ CommGrp (Sheaf J (Type w)) where
  functor := internalSheaf J
  inverse := externalSheaf J
  unitIso := (internalExternalIso J).symm
  counitIso := externalInternalIso J
  functor_unitIso_comp X := by
    apply (CommGrp.forget (Sheaf J (Type w))).map_injective
    ext U x
    rfl

end AbelianSheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- The cartesian monoidal structure on sheaves of types given by finite products. -/
noncomputable local instance : CartesianMonoidalCategory (Sheaf J (Type w)) :=
  .ofHasFiniteProducts
/-- The braiding on sheaves of types induced by the cartesian monoidal structure. -/
noncomputable local instance : BraidedCategory (Sheaf J (Type w)) :=
  .ofCartesianMonoidalCategory

/-- The inverse image functor of a morphism of topoi preserves finite limits. -/
noncomputable local instance : PreservesFiniteLimits f.inverseImage :=
  f.preservesFiniteLimits
/-- The inverse image functor of a morphism of topoi is braided monoidal for the cartesian monoidal
structures. -/
noncomputable local instance : f.inverseImage.Braided := .ofChosenFiniteProducts _

/-- The canonical inverse image of ordinary abelian sheaves: apply geometric inverse image
to their group operations and read the resulting operations as abelian groups of sections. -/
noncomputable def abelianInverseImage :
    Sheaf K AddCommGrpCat.{w'} ⥤ Sheaf J AddCommGrpCat.{w} :=
  AbelianSheaf.internalSheaf K ⋙ f.inverseImage.mapCommGrp ⋙
    AbelianSheaf.externalSheaf J

/-- Forgetting the abelian-group operations recovers the geometric inverse image, naturally
in the sheaf. In this construction the underlying sheaves and their maps agree definitionally. -/
noncomputable def abelianInverseImage_forgetIso :
    abelianInverseImage f ⋙ sheafCompose J (forget AddCommGrpCat.{w}) ≅
      sheafCompose K (forget AddCommGrpCat.{w'}) ⋙ f.inverseImage := Iso.refl _

/-- Forgetting to sheaves of types preserves finite limits of abelian sheaves. -/
private theorem preservesFiniteLimits_sheafCompose_forget {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    PreservesFiniteLimits (sheafCompose J (forget AddCommGrpCat.{w})) := by
  have : PreservesFiniteLimits
      ((sheafCompose J (forget AddCommGrpCat.{w})) ⋙ sheafToPresheaf J (Type w)) := by
    change PreservesFiniteLimits
      (sheafToPresheaf J AddCommGrpCat.{w} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{w}))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves
    (sheafCompose J (forget AddCommGrpCat.{w})) (sheafToPresheaf J (Type w))

private theorem abelianInverseImage_preservesFiniteLimitsProof
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w'))) :
    PreservesFiniteLimits (abelianInverseImage f) := by
  let G := sheafCompose J (forget AddCommGrpCat.{w})
  let : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  have : PreservesFiniteLimits (sheafCompose K (forget AddCommGrpCat.{w'})) :=
    preservesFiniteLimits_sheafCompose_forget K
  have : PreservesFiniteLimits (sheafCompose J (forget AddCommGrpCat.{w})) :=
    preservesFiniteLimits_sheafCompose_forget J
  have : PreservesFiniteLimits (abelianInverseImage f ⋙ G) := by
    have : PreservesFiniteLimits
        (sheafCompose K (forget AddCommGrpCat.{w'}) ⋙ f.inverseImage) := inferInstance
    exact preservesFiniteLimits_of_natIso (abelianInverseImage_forgetIso f).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (abelianInverseImage f) G

@[sga "4 IV 13.6" "special case"]
private theorem abelianInverseImage_preservesFiniteColimitsProof
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w'))) :
    PreservesFiniteColimits (abelianInverseImage f) := by
  let eK := AbelianSheaf.equivalence K
  let eJ := AbelianSheaf.equivalence J
  let : PreservesLimitsOfSize.{0, 0} f.pushforward := f.adj.rightAdjoint_preservesLimits
  let : PreservesFiniteLimits f.pushforward := inferInstance
  let : f.pushforward.Braided := .ofChosenFiniteProducts _
  let adj := eK.toAdjunction.comp
    ((f.adj.mapCommGrp).comp eJ.symm.toAdjunction)
  let : PreservesColimitsOfSize.{0, 0} (abelianInverseImage f) :=
    adj.leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- The inverse image of a morphism of topoi is exact on ordinary abelian sheaves. -/
@[stacks 04JC "inverse_image_exact"]
theorem abelianInverseImage_exact :
    exactFunctor (Sheaf K AddCommGrpCat.{w'}) (Sheaf J AddCommGrpCat.{w})
      (abelianInverseImage f) := by
  rw [exactFunctor_iff]
  exact ⟨abelianInverseImage_preservesFiniteLimitsProof f,
    abelianInverseImage_preservesFiniteColimitsProof f⟩

/-- Canonical inverse image of abelian sheaves preserves finite limits. -/
instance abelianInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (abelianInverseImage f) :=
  (abelianInverseImage_exact f).1

/-- Canonical inverse image of abelian sheaves preserves finite colimits. -/
instance abelianInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (abelianInverseImage f) :=
  (abelianInverseImage_exact f).2

end CategoryTheory.Sites
