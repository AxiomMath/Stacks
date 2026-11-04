module

public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf

/-!
# Abelian sheaves as internal group objects, through restriction and sheafification

An abelian sheaf on a site is the same thing as a commutative group object in its category of
sheaves of sets, and an abelian presheaf is the same thing as a commutative group object in
presheaves of sets.  This file records that the two identifications are compatible with the three
operations out of which the pullback of sheaves along a cocontinuous functor is built: passing to
the underlying presheaf, restricting a presheaf along a functor, and sheafifying.

The consequence is the comparison `cocontinuousAbelianInverseImageIso`: the pullback
`G ↦ (u^p G)^#` of abelian sheaves is obtained from the pullback of sheaves of sets by
transporting the group operations.  Unlike the corresponding statement for a continuous functor
it is not elementary, since sheafification is involved; the three steps are compatible for
different reasons, and only the sheafification step needs an adjunction argument.

## Main definitions

* `Stacks.Sites.AbelianPullback.presheafEquivalence`: abelian presheaves are commutative group
  objects in presheaves of sets.
* `Stacks.Sites.AbelianPullback.mapCommGrpBraidedIso`: the induced functor on commutative group
  objects does not depend on the chosen braiding.

## Main results

* `Stacks.Sites.AbelianPullback.sheafToPresheafInternalIso`: the underlying presheaf of an
  abelian sheaf, internalized, is the internalization of the sheaf restricted to presheaves.
* `Stacks.Sites.AbelianPullback.precompInternalIso`: restriction of presheaves along a functor
  commutes with internalizing the group operations.
* `Stacks.Sites.AbelianPullback.sheafificationInternalIso`: the sheafification of an abelian
  presheaf is the sheafification of the underlying presheaf of sets with its induced group
  operations.
* `Stacks.Sites.AbelianPullback.cocontinuousAbelianInverseImageIso`: the resulting comparison
  for `G ↦ (u^p G)^#`.

## Implementation notes

The two elementary steps, `sheafToPresheafInternalIso` and `precompInternalIso`, have components
which are the identity on sections; what has to be checked is that they are additive, and for
`precompInternalIso` this is the statement that the monoidal structure of a restriction functor is
computed sectionwise, which is `CategoryTheory.Functor.Monoidal.μ_fst` and `.μ_snd`.

`sheafificationInternalIso` is proved by uniqueness of left adjoints: both sides are left adjoint
to the inclusion of abelian sheaves into abelian presheaves, the second by the sheafification
adjunction and the first because it is a composite of three left adjoints, whose right adjoint is
identified with that inclusion by `sheafToPresheafInternalIso` and `presheafEquivalence`.

The braiding on a composite of functors obtained from instance search and the one obtained from
`CategoryTheory.Functor.Braided.ofChosenFiniteProducts` are different terms, so the statement of
`cocontinuousAbelianInverseImageIso` fixes one of them and its proof passes to the other through
`mapCommGrpBraidedIso`.

## References

* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sites CategoryTheory.Sites.AbelianSheaf Opposite

universe u v w u' v'

namespace Stacks.Sites.AbelianPullback

/-- The cartesian monoidal structure on sheaves of sets given by finite products. -/
noncomputable local instance cartesianSheafTypes {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) : CartesianMonoidalCategory (Sheaf J (Type w)) :=
  .ofHasFiniteProducts

/-- The braiding on sheaves of sets induced by their cartesian monoidal structure. -/
noncomputable local instance braidedSheafTypes {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) : BraidedCategory (Sheaf J (Type w)) :=
  .ofCartesianMonoidalCategory

/-- The cartesian monoidal structure on presheaves of sets, computed sectionwise. -/
noncomputable local instance cartesianPresheafTypes {C : Type u} [Category.{v} C] :
    CartesianMonoidalCategory (C ⥤ Type w) := Functor.cartesianMonoidalCategory

/-- The braiding on presheaves of sets induced by their cartesian monoidal structure. -/
noncomputable local instance braidedPresheafTypes {C : Type u} [Category.{v} C] :
    BraidedCategory (C ⥤ Type w) := .ofCartesianMonoidalCategory

/-- The braided structure on the inclusion of sheaves of sets into presheaves of sets, given by
its preservation of finite products. -/
noncomputable local instance braidedSheafToPresheafTypes {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) : (sheafToPresheaf J (Type w)).Braided :=
  .ofChosenFiniteProducts _

/-- Changing the braiding of a functor does not change the induced functor on commutative group
objects. -/
noncomputable def mapCommGrpBraidedIso {A : Type*} [Category* A]
    [CartesianMonoidalCategory A] [BraidedCategory A] {B : Type*} [Category* B]
    [CartesianMonoidalCategory B] [BraidedCategory B] (G : A ⥤ B) (b₁ b₂ : G.Braided) :
    (letI := b₁; G.mapCommGrp) ≅ (letI := b₂; G.mapCommGrp) :=
  @Functor.mapCommGrpNatIso _ _ _ _ _ _ _ _ G G b₁ b₂ (Iso.refl _)

/-- Abelian presheaves are the same thing as commutative group objects in presheaves of sets:
the operations of an abelian presheaf are read sectionwise, and conversely. -/
noncomputable def presheafEquivalence (C : Type u) [Category.{v} C] :
    (C ⥤ AddCommGrpCat.{w}) ≌ CommGrp (C ⥤ Type w) where
  functor := presheafCommGrp
  inverse := abelianPresheaves
  unitIso := NatIso.ofComponents fun A ↦ NatIso.ofComponents fun X ↦
    AddEquiv.toAddCommGrpIso
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl }
  counitIso := NatIso.ofComponents fun R ↦ CommGrp.mkIso (Iso.refl R.X)
    (by ext X x; rfl) (by ext X x; rfl)
  functor_unitIso_comp X := by apply CommGrp.hom_ext; rfl

/-- Internalizing the group operations of the underlying presheaf of an abelian sheaf is the same
as internalizing them on the sheaf and then passing to the underlying presheaf of sets. -/
noncomputable def sheafToPresheafInternalIso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    sheafToPresheaf J AddCommGrpCat.{w} ⋙ presheafCommGrp ≅
      internalSheaf J ⋙ (sheafToPresheaf J (Type w)).mapCommGrp :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (internalExternalIso J).symm
      (sheafToPresheaf J AddCommGrpCat.{w} ⋙ presheafCommGrp) ≪≫
    Functor.isoWhiskerLeft (internalSheaf J ⋙ (sheafToPresheaf J (Type w)).mapCommGrp)
      (presheafEquivalence _).counitIso ≪≫
    Functor.rightUnitor _

section Sheafification

variable {C : Type u} [Category.{u} C]

/-- The sheafification of an abelian presheaf is the sheafification of its underlying presheaf of
sets, carrying the induced group operations.  Both are left adjoint to the inclusion of abelian
sheaves into abelian presheaves. -/
noncomputable def sheafificationInternalIso (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] [HasWeakSheafify J AddCommGrpCat.{u}] :
    letI : (presheafToSheaf J (Type u)).Braided := .ofChosenFiniteProducts _
    presheafCommGrp ⋙ (presheafToSheaf J (Type u)).mapCommGrp ⋙ externalSheaf J ≅
      presheafToSheaf J AddCommGrpCat.{u} := by
  let L := presheafToSheaf J (Type u)
  let R := sheafToPresheaf J (Type u)
  let : L.Braided := .ofChosenFiniteProducts _
  let E : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ≌ CommGrp (Cᵒᵖ ⥤ Type u) := presheafEquivalence _
  let E' : Sheaf J AddCommGrpCat.{u} ≌ CommGrp (Sheaf J (Type u)) := AbelianSheaf.equivalence J
  let a := (E.toAdjunction.comp (sheafificationAdjunction J (Type u)).mapCommGrp).comp
    E'.symm.toAdjunction
  let e : sheafToPresheaf J AddCommGrpCat.{u} ≅
      internalSheaf J ⋙ R.mapCommGrp ⋙ abelianPresheaves :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ E.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (sheafToPresheafInternalIso J) _ ≪≫
      Functor.associator _ _ _
  exact (Functor.associator _ _ _).symm ≪≫
    (a.ofNatIsoRight e.symm).leftAdjointUniq (sheafificationAdjunction J AddCommGrpCat.{u})

end Sheafification

section Precomposition

section AnyUniverses

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Restriction of presheaves along a functor commutes with internalizing the group operations:
the comparison is the identity on sections, and it is additive because the monoidal structure of a
restriction functor is computed sectionwise. The two categories and the coefficient universe are
independent. -/
noncomputable def precompInternalIsoOfUniverses (F : C ⥤ D) :
    letI : ((Functor.whiskeringLeft C D (Type w)).obj F).Braided := .ofChosenFiniteProducts _
    (Functor.whiskeringLeft C D AddCommGrpCat.{w}).obj F ⋙ presheafCommGrp ≅
      presheafCommGrp ⋙ ((Functor.whiskeringLeft C D (Type w)).obj F).mapCommGrp := by
  let R := (Functor.whiskeringLeft C D (Type w)).obj F
  let : R.Braided := .ofChosenFiniteProducts _
  let : R.Monoidal := (inferInstance : R.Braided).toMonoidal
  let : R.LaxMonoidal := (inferInstance : R.Braided).toLaxBraided.toLaxMonoidal
  refine NatIso.ofComponents (fun A => CommGrp.mkIso (Iso.refl _) ?_ ?_) ?_
  · ext U x
    rfl
  · let A' := presheafCommGrp.obj A
    have hf := Functor.Monoidal.μ_fst R A'.X A'.X
    have hs := Functor.Monoidal.μ_snd R A'.X A'.X
    ext U x
    let add := @Add.add (A.obj (F.obj U)) inferInstance
    change add
      ((CartesianMonoidalCategory.fst (R.obj A'.X) (R.obj A'.X)).app U x)
      ((CartesianMonoidalCategory.snd (R.obj A'.X) (R.obj A'.X)).app U x) =
      add
        ((Functor.LaxMonoidal.μ R A'.X A'.X ≫ R.map
          (CartesianMonoidalCategory.fst A'.X A'.X)).app U x)
        ((Functor.LaxMonoidal.μ R A'.X A'.X ≫ R.map
          (CartesianMonoidalCategory.snd A'.X A'.X)).app U x)
    exact congrArg₂ add (ConcreteCategory.congr_hom (congr_app hf U) x).symm
      (ConcreteCategory.congr_hom (congr_app hs U) x).symm
  · intro A B f
    apply CommGrp.hom_ext
    rfl

end AnyUniverses

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]

/-- Restriction of presheaves along a functor commutes with internalizing the group operations:
the comparison is the identity on sections, and it is additive because the monoidal structure of a
restriction functor is computed sectionwise. -/
noncomputable def precompInternalIso (F : C ⥤ D) :
    letI : ((Functor.whiskeringLeft C D (Type u)).obj F).Braided := .ofChosenFiniteProducts _
    (Functor.whiskeringLeft C D AddCommGrpCat.{u}).obj F ⋙ presheafCommGrp ≅
      presheafCommGrp ⋙ ((Functor.whiskeringLeft C D (Type u)).obj F).mapCommGrp :=
  precompInternalIsoOfUniverses F

/-- **The pullback of abelian sheaves along a cocontinuous functor is the pullback of sheaves of
sets with its induced group operations.**  Restricting a sheaf along `F.op` and sheafifying is
compatible with internalizing the group operations in each of its three steps. -/
noncomputable def cocontinuousAbelianInverseImageIso (F : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasSheafify J (Type u)] [HasWeakSheafify J AddCommGrpCat.{u}] :
    letI : (sheafToPresheaf K (Type u) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj F.op ⋙
        presheafToSheaf J (Type u)).Braided := .ofChosenFiniteProducts _
    internalSheaf K ⋙ (sheafToPresheaf K (Type u) ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj F.op ⋙
        presheafToSheaf J (Type u)).mapCommGrp ⋙ externalSheaf J ≅
      sheafToPresheaf K AddCommGrpCat.{u} ⋙
        (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj F.op ⋙
        presheafToSheaf J AddCommGrpCat.{u} := by
  let U := sheafToPresheaf K (Type u)
  let V := (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj F.op
  let L := presheafToSheaf J (Type u)
  let : U.Braided := .ofChosenFiniteProducts _
  let : V.Braided := .ofChosenFiniteProducts _
  let : L.Braided := .ofChosenFiniteProducts _
  let I := internalSheaf K
  let E := externalSheaf J
  let U' := sheafToPresheaf K AddCommGrpCat.{u}
  let V' := (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj F.op
  exact Functor.isoWhiskerLeft I (Functor.isoWhiskerRight
      (mapCommGrpBraidedIso (U ⋙ V ⋙ L) (.ofChosenFiniteProducts _) inferInstance) E) ≪≫
    Functor.isoWhiskerLeft I (Functor.isoWhiskerRight Functor.mapCommGrpCompIso E) ≪≫
    Functor.isoWhiskerLeft (I ⋙ U.mapCommGrp)
      (Functor.isoWhiskerRight Functor.mapCommGrpCompIso E) ≪≫
    (Functor.associator I U.mapCommGrp (V.mapCommGrp ⋙ L.mapCommGrp ⋙ E)).symm ≪≫
    Functor.isoWhiskerRight (sheafToPresheafInternalIso K).symm
      (V.mapCommGrp ⋙ L.mapCommGrp ⋙ E) ≪≫
    Functor.associator U' presheafCommGrp (V.mapCommGrp ⋙ L.mapCommGrp ⋙ E) ≪≫
    Functor.isoWhiskerLeft U'
      ((Functor.associator presheafCommGrp V.mapCommGrp (L.mapCommGrp ⋙ E)).symm ≪≫
        Functor.isoWhiskerRight (precompInternalIso F.op).symm (L.mapCommGrp ⋙ E) ≪≫
        Functor.associator V' presheafCommGrp (L.mapCommGrp ⋙ E)) ≪≫
    Functor.isoWhiskerLeft (U' ⋙ V') (sheafificationInternalIso J)

end Precomposition

end Stacks.Sites.AbelianPullback

end
