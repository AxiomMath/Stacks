module

public import StacksFrontier.CategoryTheory.Sites.AbelianSheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.RingSheaf

/-!
# Sheaves of rings as internal ring objects, through restriction and sheafification

A sheaf of rings on a site is the same thing as a ring object in its category of sheaves of sets,
and a presheaf of rings is the same thing as a ring object in presheaves of sets
(`CategoryTheory.Sites.RingSheaf.equivalence` and `.presheafEquivalence`).  This file records
that the two identifications are compatible with the three operations out of which the pullback
of sheaves along a functor is built: passing to the underlying presheaf, restricting a presheaf
along a functor, and sheafifying.

It is the ring-level companion of
`StacksFrontier/CategoryTheory/Sites/AbelianSheafification.lean` and
`StacksFrontier/CategoryTheory/Sites/GrpSheafification.lean`.  Unlike the group case nothing about
sheafification has to be constructed: Mathlib already has colimits in `RingCat`, so
sheafification of presheaves of rings is available and `sheafificationInternalIso` is proved by
uniqueness of left adjoints, as in the abelian case.  What is not available is the action of an
adjunction on internal ring objects, since `CategoryTheory.Functor.mapRing` is itself not part of
Mathlib; `mapRingAdjunction` supplies it.

## Main definitions

* `Stacks.Sites.RingPullback.mapRingBraidedIso`: the induced functor on ring objects does not
  depend on the chosen braiding.
* `Stacks.Sites.RingPullback.fullyFaithfulMapRing`: a fully faithful braided functor is fully
  faithful on ring objects.
* `Stacks.Sites.RingPullback.mapRingNatTrans`: a natural transformation of braided functors
  acts on ring objects.
* `Stacks.Sites.RingPullback.mapRingAdjunction`: an adjunction of braided functors acts on ring
  objects.

## Main results

* `Stacks.Sites.RingPullback.sheafToPresheafInternalIso`: the underlying presheaf of a sheaf of
  rings, internalized, is the internalization of the sheaf restricted to presheaves.
* `Stacks.Sites.RingPullback.precompInternalIso`: restriction of presheaves along a functor
  commutes with internalizing the ring operations.
* `Stacks.Sites.RingPullback.sheafificationInternalIso`: the sheafification of a presheaf of
  rings is the sheafification of the underlying presheaf of sets with its induced ring
  operations.

## Implementation notes

`sheafToPresheafInternalIso` and `precompInternalIso` have components which are the identity on
sections; what has to be checked is that they are multiplicative and additive, and for
`precompInternalIso` this is the statement that the monoidal structure of a restriction functor
is computed sectionwise, which is `CategoryTheory.Functor.Monoidal.μ_fst` and `.μ_snd`.

`sheafificationInternalIso` is proved by uniqueness of left adjoints: both sides are left adjoint
to the inclusion of sheaves of rings into presheaves of rings, the second by the sheafification
adjunction and the first because it is a composite of three left adjoints, whose right adjoint is
identified with that inclusion by `sheafToPresheafInternalIso` and
`CategoryTheory.Sites.RingSheaf.presheafEquivalence`.

The unit and counit of `mapRingAdjunction` are the unit and counit of the given adjunction on the
nose, rather than conjugates of them by the comparisons with the identity and with a composite.
This keeps the two triangle identities literally those of the given adjunction, at the cost of
checking by hand that the unit and counit are homomorphisms of ring objects; the four checks are
`CategoryTheory.Functor.natTrans_one` and its siblings, corrected at one end by `id_mapRing_one`
and its siblings and at the other by `CategoryTheory.Functor.comp_mapRing_one` and its siblings.

The braiding on a composite of functors obtained from instance search and the one obtained from
`CategoryTheory.Functor.Braided.ofChosenFiniteProducts` are different terms, which is what
`mapRingBraidedIso` is for.

## References

* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.MonoidalCategory
open CategoryTheory.Sites CategoryTheory.Sites.RingSheaf Opposite

universe u v w

namespace Stacks.Sites.RingPullback

open scoped MonObj AddMonObj

attribute [local instance] Stacks.Sites.AbelianPullback.cartesianPresheafTypes
  Stacks.Sites.AbelianPullback.braidedPresheafTypes Stacks.Sites.AbelianPullback.cartesianSheafTypes
  Stacks.Sites.AbelianPullback.braidedSheafTypes
  Stacks.Sites.AbelianPullback.braidedSheafToPresheafTypes

/-- Changing the braiding of a functor does not change the induced functor on ring objects. -/
noncomputable def mapRingBraidedIso {A : Type*} [Category* A]
    [CartesianMonoidalCategory A] [BraidedCategory A] {B : Type*} [Category* B]
    [CartesianMonoidalCategory B] [BraidedCategory B] (G : A ⥤ B) (b₁ b₂ : G.Braided) :
    (letI := b₁; G.mapRing) ≅ (letI := b₂; G.mapRing) :=
  @Functor.mapRingNatIso _ _ _ _ _ _ _ _ G b₁ G b₂ (Iso.refl _)

section MapRing

variable {A : Type*} [Category* A] [CartesianMonoidalCategory A] [BraidedCategory A]
  {B : Type*} [Category* B] [CartesianMonoidalCategory B] [BraidedCategory B]

open scoped Obj in
/-- **A fully faithful braided functor is fully faithful on ring objects.** The preimage of a
homomorphism of ring objects is a homomorphism of ring objects, because it is one for the
multiplicative and for the additive structure separately. -/
noncomputable def fullyFaithfulMapRing {F : A ⥤ B} [F.Braided] (hF : F.FullyFaithful) :
    F.mapRing.FullyFaithful where
  preimage {R S} f :=
    haveI : IsMonHom (show F.obj R.X ⟶ F.obj S.X from f.hom) := f.isRingHom.toIsMonHom
    haveI : IsAddMonHom (show F.obj R.X ⟶ F.obj S.X from f.hom) := f.isRingHom.toIsAddMonHom
    haveI := Functor.FullyFaithful.isMonHom_preimage hF
      (show F.obj R.X ⟶ F.obj S.X from f.hom)
    haveI := Functor.FullyFaithful.isAddMonHom_preimage hF
      (show F.obj R.X ⟶ F.obj S.X from f.hom)
    haveI : IsRingHom (hF.preimage f.hom) := ⟨⟩
    { hom := hF.preimage f.hom }
  map_preimage f := RingObjCat.hom_ext (hF.map_preimage f.hom)
  preimage_map f := RingObjCat.hom_ext (hF.preimage_map f.hom)

/-- A faithful braided functor is faithful on ring objects. -/
instance faithful_mapRing {F : A ⥤ B} [F.Braided] [F.Faithful] : F.mapRing.Faithful where
  map_injective h := RingObjCat.hom_ext (F.map_injective (congrArg RingObjCat.Hom.hom h))

/-- A fully faithful braided functor is full on ring objects. -/
instance full_mapRing {F : A ⥤ B} [F.Braided] [F.Full] [F.Faithful] : F.mapRing.Full :=
  (fullyFaithfulMapRing (Functor.FullyFaithful.ofFullyFaithful F)).full

/-- The unit of a ring object is unchanged by the identity functor. -/
lemma id_mapRing_one (R : RingObjCat A) : η[((𝟭 A).mapRing.obj R).X] = η[R.X] :=
  Category.id_comp _

/-- The multiplication of a ring object is unchanged by the identity functor. -/
lemma id_mapRing_mul (R : RingObjCat A) : μ[((𝟭 A).mapRing.obj R).X] = μ[R.X] :=
  Category.id_comp _

/-- The zero of a ring object is unchanged by the identity functor. -/
lemma id_mapRing_zero (R : RingObjCat A) : ζ[((𝟭 A).mapRing.obj R).X] = ζ[R.X] :=
  Category.id_comp _

/-- The addition of a ring object is unchanged by the identity functor. -/
lemma id_mapRing_add (R : RingObjCat A) : σ[((𝟭 A).mapRing.obj R).X] = σ[R.X] :=
  Category.id_comp _

/-- **A natural transformation of braided functors acts on ring objects.** Its components are
the components of the given transformation, which are homomorphisms of ring objects because a
natural transformation of braided functors respects the four transported structure
morphisms. -/
noncomputable def mapRingNatTrans {F F' : A ⥤ B} [F.Braided] [F'.Braided] (e : F ⟶ F') :
    F.mapRing ⟶ F'.mapRing where
  app R :=
    { hom := e.app R.X
      isRingHom :=
        { one_hom := Functor.natTrans_one e R.X
          mul_hom := Functor.natTrans_mul e R.X
          zero_hom := Functor.natTrans_zero e R.X
          add_hom := Functor.natTrans_add e R.X } }
  naturality _ _ f := RingObjCat.hom_ext (e.naturality f.hom)

/-- **An adjunction of braided functors acts on ring objects.** The unit and counit are those of
the given adjunction, which are homomorphisms of ring objects, so the triangle identities are
the triangle identities of the given adjunction. -/
noncomputable def mapRingAdjunction {F : A ⥤ B} {G : B ⥤ A} [F.Braided] [G.Braided]
    (a : F ⊣ G) : F.mapRing ⊣ G.mapRing where
  unit :=
    { app R :=
        { hom := a.unit.app R.X
          isRingHom :=
            { one_hom := (congrArg (· ≫ a.unit.app R.X) (id_mapRing_one R)).symm.trans
                ((Functor.natTrans_one a.unit R.X).trans (Functor.comp_mapRing_one R))
              mul_hom := (congrArg (· ≫ a.unit.app R.X) (id_mapRing_mul R)).symm.trans
                ((Functor.natTrans_mul a.unit R.X).trans
                  (congrArg (fun t ↦ (a.unit.app R.X ⊗ₘ a.unit.app R.X) ≫ t)
                    (Functor.comp_mapRing_mul R)))
              zero_hom := (congrArg (· ≫ a.unit.app R.X) (id_mapRing_zero R)).symm.trans
                ((Functor.natTrans_zero a.unit R.X).trans (Functor.comp_mapRing_zero R))
              add_hom := (congrArg (· ≫ a.unit.app R.X) (id_mapRing_add R)).symm.trans
                ((Functor.natTrans_add a.unit R.X).trans
                  (congrArg (fun t ↦ (a.unit.app R.X ⊗ₘ a.unit.app R.X) ≫ t)
                    (Functor.comp_mapRing_add R))) } }
      naturality _ _ f := RingObjCat.hom_ext (a.unit.naturality f.hom) }
  counit :=
    { app S :=
        { hom := a.counit.app S.X
          isRingHom :=
            { one_hom := (congrArg (· ≫ a.counit.app S.X) (Functor.comp_mapRing_one S)).symm.trans
                ((Functor.natTrans_one a.counit S.X).trans (id_mapRing_one S))
              mul_hom := (congrArg (· ≫ a.counit.app S.X) (Functor.comp_mapRing_mul S)).symm.trans
                ((Functor.natTrans_mul a.counit S.X).trans
                  (congrArg (fun t ↦ (a.counit.app S.X ⊗ₘ a.counit.app S.X) ≫ t)
                    (id_mapRing_mul S)))
              zero_hom :=
                (congrArg (· ≫ a.counit.app S.X) (Functor.comp_mapRing_zero S)).symm.trans
                  ((Functor.natTrans_zero a.counit S.X).trans (id_mapRing_zero S))
              add_hom := (congrArg (· ≫ a.counit.app S.X) (Functor.comp_mapRing_add S)).symm.trans
                ((Functor.natTrans_add a.counit S.X).trans
                  (congrArg (fun t ↦ (a.counit.app S.X ⊗ₘ a.counit.app S.X) ≫ t)
                    (id_mapRing_add S))) } }
      naturality _ _ f := RingObjCat.hom_ext (a.counit.naturality f.hom) }
  left_triangle_components R := RingObjCat.hom_ext (a.left_triangle_components R.X)
  right_triangle_components S := RingObjCat.hom_ext (a.right_triangle_components S.X)

end MapRing

/-- Internalizing the ring operations of the underlying presheaf of a sheaf of rings is the same
as internalizing them on the sheaf and then passing to the underlying presheaf of sets. -/
noncomputable def sheafToPresheafInternalIso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    sheafToPresheaf J RingCat.{w} ⋙ presheafRing ≅
      internalSheaf J ⋙ (sheafToPresheaf J (Type w)).mapRing :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (internalExternalIso J).symm
      (sheafToPresheaf J RingCat.{w} ⋙ presheafRing) ≪≫
    Functor.isoWhiskerLeft (internalSheaf J ⋙ (sheafToPresheaf J (Type w)).mapRing)
      (RingSheaf.presheafEquivalence _).counitIso ≪≫
    Functor.rightUnitor _

section Sheafification

variable {C : Type u} [Category.{u} C]

/-- The sheafification of a presheaf of rings is the sheafification of its underlying presheaf of
sets, carrying the induced ring operations.  Both are left adjoint to the inclusion of sheaves of
rings into presheaves of rings. -/
noncomputable def sheafificationInternalIso (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] [HasWeakSheafify J RingCat.{u}] :
    letI : (presheafToSheaf J (Type u)).Braided := .ofChosenFiniteProducts _
    presheafRing ⋙ (presheafToSheaf J (Type u)).mapRing ⋙ externalSheaf J ≅
      presheafToSheaf J RingCat.{u} := by
  let L := presheafToSheaf J (Type u)
  let R := sheafToPresheaf J (Type u)
  letI : L.Braided := .ofChosenFiniteProducts _
  let E : (Cᵒᵖ ⥤ RingCat.{u}) ≌ RingObjCat (Cᵒᵖ ⥤ Type u) := RingSheaf.presheafEquivalence _
  let E' : Sheaf J RingCat.{u} ≌ RingObjCat (Sheaf J (Type u)) := RingSheaf.equivalence J
  let a := (E.toAdjunction.comp (mapRingAdjunction (sheafificationAdjunction J (Type u)))).comp
    E'.symm.toAdjunction
  let e : sheafToPresheaf J RingCat.{u} ≅
      internalSheaf J ⋙ R.mapRing ⋙ ringPresheaves :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ E.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (sheafToPresheafInternalIso J) _ ≪≫
      Functor.associator _ _ _
  exact (Functor.associator _ _ _).symm ≪≫
    (a.ofNatIsoRight e.symm).leftAdjointUniq (sheafificationAdjunction J RingCat.{u})

end Sheafification

section Precomposition

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]

/-- Restriction of presheaves along a functor commutes with internalizing the ring operations:
the comparison is the identity on sections, and it is multiplicative and additive because the
monoidal structure of a restriction functor is computed sectionwise. -/
noncomputable def precompInternalIso (F : C ⥤ D) :
    letI : ((Functor.whiskeringLeft C D (Type u)).obj F).Braided := .ofChosenFiniteProducts _
    (Functor.whiskeringLeft C D RingCat.{u}).obj F ⋙ presheafRing ≅
      presheafRing ⋙ ((Functor.whiskeringLeft C D (Type u)).obj F).mapRing := by
  let R := (Functor.whiskeringLeft C D (Type u)).obj F
  letI : R.Braided := .ofChosenFiniteProducts _
  letI : R.Monoidal := (inferInstance : R.Braided).toMonoidal
  letI : R.LaxMonoidal := (inferInstance : R.Braided).toLaxBraided.toLaxMonoidal
  refine NatIso.ofComponents (fun A => RingObjCat.mkIso (Iso.refl _) ?_ ?_ ?_ ?_) ?_
  · ext U x
    rfl
  · let A' := presheafRing.obj A
    have hf := Functor.Monoidal.μ_fst R A'.X A'.X
    have hs := Functor.Monoidal.μ_snd R A'.X A'.X
    ext U x
    let mul := @Mul.mul (A.obj (F.obj U)) inferInstance
    change mul
      ((CartesianMonoidalCategory.fst (R.obj A'.X) (R.obj A'.X)).app U x)
      ((CartesianMonoidalCategory.snd (R.obj A'.X) (R.obj A'.X)).app U x) =
      mul
        ((Functor.LaxMonoidal.μ R A'.X A'.X ≫ R.map
          (CartesianMonoidalCategory.fst A'.X A'.X)).app U x)
        ((Functor.LaxMonoidal.μ R A'.X A'.X ≫ R.map
          (CartesianMonoidalCategory.snd A'.X A'.X)).app U x)
    exact congrArg₂ mul (ConcreteCategory.congr_hom (congr_app hf U) x).symm
      (ConcreteCategory.congr_hom (congr_app hs U) x).symm
  · ext U x
    rfl
  · let A' := presheafRing.obj A
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
    apply RingObjCat.hom_ext
    rfl

end Precomposition

end Stacks.Sites.RingPullback

end
