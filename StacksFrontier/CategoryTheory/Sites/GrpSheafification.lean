module

public import StacksFrontier.CategoryTheory.Sites.AbelianSheafification
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.GrpSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves of groups as internal group objects, through restriction and sheafification

A sheaf of groups on a site is the same thing as a group object in its category of sheaves of
sets, and a presheaf of groups is the same thing as a group object in presheaves of sets
(`CategoryTheory.Sites.GrpSheaf.equivalence` and `.presheafEquivalence`).  This file records
that the two identifications are compatible with passing to the underlying presheaf, with
restricting a presheaf along a functor, and with sheafification.

It is the non-commutative companion of
`StacksFrontier/CategoryTheory/Sites/AbelianSheafification.lean`, with one structural difference.
There sheafification of abelian presheaves is available from Mathlib and the comparison with
sheafification of sets is proved by uniqueness of left adjoints.  Here it is not: Mathlib's
sheafification for a concrete target category needs colimits in that category, and `GrpCat` has
none in Mathlib — only `MonCat` and `AddCommGrpCat` do.  So sheafification of presheaves of
groups is *constructed* instead, as the composite

`(Cᵒᵖ ⥤ GrpCat) ≌ Grp (Cᵒᵖ ⥤ Type u) ⥤ Grp (Sheaf J (Type u)) ≌ Sheaf J GrpCat`,

whose middle factor is sheafification of sheaves of sets acting on group objects.  Each factor is
a left adjoint, and the composite right adjoint is identified with the inclusion of sheaves of
groups into presheaves of groups by `sheafToPresheafInternalIso` and `presheafEquivalence`; that
is `hasWeakSheafify`.  The comparison `sheafificationInternalIso` is then uniqueness of left
adjoints against that construction, exactly as in the abelian case.

## Main definitions

* `Stacks.Sites.GrpPullback.mapGrpMonoidalIso`: the induced functor on group objects does not
  depend on the chosen monoidal structure.
* `Stacks.Sites.GrpPullback.hasWeakSheafify`: presheaves of groups on a small site admit
  sheafification.

## Main results

* `Stacks.Sites.GrpPullback.sheafToPresheafInternalIso`: the underlying presheaf of a sheaf of
  groups, internalized, is the internalization of the sheaf restricted to presheaves.
* `Stacks.Sites.GrpPullback.precompInternalIso`: restriction of presheaves along a functor
  commutes with internalizing the group operations.
* `Stacks.Sites.GrpPullback.sheafificationInternalIso`: the sheafification of a presheaf of
  groups is the sheafification of the underlying presheaf of sets with its induced group
  operations.

## Implementation notes

`precompInternalIso` has components which are the identity on sections; what has to be checked is
that they are multiplicative, and that is the statement that the monoidal structure of a
restriction functor is computed sectionwise, which is `CategoryTheory.Functor.Monoidal.μ_fst`
and `.μ_snd`.

The monoidal structure on a composite of functors obtained from instance search and the one
obtained from `CategoryTheory.Functor.Monoidal.ofChosenFiniteProducts` are different terms,
which is what `mapGrpMonoidalIso` is for.

## References

* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sites CategoryTheory.Sites.GrpSheaf Opposite

universe u v w

namespace Stacks.Sites.GrpPullback

attribute [local instance] Stacks.Sites.AbelianPullback.cartesianPresheafTypes
  Stacks.Sites.AbelianPullback.braidedPresheafTypes Stacks.Sites.AbelianPullback.cartesianSheafTypes
  Stacks.Sites.AbelianPullback.braidedSheafTypes
  Stacks.Sites.AbelianPullback.braidedSheafToPresheafTypes

/-- Changing the monoidal structure of a functor does not change the induced functor on group
objects.  Unlike its commutative analogue this needs no braiding: a group object has no
commutativity to transport, so `CategoryTheory.Functor.mapGrp` asks only for
`CategoryTheory.Functor.Monoidal`. -/
noncomputable def mapGrpMonoidalIso {A : Type*} [Category* A]
    [CartesianMonoidalCategory A] {B : Type*} [Category* B]
    [CartesianMonoidalCategory B] (G : A ⥤ B) (m₁ m₂ : G.Monoidal) :
    (letI := m₁; G.mapGrp) ≅ (letI := m₂; G.mapGrp) :=
  @Functor.mapGrpNatIso _ _ _ _ _ _ G G m₁ m₂ (Iso.refl _)

/-- Internalizing the group operations of the underlying presheaf of a sheaf of groups is the
same as internalizing them on the sheaf and then passing to the underlying presheaf of sets. -/
noncomputable def sheafToPresheafInternalIso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    sheafToPresheaf J GrpCat.{w} ⋙ presheafGrp ≅
      internalSheaf J ⋙ (sheafToPresheaf J (Type w)).mapGrp :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (internalExternalIso J).symm
      (sheafToPresheaf J GrpCat.{w} ⋙ presheafGrp) ≪≫
    Functor.isoWhiskerLeft (internalSheaf J ⋙ (sheafToPresheaf J (Type w)).mapGrp)
      (presheafEquivalence _).counitIso ≪≫
    Functor.rightUnitor _

section Sheafification

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)

/-- The inclusion of sheaves of groups into presheaves of groups, read through the two
identifications with group objects.  This is the right adjoint of the composite of which
sheafification of presheaves of groups is built. -/
noncomputable def sheafToPresheafGrpIso :
    sheafToPresheaf J GrpCat.{u} ≅
      internalSheaf J ⋙ (sheafToPresheaf J (Type u)).mapGrp ⋙ grpPresheaves :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (presheafEquivalence (Cᵒᵖ)).unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafToPresheafInternalIso J) _ ≪≫
    Functor.associator _ _ _

/-- **Sheafification of presheaves of groups**, as an adjunction: a presheaf of groups is read as
a group object in presheaves of sets, its underlying presheaf is sheafified, and the resulting
group object in sheaves of sets is read back sectionwise.  Each of the three factors is a left
adjoint, and `sheafToPresheafGrpIso` identifies the composite right adjoint with the inclusion of
sheaves of groups into presheaves of groups. -/
@[ega "0 3.7.1" "special case", sga "3 IV 4.3.16"]
noncomputable def sheafificationGrpAdjunction :
    letI : (presheafToSheaf J (Type u)).Monoidal := .ofChosenFiniteProducts _
    presheafGrp ⋙ (presheafToSheaf J (Type u)).mapGrp ⋙ externalSheaf J ⊣
      sheafToPresheaf J GrpCat.{u} := by
  letI : (presheafToSheaf J (Type u)).Monoidal := .ofChosenFiniteProducts _
  exact ((((presheafEquivalence (Cᵒᵖ)).toAdjunction.comp
      (sheafificationAdjunction J (Type u)).mapGrp).comp
        (GrpSheaf.equivalence J).symm.toAdjunction).ofNatIsoRight
          (sheafToPresheafGrpIso J).symm).ofNatIsoLeft (Functor.associator _ _ _)

/-- Presheaves of groups on a small site admit sheafification.  Mathlib does not supply this:
its sheafification for a concrete target category needs colimits in that category, and it has
none for `GrpCat`.  The construction is `sheafificationGrpAdjunction`. -/
noncomputable instance hasWeakSheafify : HasWeakSheafify J GrpCat.{u} :=
  (sheafificationGrpAdjunction J).isRightAdjoint

/-- The sheafification of a presheaf of groups is the sheafification of its underlying presheaf
of sets, carrying the induced group operations.  Both are left adjoint to the inclusion of
sheaves of groups into presheaves of groups. -/
noncomputable def sheafificationInternalIso :
    letI : (presheafToSheaf J (Type u)).Monoidal := .ofChosenFiniteProducts _
    presheafGrp ⋙ (presheafToSheaf J (Type u)).mapGrp ⋙ externalSheaf J ≅
      presheafToSheaf J GrpCat.{u} := by
  letI : (presheafToSheaf J (Type u)).Monoidal := .ofChosenFiniteProducts _
  exact (sheafificationGrpAdjunction J).leftAdjointUniq (sheafificationAdjunction J GrpCat.{u})

end Sheafification

section Precomposition

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]

/-- Restriction of presheaves along a functor commutes with internalizing the group operations:
the comparison is the identity on sections, and it is multiplicative because the monoidal
structure of a restriction functor is computed sectionwise. -/
noncomputable def precompInternalIso (F : C ⥤ D) :
    letI : ((Functor.whiskeringLeft C D (Type u)).obj F).Monoidal := .ofChosenFiniteProducts _
    (Functor.whiskeringLeft C D GrpCat.{u}).obj F ⋙ presheafGrp ≅
      presheafGrp ⋙ ((Functor.whiskeringLeft C D (Type u)).obj F).mapGrp := by
  let R := (Functor.whiskeringLeft C D (Type u)).obj F
  letI : R.Monoidal := .ofChosenFiniteProducts _
  refine NatIso.ofComponents (fun A => Grp.mkIso (Iso.refl _) ?_ ?_) ?_
  · ext U x
    rfl
  · let A' := presheafGrp.obj A
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
  · intro A B f
    apply Grp.hom_ext
    rfl

end Precomposition

end Stacks.Sites.GrpPullback

end
