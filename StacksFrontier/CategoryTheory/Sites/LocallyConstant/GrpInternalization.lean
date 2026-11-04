module

public import StacksFrontier.CategoryTheory.Sites.GrpSheafification
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianInternalization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction to an object and the constant sheaf, read on internal group objects

A sheaf of groups on a site is a group object in its sheaves of sets
(`CategoryTheory.Sites.GrpSheaf.equivalence`). This file records that two further functors are
compatible with that identification: restriction to an object of the site, and the constant sheaf
functor.

Both are needed to read an argument about sheaves of sets on sheaves of groups when the argument
is phrased in terms of restrictions and of local constancy, since
`Stacks.ConstantSheaf.IsLocallyConstant` is stated with `GrothendieckTopology.overPullback` and
`constantSheaf`.

Restriction is elementary: `J.overPullback A U` is restriction of presheaves along
`(Over.forget U).op` with no sheafification, so the comparison is the identity on sections and
the work is already done by `Stacks.Sites.GrpPullback.precompInternalIso` and
`Stacks.Sites.GrpPullback.sheafToPresheafInternalIso`; the only step not available off the shelf
is that the two ways of composing the restriction with the inclusion of sheaves into presheaves
carry different monoidal structures, which `Stacks.Sites.GrpPullback.mapGrpMonoidalIso` bridges.
The comparison is then obtained at the level of presheaves and transported back along the fully
faithful `(sheafToPresheaf _ _).mapGrp` with `CategoryTheory.fullyFaithfulCancelRight`.

The constant sheaf is not elementary, because it sheafifies: `constantSheaf J A` is
`Functor.const Cᵒᵖ ⋙ presheafToSheaf J A`. The constant *presheaf* half is again identity on
sections (`constPresheafInternalIso`), and the sheafification half is
`Stacks.Sites.GrpPullback.sheafificationInternalIso`.

This is the non-commutative companion of
`StacksFrontier/CategoryTheory/Sites/LocallyConstant/AbelianInternalization.lean`, which is imported
for the coefficient-free `Stacks.Sites.AbelianPullback.overForgetRestrictTypes` and for the
instance `Stacks.Sites.AbelianPullback.preservesFiniteProducts_constantSheaf`, neither of which
mentions a group.

## Main definitions

* `Stacks.Sites.GrpPullback.overPullbackInternalIso` — restriction to an object of the site
  commutes with internalizing the group operations.
* `Stacks.Sites.GrpPullback.overPullbackExternalIso` — the same, read in the direction of
  `externalSheaf`.
* `Stacks.Sites.GrpPullback.constPresheafInternalIso` — the constant presheaf on a group,
  internalized, is the constant presheaf on the internal group object.
* `Stacks.Sites.GrpPullback.constantSheafInternalIso` — the constant sheaf of groups on a group,
  internalized, is the constant sheaf of sets on the internal group object with its induced
  operations.
* `Stacks.Sites.GrpPullback.constantSheafExternalIso` — the same, read in the direction of
  `externalSheaf`.

## Implementation notes

Every statement fixes its monoidal structures as
`CategoryTheory.Functor.Monoidal.ofChosenFiniteProducts` through a `letI` in the type: the
instance obtained from instance search on a composite is a different term, and a consumer which
let instance search choose would not be able to apply these comparisons.

The chains are split into separately named links rather than written as one term. This is not
cosmetic: a single declaration carrying two crossings between sheaves of groups and internal
group objects does not elaborate inside the per-declaration budget.

## References

* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sites CategoryTheory.Sites.GrpSheaf Opposite
open Stacks.Sites.AbelianPullback (overForgetRestrictTypes)

universe w

namespace Stacks.Sites.GrpPullback

attribute [local instance] Stacks.Sites.AbelianPullback.cartesianPresheafTypes
  Stacks.Sites.AbelianPullback.braidedPresheafTypes Stacks.Sites.AbelianPullback.cartesianSheafTypes
  Stacks.Sites.AbelianPullback.braidedSheafTypes
  Stacks.Sites.AbelianPullback.braidedSheafToPresheafTypes

/-! ### Restriction to an object of the site -/

section OverPullback

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C) (U : C)

/-- Restriction of presheaves of groups along `(Over.forget U).op`, the functor out of which
`GrothendieckTopology.overPullback` for sheaves of groups is built. -/
public abbrev overForgetRestrictGrp :=
  (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ GrpCat.{w}).obj (Over.forget U).op

/-- First link: the restriction to `C/U` of a sheaf of groups, internalized and read as
presheaves of sets, is the underlying presheaf of groups restricted along `(Over.forget U).op`
and then internalized. This is `sheafToPresheafInternalIso` on the localized site, together with
the definitional identity `J.overPullback A U ⋙ sheafToPresheaf (J.over U) A =
sheafToPresheaf J A ⋙ (whiskeringLeft _ _ A).obj (Over.forget U).op`. -/
public def overPullbackInternalPresheafIso :
    (J.overPullback GrpCat.{w} U ⋙ internalSheaf (J.over U)) ⋙
        (sheafToPresheaf (J.over U) (Type w)).mapGrp ≅
      (sheafToPresheaf J GrpCat.{w} ⋙ overForgetRestrictGrp U) ⋙ presheafGrp :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sheafToPresheafInternalIso (J.over U)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Second link: internalizing commutes with restricting a presheaf of groups along
`(Over.forget U).op`. This is `precompInternalIso` at that functor, preceded and followed by
`sheafToPresheafInternalIso` on `C` itself. -/
public def overForgetRestrictInternalIso :
    letI : (overForgetRestrictTypes (C := C) U).Monoidal := .ofChosenFiniteProducts _
    (sheafToPresheaf J GrpCat.{w} ⋙ overForgetRestrictGrp U) ⋙ presheafGrp ≅
      (internalSheaf J ⋙ (sheafToPresheaf J (Type w)).mapGrp) ⋙
        (overForgetRestrictTypes (C := C) U).mapGrp := by
  let : (overForgetRestrictTypes (C := C) U).Monoidal := .ofChosenFiniteProducts _
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (precompInternalIso (Over.forget U).op) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafToPresheafInternalIso J) _

/-- Third link: the restriction of presheaves of sets along `(Over.forget U).op`, read on
internal group objects, is the restriction of sheaves of sets to `C/U` followed by the inclusion
of sheaves into presheaves. The two composites are the same functor, but the monoidal structure
instance search produces for each of them is a different term, which is why
`mapGrpMonoidalIso` appears. -/
public def overPullbackMapGrpIso :
    letI : (overForgetRestrictTypes (C := C) U).Monoidal := .ofChosenFiniteProducts _
    letI : (J.overPullback (Type w) U).Monoidal := .ofChosenFiniteProducts _
    (internalSheaf J ⋙ (sheafToPresheaf J (Type w)).mapGrp) ⋙
        (overForgetRestrictTypes (C := C) U).mapGrp ≅
      (internalSheaf J ⋙ (J.overPullback (Type w) U).mapGrp) ⋙
        (sheafToPresheaf (J.over U) (Type w)).mapGrp := by
  let : (overForgetRestrictTypes (C := C) U).Monoidal := .ofChosenFiniteProducts _
  let : (J.overPullback (Type w) U).Monoidal := .ofChosenFiniteProducts _
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapGrpCompIso
      (F := sheafToPresheaf J (Type w)) (G := overForgetRestrictTypes (C := C) U)).symm ≪≫
    Functor.isoWhiskerLeft _ (mapGrpMonoidalIso
      (J.overPullback (Type w) U ⋙ sheafToPresheaf (J.over U) (Type w))
      (Functor.Monoidal.instComp (F := sheafToPresheaf J (Type w))
        (G := overForgetRestrictTypes (C := C) U)) inferInstance) ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapGrpCompIso
      (F := J.overPullback (Type w) U) (G := sheafToPresheaf (J.over U) (Type w))) ≪≫
    (Functor.associator _ _ _).symm

/-- **Restriction to an object of the site commutes with internalization.** Internalizing the
group operations of the restriction of a sheaf of groups to `C/U` gives the restriction to `C/U`
of its internalization.

The three links above prove this after composing with the inclusion of sheaves into presheaves,
read on group objects; that functor is fully faithful, so the comparison descends by
`CategoryTheory.fullyFaithfulCancelRight`. -/
public def overPullbackInternalIso :
    letI : (J.overPullback (Type w) U).Monoidal := .ofChosenFiniteProducts _
    J.overPullback GrpCat.{w} U ⋙ internalSheaf (J.over U) ≅
      internalSheaf J ⋙ (J.overPullback (Type w) U).mapGrp := by
  let : (overForgetRestrictTypes (C := C) U).Monoidal := .ofChosenFiniteProducts _
  let : (J.overPullback (Type w) U).Monoidal := .ofChosenFiniteProducts _
  exact fullyFaithfulCancelRight _
    (overPullbackInternalPresheafIso J U ≪≫ overForgetRestrictInternalIso J U ≪≫
      overPullbackMapGrpIso J U)

/-- **Restriction to an object of the site commutes with reading internal operations
sectionwise**, the form of `overPullbackInternalIso` for `externalSheaf`. Obtained from it by
conjugating with the unit and counit of the equivalence between sheaves of groups and internal
group objects. -/
public def overPullbackExternalIso :
    letI : (J.overPullback (Type w) U).Monoidal := .ofChosenFiniteProducts _
    externalSheaf J ⋙ J.overPullback GrpCat.{w} U ≅
      (J.overPullback (Type w) U).mapGrp ⋙ externalSheaf (J.over U) := by
  let : (J.overPullback (Type w) U).Monoidal := .ofChosenFiniteProducts _
  exact (Functor.rightUnitor (externalSheaf J ⋙ J.overPullback GrpCat.{w} U)).symm ≪≫
    Functor.isoWhiskerLeft (externalSheaf J ⋙ J.overPullback GrpCat.{w} U)
      (internalExternalIso (J.over U)).symm ≪≫
    Functor.isoWhiskerLeft (externalSheaf J)
      (Functor.isoWhiskerRight (overPullbackInternalIso J U) (externalSheaf (J.over U))) ≪≫
    Functor.isoWhiskerRight (externalInternalIso J)
      ((J.overPullback (Type w) U).mapGrp ⋙ externalSheaf (J.over U)) ≪≫
    Functor.leftUnitor _

end OverPullback

/-! ### The constant sheaf -/

section ConstantSheaf

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)

/-- **The constant presheaf commutes with internalization.** The constant presheaf of groups on a
group, with its operations internalized, is the constant presheaf on the corresponding internal
group object in sets.

The comparison is the identity on sections; what has to be checked is that it is multiplicative,
and that is the statement that the monoidal structure of `Functor.const` is computed sectionwise,
namely `CategoryTheory.Functor.Monoidal.μ_fst` and `.μ_snd`. -/
public def constPresheafInternalIso :
    letI : (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)).Monoidal := .ofChosenFiniteProducts _
    (Functor.const Cᵒᵖ : GrpCat.{w} ⥤ (Cᵒᵖ ⥤ GrpCat.{w})) ⋙ presheafGrp ≅
      grpTypeEquivalenceGrp.inverse ⋙
        (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)).mapGrp := by
  let : (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)).Monoidal := .ofChosenFiniteProducts _
  refine NatIso.ofComponents (fun E => Grp.mkIso (Iso.refl _) rfl ?_)
    fun _ => Grp.hom_ext _ _ rfl
  let X := (grpTypeEquivalenceGrp.inverse.obj E).X
  let R := (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w))
  ext V x
  let mul := @Mul.mul (((Functor.const Cᵒᵖ).obj E).obj V) inferInstance
  change mul ((CartesianMonoidalCategory.fst (R.obj X) (R.obj X)).app V x)
      ((CartesianMonoidalCategory.snd (R.obj X) (R.obj X)).app V x) =
    mul ((Functor.LaxMonoidal.μ R X X ≫ R.map (CartesianMonoidalCategory.fst X X)).app V x)
      ((Functor.LaxMonoidal.μ R X X ≫ R.map (CartesianMonoidalCategory.snd X X)).app V x)
  exact congrArg₂ mul
    (ConcreteCategory.congr_hom (congr_app (Functor.Monoidal.μ_fst R X X) V) x).symm
    (ConcreteCategory.congr_hom (congr_app (Functor.Monoidal.μ_snd R X X) V) x).symm

/-- **Sheafification commutes with internalization**, in the direction of `internalSheaf`. This
is `sheafificationInternalIso` with the equivalence between sheaves of groups and internal group
objects applied to its right-hand side. -/
public def presheafToSheafInternalIso :
    letI : (presheafToSheaf J (Type w)).Monoidal := .ofChosenFiniteProducts _
    presheafToSheaf J GrpCat.{w} ⋙ internalSheaf J ≅
      presheafGrp ⋙ (presheafToSheaf J (Type w)).mapGrp := by
  let : (presheafToSheaf J (Type w)).Monoidal := .ofChosenFiniteProducts _
  exact (Functor.isoWhiskerRight (sheafificationInternalIso J) (internalSheaf J)).symm ≪≫
    Functor.isoWhiskerLeft (presheafGrp ⋙ (presheafToSheaf J (Type w)).mapGrp)
      (externalInternalIso J) ≪≫
    Functor.rightUnitor _

/-- **The constant sheaf commutes with internalization.** The constant sheaf of groups on a
group, with its operations internalized, is the constant sheaf of sets on the corresponding
internal group object, with the operations induced on it.

The constant sheaf functor is the constant presheaf functor followed by sheafification, and the
two halves are `constPresheafInternalIso` and `presheafToSheafInternalIso`. -/
@[sga "4 IV 4.3.4" "Group clause"]
public def constantSheafInternalIso :
    letI : (constantSheaf J (Type w)).Monoidal := .ofChosenFiniteProducts _
    constantSheaf J GrpCat.{w} ⋙ internalSheaf J ≅
      grpTypeEquivalenceGrp.inverse ⋙ (constantSheaf J (Type w)).mapGrp := by
  let : (presheafToSheaf J (Type w)).Monoidal := .ofChosenFiniteProducts _
  let : (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)).Monoidal := .ofChosenFiniteProducts _
  let : (constantSheaf J (Type w)).Monoidal := .ofChosenFiniteProducts _
  exact Functor.isoWhiskerLeft
      (Functor.const Cᵒᵖ : GrpCat.{w} ⥤ (Cᵒᵖ ⥤ GrpCat.{w}))
      (presheafToSheafInternalIso J) ≪≫
    Functor.isoWhiskerRight (constPresheafInternalIso (C := C))
      ((presheafToSheaf J (Type w)).mapGrp) ≪≫
    Functor.isoWhiskerLeft grpTypeEquivalenceGrp.inverse
      (Functor.mapGrpCompIso (F := (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)))
        (G := presheafToSheaf J (Type w))).symm ≪≫
    Functor.isoWhiskerLeft grpTypeEquivalenceGrp.inverse
      (mapGrpMonoidalIso (constantSheaf J (Type w))
        (Functor.Monoidal.instComp (F := (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)))
          (G := presheafToSheaf J (Type w))) inferInstance)

/-- **The constant sheaf commutes with reading internal operations sectionwise**, the form of
`constantSheafInternalIso` for `externalSheaf`. Obtained from it by conjugating with the unit and
counit of the equivalence between sheaves of groups and internal group objects. -/
@[sga "4 IV 4.3.4" "Group clause"]
public def constantSheafExternalIso :
    letI : (constantSheaf J (Type w)).Monoidal := .ofChosenFiniteProducts _
    grpTypeEquivalenceGrp.inverse ⋙ (constantSheaf J (Type w)).mapGrp ⋙
        externalSheaf J ≅
      constantSheaf J GrpCat.{w} := by
  let : (constantSheaf J (Type w)).Monoidal := .ofChosenFiniteProducts _
  exact (Functor.isoWhiskerRight (constantSheafInternalIso J) (externalSheaf J)).symm ≪≫
    Functor.isoWhiskerLeft (constantSheaf J GrpCat.{w}) (internalExternalIso J) ≪≫
    Functor.rightUnitor _

end ConstantSheaf

end Stacks.Sites.GrpPullback

end
