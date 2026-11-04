module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafification
public import StacksFrontier.CategoryTheory.Sites.Point.SkyscraperStalkSplitting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction to an object and the constant sheaf, read on internal commutative groups

An abelian sheaf on a site is a commutative group object in its sheaves of sets
(`CategoryTheory.Sites.AbelianSheaf.equivalence`). This file records that two further functors
are compatible with that identification: restriction to an object of the site, and the constant
sheaf functor.

Both are needed to read an argument about sheaves of sets on sheaves of abelian groups when the
argument is phrased in terms of restrictions and of local constancy, since `IsLocallyConstant`
is stated with `GrothendieckTopology.overPullback` and `constantSheaf`.

Restriction is elementary: `J.overPullback A U` is restriction of presheaves along
`(Over.forget U).op` with no sheafification, so the comparison is the identity on sections and
the work is already done by `Stacks.Sites.AbelianPullback.precompInternalIso` and
`Stacks.Sites.AbelianPullback.sheafToPresheafInternalIso`; the only step not available off the
shelf is that the two ways of composing the restriction with the inclusion of sheaves into
presheaves carry different braidings, which `Stacks.Sites.AbelianPullback.mapCommGrpBraidedIso`
bridges. The comparison is then obtained at the level of presheaves and transported back along
the fully faithful `(sheafToPresheaf _ _).mapCommGrp` with
`CategoryTheory.fullyFaithfulCancelRight`.

The constant sheaf is not elementary, because it sheafifies: `constantSheaf J A` is
`Functor.const Cᵒᵖ ⋙ presheafToSheaf J A`. The constant *presheaf* half is again identity on
sections (`constPresheafInternalIso`), and the sheafification half is
`Stacks.Sites.AbelianPullback.sheafificationInternalIso`, which is proved by uniqueness of left
adjoints.

Each comparison is given in two forms, one for each direction of the equivalence between abelian
sheaves and internal commutative groups: an `internalSheaf` form, used to push a hypothesis about
abelian sheaves into sheaves of sets, and an `externalSheaf` form, used to read a conclusion
back. The second is deduced from the first by conjugating with
`CategoryTheory.Sites.AbelianSheaf.internalExternalIso` and `.externalInternalIso`, never
reproved.

## Main definitions

* `Stacks.Sites.AbelianPullback.overPullbackInternalIso` — restriction to an object of the site
  commutes with internalizing the group operations.
* `Stacks.Sites.AbelianPullback.overPullbackExternalIso` — the same, read in the direction of
  `externalSheaf`.
* `Stacks.Sites.AbelianPullback.constPresheafInternalIso` — the constant presheaf on an abelian
  group, internalized, is the constant presheaf on the internal commutative group.
* `Stacks.Sites.AbelianPullback.constantSheafInternalIso` — the constant abelian sheaf on an
  abelian group, internalized, is the constant sheaf of sets on the internal commutative group
  with its induced operations.
* `Stacks.Sites.AbelianPullback.constantSheafExternalIso` — the same, read in the direction of
  `externalSheaf`.

## Implementation notes

Every statement fixes its braidings as `CategoryTheory.Functor.Braided.ofChosenFiniteProducts`
through a `letI` in the type, as `precompInternalIso` and `cocontinuousAbelianInverseImageIso`
do: the braiding obtained from instance search on a composite is a different term, and a
consumer which lets instance search choose would not be able to apply these comparisons.

The chains are split into separately named links rather than written as one term. This is not
cosmetic: a single declaration carrying two crossings between sheaves of abelian groups and
internal commutative groups does not elaborate inside the per-declaration budget.

## References

* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sites CategoryTheory.Sites.AbelianSheaf Opposite
open Stacks.Topos.Skyscraper

universe w

namespace Stacks.Sites.AbelianPullback

attribute [local instance] cartesianPresheafTypes braidedPresheafTypes cartesianSheafTypes
  braidedSheafTypes braidedSheafToPresheafTypes

/-! ### Restriction to an object of the site -/

section OverPullback

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C) (U : C)

/-- Restriction of presheaves of sets along `(Over.forget U).op`, the functor out of which
`GrothendieckTopology.overPullback` for sheaves of sets is built. -/
public abbrev overForgetRestrictTypes :=
  (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type w)).obj (Over.forget U).op

/-- Restriction of abelian presheaves along `(Over.forget U).op`, the functor out of which
`GrothendieckTopology.overPullback` for abelian sheaves is built. -/
public abbrev overForgetRestrictAb :=
  (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ AddCommGrpCat.{w}).obj (Over.forget U).op

/-- First link: the restriction to `C/U` of an abelian sheaf, internalized and read as presheaves
of sets, is the underlying abelian presheaf restricted along `(Over.forget U).op` and then
internalized. This is `sheafToPresheafInternalIso` on the localized site, together with the
definitional identity `J.overPullback A U ⋙ sheafToPresheaf (J.over U) A =
sheafToPresheaf J A ⋙ (whiskeringLeft _ _ A).obj (Over.forget U).op`. -/
public def overPullbackInternalPresheafIso :
    (J.overPullback AddCommGrpCat.{w} U ⋙ internalSheaf (J.over U)) ⋙
        (sheafToPresheaf (J.over U) (Type w)).mapCommGrp ≅
      (sheafToPresheaf J AddCommGrpCat.{w} ⋙ overForgetRestrictAb U) ⋙ presheafCommGrp :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sheafToPresheafInternalIso (J.over U)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Second link: internalizing commutes with restricting an abelian presheaf along
`(Over.forget U).op`. This is `precompInternalIso` at that functor, preceded and followed by
`sheafToPresheafInternalIso` on `C` itself. -/
public def overForgetRestrictInternalIso :
    letI : (overForgetRestrictTypes (C := C) U).Braided := .ofChosenFiniteProducts _
    (sheafToPresheaf J AddCommGrpCat.{w} ⋙ overForgetRestrictAb U) ⋙ presheafCommGrp ≅
      (internalSheaf J ⋙ (sheafToPresheaf J (Type w)).mapCommGrp) ⋙
        (overForgetRestrictTypes (C := C) U).mapCommGrp := by
  letI : (overForgetRestrictTypes (C := C) U).Braided := .ofChosenFiniteProducts _
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (precompInternalIso (Over.forget U).op) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafToPresheafInternalIso J) _

/-- Third link: the restriction of presheaves of sets along `(Over.forget U).op`, read on
internal commutative groups, is the restriction of sheaves of sets to `C/U` followed by the
inclusion of sheaves into presheaves. The two composites are the same functor, but the braiding
instance search produces for each of them is a different term, which is why
`mapCommGrpBraidedIso` appears. -/
public def overPullbackMapCommGrpIso :
    letI : (overForgetRestrictTypes (C := C) U).Braided := .ofChosenFiniteProducts _
    letI : (J.overPullback (Type w) U).Braided := .ofChosenFiniteProducts _
    (internalSheaf J ⋙ (sheafToPresheaf J (Type w)).mapCommGrp) ⋙
        (overForgetRestrictTypes (C := C) U).mapCommGrp ≅
      (internalSheaf J ⋙ (J.overPullback (Type w) U).mapCommGrp) ⋙
        (sheafToPresheaf (J.over U) (Type w)).mapCommGrp := by
  letI : (overForgetRestrictTypes (C := C) U).Braided := .ofChosenFiniteProducts _
  letI : (J.overPullback (Type w) U).Braided := .ofChosenFiniteProducts _
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapCommGrpCompIso
      (F := sheafToPresheaf J (Type w)) (G := overForgetRestrictTypes (C := C) U)).symm ≪≫
    Functor.isoWhiskerLeft _ (mapCommGrpBraidedIso
      (J.overPullback (Type w) U ⋙ sheafToPresheaf (J.over U) (Type w))
      (Functor.Braided.instComp (sheafToPresheaf J (Type w))
        (overForgetRestrictTypes (C := C) U)) inferInstance) ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapCommGrpCompIso
      (F := J.overPullback (Type w) U) (G := sheafToPresheaf (J.over U) (Type w))) ≪≫
    (Functor.associator _ _ _).symm

/-- **Restriction to an object of the site commutes with internalization.** Internalizing the
group operations of the restriction of an abelian sheaf to `C/U` gives the restriction to `C/U`
of its internalization.

The three links above prove this after composing with the inclusion of sheaves into presheaves,
read on commutative group objects; that functor is fully faithful, so the comparison descends by
`CategoryTheory.fullyFaithfulCancelRight`. -/
public def overPullbackInternalIso :
    letI : (J.overPullback (Type w) U).Braided := .ofChosenFiniteProducts _
    J.overPullback AddCommGrpCat.{w} U ⋙ internalSheaf (J.over U) ≅
      internalSheaf J ⋙ (J.overPullback (Type w) U).mapCommGrp := by
  letI : (overForgetRestrictTypes (C := C) U).Braided := .ofChosenFiniteProducts _
  letI : (J.overPullback (Type w) U).Braided := .ofChosenFiniteProducts _
  exact fullyFaithfulCancelRight _
    (overPullbackInternalPresheafIso J U ≪≫ overForgetRestrictInternalIso J U ≪≫
      overPullbackMapCommGrpIso J U)

/-- **Restriction to an object of the site commutes with reading internal operations
sectionwise**, the form of `overPullbackInternalIso` for `externalSheaf`. Obtained from it by
conjugating with the unit and counit of the equivalence between abelian sheaves and internal
commutative groups. -/
public def overPullbackExternalIso :
    letI : (J.overPullback (Type w) U).Braided := .ofChosenFiniteProducts _
    externalSheaf J ⋙ J.overPullback AddCommGrpCat.{w} U ≅
      (J.overPullback (Type w) U).mapCommGrp ⋙ externalSheaf (J.over U) := by
  letI : (J.overPullback (Type w) U).Braided := .ofChosenFiniteProducts _
  exact (Functor.rightUnitor (externalSheaf J ⋙ J.overPullback AddCommGrpCat.{w} U)).symm ≪≫
    Functor.isoWhiskerLeft (externalSheaf J ⋙ J.overPullback AddCommGrpCat.{w} U)
      (internalExternalIso (J.over U)).symm ≪≫
    Functor.isoWhiskerLeft (externalSheaf J)
      (Functor.isoWhiskerRight (overPullbackInternalIso J U) (externalSheaf (J.over U))) ≪≫
    Functor.isoWhiskerRight (externalInternalIso J)
      ((J.overPullback (Type w) U).mapCommGrp ⋙ externalSheaf (J.over U)) ≪≫
    Functor.leftUnitor _

end OverPullback

/-! ### The constant sheaf -/

section ConstantSheaf

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)

/-- **The constant presheaf commutes with internalization.** The constant abelian presheaf on an
abelian group, with its operations internalized, is the constant presheaf on the corresponding
internal commutative group in sets.

The comparison is the identity on sections; what has to be checked is that it is additive, and
that is the statement that the monoidal structure of `Functor.const` is computed sectionwise,
namely `CategoryTheory.Functor.Monoidal.μ_fst` and `.μ_snd`. -/
public def constPresheafInternalIso :
    letI : (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)).Braided := .ofChosenFiniteProducts _
    (Functor.const Cᵒᵖ : AddCommGrpCat.{w} ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{w})) ⋙ presheafCommGrp ≅
      commGrpAddEquivalence.inverse ⋙
        (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)).mapCommGrp := by
  letI : (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)).Braided := .ofChosenFiniteProducts _
  refine NatIso.ofComponents (fun E => CommGrp.mkIso (Iso.refl _) ?_ ?_) ?_
  · rfl
  · let A' := commGrpAddEquivalence.inverse.obj E
    let R := (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w))
    let : R.Monoidal := (inferInstance : R.Braided).toMonoidal
    ext V x
    let add := @Add.add (((Functor.const Cᵒᵖ).obj E).obj V) inferInstance
    change add ((CartesianMonoidalCategory.fst (R.obj A'.X) (R.obj A'.X)).app V x)
        ((CartesianMonoidalCategory.snd (R.obj A'.X) (R.obj A'.X)).app V x) =
      add ((Functor.LaxMonoidal.μ R A'.X A'.X ≫ R.map
            (CartesianMonoidalCategory.fst A'.X A'.X)).app V x)
        ((Functor.LaxMonoidal.μ R A'.X A'.X ≫ R.map
            (CartesianMonoidalCategory.snd A'.X A'.X)).app V x)
    exact congrArg₂ add
      (ConcreteCategory.congr_hom (congr_app (Functor.Monoidal.μ_fst R A'.X A'.X) V) x).symm
      (ConcreteCategory.congr_hom (congr_app (Functor.Monoidal.μ_snd R A'.X A'.X) V) x).symm
  · intro A B g
    apply CommGrp.hom_ext
    rfl

/-- **Sheafification commutes with internalization**, in the direction of `internalSheaf`. This
is `sheafificationInternalIso` with the equivalence between abelian sheaves and internal
commutative groups applied to its right-hand side. -/
public def presheafToSheafInternalIso :
    letI : (presheafToSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
    presheafToSheaf J AddCommGrpCat.{w} ⋙ internalSheaf J ≅
      presheafCommGrp ⋙ (presheafToSheaf J (Type w)).mapCommGrp := by
  letI : (presheafToSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
  exact (Functor.isoWhiskerRight (sheafificationInternalIso J) (internalSheaf J)).symm ≪≫
    Functor.isoWhiskerLeft (presheafCommGrp ⋙ (presheafToSheaf J (Type w)).mapCommGrp)
      (externalInternalIso J) ≪≫
    Functor.rightUnitor _

/-- The constant sheaf functor on sheaves of sets preserves finite products: it is the constant
presheaf functor, which does, followed by sheafification, which is left exact. -/
@[sga "3 I 1.8" "special case"]
public instance preservesFiniteProducts_constantSheaf :
    PreservesFiniteProducts (constantSheaf J (Type w)) :=
  inferInstanceAs (PreservesFiniteProducts (Functor.const Cᵒᵖ ⋙ presheafToSheaf J (Type w)))

/-- **The constant sheaf commutes with internalization.** The constant abelian sheaf on an
abelian group, with its operations internalized, is the constant sheaf of sets on the
corresponding internal commutative group, with the operations induced on it.

The constant sheaf functor is the constant presheaf functor followed by sheafification, and the
two halves are `constPresheafInternalIso` and `presheafToSheafInternalIso`. -/
public def constantSheafInternalIso :
    letI : (constantSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
    constantSheaf J AddCommGrpCat.{w} ⋙ internalSheaf J ≅
      commGrpAddEquivalence.inverse ⋙ (constantSheaf J (Type w)).mapCommGrp := by
  letI : (presheafToSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
  letI : (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)).Braided := .ofChosenFiniteProducts _
  letI : (constantSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
  exact Functor.isoWhiskerLeft
      (Functor.const Cᵒᵖ : AddCommGrpCat.{w} ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{w}))
      (presheafToSheafInternalIso J) ≪≫
    Functor.isoWhiskerRight (constPresheafInternalIso (C := C))
      ((presheafToSheaf J (Type w)).mapCommGrp) ≪≫
    Functor.isoWhiskerLeft commGrpAddEquivalence.inverse
      (Functor.mapCommGrpCompIso (F := (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)))
        (G := presheafToSheaf J (Type w))).symm ≪≫
    Functor.isoWhiskerLeft commGrpAddEquivalence.inverse
      (mapCommGrpBraidedIso (constantSheaf J (Type w))
        (Functor.Braided.instComp (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w))
          (presheafToSheaf J (Type w))) inferInstance)

/-- **The constant sheaf commutes with reading internal operations sectionwise**, the form of
`constantSheafInternalIso` for `externalSheaf`. Obtained from it by conjugating with the unit and
counit of the equivalence between abelian sheaves and internal commutative groups. -/
public def constantSheafExternalIso :
    letI : (constantSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
    commGrpAddEquivalence.inverse ⋙ (constantSheaf J (Type w)).mapCommGrp ⋙
        externalSheaf J ≅
      constantSheaf J AddCommGrpCat.{w} := by
  letI : (constantSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
  exact (Functor.isoWhiskerRight (constantSheafInternalIso J) (externalSheaf J)).symm ≪≫
    Functor.isoWhiskerLeft (constantSheaf J AddCommGrpCat.{w}) (internalExternalIso J) ≪≫
    Functor.rightUnitor _

end ConstantSheaf

end Stacks.Sites.AbelianPullback

end
