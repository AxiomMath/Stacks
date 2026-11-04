module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import StacksFrontier.CategoryTheory.Monoidal.RingObjTypes
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianInternalization
public import StacksFrontier.CategoryTheory.Sites.RingSheafification

/-!
# Restriction to an object and the constant sheaf, read on internal ring objects

A sheaf of rings on a site is a ring object in its sheaves of sets
(`CategoryTheory.Sites.RingSheaf.equivalence`). This file records that two further functors are
compatible with that identification: restriction to an object of the site, and the constant
sheaf functor.

Both are needed to read an argument about sheaves of sets on sheaves of rings when the argument
is phrased in terms of restrictions and of local constancy, since
`Stacks.ConstantSheaf.IsLocallyConstant` is stated with `GrothendieckTopology.overPullback` and
`constantSheaf`.

Restriction is elementary: `J.overPullback A U` is restriction of presheaves along
`(Over.forget U).op` with no sheafification, so the comparison is the identity on sections and
the work is already done by `Stacks.Sites.RingPullback.precompInternalIso` and
`Stacks.Sites.RingPullback.sheafToPresheafInternalIso`; the only step not available off the
shelf is that the two ways of composing the restriction with the inclusion of sheaves into
presheaves carry different braidings, which `Stacks.Sites.RingPullback.mapRingBraidedIso`
bridges. The comparison is then obtained at the level of presheaves and transported back along
the fully faithful `(sheafToPresheaf _ _).mapRing` with
`CategoryTheory.fullyFaithfulCancelRight`.

The constant sheaf is not elementary, because it sheafifies: `constantSheaf J A` is
`Functor.const Cᵒᵖ ⋙ presheafToSheaf J A`. The constant *presheaf* half is again identity on
sections (`constPresheafInternalIso`), and the sheafification half is
`Stacks.Sites.RingPullback.sheafificationInternalIso`, which is proved by uniqueness of left
adjoints.

Each comparison is given in two forms, one for each direction of the equivalence between sheaves
of rings and internal ring objects: an `internalSheaf` form, used to push a hypothesis about
sheaves of rings into sheaves of sets, and an `externalSheaf` form, used to read a conclusion
back. The second is deduced from the first by conjugating with
`CategoryTheory.Sites.RingSheaf.internalExternalIso` and `.externalInternalIso`, never reproved.

This is the ring-level companion of
`StacksFrontier/CategoryTheory/Sites/LocallyConstant/AbelianInternalization.lean`, which is
imported for the coefficient-free `Stacks.Sites.AbelianPullback.overForgetRestrictTypes` and for
the instance `Stacks.Sites.AbelianPullback.preservesFiniteProducts_constantSheaf`, neither of
which mentions a ring.

## Main definitions

* `Stacks.Sites.RingPullback.overPullbackInternalIso` — restriction to an object of the site
  commutes with internalizing the ring operations.
* `Stacks.Sites.RingPullback.overPullbackExternalIso` — the same, read in the direction of
  `externalSheaf`.
* `Stacks.Sites.RingPullback.constPresheafInternalIso` — the constant presheaf on a ring,
  internalized, is the constant presheaf on the internal ring object.
* `Stacks.Sites.RingPullback.constantSheafInternalIso` — the constant sheaf of rings on a ring,
  internalized, is the constant sheaf of sets on the internal ring object with its induced
  operations.
* `Stacks.Sites.RingPullback.constantSheafExternalIso` — the same, read in the direction of
  `externalSheaf`.

## Implementation notes

Every statement fixes its braidings as `CategoryTheory.Functor.Braided.ofChosenFiniteProducts`
through a `letI` in the type, as `Stacks.Sites.RingPullback.precompInternalIso` does: the
braiding obtained from instance search on a composite is a different term, and a consumer which
lets instance search choose would not be able to apply these comparisons.

The chains are split into separately named links rather than written as one term. This is not
cosmetic: a single declaration carrying two crossings between sheaves of rings and internal ring
objects does not elaborate inside the per-declaration budget.

## References

* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

-- Internal algebraic objects in sheaves of sets are taken for the `⨯` products.
open scoped Stacks.SheafLimitsProd

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Sites CategoryTheory.Sites.RingSheaf Opposite
open Stacks.Sites.AbelianPullback (overForgetRestrictTypes)

universe w

namespace Stacks.Sites.RingPullback

attribute [local instance] Stacks.Sites.AbelianPullback.cartesianPresheafTypes
  Stacks.Sites.AbelianPullback.braidedPresheafTypes Stacks.Sites.AbelianPullback.cartesianSheafTypes
  Stacks.Sites.AbelianPullback.braidedSheafTypes
  Stacks.Sites.AbelianPullback.braidedSheafToPresheafTypes

/-! ### Restriction to an object of the site -/

section OverPullback

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C) (U : C)

/-- Restriction of presheaves of rings along `(Over.forget U).op`, the functor out of which
`GrothendieckTopology.overPullback` for sheaves of rings is built. -/
public abbrev overForgetRestrictRing :=
  (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ RingCat.{w}).obj (Over.forget U).op

/-- First link: the restriction to `C/U` of a sheaf of rings, internalized and read as presheaves
of sets, is the underlying presheaf of rings restricted along `(Over.forget U).op` and then
internalized. This is `sheafToPresheafInternalIso` on the localized site, together with the
definitional identity `J.overPullback A U ⋙ sheafToPresheaf (J.over U) A =
sheafToPresheaf J A ⋙ (whiskeringLeft _ _ A).obj (Over.forget U).op`. -/
public def overPullbackInternalPresheafIso :
    (J.overPullback RingCat.{w} U ⋙ internalSheaf (J.over U)) ⋙
        (sheafToPresheaf (J.over U) (Type w)).mapRing ≅
      (sheafToPresheaf J RingCat.{w} ⋙ overForgetRestrictRing U) ⋙ presheafRing :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sheafToPresheafInternalIso (J.over U)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Second link: internalizing commutes with restricting a presheaf of rings along
`(Over.forget U).op`. This is `precompInternalIso` at that functor, preceded and followed by
`sheafToPresheafInternalIso` on `C` itself. -/
public def overForgetRestrictInternalIso :
    letI : (overForgetRestrictTypes (C := C) U).Braided := .ofChosenFiniteProducts _
    (sheafToPresheaf J RingCat.{w} ⋙ overForgetRestrictRing U) ⋙ presheafRing ≅
      (internalSheaf J ⋙ (sheafToPresheaf J (Type w)).mapRing) ⋙
        (overForgetRestrictTypes (C := C) U).mapRing := by
  let : (overForgetRestrictTypes (C := C) U).Braided := .ofChosenFiniteProducts _
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (precompInternalIso (Over.forget U).op) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafToPresheafInternalIso J) _

/-- Third link: the restriction of presheaves of sets along `(Over.forget U).op`, read on
internal ring objects, is the restriction of sheaves of sets to `C/U` followed by the inclusion
of sheaves into presheaves. The two composites are the same functor, but the braiding instance
search produces for each of them is a different term, which is why `mapRingBraidedIso`
appears. -/
public def overPullbackMapRingIso :
    letI : (overForgetRestrictTypes (C := C) U).Braided := .ofChosenFiniteProducts _
    letI : (J.overPullback (Type w) U).Braided := .ofChosenFiniteProducts _
    (internalSheaf J ⋙ (sheafToPresheaf J (Type w)).mapRing) ⋙
        (overForgetRestrictTypes (C := C) U).mapRing ≅
      (internalSheaf J ⋙ (J.overPullback (Type w) U).mapRing) ⋙
        (sheafToPresheaf (J.over U) (Type w)).mapRing := by
  let : (overForgetRestrictTypes (C := C) U).Braided := .ofChosenFiniteProducts _
  let : (J.overPullback (Type w) U).Braided := .ofChosenFiniteProducts _
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapRingCompIso
      (F := sheafToPresheaf J (Type w)) (G := overForgetRestrictTypes (C := C) U)).symm ≪≫
    Functor.isoWhiskerLeft _ (mapRingBraidedIso
      (J.overPullback (Type w) U ⋙ sheafToPresheaf (J.over U) (Type w))
      (Functor.Braided.instComp (sheafToPresheaf J (Type w))
        (overForgetRestrictTypes (C := C) U)) inferInstance) ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapRingCompIso
      (F := J.overPullback (Type w) U) (G := sheafToPresheaf (J.over U) (Type w))) ≪≫
    (Functor.associator _ _ _).symm

/-- **Restriction to an object of the site commutes with internalization.** Internalizing the
ring operations of the restriction of a sheaf of rings to `C/U` gives the restriction to `C/U` of
its internalization.

The three links above prove this after composing with the inclusion of sheaves into presheaves,
read on ring objects; that functor is fully faithful, so the comparison descends by
`CategoryTheory.fullyFaithfulCancelRight`. -/
public def overPullbackInternalIso :
    letI : (J.overPullback (Type w) U).Braided := .ofChosenFiniteProducts _
    J.overPullback RingCat.{w} U ⋙ internalSheaf (J.over U) ≅
      internalSheaf J ⋙ (J.overPullback (Type w) U).mapRing := by
  let : (overForgetRestrictTypes (C := C) U).Braided := .ofChosenFiniteProducts _
  let : (J.overPullback (Type w) U).Braided := .ofChosenFiniteProducts _
  exact fullyFaithfulCancelRight _
    (overPullbackInternalPresheafIso J U ≪≫ overForgetRestrictInternalIso J U ≪≫
      overPullbackMapRingIso J U)

/-- **Restriction to an object of the site commutes with reading internal operations
sectionwise**, the form of `overPullbackInternalIso` for `externalSheaf`. Obtained from it by
conjugating with the unit and counit of the equivalence between sheaves of rings and internal
ring objects. -/
public def overPullbackExternalIso :
    letI : (J.overPullback (Type w) U).Braided := .ofChosenFiniteProducts _
    externalSheaf J ⋙ J.overPullback RingCat.{w} U ≅
      (J.overPullback (Type w) U).mapRing ⋙ externalSheaf (J.over U) := by
  let : (J.overPullback (Type w) U).Braided := .ofChosenFiniteProducts _
  exact (Functor.rightUnitor (externalSheaf J ⋙ J.overPullback RingCat.{w} U)).symm ≪≫
    Functor.isoWhiskerLeft (externalSheaf J ⋙ J.overPullback RingCat.{w} U)
      (internalExternalIso (J.over U)).symm ≪≫
    Functor.isoWhiskerLeft (externalSheaf J)
      (Functor.isoWhiskerRight (overPullbackInternalIso J U) (externalSheaf (J.over U))) ≪≫
    Functor.isoWhiskerRight (externalInternalIso J)
      ((J.overPullback (Type w) U).mapRing ⋙ externalSheaf (J.over U)) ≪≫
    Functor.leftUnitor _

end OverPullback

/-! ### The constant sheaf -/

section ConstantSheaf

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)

/-- **The constant presheaf commutes with internalization.** The constant presheaf of rings on a
ring, with its operations internalized, is the constant presheaf on the corresponding internal
ring object in sets.

The comparison is the identity on sections; what has to be checked is that it is multiplicative
and additive, and that is the statement that the monoidal structure of `Functor.const` is
computed sectionwise, namely `CategoryTheory.Functor.Monoidal.μ_fst` and `.μ_snd`. -/
public def constPresheafInternalIso :
    letI : (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)).Braided := .ofChosenFiniteProducts _
    (Functor.const Cᵒᵖ : RingCat.{w} ⥤ (Cᵒᵖ ⥤ RingCat.{w})) ⋙ presheafRing ≅
      CategoryTheory.ringTypeEquivalenceRing.inverse ⋙
        (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)).mapRing := by
  let : (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)).Braided := .ofChosenFiniteProducts _
  refine NatIso.ofComponents (fun E => RingObjCat.mkIso (Iso.refl _) ?_ ?_ ?_ ?_) ?_
  · rfl
  · let A' := CategoryTheory.ringTypeEquivalenceRing.inverse.obj E
    let R := (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w))
    let : R.Monoidal := (inferInstance : R.Braided).toMonoidal
    ext V x
    let mul := @Mul.mul (((Functor.const Cᵒᵖ).obj E).obj V) inferInstance
    change mul ((CartesianMonoidalCategory.fst (R.obj A'.X) (R.obj A'.X)).app V x)
        ((CartesianMonoidalCategory.snd (R.obj A'.X) (R.obj A'.X)).app V x) =
      mul ((Functor.LaxMonoidal.μ R A'.X A'.X ≫ R.map
            (CartesianMonoidalCategory.fst A'.X A'.X)).app V x)
        ((Functor.LaxMonoidal.μ R A'.X A'.X ≫ R.map
            (CartesianMonoidalCategory.snd A'.X A'.X)).app V x)
    exact congrArg₂ mul
      (ConcreteCategory.congr_hom (congr_app (Functor.Monoidal.μ_fst R A'.X A'.X) V) x).symm
      (ConcreteCategory.congr_hom (congr_app (Functor.Monoidal.μ_snd R A'.X A'.X) V) x).symm
  · rfl
  · let A' := CategoryTheory.ringTypeEquivalenceRing.inverse.obj E
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
    apply RingObjCat.hom_ext
    rfl

/-- **Sheafification commutes with internalization**, in the direction of `internalSheaf`. This
is `sheafificationInternalIso` with the equivalence between sheaves of rings and internal ring
objects applied to its right-hand side. -/
public def presheafToSheafInternalIso :
    letI : (presheafToSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
    presheafToSheaf J RingCat.{w} ⋙ internalSheaf J ≅
      presheafRing ⋙ (presheafToSheaf J (Type w)).mapRing := by
  let : (presheafToSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
  exact (Functor.isoWhiskerRight (sheafificationInternalIso J) (internalSheaf J)).symm ≪≫
    Functor.isoWhiskerLeft (presheafRing ⋙ (presheafToSheaf J (Type w)).mapRing)
      (externalInternalIso J) ≪≫
    Functor.rightUnitor _

/-- **The constant sheaf commutes with internalization.** The constant sheaf of rings on a ring,
with its operations internalized, is the constant sheaf of sets on the corresponding internal
ring object, with the operations induced on it.

The constant sheaf functor is the constant presheaf functor followed by sheafification, and the
two halves are `constPresheafInternalIso` and `presheafToSheafInternalIso`. -/
public def constantSheafInternalIso :
    letI : (constantSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
    constantSheaf J RingCat.{w} ⋙ internalSheaf J ≅
      CategoryTheory.ringTypeEquivalenceRing.inverse ⋙ (constantSheaf J (Type w)).mapRing := by
  let : (presheafToSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
  let : (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)).Braided := .ofChosenFiniteProducts _
  let : (constantSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
  exact Functor.isoWhiskerLeft
      (Functor.const Cᵒᵖ : RingCat.{w} ⥤ (Cᵒᵖ ⥤ RingCat.{w}))
      (presheafToSheafInternalIso J) ≪≫
    Functor.isoWhiskerRight (constPresheafInternalIso (C := C))
      ((presheafToSheaf J (Type w)).mapRing) ≪≫
    Functor.isoWhiskerLeft CategoryTheory.ringTypeEquivalenceRing.inverse
      (Functor.mapRingCompIso (F := (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w)))
        (G := presheafToSheaf J (Type w))).symm ≪≫
    Functor.isoWhiskerLeft CategoryTheory.ringTypeEquivalenceRing.inverse
      (mapRingBraidedIso (constantSheaf J (Type w))
        (Functor.Braided.instComp (Functor.const Cᵒᵖ : Type w ⥤ (Cᵒᵖ ⥤ Type w))
          (presheafToSheaf J (Type w))) inferInstance)

/-- **The constant sheaf commutes with reading internal operations sectionwise**, the form of
`constantSheafInternalIso` for `externalSheaf`. Obtained from it by conjugating with the unit and
counit of the equivalence between sheaves of rings and internal ring objects. -/
public def constantSheafExternalIso :
    letI : (constantSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
    CategoryTheory.ringTypeEquivalenceRing.inverse ⋙ (constantSheaf J (Type w)).mapRing ⋙
        externalSheaf J ≅
      constantSheaf J RingCat.{w} := by
  let : (constantSheaf J (Type w)).Braided := .ofChosenFiniteProducts _
  exact (Functor.isoWhiskerRight (constantSheafInternalIso J) (externalSheaf J)).symm ≪≫
    Functor.isoWhiskerLeft (constantSheaf J RingCat.{w}) (internalExternalIso J) ≪≫
    Functor.rightUnitor _

end ConstantSheaf

end Stacks.Sites.RingPullback

end
