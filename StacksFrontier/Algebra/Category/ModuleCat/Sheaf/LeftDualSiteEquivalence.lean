module

public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualRingedSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.WhiskerRestrictionMonoidal

/-!
# Duals of sheaves of modules through an equivalence of sites

Let `e : C' ≌ C` be an equivalence of sites, continuous in both directions and cocontinuous in the
forward one, and let `O` be a sheaf of rings on `C` valued in `CommRingCat.{max u' v'}`, where `u'`
and `v'` are the universes of the objects and arrows of `C'`. A sheaf of `O`-modules whose
transport along `e` is locally a direct summand of a finite free module has a right dual. For a
small model `C' : Type u'` with `Category.{u'} C'` of a site `C`, this gives the duality for
sheaves of modules on a site whose objects lie one universe above its arrows.

## Main definitions

* `Stacks.SheafOfModules.ReindexLeftDual.reindexRingPresheaf`: the structure presheaf of the
  reindexed site.
* `Stacks.SheafOfModules.ReindexLeftDual.reindexLocalized`: the transport along `e` between the two
  type synonyms carrying the localized monoidal structures.
* `Stacks.SheafOfModules.ReindexLeftDual.reindexLocalizedMonoidal`: the monoidal structure of
  `reindexLocalized`.
* `Stacks.SheafOfModules.ReindexLeftDual.reindexAdj`: the adjunction exhibiting
  `reindexLocalized` as an equivalence.

## Main results

* `Stacks.SheafOfModules.ReindexLeftDual.reindexIsSheaf`: the reindexed structure presheaf is a
  sheaf.
* `Stacks.SheafOfModules.ReindexLeftDual.reindexHasRightDualStrict` and
  `reindexHasRightDualLocalized`: on the reindexed site, a sheaf of modules locally a direct
  summand of a finite free module has a right dual, in the strict and in the localized monoidal
  structure.
* `Stacks.SheafOfModules.ReindexLeftDual.hasRightDualOfReindexLocalSummand` and
  `hasRightDualOfReindexLocalSummandExplicit`: a sheaf of `O`-modules whose transport along `e` is
  locally a direct summand of a finite free module has a right dual.

## References

* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ)
* [Stacks Project, Tag 0FFP](https://stacks.math.columbia.edu/tag/0FFP)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Localization

universe v u v' u'

namespace Stacks.SheafOfModules.ReindexLeftDual

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  (O : Cᵒᵖ ⥤ CommRingCat.{max u' v'})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  (e : C' ≌ C) [e.functor.IsContinuous J' J]

/-- The structure presheaf of the site `(C', J')`, obtained from `O` by restriction of sections
along `e.functor`. -/
abbrev reindexRingPresheaf : C'ᵒᵖ ⥤ CommRingCat.{max u' v'} := e.functor.op ⋙ O

include hO in
/-- The reindexed structure presheaf `reindexRingPresheaf O e` is a sheaf for `J'`. -/
theorem reindexIsSheaf :
    Presheaf.IsSheaf J' (TensorSheafification.structureRingPresheaf (reindexRingPresheaf O e)) :=
  TensorPower.whiskerStructureIsSheaf (J' := J') O hO e.functor

variable [e.inverse.IsContinuous J J'] [e.functor.IsCocontinuous J' J]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u' v'}]
  [HasWeakSheafify J AddCommGrpCat.{max u' v'}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max u' v'}]
  [HasWeakSheafify J' AddCommGrpCat.{max u' v'}]
  [∀ V : C', HasWeakSheafify (J'.over V) AddCommGrpCat.{max u' v'}]
  [∀ V : C', (J'.over V).WEqualsLocallyBijective AddCommGrpCat.{max u' v'}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u' v'} RingCat.{max u' v'})]
  [J'.HasSheafCompose (forget₂ CommRingCat.{max u' v'} RingCat.{max u' v'})]
  (hO' : Presheaf.IsSheaf J'
    (TensorSheafification.structureRingPresheaf (reindexRingPresheaf O e)))

section Strict

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory
  monoidalCategoryPresheafOfModules

/-- A sheaf of modules on the reindexed site `(C', J')` that is locally a direct summand of a
finite free module has a right dual in `Stacks.SheafOfModules.Strict.monoidalCategory`. -/
@[instance_reducible]
noncomputable def reindexHasRightDualStrict
    (N : _root_.SheafOfModules.{max u' v'}
      (TensorSheafification.structureSheaf (reindexRingPresheaf O e) hO'))
    (hN : IsLocallyDirectSummandOfFiniteFree (reindexRingPresheaf O e) hO' N) :
    HasRightDual N :=
  hasRightDualOfLocalSummand (J := J') (reindexRingPresheaf O e) hO' N hN

end Strict

section Localized

open Stacks.SheafOfModules.SliceRestriction

/-- A sheaf of modules on the reindexed site `(C', J')` that is locally a direct summand of a
finite free module has the right dual `Stacks.SheafOfModules.dualSheaf` in the localized monoidal
structure `Stacks.SheafOfModules.monoidalCategory`. -/
@[instance_reducible]
noncomputable def reindexHasRightDualLocalized
    (N : localizedSrc (reindexRingPresheaf O e) hO')
    (hN : IsLocallyDirectSummandOfFiniteFree (reindexRingPresheaf O e) hO' N) :
    HasRightDual N :=
  letI := Stacks.SheafOfModules.Strict.monoidalCategory (J := J') (reindexRingPresheaf O e) hO'
  letI : (fromLocalizedMonoidal (reindexRingPresheaf O e) hO').Monoidal :=
    fromLocalizedMonoidalMonoidal (reindexRingPresheaf O e) hO'
  letI : (fromLocalizedMonoidal (reindexRingPresheaf O e) hO').Full := ⟨fun f ↦ ⟨f, rfl⟩⟩
  letI : (fromLocalizedMonoidal (reindexRingPresheaf O e) hO').Faithful := ⟨fun h ↦ h⟩
  letI := monoidalCategoryPresheafOfModules (reindexRingPresheaf O e)
  letI : ExactPairing
      ((fromLocalizedMonoidal (reindexRingPresheaf O e) hO').obj N)
      ((fromLocalizedMonoidal (reindexRingPresheaf O e) hO').obj
        (dualSheaf (reindexRingPresheaf O e) hO' N)) :=
    exactPairingDualSheafOfLocalSummand (J := J') (reindexRingPresheaf O e) hO' N hN
  { rightDual := dualSheaf (reindexRingPresheaf O e) hO' N
    exact := ExactPairing.ofFullyFaithful
      (fromLocalizedMonoidal (reindexRingPresheaf O e) hO') N _ }

end Localized

section Transport

open Stacks.SheafOfModules.SliceRestriction Stacks.SheafOfModules.RestrictionMonoidal

/-- The transport of sheaves of modules along `e`, as a functor between the two type synonyms
carrying the localized monoidal structures. -/
noncomputable abbrev reindexLocalized :
    localizedSrc O hO ⥤ localizedSrc (reindexRingPresheaf O e) hO' :=
  TensorPower.whiskerRestriction (J' := J') O hO e.functor

/-- The functor `reindexLocalized` is monoidal for the localized monoidal structures. -/
@[instance_reducible]
noncomputable def reindexLocalizedMonoidal : (reindexLocalized O hO e hO').Monoidal :=
  whiskerRestrictionLocalizedMonoidal O hO e.functor

/-- `reindexLocalized` is an equivalence, with the inverse of
`Stacks.SheafOfModules.reindexEquivalence` as its right adjoint. -/
noncomputable def reindexAdj :
    reindexLocalized O hO e hO' ⊣
      (Stacks.SheafOfModules.reindexEquivalence (J' := J') e
        (TensorSheafification.structureSheaf O hO)).inverse :=
  (Stacks.SheafOfModules.reindexEquivalence (J' := J') e
    (TensorSheafification.structureSheaf O hO)).toAdjunction

/-- The functor `reindexLocalized` is an equivalence of categories. -/
instance isEquivalence_reindexLocalized : (reindexLocalized O hO e hO').IsEquivalence :=
  inferInstanceAs (Stacks.SheafOfModules.reindexEquivalence (J' := J') e
    (TensorSheafification.structureSheaf O hO)).functor.IsEquivalence

/-- A sheaf of `O`-modules whose transport along `e` is locally a direct summand of a finite free
module has a right dual in the localized monoidal structure. -/
@[instance_reducible]
noncomputable def hasRightDualOfReindexLocalSummand (M : localizedSrc O hO)
    (hM : IsLocallyDirectSummandOfFiniteFree (reindexRingPresheaf O e) hO'
      ((reindexLocalized O hO e hO').obj M)) :
    HasRightDual M :=
  letI := reindexLocalizedMonoidal O hO e hO'
  letI := reindexHasRightDualLocalized.{v, u, v', u'} O e hO'
    ((reindexLocalized O hO e hO').obj M) hM
  hasRightDualOfEquivalence (reindexAdj O hO e hO') M

/-- A sheaf of `O`-modules whose transport along `e` is locally a direct summand of a finite free
module has a right dual in `Stacks.SheafOfModules.monoidalCategory`. -/
@[instance_reducible]
noncomputable def hasRightDualOfReindexLocalSummandExplicit
    (M : _root_.SheafOfModules.{max u' v'} (TensorSheafification.structureSheaf O hO))
    (hM : IsLocallyDirectSummandOfFiniteFree (reindexRingPresheaf O e) hO'
      ((TensorPower.whiskerRestriction (J' := J') O hO e.functor).obj M)) :
    letI := Stacks.SheafOfModules.monoidalCategory O hO
    HasRightDual M :=
  hasRightDualOfReindexLocalSummand O hO e hO' M hM

end Transport

end Stacks.SheafOfModules.ReindexLeftDual

end
