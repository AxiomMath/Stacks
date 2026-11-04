module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafOverSlice
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction of sheaves of modules along a functor of sites is a monoidal functor

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `H : C' ⥤ C` be continuous
and cocontinuous for a topology `J'` on `C'`.  Restriction of sections along `H` carries sheaves
of `O`-modules to sheaves of `H.op ⋙ O`-modules;  that functor is
`Stacks.SheafOfModules.TensorPower.whiskerRestriction`, which is `SheafOfModules.pushforward`
along `H` with the identity comparison of structure sheaves.  This file equips it with a
`CategoryTheory.Functor.Monoidal` structure, for both monoidal structures on sheaves of
modules: the localized one `Stacks.SheafOfModules.monoidalCategory` and the strict one
`Stacks.SheafOfModules.Strict.monoidalCategory`, whose tensor product is the tensor product sheaf
of Tag 01CA on the nose.

The two sites live in independent universe pairs, and neither is tied to the universe `w` of
the rings and the modules.  Specialized to an equivalence of sites, this makes
`Stacks.SheafOfModules.reindexEquivalence` a monoidal equivalence.

## Main definitions

* `Stacks.SheafOfModules.RestrictionMonoidal.presheafRestriction` and `restrictionSheafify`:
  restriction of presheaves of modules along `H`, and sheafification on `(C', J')`.
* `Stacks.SheafOfModules.RestrictionMonoidal.whiskerRestrictionStrict`: restriction read between
  the two spellings carrying the strict monoidal structure, as a composite of three monoidal
  functors.  It is the restriction functor itself, by `whiskerRestrictionStrict_eq`.
* `Stacks.SheafOfModules.RestrictionMonoidal.reindexFunctor`: the functor of
  `Stacks.SheafOfModules.reindexEquivalence` at a structure sheaf, retyped so that its target
  ring sheaf is spelled `Stacks.SheafOfModules.TensorSheafification.structureSheaf`.

## Main results

* `Stacks.SheafOfModules.RestrictionMonoidal.restrictionSheafifyIso`: sheafification commutes
  with restriction along `H`.
* `Stacks.SheafOfModules.RestrictionMonoidal.whiskerRestrictionMonoidalLocalized`:
  **restriction of sheaves of modules along a continuous and cocontinuous functor of sites is a
  monoidal functor** for `Stacks.SheafOfModules.monoidalCategory`.
* `Stacks.SheafOfModules.RestrictionMonoidal.whiskerRestrictionStrictMonoidal` and
  `whiskerRestrictionMonoidalStrict`: the same for
  `Stacks.SheafOfModules.Strict.monoidalCategory`, the second stated for
  `Stacks.SheafOfModules.TensorPower.whiskerRestriction` itself.
* `Stacks.SheafOfModules.RestrictionMonoidal.reindexMonoidalLocalized` and
  `reindexMonoidalStrict`: **the transport of sheaves of modules along an equivalence of sites is
  a monoidal functor**, for each of the two structures.
* `Stacks.SheafOfModules.RestrictionMonoidal.reindexFunctor_eq`: the retyped transport is the
  functor of `Stacks.SheafOfModules.reindexEquivalence`, on the nose.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG), method (2)
* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Localization

universe v u v' u' w

namespace Stacks.SheafOfModules.RestrictionMonoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  (H : C' ⥤ C) [H.IsContinuous J' J] [H.IsCocontinuous J' J]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J' AddCommGrpCat.{w}]

/-- Restriction of presheaves of modules along `H`, as Mathlib's
`PresheafOfModules.pushforward₀OfCommRingCat`, with its target written over
`Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (H.op ⋙ O)`. -/
noncomputable abbrev presheafRestriction :
    PresheafOfModules.{w} (TensorSheafification.structureRingPresheaf O) ⥤
      PresheafOfModules.{w} (TensorSheafification.structureRingPresheaf (H.op ⋙ O)) :=
  PresheafOfModules.pushforward₀OfCommRingCat.{w} H O

/-- Sheafification of presheaves of modules on `(C', J')`, over the restricted structure
sheaf. -/
noncomputable abbrev restrictionSheafify :
    PresheafOfModules.{w} (TensorSheafification.structureRingPresheaf (H.op ⋙ O)) ⥤
      _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf (H.op ⋙ O)
        (TensorPower.whiskerStructureIsSheaf (J' := J') O hO H)) :=
  sheafifyFunctor (H.op ⋙ O) (TensorPower.whiskerStructureIsSheaf (J' := J') O hO H)

/-- **Sheafification of presheaves of modules commutes with restriction along a continuous and
cocontinuous functor of sites**: this is
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyNatIso` with its two sides
exchanged and both ring sheaves written as structure sheaves. -/
noncomputable def restrictionSheafifyIso :
    sheafifyFunctor O hO ⋙ TensorPower.whiskerRestriction (J' := J') O hO H ≅
      presheafRestriction O H ⋙ restrictionSheafify O hO H :=
  (PushforwardSheafification.pushforwardSheafifyNatIso.{w} J' H
    (TensorSheafification.structureSheaf O hO)).symm

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategory

/-- The presheaf-level restriction along `H`, followed by sheafification on `(C', J')`, is
monoidal: the first is Mathlib's `PresheafOfModules.pushforward₀OfCommRingCat` and the second is
the monoidal localization functor. -/
@[instance_reducible]
noncomputable def restrictionCompSheafifyMonoidal :
    (presheafRestriction O H ⋙ restrictionSheafify (J' := J') O hO H).Monoidal :=
  letI := Stacks.SheafOfModules.sheafifyFunctor_monoidal (H.op ⋙ O)
    (TensorPower.whiskerStructureIsSheaf (J' := J') O hO H)
  inferInstance

/-- Restriction of sheaves of modules along `H` lifts the presheaf-level restriction followed by
sheafification, along sheafification on `(C, J)`. -/
noncomputable instance lifting :
    Localization.Lifting (sheafifyFunctor O hO) (localIso (J := J) O)
      (presheafRestriction O H ⋙ restrictionSheafify (J' := J') O hO H)
      (TensorPower.whiskerRestriction (J' := J') O hO H) :=
  ⟨restrictionSheafifyIso O hO H⟩

/-- **Restriction of sheaves of modules along a continuous and cocontinuous functor of sites is a
monoidal functor**, for the localized monoidal structure
`Stacks.SheafOfModules.monoidalCategory` of Tag 01CA on each side. -/
@[instance_reducible]
noncomputable def whiskerRestrictionMonoidalLocalized :
    (TensorPower.whiskerRestriction (J' := J') O hO H).Monoidal :=
  letI := Stacks.SheafOfModules.sheafifyFunctor_monoidal O hO
  letI := restrictionCompSheafifyMonoidal (J' := J') O hO H
  Localization.Monoidal.functorMonoidalOfComp (sheafifyFunctor O hO) (localIso (J := J) O)
    (TensorPower.whiskerRestriction (J' := J') O hO H)
    (presheafRestriction O H ⋙ restrictionSheafify (J' := J') O hO H)

/-- `whiskerRestrictionMonoidalLocalized` with both monoidal structures named explicitly,
outside the scope of any local instance: **restriction along `H` is a monoidal functor from
`Stacks.SheafOfModules.monoidalCategory` on `(C, J)` to
`Stacks.SheafOfModules.monoidalCategory` on `(C', J')`.** -/
@[instance_reducible]
noncomputable def whiskerRestrictionLocalizedMonoidalExplicit :
    letI := Stacks.SheafOfModules.monoidalCategory O hO
    letI := Stacks.SheafOfModules.monoidalCategory (H.op ⋙ O)
      (TensorPower.whiskerStructureIsSheaf (J' := J') O hO H)
    (TensorPower.whiskerRestriction (J' := J') O hO H).Monoidal :=
  whiskerRestrictionMonoidalLocalized O hO H

end Monoidal

section Strict

open Stacks.SheafOfModules.SliceRestriction Stacks.SheafOfModules.Strict

/-- Restriction along `H`, retyped between the two type synonyms carrying the localized monoidal
structures. -/
noncomputable abbrev whiskerRestrictionLocalized :
    localizedSrc O hO ⥤
      localizedSrc (H.op ⋙ O) (TensorPower.whiskerStructureIsSheaf (J' := J') O hO H) :=
  TensorPower.whiskerRestriction (J' := J') O hO H

/-- `whiskerRestrictionMonoidalLocalized`, read at the type-synonym spelling. -/
@[instance_reducible]
noncomputable def whiskerRestrictionLocalizedMonoidal :
    (whiskerRestrictionLocalized (J' := J') O hO H).Monoidal :=
  whiskerRestrictionMonoidalLocalized O hO H

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory

/-- Restriction of sheaves of modules along `H`, read between the two spellings carrying the
*strict* monoidal structure of Tag 01CA, as the composite of three functors each of which is
monoidal: the identity into the localized spelling, the restriction, and the identity back.  It
is the restriction functor itself, by `whiskerRestrictionStrict_eq`. -/
noncomputable abbrev whiskerRestrictionStrict :
    _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO) ⥤
      _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf (H.op ⋙ O)
        (TensorPower.whiskerStructureIsSheaf (J' := J') O hO H)) :=
  toLocalizedMonoidal O hO ⋙ whiskerRestrictionLocalized (J' := J') O hO H ⋙
    fromLocalizedMonoidal (H.op ⋙ O) (TensorPower.whiskerStructureIsSheaf (J' := J') O hO H)

omit [H.IsCocontinuous J' J] in
/-- `whiskerRestrictionStrict` is the restriction functor itself: the two outer factors are
identity functors. -/
theorem whiskerRestrictionStrict_eq :
    whiskerRestrictionStrict (J' := J') O hO H =
      TensorPower.whiskerRestriction (J' := J') O hO H :=
  rfl

/-- **Restriction of sheaves of modules along a continuous and cocontinuous functor of sites is a
monoidal functor for the strict monoidal structure of Tag 01CA**, whose tensor product is the
tensor product sheaf `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` on the nose. -/
@[instance_reducible]
noncomputable def whiskerRestrictionStrictMonoidal :
    (whiskerRestrictionStrict (J' := J') O hO H).Monoidal :=
  letI := whiskerRestrictionLocalizedMonoidal (J' := J') O hO H
  letI := toLocalizedMonoidalMonoidal O hO
  letI := fromLocalizedMonoidalMonoidal (H.op ⋙ O)
    (TensorPower.whiskerStructureIsSheaf (J' := J') O hO H)
  inferInstance

/-- **`whiskerRestrictionStrictMonoidal` stated for
`Stacks.SheafOfModules.TensorPower.whiskerRestriction`**, which equals `whiskerRestrictionStrict`
by `whiskerRestrictionStrict_eq`. -/
@[instance_reducible]
noncomputable def whiskerRestrictionMonoidalStrict :
    (TensorPower.whiskerRestriction (J' := J') O hO H).Monoidal :=
  whiskerRestrictionStrict_eq (J' := J') O hO H ▸ whiskerRestrictionStrictMonoidal O hO H

/-- `whiskerRestrictionMonoidalStrict` with both monoidal structures named explicitly, outside
the scope of any local instance: **restriction along `H` is a monoidal functor from
`Stacks.SheafOfModules.Strict.monoidalCategory` on `(C, J)` to
`Stacks.SheafOfModules.Strict.monoidalCategory` on `(C', J')`.** -/
@[instance_reducible, ega "IV 10.2.8" "special case"]
noncomputable def whiskerRestrictionStrictMonoidalExplicit :
    letI := Stacks.SheafOfModules.Strict.monoidalCategory O hO
    letI := Stacks.SheafOfModules.Strict.monoidalCategory (H.op ⋙ O)
      (TensorPower.whiskerStructureIsSheaf (J' := J') O hO H)
    (TensorPower.whiskerRestriction (J' := J') O hO H).Monoidal :=
  whiskerRestrictionMonoidalStrict O hO H

end Strict

/-! ### The special case of an equivalence of sites -/

section Equivalence

variable (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  [e.functor.IsCocontinuous J' J]

/-- The functor of `Stacks.SheafOfModules.reindexEquivalence` at a structure sheaf, with its
target ring sheaf spelled
`Stacks.SheafOfModules.TensorSheafification.structureSheaf (e.functor.op ⋙ O)` rather than
`Stacks.SheafOfModules.reindexRing`; the two sheaves of rings are equal by `rfl`. -/
noncomputable abbrev reindexFunctor :
    _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO) ⥤
      _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf (e.functor.op ⋙ O)
        (TensorPower.whiskerStructureIsSheaf (J' := J') O hO e.functor)) :=
  TensorPower.whiskerRestriction (J' := J') O hO e.functor

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J' AddCommGrpCat.{w}]
  [e.functor.IsCocontinuous J' J] in
/-- **`reindexFunctor` is the functor of `Stacks.SheafOfModules.reindexEquivalence`**, on the
nose: both are `SheafOfModules.pushforward` along `e.functor` with the identity comparison of
structure sheaves. -/
theorem reindexFunctor_eq :
    reindexFunctor (J' := J') O hO e =
      (Stacks.SheafOfModules.reindexEquivalence (J' := J') e
        (TensorSheafification.structureSheaf O hO)).functor :=
  rfl

/-- **The transport of sheaves of modules along an equivalence of sites is a monoidal
functor**, for the localized monoidal structure `Stacks.SheafOfModules.monoidalCategory` of
Tag 01CA on each side. -/
@[instance_reducible]
noncomputable def reindexMonoidalLocalized :
    letI := Stacks.SheafOfModules.monoidalCategory O hO
    letI := Stacks.SheafOfModules.monoidalCategory (e.functor.op ⋙ O)
      (TensorPower.whiskerStructureIsSheaf (J' := J') O hO e.functor)
    (reindexFunctor (J' := J') O hO e).Monoidal :=
  whiskerRestrictionLocalizedMonoidalExplicit O hO e.functor

/-- **The transport of sheaves of modules along an equivalence of sites is a monoidal
functor for the strict monoidal structure of Tag 01CA**, whose tensor product is the tensor
product sheaf on the nose. -/
@[instance_reducible]
noncomputable def reindexMonoidalStrict :
    letI := Stacks.SheafOfModules.Strict.monoidalCategory O hO
    letI := Stacks.SheafOfModules.Strict.monoidalCategory (e.functor.op ⋙ O)
      (TensorPower.whiskerStructureIsSheaf (J' := J') O hO e.functor)
    (reindexFunctor (J' := J') O hO e).Monoidal :=
  whiskerRestrictionStrictMonoidalExplicit O hO e.functor

end Equivalence

end Stacks.SheafOfModules.RestrictionMonoidal

end
