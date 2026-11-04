module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal
public import StacksFrontier.AlgebraicGeometry.SheafInternalHom.Basic

/-!
# Restriction to a slice site is monoidal for the internal-hom monoidal structure

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SliceRestrictionMonoidal.lean` makes restriction of
sheaves of modules to a slice site a monoidal functor for two of the three monoidal structures
this repository carries on `SheafOfModules`: the localized structure
`Stacks.SheafOfModules.monoidalCategory`, whose unit is `SheafOfModules.unit`, and the strict
structure `Stacks.SheafOfModules.Strict.monoidalCategory` of Tag 01CA. **This file supplies the
third**, `Stacks.SheafInternalHom.monoidalCategory`, which is the same localization of the
objectwise tensor product of presheaves of modules taken at the unit comparison isomorphism
`Iso.refl _` rather than `Stacks.SheafOfModules.sheafifyUnitIso`, so that its tensor unit is the
sheafification `(sheafify 𝒪 h𝒪).obj (𝟙_ _)` of the presheaf unit instead of
`SheafOfModules.unit`.

**The three are genuinely different `MonoidalCategory` terms**: the unit object is a parameter of
`CategoryTheory.LocalizedMonoidal`, so the two localized structures differ already in their unit
*objects*, and `rfl` does not identify them. Consequently neither
`Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidalLocalized` nor
`Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidal` is a `Functor.Monoidal` instance for
the structure used here.

Nothing is reproved. The construction is the one of
`Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidalLocalized` run again at the other unit
comparison: one application of `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` to the
`CategoryTheory.Localization.Lifting` isomorphism
`Stacks.SheafOfModules.SliceRestriction.sliceSheafifyIso` ("sheafification commutes with
restriction to a slice site"), which does not mention a monoidal structure and is reused as it
stands. The monoidality of sheafification at this unit is likewise already available:
`Stacks.SheafInternalHom.sheafifyMonoidal` is it, and is used here by retyping its source
category — `Stacks.SheafOfModules.sheafifyFunctor` is `@[reducible]` for
`Stacks.SheafOfModules.TensorSheafification.sheafify`, with the ring presheaf spelled so that
Mathlib's monoidal structure on presheaves of modules is found by instance search.

## Main definitions

* `Stacks.SheafInternalHom.SliceRestriction.sliceCompSheafifyMonoidal`: restriction of presheaves
  of modules to the slice site followed by sheafification there is monoidal.
* `Stacks.SheafInternalHom.SliceRestriction.overFunctorMonoidal`: **restriction of sheaves of
  modules to a slice site is a monoidal functor for
  `Stacks.SheafInternalHom.monoidalCategory`.**
* `Stacks.SheafInternalHom.SliceRestriction.overFunctorMonoidalExplicit`: the same with both
  monoidal structures named by `letI` in the statement, outside the scope of any local instance,
  so that it is a check and not a restatement.
* `Stacks.SheafInternalHom.SliceRestriction.schemeOpenRestriction` and
  `schemeOverFunctorMonoidal`: the same for a scheme, with the source category spelled
  `X.Modules` and the source monoidal structure
  `Stacks.SheafInternalHom.schemeMonoidalCategory`. This is the shape consumed by the
  twisted-section machinery of
  `StacksFrontier/AlgebraicGeometry/TwistedSectionModule/MonoidalFunctor.lean`, whose
  `Stacks.TwistedSections.twistPow` on `X.Modules` is taken at that structure.
* `Stacks.SheafInternalHom.SliceRestriction.schemeOpenRestrictionAdditive`: additivity of that
  restriction, likewise retyped.

## Implementation notes

The hypotheses are exactly those of the imported file: `J.WEqualsLocallyBijective AddCommGrpCat`
and `HasWeakSheafify J AddCommGrpCat` for `J` and for `J.over U`, which is what the two
sheafification functors need. No `GrothendieckTopology.HasSheafCompose` instance is required.

Each monoidal structure is introduced by `letI`, never by `have`: `Functor.Monoidal` and
`MonoidalCategory` are data classes, and a `have` would register an opaque local instance that
instance search prefers to the intended one.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Localization AlgebraicGeometry

universe v u w

namespace Stacks.SheafInternalHom.SliceRestriction

open Stacks.SheafOfModules.SliceRestriction
open Stacks.SheafOfModules (sheafifyFunctor)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  (U : C)
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

section Localized

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

/-- Restriction of presheaves of modules to the slice site over `U`, followed by sheafification
there, is monoidal: the first is Mathlib's `PresheafOfModules.pushforward₀OfCommRingCat` and the
second is the monoidal localization functor at the unit comparison `Iso.refl _`. -/
@[instance_reducible]
def sliceCompSheafifyMonoidal : (sliceFunctor 𝒪 U ⋙ sliceSheafify 𝒪 h𝒪 U).Monoidal :=
  letI : (sliceSheafify 𝒪 h𝒪 U).Monoidal :=
    Stacks.SheafInternalHom.sheafifyMonoidal (sliceRingPresheaf 𝒪 U)
      (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
  inferInstance

/-- **Restriction of sheaves of modules to a slice site is a monoidal functor** for
`Stacks.SheafInternalHom.monoidalCategory` on each side. -/
@[instance_reducible]
def overFunctorMonoidal : (overFunctor 𝒪 h𝒪 U).Monoidal :=
  letI : (sheafifyFunctor 𝒪 h𝒪).Monoidal := Stacks.SheafInternalHom.sheafifyMonoidal 𝒪 h𝒪
  letI := sliceCompSheafifyMonoidal 𝒪 h𝒪 U
  Localization.Monoidal.functorMonoidalOfComp (sheafifyFunctor 𝒪 h𝒪)
    (Stacks.SheafOfModules.localIso (J := J) 𝒪) (overFunctor 𝒪 h𝒪 U)
    (sliceFunctor 𝒪 U ⋙ sliceSheafify 𝒪 h𝒪 U)

end Localized

/-- `overFunctorMonoidal` with both monoidal structures named explicitly, outside the scope of
any local instance: **restriction to the slice site over `U` is a monoidal functor from
`Stacks.SheafInternalHom.monoidalCategory` on `C` to `Stacks.SheafInternalHom.monoidalCategory`
on `Over U`.** -/
@[instance_reducible]
def overFunctorMonoidalExplicit :
    letI := Stacks.SheafInternalHom.monoidalCategory 𝒪 h𝒪
    letI := Stacks.SheafInternalHom.monoidalCategory (sliceRingPresheaf 𝒪 U)
      (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
    (overFunctor 𝒪 h𝒪 U).Monoidal :=
  overFunctorMonoidal 𝒪 h𝒪 U

section Scheme

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory

/-- Restriction of the modules on a scheme to an open, **with the source category spelled
`AlgebraicGeometry.Scheme.Modules`**, which is the spelling the ampleness and section-ring
development uses. The retyping matters for instance search and not for the kernel: `X.Modules` is
`SheafOfModules X.ringCatSheaf`, and `X.ringCatSheaf` is
`Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf _` by
`Stacks.SheafInternalHom.structureSheaf_eq_ringCatSheaf`, but instance search is keyed
syntactically and the instances of the two spellings do not match each other. -/
abbrev schemeOpenRestriction (X : Scheme.{u}) (V : X.Opens) :
    X.Modules ⥤ SheafOfModules.{u} (sliceStructureSheaf X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V) :=
  overFunctor X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V

/-- **Restriction of the modules on a scheme to an open, as a monoidal functor for
`Stacks.SheafInternalHom.schemeMonoidalCategory`.** The source monoidal structure is the one the
twisted-section machinery is stated over: `Stacks.SheafInternalHom.schemeMonoidalCategory X` is
`Stacks.SheafInternalHom.monoidalCategory X.presheaf _` by definition. -/
@[instance_reducible]
def schemeOverFunctorMonoidal (X : Scheme.{u}) (V : X.Opens) :
    (schemeOpenRestriction X V).Monoidal :=
  overFunctorMonoidal X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V

/-- Restriction to an open is additive, at the `X.Modules` spelling. The site-level statement is
`Stacks.SheafOfModules.SliceFinite.additive_overFunctor`; this is that instance retyped, for the
reason given at `schemeOpenRestriction`. -/
instance schemeOpenRestrictionAdditive (X : Scheme.{u}) (V : X.Opens) :
    (schemeOpenRestriction X V).Additive :=
  Stacks.SheafOfModules.SliceFinite.additive_overFunctor
    (Rs := Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)) V

end Scheme

end Stacks.SheafInternalHom.SliceRestriction

end
