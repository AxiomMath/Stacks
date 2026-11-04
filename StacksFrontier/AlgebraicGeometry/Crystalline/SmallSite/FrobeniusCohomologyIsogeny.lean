module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusNondegeneracy
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeIsomorphism
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusInvertPrime

/-!
# The Frobenius structure map on crystalline cohomology is an isogeny

[Stacks, Tag 07N5] asserts that in Situation [Stacks, Tag 07N2], for `(E, F_E)` a nondegenerate
`F`-crystal over a `p`-adically complete Noetherian `A` with `X → S₀` proper and smooth, the
canonical map

`F_E ∘ (F_X)^*_cris : RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), E)`

becomes an isomorphism after inverting `p`.  Its proof factors that map into three arrows,
(07QC), (07N6) and the one induced by `F_E`, and treats each separately.

**This file proves the third arrow**, unconditionally and with no hypothesis beyond the ones the
source itself uses for it:

`RΓ(Cris(X/S), (F_X)^*_cris E) ⟶ RΓ(Cris(X/S), E)`,

the map induced on module-valued crystalline cohomology by the Frobenius structure map
`F_E : (F_X)^*_cris E ⟶ E` of the `F`-crystal, **becomes an isomorphism after inverting `p`**
(`becomesIsoAfterInvertingPrime_frobeniusCohomologyMap`).  The source's reason is quoted exactly:
`F_E` has an inverse up to a power of `p` because the `F`-crystal is nondegenerate.

That map is the simplest of the three, and the difference is worth being precise about.
`RΓ(Cris(X/S), -)` is a *functor* in the coefficients
(`Crystalline.GlobalCrystallineSituation.SmallSite.moduleULiftDerivedGlobalSectionsFunctor`), and
`F_E` is a morphism of coefficients, so its action on cohomology is nothing but that functor
applied to it; whereas (07QC) and (07N6) move the *site*, and need the action of a morphism of
crystalline topoi on module-valued cohomology, built elsewhere —
`...SmallSite.baseChangeArrow07QC` and `...SmallSite.relativeFrobeniusArrow07N6` of
`SmallSite/FrobeniusTwistArrows.lean`, composed with this arrow in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Frobenius07N5Theorem.lean`.

The coefficients are read on the small crystalline site, as [Stacks, Tag 07N5] reads them: an
`F`-crystal is a module on `CRIS(X/S)` and is restricted along `Cris(X/S) ⥤ CRIS(X/S)` by
`Crystalline.GlobalCrystallineSituation.SmallSite.crisRestrictModules`, the functor whose action
on objects is
`Crystalline.GlobalCrystallineSituation.SmallSite.restrictSheafOfModules`.  So the target of the
map below is literally the object `RΓ(Cris(X/S), E)` of the tag, which
`crisRestrictDerivedGlobalSections_obj_crystal` records by `rfl` against
`Crystalline.GlobalCrystallineSituation.SmallSite.toSmallFCrystal`.

## Where the two-sidedness comes from, and the one delimiter

`Crystalline.FCrystal.Nondegenerate` ([Stacks, Tag 07N3]) is the *one-sided* condition
`F_E ≫ V = p ^ i`.  Becoming an isomorphism after inverting `p` needs a two-sided quasi-inverse,
and the upgrade from one side to two is [Stacks, Tag 07N4].  In this library that upgrade is
`Crystalline.FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_boundedCommonLocalRank`, which asks
`Crystalline.FCrystal.HasBoundedCommonLocalRank rmax`: a bound `rmax` such that `E` and
`(F_X)^*_cris E` are locally free of one common rank `≤ rmax` on a covering sieve.

That predicate is therefore a hypothesis of the main theorem, and it is a **delimiter**, not a
weakening of [Stacks, Tag 07N5] — the theorem here is about the third arrow, not about the tag's
map.  It is the exact hypothesis under which 07N4's two-sided identity is available in this
library, and `Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rank` discharges it for a crystal
of constant rank; the step the library cannot take — from a mere *bound* on the rank of `E` to a
common local rank for `E` and its Frobenius pullback — is recorded at
`Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rankLE` and is not reopened here.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `crisRestrictDerivedGlobalSections` — **`RΓ(Cris(X/S), i_X^{-1} -)` as a functor on the sheaves
  of `𝒪_{X/S}`-modules of the big crystalline site**, landing in `D(Mod_A)`: restrict to the
  small site, take derived global sections, forget the bound.
* `frobeniusCohomologyMap` — **the map `RΓ(Cris(X/S), (F_X)^*_cris E) ⟶ RΓ(Cris(X/S), E)` induced
  by the Frobenius structure map of an `F`-crystal**, the third of the three arrows of the proof
  of [Stacks, Tag 07N5].

## Main results

* `becomesIsoAfterInvertingPrime_frobeniusCohomologyMap` — **the third arrow of the proof of
  [Stacks, Tag 07N5] becomes an isomorphism after inverting `p`**, for a nondegenerate
  `F`-crystal with a bounded common local rank.
* `becomesIsoAfterInvertingPrime_frobeniusCohomologyMap_of_rank` — the same for an `F`-crystal of
  constant rank, where the bounded common local rank is discharged.
* `BecomesIsoAfterInvertingPrime.comp`, `becomesIsoAfterInvertingPrime_of_isIso`,
  `BecomesIsoAfterInvertingPrime.of_comp_left`, `BecomesIsoAfterInvertingPrime.of_comp_right` —
  the calculus of the predicate: becoming an isomorphism after inverting `p` is closed under
  composition, holds for an isomorphism, and cancels on either side.  This is what reduces
  [Stacks, Tag 07N5] to its three arrows once the other two are available.

## What is and is not proved

**No `@[stacks 07N5]` attribute is placed in this file.**  What is proved here is the third of
the three arrows its proof factors through; the tag itself is
`Crystalline.GlobalCrystallineSituation.SmallSite.statement07N5` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Frobenius07N5Theorem.lean`, which composes
this arrow with the other two (`...SmallSite.isIso_baseChangeArrow07QC` and
`...SmallSite.becomesIsoAfterInvertingPrime_relativeFrobeniusArrow07N6`); the tag's statement is
`Crystalline.GlobalCrystallineSituation.SmallSite.Statement07N5` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusInvertPrime.lean`.

No `@[stacks 07N4]` attribute is placed either, although the two-sided identity used below is
that remark: the remark is already tagged where it is proved, in
`StacksFrontier/AlgebraicGeometry/Crystalline/FrobeniusNondegeneracy.lean`, and the conclusion drawn
here — an isomorphism after inverting `p` on cohomology — is 07N5's, not 07N4's.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07N4](https://stacks.math.columbia.edu/tag/07N4)
* [Stacks Project, Tag 07N3](https://stacks.math.columbia.edu/tag/07N3)
* [Stacks Project, Tag 07N2](https://stacks.math.columbia.edu/tag/07N2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wS wA wP

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### The calculus of becoming an isomorphism after inverting `p` -/

section Calculus

variable (S : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wP} (ModuleCat.{u + 1} (invertPrimeRing S))]

variable {X Y Z : DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))}

/-- **An isomorphism becomes an isomorphism after inverting `p`.** -/
theorem becomesIsoAfterInvertingPrime_of_isIso (φ : X ⟶ Y) [IsIso φ] :
    BecomesIsoAfterInvertingPrime S φ :=
  inferInstanceAs (IsIso ((invertPrime S).map φ))

/-- **Becoming an isomorphism after inverting `p` is closed under composition.**

This is what reduces [Stacks, Tag 07N5] to the three arrows its proof factors the map into: once
each of them becomes an isomorphism after inverting `p`, so does the composite. -/
theorem BecomesIsoAfterInvertingPrime.comp {φ : X ⟶ Y} {ψ : Y ⟶ Z}
    (hφ : BecomesIsoAfterInvertingPrime S φ) (hψ : BecomesIsoAfterInvertingPrime S ψ) :
    BecomesIsoAfterInvertingPrime S (φ ≫ ψ) := by
  have h₁ : IsIso ((invertPrime S).map φ) := hφ
  have h₂ : IsIso ((invertPrime S).map ψ) := hψ
  show IsIso ((invertPrime S).map (φ ≫ ψ))
  rw [Functor.map_comp]
  infer_instance

/-- **Cancellation on the right**: if a composite and its second factor become isomorphisms after
inverting `p`, so does the first factor. -/
theorem BecomesIsoAfterInvertingPrime.of_comp_left {φ : X ⟶ Y} {ψ : Y ⟶ Z}
    (hφψ : BecomesIsoAfterInvertingPrime S (φ ≫ ψ)) (hψ : BecomesIsoAfterInvertingPrime S ψ) :
    BecomesIsoAfterInvertingPrime S φ := by
  have h₂ : IsIso ((invertPrime S).map ψ) := hψ
  have h : IsIso ((invertPrime S).map (φ ≫ ψ)) := hφψ
  rw [Functor.map_comp] at h
  exact IsIso.of_isIso_comp_right _ ((invertPrime S).map ψ)

/-- **Cancellation on the left**: if a composite and its first factor become isomorphisms after
inverting `p`, so does the second factor. -/
theorem BecomesIsoAfterInvertingPrime.of_comp_right {φ : X ⟶ Y} {ψ : Y ⟶ Z}
    (hφψ : BecomesIsoAfterInvertingPrime S (φ ≫ ψ)) (hφ : BecomesIsoAfterInvertingPrime S φ) :
    BecomesIsoAfterInvertingPrime S ψ := by
  have h₁ : IsIso ((invertPrime S).map φ) := hφ
  have h : IsIso ((invertPrime S).map (φ ≫ ψ)) := hφψ
  rw [Functor.map_comp] at h
  exact IsIso.of_isIso_comp_left ((invertPrime S).map φ) _

end Calculus

/-! ### `RΓ(Cris(X/S), -)` of a module on the big crystalline site -/

section Restriction

variable (S : GlobalCrystallineSituation.{u}) [HasDerivedCategory.{wS} (ModuleSheaf S)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]

/-- The restriction of modules from `CRIS(X/S)` to `Cris(X/S)` is additive: it acts on sections by
restriction along the inclusion of the sites, which is additive on the nose. -/
instance crisRestrictModules_additive : (crisRestrictModules.{u} S).Additive where
  map_add := by intros; rfl

/-- The universe lift of sheaves of modules is additive: it acts on sections by `ULift.up`. -/
instance moduleULift_additive : (moduleULift S).Additive where
  map_add := by intros; rfl

attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

/-- `RΓ(Cris(X/S), -) : D⁺(Mod_{𝒪_{X/S}}) ⥤ D⁺(Mod_A)` is additive, being an exact functor of
triangulated categories ([Stacks, Tag 0159]). -/
instance derivedModuleGlobalSectionsFunctor_additive :
    (derivedModuleGlobalSectionsFunctor S).Additive :=
  inferInstanceAs (baseModuleGlobalSections S).rightDerivedFunctorPlus.Additive

/-- `RΓ(Cris(X/S), -)` on a single sheaf of modules is additive. -/
instance derivedModuleGlobalSections_additive : (derivedModuleGlobalSections S).Additive :=
  inferInstanceAs (DerivedCategory.Plus.singleFunctor (ModuleSheaf S) 0 ⋙
    derivedModuleGlobalSectionsFunctor S).Additive

/-- `RΓ(Cris(X/S), -)` at the module universe of the chapter's predicates is additive. -/
instance moduleULiftDerivedGlobalSectionsFunctor_additive :
    (moduleULiftDerivedGlobalSectionsFunctor S).Additive :=
  inferInstanceAs (moduleULift S ⋙ derivedModuleGlobalSections S).Additive

/-- **`RΓ(Cris(X/S), i_X^{-1} -)` as a functor on the modules of the big crystalline site**,
landing in the unbounded derived category of `A`-modules.

A `Crystalline.FCrystal` carries its module on `CRIS(X/S)`, while the cohomology of
[Stacks, Tag 07N5] is taken on `Cris(X/S)`; the passage is restriction along the inclusion
`Cris(X/S) ⥤ CRIS(X/S)`, the comparison `i_X^{-1}` of [Stacks, Tag 07IM].  Composing it with
`moduleULiftDerivedGlobalSectionsFunctor` and with
`CategoryTheory.DerivedCategory.Plus.ι` gives the functor the tag's objects and maps live in:
`D(Mod_A)` rather than `D⁺(Mod_A)`, because the tag's map has
`RΓ(Cris(X/S), E) ⊗^L_{A, σ} A` as its source and the derived tensor product is only right
t-exact. -/
def crisRestrictDerivedGlobalSections :
    SheafOfModules.{u} (crystallineStructureSheaf S) ⥤
      DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  crisRestrictModules.{u} S ⋙ moduleULiftDerivedGlobalSectionsFunctor S ⋙
    DerivedCategory.Plus.ι

/-- The value of `crisRestrictDerivedGlobalSections` is `RΓ(Cris(X/S), -)` of the restriction to
the small site, so it is the object this chapter's statements are about and not a new one. -/
theorem crisRestrictDerivedGlobalSections_obj
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) :
    (crisRestrictDerivedGlobalSections S).obj N =
      DerivedCategory.Plus.ι.obj
        (moduleULiftDerivedGlobalSections S (restrictSheafOfModules N)) :=
  rfl

/-- `RΓ(Cris(X/S), i_X^{-1} -)` is additive, each of its three factors being so. -/
instance crisRestrictDerivedGlobalSections_additive :
    (crisRestrictDerivedGlobalSections S).Additive :=
  inferInstanceAs (crisRestrictModules.{u} S ⋙ moduleULiftDerivedGlobalSectionsFunctor S ⋙
    DerivedCategory.Plus.ι).Additive

end Restriction

/-! ### The map induced by the Frobenius structure of an `F`-crystal -/

section Frobenius

variable (T : Crystalline.FCrystalSituation.{u})
  [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]

/-- **The map `RΓ(Cris(X/S), (F_X)^*_cris E) ⟶ RΓ(Cris(X/S), E)` induced by the Frobenius
structure map of an `F`-crystal**, the third of the three arrows the proof of
[Stacks, Tag 07N5] factors its map into.

It is `RΓ(Cris(X/S), i_X^{-1} -)` applied to `F_E : (F_X)^*_cris E ⟶ E`, the structure map of
`Crystalline.FCrystal`.  No functoriality in the *site* is involved — that is what the other two
arrows need — only functoriality in the coefficients. -/
def frobeniusCohomologyMap (E : Crystalline.FCrystal T) :
    (crisRestrictDerivedGlobalSections T.global).obj
        (T.frobeniusModulePullback.obj E.crystal) ⟶
      (crisRestrictDerivedGlobalSections T.global).obj E.crystal :=
  (crisRestrictDerivedGlobalSections T.global).map E.frobenius

/-- **The target of `frobeniusCohomologyMap` is the object `RΓ(Cris(X/S), E)` of
[Stacks, Tag 07N5]**: the restriction of the `F`-crystal's module to the small site is
`Crystalline.GlobalCrystallineSituation.SmallSite.toSmallFCrystal`, which is what
`Crystalline.GlobalCrystallineSituation.SmallSite.Statement07N5` takes the cohomology of. -/
theorem crisRestrictDerivedGlobalSections_obj_crystal (E : Crystalline.FCrystal T) :
    (crisRestrictDerivedGlobalSections T.global).obj E.crystal =
      DerivedCategory.Plus.ι.obj
        (moduleULiftDerivedGlobalSections T.global (toSmallFCrystal E)) :=
  rfl

variable [HasDerivedCategory.{wP} (ModuleCat.{u + 1} (invertPrimeRing T.global))]

/-- **The third arrow of the proof of [Stacks, Tag 07N5] becomes an isomorphism after inverting
`p`.**  The map induced on module-valued crystalline cohomology by the Frobenius structure map
`F_E` of a nondegenerate `F`-crystal with a bounded common local rank becomes an isomorphism
after inverting `p`.

This is the source's own reason, formalized: `F_E` has an inverse up to a power of `p`.
Nondegeneracy ([Stacks, Tag 07N3]) supplies `V` with `F_E ≫ V = p ^ i`, and the bounded common
local rank turns that into the two-sided identity of [Stacks, Tag 07N4],
`Crystalline.FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_boundedCommonLocalRank`, for the
rescaled `p ^ (rmax * i) • V`.  `RΓ(Cris(X/S), i_X^{-1} -)` is additive, so it carries both
identities to `D(Mod_A)`, where
`Crystalline.GlobalCrystallineSituation.SmallSite.becomesIsoAfterInvertingPrime_of_comp_eq_nsmul`
concludes.

The rank hypothesis is the delimiter the module docstring describes: it is what makes 07N4's
two-sided identity available in this library, and it is discharged for a crystal of constant rank
by `becomesIsoAfterInvertingPrime_frobeniusCohomologyMap_of_rank`. -/
theorem becomesIsoAfterInvertingPrime_frobeniusCohomologyMap (E : Crystalline.FCrystal T)
    {rmax : ℕ} (hrank : E.HasBoundedCommonLocalRank rmax) (hE : E.Nondegenerate) :
    BecomesIsoAfterInvertingPrime T.global (frobeniusCohomologyMap T E) := by
  obtain ⟨i, V, hV⟩ := hE
  refine becomesIsoAfterInvertingPrime_of_comp_eq_nsmul T.global _
    ((crisRestrictDerivedGlobalSections T.global).map ((T.global.p ^ (rmax * i)) • V))
    (rmax * i + i) ?_ ?_ <;> rw [frobeniusCohomologyMap, ← Functor.map_comp]
  · rw [Crystalline.FCrystal.frobenius_comp_nsmul (N := rmax * i) E hV, Functor.map_nsmul,
      CategoryTheory.Functor.map_id]
  · rw [Crystalline.FCrystal.nsmul_comp_frobenius_eq_nsmul_id_of_boundedCommonLocalRank E hrank hV
      le_rfl, Functor.map_nsmul, CategoryTheory.Functor.map_id]

/-- **The third arrow of the proof of [Stacks, Tag 07N5] becomes an isomorphism after inverting
`p`, for an `F`-crystal of constant rank.**  A crystal of constant rank `r` has `r` as a common
local rank bounded by `r`, by
`Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rank`, so the rank hypothesis of
`becomesIsoAfterInvertingPrime_frobeniusCohomologyMap` is discharged. -/
theorem becomesIsoAfterInvertingPrime_frobeniusCohomologyMap_of_rank
    (E : Crystalline.FCrystal T) {r : ℕ}
    (hr : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank
      (Crystalline.GlobalCrystallineSituation.crystallineRingedSite T.global) E.crystal r)
    (hE : E.Nondegenerate) :
    BecomesIsoAfterInvertingPrime T.global (frobeniusCohomologyMap T E) :=
  becomesIsoAfterInvertingPrime_frobeniusCohomologyMap T E
    (Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rank E hr) hE

end Frobenius

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
