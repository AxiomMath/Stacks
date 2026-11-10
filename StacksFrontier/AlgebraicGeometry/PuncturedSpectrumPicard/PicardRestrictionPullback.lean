module

public import StacksFrontier.AlgebraicGeometry.Thickenings.PicardTorsionGeneral
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.FormalTower

/-!
# Restriction of Picard classes along a thickening is pullback of Picard classes

This library carries two spellings of the restriction map `Pic(X') ⟶ Pic(X)` attached to a
first-order thickening `i : X ⟶ X'` of schemes.

* `Stacks.Thickenings.picardRestriction`, which is the map of the exact sequence of
  [Stacks, Tag 0C6R]: the map on first cohomology of the sheaves of units induced by
  `𝒪_{X'}^* ⟶ i_* 𝒪_X^*`, read through the identification of [Stacks, Tag 09NU] with
  `Stacks.SheafOfModules.Picard.PicardGroup`, and through the comparison of the cohomology of
  `i_* 𝒪_X^*` on `X'` with the cohomology of `𝒪_X^*` on `X`.
* `Stacks.Picard.schemePullbackClass`, which is pullback of invertible modules, read on
  `Stacks.Picard.ofScheme`.

Both are "restrict an invertible module along `i`", but they are built from different data —
one cohomologically, one by pulling modules back — and nothing connected them. This file
connects them, in the form the lifting statements need: **the two maps are simultaneously
surjective**. Both are the conjugate, by isomorphisms of abelian groups, of one and the same
map of cohomology groups, namely the map induced by restriction of units
`𝒪_{X'}^* ⟶ i_* 𝒪_X^*` in degree one.

For `picardRestriction` that is its definition. For `schemePullbackClass` it is the naturality
of [Stacks, Tag 09NU] in a morphism of schemes,
`Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard_naturality`, together with the bijectivity
of the first Leray edge map of a closed embedding,
`Stacks.Thickenings.bijective_abelianEdgeMap_of_isClosedEmbedding`. The two spellings of first
cohomology — the first right-derived functor of global sections, and `Ext` from the constant
sheaf of integers — are compared naturally in the sheaf by
`Stacks.PuncturedSpectrumPicard.cohomologyRightDerivedExtIso`.

## Main definitions

* `Stacks.PuncturedSpectrumPicard.cohomologyRightDerivedExtIso`: first cohomology as the first
  right-derived functor of global sections is first cohomology as `Ext` from the constant sheaf
  of integers, naturally in the sheaf.
* `Stacks.PuncturedSpectrumPicard.IsCompatiblePullback`: a family of classes in
  `Stacks.Picard.ofScheme`, one on each stage of a
  `Stacks.PuncturedSpectrumPicard.ThickeningTower`, each the pullback of the next. This is
  `Stacks.PuncturedSpectrumPicard.IsCompatible` in the pullback spelling.

## Main results

* `Stacks.PuncturedSpectrumPicard.surjective_schemePullbackClass_iff_surjective_picardRestriction`:
  **the identification of the two spellings**, in the form the lifting statements use:
  pullback of Picard classes along a first-order thickening is surjective exactly when the
  restriction map of the sequence of [Stacks, Tag 0C6R] is.
* `Stacks.PuncturedSpectrumPicard.surjective_schemePullbackClass_of_forall_eq_zero`: if the
  second cohomology of the ideal sheaf vanishes, pullback of Picard classes along the
  thickening is surjective.
* `Stacks.PuncturedSpectrumPicard.exists_isCompatiblePullback`: **the first half of the proof of
  [Stacks, Tag 0F2D] in the pullback spelling.** Along a tower of first-order thickenings whose
  ideal sheaves have vanishing second cohomology, every class in `Stacks.Picard.ofScheme` of the
  bottom stage extends to a compatible family of pullbacks along the whole tower. This is
  `Stacks.PuncturedSpectrumPicard.exists_isCompatible` transported along the identification
  above.

## Implementation notes

**Why surjectivity and not equality.** What is proved is that the two maps are conjugate, by
explicit isomorphisms, to a common third map, and hence are simultaneously surjective. They are
*not* shown to be equal. The two conjugations differ by the comparison of
`Stacks.Thickenings.unitsCohomologyEquiv` — the pushforward isomorphism of a closed embedding
on cohomology — with the first Leray edge map of the same closed embedding, which is an
automorphism of `H¹(X, 𝒪_X^*)` that this library does not identify with the identity. Every
consumer of the two spellings in this library uses only surjectivity (or bijectivity on a
subgroup, as in `Stacks.Thickenings.bijOn_schemePullbackClass_zsmulTorsion_of_isThickening`,
which is proved by exactly this conjugation), so nothing is lost; recording the equality would
need that further comparison.

**The `hasExt` local instance** repeats the local instance of
`StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.FormalTower` under a new name, because it
is local there and the statements below cannot be written without it. **The abelian group
structure** on the Picard group is not restated: it is
`Stacks.Cohomology.Generators.picardGroupAddCommGroup`, re-activated here as in
`StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.FormalTower`.

## References

* [Stacks Project, Tag 0C6R](https://stacks.math.columbia.edu/tag/0C6R)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 0F2D](https://stacks.math.columbia.edu/tag/0F2D)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.PuncturedSpectrumPicard

open Stacks.Cohomology.Generators (unitsSheaf)
open Stacks.Cohomology.LerayLowDegree (abelianCohomology abelianEdgeMap)
open Stacks.Picard.FirstCohomology (h1UnitsRightDerived h1UnitsAddEquivPicard
  h1UnitsAddEquivPicard_naturality)
open Stacks.GlueSquishUnits (unitsPushforwardMap unitsPushforwardMap_app)
open Stacks.Picard (ofScheme schemePullbackClass)
open Stacks.Thickenings (IsFirstOrderThickening picardRestriction unitsToSubCohomology
  unitsRestrictionSheafHom unitsRestrictionSheafHom_app unitsCohomologyEquiv
  unitsCohomologyPicardEquiv bijective_abelianEdgeMap_of_isClosedEmbedding sectionsCoyonedaIso
  idealAddSheafOnSub pushforwardUnitsSheaf)

attribute [local implicit_reducible] TopCat.Sheaf

/-- `Ext`-groups of abelian sheaves on a topological space are computed in the universe of the
sections, because the category of abelian sheaves has enough injectives. This repeats the local
instance of `StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.FormalTower`. -/
local instance hasExtAbelianSheafPullbackBridge (Y : TopCat.{u}) :
    HasExt.{u} (TopCat.Sheaf AddCommGrpCat.{u} Y) :=
  hasExt_of_enoughInjectives _

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

/-! ### Transporting surjectivity along isomorphisms -/

/-- Two maps that agree after relabelling their sources and their targets are simultaneously
surjective. -/
theorem surjective_iff_of_conjugate {A B A' B' : Type*} (f : A → B) (g : A' → B') (eA : A ≃ A')
    (eB : B ≃ B') (h : ∀ x, g (eA x) = eB (f x)) :
    Function.Surjective g ↔ Function.Surjective f := by
  rw [← eA.surjective_comp, show g ∘ eA = eB ∘ f from funext h, eB.comp_surjective]

/-! ### The two spellings of first cohomology -/

/-- First cohomology computed as the first right-derived functor of global sections agrees,
naturally in the sheaf, with first cohomology computed as `Ext` from the constant sheaf of
integers. This is the functorial form of
`Stacks.Thickenings.sheafCohomologyOneExtEquiv`. -/
def cohomologyRightDerivedExtIso (Y : TopCat.{u}) :
    abelianCohomology.{u, u} Y ⊤ 1 ≅
      CategoryTheory.Sheaf.functorH.{u, u, u, u} (Opens.grothendieckTopology Y) 1 :=
  ModuleSheafCohomology.rightDerivedIso (sectionsCoyonedaIso Y).symm 1 ≪≫
    ModuleSheafCohomology.rightDerivedCoyonedaSuccIso
      ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) 0

/-! ### The comparison -/

section Comparison

variable {X X' : Scheme.{u}}

/-- Restriction of units and the map on units of the sheaf-of-units sequence are the same map
of sheaves of abelian groups: both are `Units.map (i.app U)` on sections. -/
theorem unitsPushforwardMap_eq_unitsRestriction (i : X ⟶ X') :
    unitsPushforwardMap i = unitsRestrictionSheafHom i := by
  apply Sheaf.hom_ext
  ext U s
  exact (unitsPushforwardMap_app i U.unop (Additive.toMul s)).trans
    (unitsRestrictionSheafHom_app i U.unop (Additive.toMul s)).symm

/-- Pullback of Picard classes along a closed immersion is surjective exactly when the map it
induces on first cohomology of the sheaves of units, in the right-derived spelling, is. -/
theorem surjective_schemePullbackClass_iff_surjective_cohomologyMap (i : X ⟶ X')
    (hi : IsClosedImmersion i) :
    Function.Surjective (schemePullbackClass i) ↔
      Function.Surjective ((abelianCohomology.{u, u} X' ⊤ 1).map
        (unitsRestrictionSheafHom i)) := by
  have hedge := bijective_abelianEdgeMap_of_isClosedEmbedding i.base hi.isClosedEmbedding
    (unitsSheaf X.toLocallyRingedSpace.toRingedSpace)
  let eEdge := AddEquiv.ofBijective
    ((abelianEdgeMap.{u, u} i.base 1).app
      (unitsSheaf X.toLocallyRingedSpace.toRingedSpace)).hom hedge
  refine surjective_iff_of_conjugate _ _ (h1UnitsAddEquivPicard X').toEquiv
    ((eEdge.trans (h1UnitsAddEquivPicard X)).toEquiv) fun c => ?_
  rw [← unitsPushforwardMap_eq_unitsRestriction]
  exact (h1UnitsAddEquivPicard_naturality i c).symm

/-- The restriction map of the exact sequence of [Stacks, Tag 0C6R] is surjective exactly when
the map it induces on first cohomology of the sheaves of units, in the `Ext` spelling, is. -/
theorem surjective_picardRestriction_iff_unitsToSubCohomology (i : X ⟶ X')
    (hi : IsFirstOrderThickening i) :
    Function.Surjective (picardRestriction i hi) ↔
      Function.Surjective (unitsToSubCohomology i 1) := by
  refine surjective_iff_of_conjugate _ _ (unitsCohomologyPicardEquiv X').toEquiv
    (((unitsCohomologyEquiv i hi 1).symm.trans (unitsCohomologyPicardEquiv X)).toEquiv)
    fun x => ?_
  change unitsCohomologyPicardEquiv X ((unitsCohomologyEquiv i hi 1).symm
      (unitsToSubCohomology i 1 ((unitsCohomologyPicardEquiv X').symm
        (unitsCohomologyPicardEquiv X' x)))) =
    unitsCohomologyPicardEquiv X ((unitsCohomologyEquiv i hi 1).symm
      (unitsToSubCohomology i 1 x))
  rw [AddEquiv.symm_apply_apply]

/-- **The two spellings of restriction of invertible modules along a first-order thickening are
simultaneously surjective.** `Stacks.Thickenings.picardRestriction` is the map of the exact
sequence of [Stacks, Tag 0C6R] and `Stacks.Picard.schemePullbackClass` is pullback of invertible
modules; both are conjugate, by isomorphisms of abelian groups, to the map induced in degree one
by restriction of units `𝒪_{X'}^* ⟶ i_* 𝒪_X^*`. -/
theorem surjective_schemePullbackClass_iff_surjective_picardRestriction (i : X ⟶ X')
    (hi : IsFirstOrderThickening i) :
    Function.Surjective (schemePullbackClass i) ↔
      Function.Surjective (picardRestriction i hi) := by
  rw [surjective_schemePullbackClass_iff_surjective_cohomologyMap i hi.1,
    surjective_picardRestriction_iff_unitsToSubCohomology i hi]
  refine surjective_iff_of_conjugate _ _
    ((cohomologyRightDerivedExtIso X').app
      (unitsSheaf X'.toLocallyRingedSpace.toRingedSpace)).symm.addCommGroupIsoToAddEquiv.toEquiv
    ((cohomologyRightDerivedExtIso X').app
      (pushforwardUnitsSheaf i)).symm.addCommGroupIsoToAddEquiv.toEquiv fun x =>
    (ConcreteCategory.congr_hom
      ((cohomologyRightDerivedExtIso X').inv.naturality (unitsRestrictionSheafHom i)) x).symm

/-- If the second cohomology of the ideal sheaf of a first-order thickening `i : X ⟶ X'`
vanishes, then pullback of Picard classes `Pic(X') → Pic(X)` is surjective.

This is `Stacks.PuncturedSpectrumPicard.surjective_picardRestriction_of_forall_eq_zero` — the
one step the proof of [Stacks, Tag 0F2D] takes from [Stacks, Tag 0C6R] — transported to the
pullback spelling. -/
theorem surjective_schemePullbackClass_of_forall_eq_zero (i : X ⟶ X')
    (hi : IsFirstOrderThickening i)
    (h2 : ∀ x : CategoryTheory.Sheaf.H.{u} (idealAddSheafOnSub i) 2, x = 0) :
    Function.Surjective (schemePullbackClass i) :=
  (surjective_schemePullbackClass_iff_surjective_picardRestriction i hi).mpr
    (surjective_picardRestriction_of_forall_eq_zero i hi h2)

end Comparison

/-! ### Compatible families along a tower, in the pullback spelling -/

variable (T : ThickeningTower.{u})

/-- A family of classes in `Stacks.Picard.ofScheme`, one on each stage of a tower of first-order
thickenings, each the pullback of the next. This is
`Stacks.PuncturedSpectrumPicard.IsCompatible` in the spelling of
`Stacks.Picard.schemePullbackClass`. -/
def IsCompatiblePullback (c : (n : ℕ) → ofScheme (T.obj n)) : Prop :=
  ∀ n, schemePullbackClass (T.hom n) (c (n + 1)) = c n

/-- **The first half of the proof of [Stacks, Tag 0F2D], in the pullback spelling.** Let
`X₀ ⟶ X₁ ⟶ X₂ ⟶ ⋯` be a tower of first-order thickenings in which the ideal sheaf of every
stage has vanishing second cohomology. Then every class in `Stacks.Picard.ofScheme` of the
bottom stage extends to a family of classes along the whole tower, each the pullback of the
next.

This is `Stacks.PuncturedSpectrumPicard.exists_isCompatible` read through
`Stacks.PuncturedSpectrumPicard.surjective_schemePullbackClass_iff_surjective_picardRestriction`:
the single-stage lift is
`Stacks.PuncturedSpectrumPicard.surjective_schemePullbackClass_of_forall_eq_zero`, and the
family is assembled by recursion on the stage, choosing a lift at each step. -/
theorem exists_isCompatiblePullback
    (h2 : ∀ n, ∀ x : CategoryTheory.Sheaf.H.{u}
      (idealAddSheafOnSub (T.hom n)) 2, x = 0)
    (c₀ : ofScheme (T.obj 0)) :
    ∃ c : (n : ℕ) → ofScheme (T.obj n), c 0 = c₀ ∧ IsCompatiblePullback T c := by
  have hsurj : ∀ n, Function.Surjective (schemePullbackClass (T.hom n)) := fun n =>
    surjective_schemePullbackClass_of_forall_eq_zero (T.hom n) (T.isFirstOrderThickening n) (h2 n)
  exact ⟨fun n => Nat.rec (motive := fun n => ofScheme (T.obj n)) c₀
    (fun n x => (hsurj n x).choose) n, rfl, fun n => (hsurj n _).choose_spec⟩

end Stacks.PuncturedSpectrumPicard

end
