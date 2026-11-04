module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetDegreewise
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianModelPushforwardBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyDegreewiseExcision

/-!
# Stacks 0G74 part (2) in the Gysin spelling is Stacks 0G74 part (2) at the endofunctor spelling

Let `X` be a scheme, `T ⊆ X` a closed subset and `n : ℕ`.  [Stacks, Tag 0G74] part (2) — the
canonical comparison `ℋ ⁿ_T(ℱ)_ab ⟶ ℋ ⁿ_T(ℱ_ab)` of the local cohomology sheaves with the local
cohomology sheaves of the underlying sheaves of abelian groups — occurs in this library in two
spellings that no declaration related:

* the **Gysin** spelling `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafForgetIso`,
  whose source is `Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor`, the degree-`n`
  cohomology sheaf of `i_* R𝓗_T(ℱ[0])` taken in the unbounded derived category, and whose target
  is `Stacks.Perfect.GysinAbelianSquare.abelianLocalCohomologyPushforward`, the classical abelian
  local cohomology sheaf on `T` pushed forward to `X`.  This is the spelling the target of
  `AlgebraicGeometry.Scheme.Hom.gysinMap` and the square of [Stacks, Tag 0G85] are written in;
* the **endofunctor** spelling
  `Stacks.Cohomology.DegreewiseExcisionSquare.localCohomologyEndoForgetComparison`, in which both
  sides are Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived` of the supported-sections
  *endofunctor* — of `𝒪_X`-modules on one side and of abelian sheaves on the other.  This is the
  spelling the two classical excisions use, and the one the degreewise square of
  [Stacks, Tag 0G87],
  `Stacks.Cohomology.DegreewiseExcisionSquare.forget_localCohomologyRestrict_comm`, is stated in.

This file identifies the two: `supportCohomologySheafForgetIso_eq_localCohomologyEndoForget`.
It is the last thing between [Stacks, Tag 0G87] in the endofunctor spelling and
[Stacks, Tag 0G87] for the Gysin map's local cohomology sheaves; the statement is proved at a
scheme and a closed subset with no restriction on the degree, so it applies verbatim on an open
subscheme and the preimage of `T` as well.

## Main definitions

* `supportCohomologySheafFunctorEndoIso`: **the Gysin spelling of `i_*ℋ ⁿ_T` is the degree-`n`
  right derived functor of the supported-sections endofunctor.**  This is the bridge
  `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` at
  `Stacks.Perfect.SupportedFraction.supportPush` — nothing more: the Gysin spelling of the
  functor *is* a module placed in degree `0`, then `i_* R𝓗_T`, then degree-`n` cohomology, which
  is the source of that bridge verbatim.

## Main results

* `supportCohomologySheafForgetIso_eq_localCohomologyEndoForget`: **the two spellings of
  [Stacks, Tag 0G74] part (2) agree**, at every closed subset, in every degree and at every
  module, across `supportCohomologySheafFunctorEndoIso` on the module side and
  `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafPushforwardIso` on the abelian
  side.

## Implementation notes

**Carried hypotheses: a closed subset, and nothing else.**  No restriction on `n`, no
quasi-coherence, no hypothesis on the module.  Closedness is needed for the direct images from
`T` to be exact and so for every functor in sight to exist.

**The total derived functors are the canonical ones.**  The endofunctor spelling takes the two
total right derived functors and their units as data; here they are
`Stacks.Perfect.SupportedFraction.supportPush` with
`Stacks.Perfect.SupportedQuasicoherent.derivedSupportedPushforwardUnit` and
`Stacks.Cohomology.AbelianSupportedCounit.derivedAbelianSupportedPushforward` with
`..derivedAbelianSupportedPushforwardUnit`.  That is not a restriction on the statement but what
makes it the statement it is: at those two,
`Stacks.Cohomology.DerivedExcisionSquare.forgetComparison` *is*
`Stacks.Perfect.AbelianCechDerivedSquare.forgetComparison`, the comparison the Gysin spelling is
built from — both being
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison` at the same four
arguments.  Any consumer stated at arbitrary total derived functors, in particular
`forget_localCohomologyRestrict_comm`, is instantiated at these.

**How the proof splits.**  Reading
`Stacks.Cohomology.SupportedComplexes.degreewiseForgetComparison` through its definition, the
endofunctor comparison at a module is the source corner inverted, the degree-`n` cohomology of the
comparison of total derived functors, and the target corner; and reading
`Stacks.Perfect.AbelianSupportedEndoModelBridge.endoForgetIsoApp` through its definition, the
Gysin spelling at a module — by
`Stacks.Perfect.SupportedEndoForgetDegreewise.supportCohomologySheafForgetIso_hom_app` — is the
same middle factor with
`Stacks.Perfect.AbelianCechCokernelPassage.forgetDerivedHomology` inverted before it and
`Stacks.Perfect.AbelianSupportedEndoModelBridge.abelianModelApp` after it.  So three identities
are needed, and each is one declaration below:

* the source corners agree once `supportCohomologySheafFunctorEndoIso` is cancelled: the pull of
  the forgetful functor out of the cohomology of the derived category *is*
  `forgetDerivedHomology`, both being
  `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` — `lhs_hom`, `endo_app`;
* the two readings of `Φ(ℱ[0]) ≅ (Φℱ)[0]` agree, which is
  `Stacks.Perfect.AbelianSupportedEndoModelFactors.singleForgetIso_eq`;
* the target corners agree, which is
  `Stacks.Cohomology.SupportedComplexes.abelianModelComponent_hom_comp_pushforwardIso`, the one
  piece of mathematics this chapter needed: the canonical bridge of `i_* R𝓗_T^{ab}` is the
  abelian model comparison followed by `abelianLocalCohomologySheafPushforwardIso`.

Each of `lhs_hom` and `endo_app` performs exactly one crossing of two definitionally equal
spellings, and the assembly is a `private` lemma at a variable category applied with `exact` —
the device of `Stacks.Perfect.SupportedEndoForgetDegreewise`, whose implementation notes record
why a rewrite in place is not available in these composites.

**No `@[stacks ...]` attribute is attached to any declaration here**, and nothing here proves
[Stacks, Tag 0G74] or [Stacks, Tag 0G87] on its own.

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Lemma 20.34.9 (Tag 0G87)](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.AbelianSupportedCounit (derivedAbelianSupportedPushforward
  derivedAbelianSupportedPushforwardUnit)
open Stacks.Cohomology.DegreewiseExcisionSquare (localCohomologyEndoForgetComparison)
open Stacks.Cohomology.Localization (enoughKInjectives)
open Stacks.Cohomology.SupportedComplexes (abelianLocalCohomologySheafPushforwardIso
  abelianModelComponent_hom_comp_pushforwardIso abelianSupportedSections)
open Stacks.DerivedFunctor (singleCompDerivedCompHomologyIsoRightDerived)
open Stacks.Perfect.AbelianCechCokernelPassage (forgetDerivedHomology)
open Stacks.Perfect.AbelianCechDerivedSquare (forgetComparison)
open Stacks.Perfect.AbelianFraction (abelianSheaf)
open Stacks.Perfect.AbelianSupportedEndoModelBridge (abelianModelApp singleForgetIso)
open Stacks.Perfect.AbelianSupportedEndoModelFactors (singleForgetIso_eq singleForgetMathlib)
open Stacks.Perfect.SupportedFraction (supportCohomologySheafFunctor supportPush
  supportPushSingle)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforwardUnit)
open Stacks.SheafOfModules.SupportedSections (supportedSectionsFunctor)

universe u

namespace Stacks.Perfect.SupportedEndoForgetEndofunctor

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Formal assembly -/

/-- **The assembly of the two readings, at an abstract category.**  The Gysin reading is the
inverse of the pull of the forgetful functor, the degree-`n` cohomology of the comparison of
total derived functors, the first reading of `Φ(ℱ[0]) ≅ (Φℱ)[0]`, and the model bridge; the
endofunctor reading is the bridge of the Gysin spelling, then the same four factors with the
bridge inverted in front, the second reading of `Φ(ℱ[0]) ≅ (Φℱ)[0]`, and the canonical bridge of
`i_* R𝓗_T^{ab}` followed by the comparison of the two models.

Stated at a variable category with the objects implicit and the morphisms explicit: the two sides
contain components whose types are written through composite functors, in which `Category.assoc`
and `CategoryTheory.Functor.map_comp` rewrite nothing in place.  This is the device of
`Stacks.Perfect.SupportedEndoForgetDegreewise.assemble_formal`. -/
private lemma assemble_formal {C₀ : Type*} [Category* C₀] {x y z w v s t : C₀}
    (u : x ⟶ y) (u' : y ⟶ x) (d : x ⟶ z) (c : z ⟶ w) (g g' : w ⟶ v) (m : v ⟶ s) (pp : s ⟶ t)
    (A : v ⟶ t) (huu : u ≫ u' = CategoryStruct.id x) (hg : g' = g) (hA : m ≫ pp = A) :
    (d ≫ c ≫ g') ≫ A = u ≫ ((u' ≫ d) ≫ c ≫ g ≫ m) ≫ pp := by
  calc (d ≫ c ≫ g') ≫ A = d ≫ c ≫ g ≫ m ≫ pp := by
        rw [hg, ← hA]; simp only [Category.assoc]
    _ = (u ≫ u') ≫ d ≫ c ≫ g ≫ m ≫ pp := by rw [huu, Category.id_comp]
    _ = u ≫ ((u' ≫ d) ≫ c ≫ g ≫ m) ≫ pp := by simp only [Category.assoc]

/-! ### The Gysin spelling of the local cohomology sheaf is the endofunctor's derived functor -/

variable {X : Scheme.{u}} {T : Set X} (hT : IsClosed T) (n : ℕ)

/-- **The Gysin spelling of `i_*ℋ ⁿ_T` is the degree-`n` right derived functor of the
supported-sections endofunctor of `𝒪_X`-modules.**

`Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor` is by definition the module
placed in degree `0`, then `i_* R𝓗_T` — the canonical total right derived functor
`Stacks.Perfect.SupportedFraction.supportPush` of `ℱ ↦ i_*ℋ_T(ℱ)` — then the degree-`n`
cohomology sheaf.  That is the source of the bridge
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` verbatim, so this is that
bridge and nothing else.

It is the module-side counterpart of
`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafPushforwardIso` composed with
`Stacks.Cohomology.AbelianModelComparison.abelianSupportedPushforwardModelIso`, and it is what
carries the Gysin spelling of [Stacks, Tag 0G74] part (2) to the endofunctor spelling. -/
def supportCohomologySheafFunctorEndoIso :
    supportCohomologySheafFunctor hT (n : ℤ) ≅
      (supportedSectionsFunctor X.toRingedSpace T).rightDerived n :=
  singleCompDerivedCompHomologyIsoRightDerived (supportedSectionsFunctor X.toRingedSpace T)
    (supportPush hT) (derivedSupportedPushforwardUnit X.toRingedSpace T hT) enoughKInjectives n

/-! ### The two readings, each written out -/

variable (F : X.Modules)

/-- **The Gysin reading of [Stacks, Tag 0G74] part (2) at a module, written out.**  The lemma
`Stacks.Perfect.SupportedEndoForgetDegreewise.supportCohomologySheafForgetIso_hom_app` says it is
`Stacks.Perfect.AbelianSupportedEndoModelBridge.endoForgetIsoApp`, and that is by definition the
inverse of `Stacks.Perfect.AbelianCechCokernelPassage.forgetDerivedHomology`, the degree-`n`
cohomology of [Stacks, Tag 0G74] part (2) on the unbounded derived category, the derived functor
applied to `Φ(ℱ[0]) ≅ (Φℱ)[0]`, and the model bridge
`Stacks.Perfect.AbelianSupportedEndoModelBridge.abelianModelApp`. -/
theorem lhs_hom :
    (Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafForgetIso hT n).hom.app F =
      ((forgetDerivedHomology (supportPushSingle hT F) (n : ℤ)).inv ≫
          (DerivedCategory.homologyFunctor
              (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).map
            ((forgetComparison hT).app
              ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≫
            (DerivedCategory.homologyFunctor
                (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).map
              ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).map
                (singleForgetIso F).hom)) ≫
        (abelianModelApp hT n F).hom :=
  Stacks.Perfect.SupportedEndoForgetDegreewise.supportCohomologySheafForgetIso_hom_app hT n F

/-- **The endofunctor reading of [Stacks, Tag 0G74] part (2) at a module, written out.**
`Stacks.Cohomology.SupportedComplexes.degreewiseForgetComparison` is by definition the source
corner inverted, the degree-`n` cohomology of the comparison of total derived functors, and the
target corner; the three are spelled out here.

The source corner contributes `supportCohomologySheafFunctorEndoIso` inverted followed by
`forgetDerivedHomology` inverted — the pull of the forgetful functor out of the cohomology of the
derived category *is* `forgetDerivedHomology`, both being
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`.  The middle factor is the degree-`n`
cohomology of `Stacks.Perfect.AbelianCechDerivedSquare.forgetComparison`, which at the canonical
total derived functors is `Stacks.Cohomology.DerivedExcisionSquare.forgetComparison`.  The target
corner contributes `Φ` pushed into the single functor — the Mathlib reading of
`Φ(ℱ[0]) ≅ (Φℱ)[0]` — followed by the canonical bridge of `i_* R𝓗_T^{ab}`. -/
theorem endo_app :
    (localCohomologyEndoForgetComparison T (supportPush hT)
        (derivedSupportedPushforwardUnit X.toRingedSpace T hT)
        (derivedAbelianSupportedPushforward X.toRingedSpace T hT)
        (derivedAbelianSupportedPushforwardUnit X.toRingedSpace T hT) n).app F =
      ((abelianSheaf X).map ((supportCohomologySheafFunctorEndoIso hT n).inv.app F) ≫
            (forgetDerivedHomology (supportPushSingle hT F) (n : ℤ)).inv) ≫
        (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).map
          ((forgetComparison hT).app
            ((DerivedCategory.singleFunctor X.Modules 0).obj F)) ≫
          (DerivedCategory.homologyFunctor
              (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).map
            ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).map
              (singleForgetMathlib X.toRingedSpace F).hom) ≫
            (singleCompDerivedCompHomologyIsoRightDerived (abelianSupportedSections T)
              (derivedAbelianSupportedPushforward X.toRingedSpace T hT)
              (derivedAbelianSupportedPushforwardUnit X.toRingedSpace T hT)
              enoughKInjectives n).hom.app ((abelianSheaf X).obj F) := rfl

/-! ### The two spellings of Stacks 0G74 part (2) agree -/

/-- **[Stacks, Tag 0G74] part (2) in the Gysin spelling is [Stacks, Tag 0G74] part (2) at the
supported-sections endofunctor spelling.**

For a scheme `X`, a closed subset `T ⊆ X`, a degree `n : ℕ` and an `𝒪_X`-module `ℱ`, the
comparison `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafForgetIso` — whose source is
the degree-`n` cohomology sheaf of `i_* R𝓗_T(ℱ[0])` and whose target the classical abelian local
cohomology sheaf on `T` pushed forward to `X` — is the comparison
`Stacks.Cohomology.DegreewiseExcisionSquare.localCohomologyEndoForgetComparison` between the two
`ℕ`-indexed right derived functors of the supported-sections endofunctors, conjugated by
`supportCohomologySheafFunctorEndoIso` on the module side and by
`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafPushforwardIso` on the abelian
side.

The endofunctor comparison is taken at the canonical total right derived functors
`Stacks.Perfect.SupportedFraction.supportPush` and
`Stacks.Cohomology.AbelianSupportedCounit.derivedAbelianSupportedPushforward`, which is what
makes the two comparisons of [Stacks, Tag 0G74] part (2) on the unbounded derived category the
same transformation.

There is no hypothesis beyond `hT`: no restriction on the degree, no quasi-coherence, nothing on
the module.  In particular the statement holds verbatim on an open subscheme `U ⊆ X` at the
subset `U.ι ⁻¹' T`, which is what [Stacks, Tag 0G87] for the Gysin map's local cohomology sheaves
needs. -/
theorem supportCohomologySheafForgetIso_eq_localCohomologyEndoForget :
    (Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafForgetIso hT n).hom.app F =
      (abelianSheaf X).map ((supportCohomologySheafFunctorEndoIso hT n).hom.app F) ≫
        (localCohomologyEndoForgetComparison T (supportPush hT)
            (derivedSupportedPushforwardUnit X.toRingedSpace T hT)
            (derivedAbelianSupportedPushforward X.toRingedSpace T hT)
            (derivedAbelianSupportedPushforwardUnit X.toRingedSpace T hT) n).app F ≫
          (abelianLocalCohomologySheafPushforwardIso T hT n).inv.app
            ((abelianSheaf X).obj F) := by
  have huu : (abelianSheaf X).map ((supportCohomologySheafFunctorEndoIso hT n).hom.app F) ≫
        (abelianSheaf X).map ((supportCohomologySheafFunctorEndoIso hT n).inv.app F) =
      CategoryStruct.id
        ((abelianSheaf X).obj ((supportCohomologySheafFunctor hT (n : ℤ)).obj F)) := by
    rw [← (abelianSheaf X).map_comp,
      (supportCohomologySheafFunctorEndoIso hT n).hom_inv_id_app, (abelianSheaf X).map_id]
  have hg : (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).map
        ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).map
          (singleForgetIso F).hom) =
      (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).map
        ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).map
          (singleForgetMathlib X.toRingedSpace F).hom) :=
    congrArg (fun z => (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).map
        ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).map (Iso.hom z)))
      (singleForgetIso_eq F)
  have hA : (singleCompDerivedCompHomologyIsoRightDerived (abelianSupportedSections T)
            (derivedAbelianSupportedPushforward X.toRingedSpace T hT)
            (derivedAbelianSupportedPushforwardUnit X.toRingedSpace T hT)
            enoughKInjectives n).hom.app ((abelianSheaf X).obj F) ≫
        (abelianLocalCohomologySheafPushforwardIso T hT n).inv.app
          ((abelianSheaf X).obj F) =
      (abelianModelApp hT n F).hom :=
    (abelianModelComponent_hom_comp_pushforwardIso X.toRingedSpace T hT n
      ((abelianSheaf X).obj F)).symm
  exact (lhs_hom hT n F).trans
    ((assemble_formal _ _ _ _ _ _ _ _ _ huu hg hA).trans
      (congrArg (fun t =>
          (abelianSheaf X).map ((supportCohomologySheafFunctorEndoIso hT n).hom.app F) ≫ t ≫
            (abelianLocalCohomologySheafPushforwardIso T hT n).inv.app
              ((abelianSheaf X).obj F))
        (endo_app hT n F).symm))

/-! ### The same on an open subscheme, in the spelling the degreewise square of 0G87 uses -/

/-- **[Stacks, Tag 0G74] part (2) in the Gysin spelling is
`Stacks.Cohomology.DegreewiseExcisionSquare.localCohomologyEndoForgetComparisonOpen`**, the
degree-`n` comparison on the open subscheme `U` at the preimage of `T` — the spelling that the
left-hand leg of the degreewise square
`Stacks.Cohomology.DegreewiseExcisionSquare.forget_localCohomologyRestrict_comm` of
[Stacks, Tag 0G87] is stated in.

This is `supportCohomologySheafForgetIso_eq_localCohomologyEndoForget` at the scheme `U` and the
closed subset `U.ι ⁻¹' T`: the comparison on `U` is the comparison of this file at that scheme
and that subset, the two being
`Stacks.Cohomology.SupportedComplexes.degreewiseForgetComparison` at the same datum.  It is
recorded because the square of [Stacks, Tag 0G87] names the `..Open` spelling, and reading the
identity there should not ask a consumer to cross the two spellings itself. -/
theorem supportCohomologySheafForgetIso_eq_localCohomologyEndoForgetOpen (T : Set X)
    (U : X.Opens) (hTU : IsClosed (U.ι ⁻¹' T)) (F : U.toScheme.Modules) :
    (Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafForgetIso hTU n).hom.app F =
      (abelianSheaf U.toScheme).map
          ((supportCohomologySheafFunctorEndoIso hTU n).hom.app F) ≫
        (Stacks.Cohomology.DegreewiseExcisionSquare.localCohomologyEndoForgetComparisonOpen T U
            (supportPush hTU)
            (derivedSupportedPushforwardUnit U.toScheme.toRingedSpace (U.ι ⁻¹' T) hTU)
            (derivedAbelianSupportedPushforward U.toScheme.toRingedSpace (U.ι ⁻¹' T) hTU)
            (derivedAbelianSupportedPushforwardUnit U.toScheme.toRingedSpace (U.ι ⁻¹' T) hTU)
            n).app F ≫
          (abelianLocalCohomologySheafPushforwardIso (U.ι ⁻¹' T) hTU n).inv.app
            ((abelianSheaf U.toScheme).obj F) :=
  supportCohomologySheafForgetIso_eq_localCohomologyEndoForget hTU n F

end Stacks.Perfect.SupportedEndoForgetEndofunctor

end
