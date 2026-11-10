module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.QuasicoherentSupportedComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalToGlobalSectionsWithSupport

/-!
# The two spellings of the canonical map `i_* R𝓗_T(K) ⟶ K` agree

Let `T` be a closed subset of a ringed space `X` and let `i : (T, 𝒪_X|_T) ⟶ (X, 𝒪_X)` be the
inclusion.  The canonical map `i_* R𝓗_T(K) ⟶ K` of [Stacks, Tag 0G72] is built in this
repository in two different ways, and nothing so far relates them.

* As a **derived-functor transition**:
  `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsToId` descends the sheaf-level
  inclusion `i_*ℋ_T(ℱ) ⊆ ℱ` along the derivation unit of an arbitrary right derived functor of
  `ℱ ↦ i_*ℋ_T(ℱ)`.  At the chosen derived functor
  `Stacks.Perfect.SupportedQuasicoherent.derivedSupportedPushforward` this is the map that
  `Stacks.Perfect.SupportedFraction.supportPushCounit` abbreviates, hence the map that
  `Stacks.Perfect.SupportedFraction.cechToDerivedSupport` inverts and that
  `Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare` is stated for.
* As an **adjunction counit**: the counit of
  `Stacks.Cohomology.SupportedComplexes.derivedPushforwardAdjunction`, the term form of
  [Stacks, Tag 0A3B] part (1).  This is the map that
  `Stacks.Cohomology.SupportedComplexes.derivedPushforwardSupportedSectionsIso` of
  [Stacks, Tag 0AEF] part (2) inverts, hence the map underlying
  `Stacks.Perfect.CechLocalCohomology.pushforwardLocalCohomologyIso` and the Gysin classes built
  from it.

## Main results

* `derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit`: the two are **equal**,

  `derivedSupportedSectionsToId X T (derivedSupportedPushforward X T hT)
      (derivedSupportedPushforwardUnit X T hT) = (derivedPushforwardAdjunction X T hT).counit`

  as natural transformations `i_* R𝓗_T ⟶ 𝟭` on `D(𝒪_X)`.  The only hypothesis is `IsClosed T`.
  Since `Stacks.Perfect.SupportedFraction.supportPush` and
  `Stacks.Perfect.SupportedFraction.supportPushCounit` are reducible abbreviations of the two
  arguments of the left-hand side at `X.toRingedSpace`, this is also the identification of
  `supportPushCounit hT` with the Tag 0A3B counit for a scheme `X`.

* `derivedPushforwardAdjunction_counit_app` and
  `derivedAdjunctionOfExactLeftAdjoint_counit_app`: the counit counterparts of
  `Stacks.Cohomology.SupportedComplexes.derivedPushforwardAdjunction_unit_app` and
  `Stacks.Cohomology.SupportedComplexes.derivedAdjunctionOfExactLeftAdjoint_unit_app` — the
  compatibility of the derived counit with the underived one, which is
  `CategoryTheory.Adjunction.derivedε_fac_app` read at the chosen adjunction.

## Implementation notes

Both sides are transformations **out of a right derived functor** of `ℱ ↦ i_*ℋ_T(ℱ)`, namely out
of `i_* R𝓗_T` at the derivation unit
`Stacks.Perfect.SupportedQuasicoherent.derivedSupportedPushforwardUnit`, so
`CategoryTheory.Functor.rightDerived_ext` reduces the equality to an equality after composing
with that derivation unit.  There the two sides become computable:

* the transition side is `derivedSupportedSectionsToId_fac`, the sheaf-level inclusion localized;
* the adjunction side is `derivedPushforwardAdjunction_counit_app` after the derivation unit is
  split into its three factors by `derivedSupportedPushforwardUnit` and
  `derivedSupportedPushforwardSplit`; the comparison of the exact direct image occurs there once
  inverted and once not, and cancels.

What is left is an identity in the homotopy category between the localization of the inclusion
`i_*ℋ_T(ℱ) ⊆ ℱ` and the localization of the counit of the underived adjunction of
[Stacks, Tag 0G6P], transported along the realization isomorphism
`supportedSectionsOnClosedFunctor_comp_modulePushforward_iso`.  Every term of it is the class of
a map of complexes, so it is `congrArg` of a degreewise identity, and in each degree it is
exactly `Stacks.Cohomology.LocalToGlobalSupport.counit_app_eq`: *the counit of Tag 0G6P is the
inclusion of the supported-sections subsheaf*.

**Carried hypotheses.**  `derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit`
carries only `hT : IsClosed T`, which is already needed to write either side down (the direct
image from `T` is exact only for a closed `T`, and `derivedSupportedSectionsOnClosed` takes
`hT`).  There is no quasi-coherence hypothesis, no hypothesis on the coefficient sheaf and no
retrocompactness of the open complement.

**No `@[stacks ...]` attribute is attached to any declaration here.**

## References

* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Lemma 17.5.7 (Tag 0G6P)](https://stacks.math.columbia.edu/tag/0G6P)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.RestrictionCover (homotopyIdentityIso)
open Stacks.Cohomology.SupportedComplexes
open Stacks.SheafOfModules.SupportedSections
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward
  derivedSupportedPushforwardSplit derivedSupportedPushforwardUnit)

universe u

namespace Stacks.Perfect.SupportCounitComparison

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The counit of a chosen derived adjunction with exact left adjoint -/

section Derived

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  {G₀ : B ⥤ A} {H₀ : A ⥤ B} [G₀.Additive] [H₀.Additive]
  [PreservesFiniteLimits G₀] [PreservesFiniteColimits G₀]

/-- **The counit of the chosen derived adjunction is the canonical comparison.**  For an
adjunction `G₀ ⊣ H₀` of additive functors with `G₀` exact and a right derived functor `RF` of
`H₀` with derivation unit `β`, the counit of
`Stacks.Cohomology.SupportedComplexes.derivedAdjunctionOfExactLeftAdjoint`, preceded by `G₀`
applied to `β`, is computed from the counit of the underived adjunction on homotopy categories.

This is `CategoryTheory.Adjunction.derivedε_fac_app`, and it is the counit counterpart of
`Stacks.Cohomology.SupportedComplexes.derivedAdjunctionOfExactLeftAdjoint_unit_app`; the three
derived-functor instances are discharged exactly as there. -/
theorem derivedAdjunctionOfExactLeftAdjoint_counit_app (adj : G₀ ⊣ H₀)
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (β : H₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (J : CochainComplex A ℤ) (q : K ⟶ J),
      J.IsKInjective ∧ QuasiIso q)
    (M : HomotopyCategory A (ComplexShape.up ℤ)) :
    G₀.mapDerivedCategory.map (β.app M) ≫
        (derivedAdjunctionOfExactLeftAdjoint adj RF β hres).counit.app
          (DerivedCategory.Qh.obj M) =
      G₀.mapDerivedCategoryFactorsh.hom.app
          ((H₀.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).counit.app M) :=
  let _ := isLeftDerivedFunctor_mapDerivedCategory_of_exact (G₀ := G₀)
  let _ := isLeftDerivedFunctor_mapDerivedCategory_comp_of_exact (G₀ := G₀) RF
  let _ := Functor.isRightDerivedFunctor_comp_of_coresolutions
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) β G₀.mapDerivedCategory
    (exists_quasiIso_qh_map_bijective hres)
  (Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    G₀.mapDerivedCategoryFactorsh.hom β M

end Derived

/-! ### The counit of the adjunction of Stacks 0A3B -/

variable (X : RingedSpace.{u, u}) (T : Set X.carrier) (hT : IsClosed T)

/-- **The counit of the chosen adjunction of [Stacks, Tag 0A3B] part (1) is the canonical
comparison** `i_* R𝓗_T(K) ⟶ K`: preceded by `i_*` applied to the derivation unit of `R𝓗_T` it is
computed from the counit `i_* H_T(F) ⟶ F` of the underived adjunction of [Stacks, Tag 0G6P].

This is the counit counterpart of
`Stacks.Cohomology.SupportedComplexes.derivedPushforwardAdjunction_unit_app`. -/
theorem derivedPushforwardAdjunction_counit_app
    (M : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    letI := pushforward_preservesFiniteLimits X T
    letI := pushforward_preservesFiniteColimits X T hT
    (modulePushforward (closedSubsetInclusion X T)).mapDerivedCategory.map
          ((derivedSupportedSectionsOnClosedUnit X T hT).app M) ≫
        (derivedPushforwardAdjunction X T hT).counit.app (DerivedCategory.Qh.obj M) =
      (modulePushforward (closedSubsetInclusion X T)).mapDerivedCategoryFactorsh.hom.app
          (((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map
          ((Adjunction.mapHomotopyCategoryAdjunction
            (modulePushforward_supportedSectionsOnClosed_adjunction X T hT)
            (ComplexShape.up ℤ)).counit.app M) :=
  let _ := pushforward_preservesFiniteLimits X T
  let _ := pushforward_preservesFiniteColimits X T hT
  derivedAdjunctionOfExactLeftAdjoint_counit_app
    (modulePushforward_supportedSectionsOnClosed_adjunction X T hT)
    (derivedSupportedSectionsOnClosed X T hT) (derivedSupportedSectionsOnClosedUnit X T hT)
    (exists_isKInjective_quasiIso_moduleSheaves X) M

/-! ### The underived identity, transported -/

/-- The two spellings of the inclusion of the subsheaf of sections supported on `T` as a natural
transformation into the identity functor agree:
`Stacks.Cohomology.SupportedComplexes.supportedSectionsSubsheafInclusion` and
`Stacks.Cohomology.LocalToGlobalSupport.supportedSectionsι` are both given at a module by
`supportedSectionsSheafι`. -/
theorem supportedSectionsSubsheafInclusion_eq_supportedSectionsι :
    supportedSectionsSubsheafInclusion X T =
      Stacks.Cohomology.LocalToGlobalSupport.supportedSectionsι X T :=
  NatTrans.ext (funext fun _ => rfl)

/-- **The counit of [Stacks, Tag 0G6P] is the inclusion of the supported sections, degreewise on
a complex.**  Both sides are, in each degree, the inclusion `H_T(K.X i) ⊆ K.X i`, so this is
`Stacks.Cohomology.LocalToGlobalSupport.counit_app_eq` at `K.X i`. -/
private lemma counit_eq_inclusion_complex
    (K : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (NatTrans.mapHomologicalComplex (supportedSectionsSubsheafInclusion X T)
          (ComplexShape.up ℤ)).app K ≫
        (Functor.mapHomologicalComplexIdIso (_root_.SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).hom.app K =
      (Functor.mapHomologicalComplexCompIso
          (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X T hT)
          (ComplexShape.up ℤ)).inv.app K ≫
        (Adjunction.mapHomologicalComplexAdjunction
          (modulePushforward_supportedSectionsOnClosed_adjunction X T hT)
          (ComplexShape.up ℤ)).counit.app K := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  change (supportedSectionsSubsheafInclusion X T).app (K.X i) ≫ 𝟙 _ =
    (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X T hT).inv.app (K.X i) ≫
      (modulePushforward_supportedSectionsOnClosed_adjunction X T hT).counit.app (K.X i)
  rw [Stacks.Cohomology.LocalToGlobalSupport.counit_app_eq X T hT (K.X i),
    supportedSectionsSubsheafInclusion_eq_supportedSectionsι X T, Category.comp_id,
    Iso.inv_hom_id_app_assoc]

/-- **The counit of [Stacks, Tag 0G6P] is the inclusion of the supported sections, in the
homotopy category.**  Every term is the class of a map of complexes, so this is `congrArg` of
`counit_eq_inclusion_complex` at the representing complex. -/
private lemma counit_eq_inclusion_homotopy
    (M : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (NatTrans.mapHomotopyCategory (supportedSectionsSubsheafInclusion X T)
          (ComplexShape.up ℤ)).app M ≫ (homotopyIdentityIso (structureSheafRing X)).hom.app M =
      (Functor.mapHomotopyCategoryCompIso
          (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X T hT)
          (ComplexShape.up ℤ)).inv.app M ≫
        (Adjunction.mapHomotopyCategoryAdjunction
          (modulePushforward_supportedSectionsOnClosed_adjunction X T hT)
          (ComplexShape.up ℤ)).counit.app M := by
  have h := congrArg
    (HomotopyCategory.quotient (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)).map (counit_eq_inclusion_complex X T hT M.as)
  simp only [Functor.map_comp] at h
  exact h

/-! ### The two constructions agree -/

/-- The reassociation of `derivedSupportedPushforwardSplit`, which splits the exact direct image
off the derivation unit, followed by the comparison of that direct image, is the localized
realization isomorphism of [Stacks, Tag 0G6N]: the two comparisons of the exact direct image
occur once inverted and once not, and cancel. -/
private lemma split_comp_factorsh
    (M : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    letI := pushforward_preservesFiniteLimits X T
    letI := pushforward_preservesFiniteColimits X T hT
    (derivedSupportedPushforwardSplit X T hT).hom.app M ≫
        (modulePushforward (closedSubsetInclusion X T)).mapDerivedCategoryFactorsh.hom.app
          (((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj M) =
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso
          (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X T hT)
          (ComplexShape.up ℤ)).inv.app M) := by
  let _ := pushforward_preservesFiniteLimits X T
  let _ := pushforward_preservesFiniteColimits X T hT
  change (DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso
          (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X T hT)
          (ComplexShape.up ℤ)).inv.app M) ≫
      (𝟙 _ ≫
        ((modulePushforward (closedSubsetInclusion X T)).mapDerivedCategoryFactorsh.inv.app
            (((supportedSectionsOnClosedFunctor X T hT).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj M) ≫ 𝟙 _))) ≫ _ = _
  rw [Category.id_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- **The adjunction counit of [Stacks, Tag 0A3B] part (1), preceded by the derivation unit of
`i_* R𝓗_T`, is the localized inclusion of the supported sections.**  The derivation unit is
spelled out through `derivedSupportedPushforwardSplit`, so that no step has to unfold `i_* R𝓗_T`;
what remains is `derivedPushforwardAdjunction_counit_app`, the cancellation
`split_comp_factorsh`, and the underived identity `counit_eq_inclusion_homotopy`. -/
private lemma unit_comp_counit_app
    (M : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    letI := pushforward_preservesFiniteLimits X T
    letI := pushforward_preservesFiniteColimits X T hT
    ((derivedSupportedPushforwardSplit X T hT).hom.app M ≫
          ((modulePushforward (closedSubsetInclusion X T)).mapDerivedCategory.map
              ((derivedSupportedSectionsOnClosedUnit X T hT).app M) ≫ 𝟙 _)) ≫
        (derivedPushforwardAdjunction X T hT).counit.app (DerivedCategory.Qh.obj M) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (supportedSectionsSubsheafInclusion X T)
            (ComplexShape.up ℤ)).app M) ≫
        DerivedCategory.Qh.map ((homotopyIdentityIso (structureSheafRing X)).hom.app M) := by
  let _ := pushforward_preservesFiniteLimits X T
  let _ := pushforward_preservesFiniteColimits X T hT
  rw [Category.comp_id, Category.assoc, derivedPushforwardAdjunction_counit_app X T hT M,
    ← Category.assoc, split_comp_factorsh X T hT M, ← Functor.map_comp, ← Functor.map_comp,
    counit_eq_inclusion_homotopy X T hT M]

/-- **The derived-functor transition and the adjunction counit are the same map
`i_* R𝓗_T(K) ⟶ K`.**  The canonical map of [Stacks, Tag 0G72] obtained by descending the
sheaf-level inclusion `i_*ℋ_T(ℱ) ⊆ ℱ` along the derivation unit of the chosen derived functor
`i_* R𝓗_T` is the counit of the adjunction `i_*^D ⊣ R𝓗_T` of [Stacks, Tag 0A3B] part (1).

Both sides are transformations out of a right derived functor of `ℱ ↦ i_*ℋ_T(ℱ)`, so they agree
as soon as they agree after composing with the derivation unit, which is
`derivedSupportedSectionsToId_fac` on one side and `unit_comp_counit_app` on the other.

The only hypothesis is `hT : IsClosed T`. -/
theorem derivedSupportedSectionsToId_eq_derivedPushforwardAdjunction_counit :
    letI := pushforward_preservesFiniteLimits X T
    letI := pushforward_preservesFiniteColimits X T hT
    derivedSupportedSectionsToId X T (derivedSupportedPushforward X T hT)
        (derivedSupportedPushforwardUnit X T hT) =
      (derivedPushforwardAdjunction X T hT).counit := by
  let _ := pushforward_preservesFiniteLimits X T
  let _ := pushforward_preservesFiniteColimits X T hT
  change derivedSupportedSectionsToId X T (derivedSupportedPushforward X T hT)
      (derivedSupportedPushforwardUnit X T hT) =
    (derivedPushforwardAdjunction X T hT).counit
  refine Functor.rightDerived_ext (derivedSupportedPushforward X T hT)
    (derivedSupportedPushforwardUnit X T hT)
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) _ _ _ ?_
  rw [derivedSupportedSectionsToId_fac]
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  exact (unit_comp_counit_app X T hT M).symm

end Stacks.Perfect.SupportCounitComparison

end
