module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps

/-!
# Complexes supported on a closed subset come from that subset

Let `Z` be a closed subset of a ringed space `X`, let `i : (Z, 𝒪_X|_Z) ⟶ (X, 𝒪_X)` be the
inclusion and let `RH_Z : D(𝒪_X) ⥤ D(𝒪_X|_Z)` be the right derived functor of sections
supported on `Z`.  Pushforward along `i` is exact, so it induces `i_*^D : D(𝒪_X|_Z) ⥤ D(𝒪_X)`,
and it is fully faithful.  This file proves that its essential image is exactly the complexes
whose cohomology sheaves are supported on `Z`: for such a complex `K` the canonical map
`i_* RH_Z(K) ⟶ K`, the counit of the adjunction `i_*^D ⊣ RH_Z`, is an isomorphism, and
`i_*^D` is therefore an equivalence of `D(𝒪_X|_Z)` with the full subcategory `D_Z(𝒪_X)`.

## Main definitions

* `equivalenceOfCounitIso`: an adjunction with invertible unit, as an equivalence onto a full
  subcategory on which the counit is invertible.
* `supportedDerivedProperty`: `D_Z(𝒪_X)` as a property of objects of `D(𝒪_X)`.
* `derivedPushforwardSupportedSectionsIso`: the canonical isomorphism `i_* RH_Z(K) ≅ K` for `K`
  supported on `Z`.
* `closedSubsetDerivedPushforwardEquivalence`: the equivalence `D(𝒪_X|_Z) ≌ D_Z(𝒪_X)` induced
  by `i_*`.

## Main results

* `essImage_derivedPushforward_of_supported`: a complex with cohomology sheaves supported on `Z`
  is the derived pushforward of a complex on `Z`.
* `isIso_derivedPushforwardAdjunction_counit_app_of_supported`: **Stacks 0AEF, part (2)**, the
  counit `i_* RH_Z(K) ⟶ K` is an isomorphism at such a `K`.
* `closedSubsetDerivedPushforwardEquivalence_functor` and `…_inverse`: the equivalence is given
  by `i_*` and its quasi-inverse by `RH_Z`.

## Implementation notes

The essential-image statement is the whole content, the rest being formal: for an adjunction
`L ⊣ R` with `L` fully faithful the counit is invertible at `K` exactly when `K` lies in the
essential image of `L`, by `CategoryTheory.Adjunction.isIso_counit_app_iff_mem_essImage`, and
full faithfulness of `i_*^D` is invertibility of the unit, which is Stacks 0A3B (2).

That a supported complex lies in the essential image is proved at a K-injective representative
`I` with injective terms, as [Stacks, Tag 0AEF] does it, by way of the short exact sequence

`0 ⟶ i_* ℋ_Z(I) ⟶ I ⟶ j_*(I|_U) ⟶ 0`, `U = X ∖ Z`

of Stacks 0G72 — short exact degreewise because the terms of `I` are injective, which is
`supportedSectionsRestrictPushShortExact` — turned into a distinguished triangle by
`DerivedCategory.triangleOfSES`.  Its third term vanishes in the derived category: the
restriction of `I` to `U` is an acyclic K-injective complex, hence null-homotopic, and `j_*` is
additive, which is `isZero_Q_restrictPush_of_supported`.  So the first map is invertible, and
its source is `i_*` applied degreewise to `ℋ_Z(I)`, hence in the essential image of `i_*^D`
through `Functor.mapDerivedCategoryFactors`.

The triangle is used only at the K-injective representative, so the functorial triangle of
Stacks 0G72 in the derived category is not needed; nor is any identification of the connecting
map, only the vanishing of the third term.

## References

* [Stacks Project, Lemma 20.34.4 (Tag 0AEF)](https://stacks.math.columbia.edu/tag/0AEF)
* [Stacks Project, Lemma 20.34.1 (Tag 0A3B)](https://stacks.math.columbia.edu/tag/0A3B)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Lemma 59.46.1 (Tag 0AEG)](https://stacks.math.columbia.edu/tag/0AEG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open ExtensionByZeroModules
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.RestrictionCover
open Stacks.Cohomology.SectionsWithSupport (openComplement)
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

/-! ### An adjunction with invertible unit as an equivalence onto a subcategory -/

section Equivalence

variable {A C : Type*} [Category* A] [Category* C]

/-- An adjunction whose unit is invertible restricts to an equivalence of the left adjoint's
source with any full subcategory of its target which contains the image of the left adjoint and
on which the counit is invertible; the quasi-inverse is the right adjoint restricted there.

This is the dual of `AlgebraicGeometry.equivalenceOfUnitIso`. -/
def equivalenceOfCounitIso {L : A ⥤ C} {R : C ⥤ A} (adj : L ⊣ R) [IsIso adj.unit]
    (P : ObjectProperty C) (hL : ∀ X, P (L.obj X))
    (hP : ∀ Y, P Y → IsIso (adj.counit.app Y)) :
    A ≌ P.FullSubcategory :=
  let F := P.lift L hL
  let G := P.ι ⋙ R
  let α : 𝟭 A ≅ F ⋙ G := asIso adj.unit
  let β : G ⋙ F ≅ 𝟭 P.FullSubcategory :=
    Functor.fullyFaithfulCancelRight P.ι (NatIso.ofComponents
      (fun Y => letI := hP Y.obj Y.property; asIso (adj.counit.app Y.obj))
      (fun f => adj.counit.naturality f.hom))
  CategoryTheory.Equivalence.mk F G α β

/-- For an adjunction `L ⊣ R` whose counit is invertible on a full subcategory `P`, the counit
identifies the inclusion `P.ι` with `R` followed by `L`.

This is the natural isomorphism underlying the quasi-inverse half of `equivalenceOfCounitIso`. -/
def iotaIsoCompOfCounitIso {L : A ⥤ C} {R : C ⥤ A} (adj : L ⊣ R) (P : ObjectProperty C)
    (hP : ∀ Y, P Y → IsIso (adj.counit.app Y)) :
    (P.ι ⋙ R) ⋙ L ≅ P.ι :=
  letI : ∀ Y : P.FullSubcategory, IsIso (adj.counit.app Y.obj) := fun Y => hP Y.obj Y.property
  NatIso.ofComponents (fun Y => asIso (adj.counit.app Y.obj))
    (fun f => adj.counit.naturality f.hom)

/-- In the situation of `equivalenceOfCounitIso`, the inclusion of the full subcategory is a
*left* adjoint, with right adjoint the right adjoint `R` followed by the lift of `L`.

Indeed `P.ι` is the quasi-inverse of that equivalence followed by `L`, the comparison being
`iotaIsoCompOfCounitIso`, so `Adjunction.comp` of the equivalence with `adj` has `P.ι` as left
adjoint. -/
def iotaAdjunctionOfCounitIso {L : A ⥤ C} {R : C ⥤ A} (adj : L ⊣ R) [IsIso adj.unit]
    (P : ObjectProperty C) (hL : ∀ X, P (L.obj X))
    (hP : ∀ Y, P Y → IsIso (adj.counit.app Y)) :
    P.ι ⊣ R ⋙ P.lift L hL :=
  Adjunction.ofNatIsoLeft
    ((equivalenceOfCounitIso adj P hL hP).symm.toAdjunction.comp adj)
    (iotaIsoCompOfCounitIso adj P hP)

end Equivalence

/-! ### The supported-sections sequence of a complex -/

/-- `D_Z(𝒪_X)`, as a property of objects of `D(𝒪_X)`: every cohomology sheaf of the complex is
supported on the closed subset `Z`. -/
abbrev supportedDerivedProperty (X : RingedSpace.{u, u}) (Z : Set X.carrier) :
    ObjectProperty (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :=
  AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z

section EssImage

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-- The short complex `i_* ℋ_Z(I) ⟶ I ⟶ j_*(I|_U)` of a cochain complex `I` of `𝒪_X`-modules,
where `U = X ∖ Z`, obtained by applying the three functors degreewise. -/
private def supportedSectionsComplexShortComplex
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    ShortComplex (CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ) where
  X₁ := ((supportedSectionsFunctor X Z).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  X₂ := I
  X₃ := ((restrictPush (structureSheafRing X) (openComplement Z hZ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I
  f :=
    { f := fun n => (supportedSectionsSubsheafInclusion X Z).app (I.X n)
      comm' := fun n m _ =>
        ((supportedSectionsSubsheafInclusion X Z).naturality (I.d n m)).symm }
  g :=
    { f := fun n => (jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit.app (I.X n)
      comm' := fun n m _ =>
        ((jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit.naturality
          (I.d n m)).symm }
  zero := HomologicalComplex.hom_ext _ _ fun n => by
    simpa using
      NatTrans.congr_app (supportedSectionsSubsheafInclusion_comp_unit X Z hZ) (I.X n)

/-- The supported-sections sequence of a cochain complex with injective terms is short exact,
being degreewise the short exact sequence of Stacks 0G72 at an injective sheaf of modules. -/
@[sga "2 I 1.9" "special case"]
private theorem supportedSectionsComplexShortExact
    (I : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hInj : ∀ n : ℤ, Injective (I.X n)) :
    (supportedSectionsComplexShortComplex X Z hZ I).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  exact fun n => have := hInj n; supportedSectionsRestrictPushShortExact X Z hZ (I.X n)

/-- A complex of `𝒪_X`-modules whose cohomology sheaves are supported on the closed subset `Z`
is the derived pushforward of a complex of `𝒪_X|_Z`-modules: at a K-injective representative
with injective terms it is `i_*` of the complex of sections supported on `Z`. -/
theorem essImage_derivedPushforward_of_supported
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z K) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.essImage K := by
  let _ := pushforward_preservesFiniteLimits X Z
  let _ := pushforward_preservesFiniteColimits X Z hZ
  let Q := DerivedCategory.Q (C := _root_.SheafOfModules.{u} (structureSheafRing X))
  obtain ⟨I, q, hKI, hInj, hq⟩ :=
    Stacks.Cohomology.PushforwardRestriction.exists_quasiIso_isKInjective_injective_sheafOfModules
      (structureSheafRing X) (Q.objPreimage K)
  let e : K ≅ Q.obj I := (Q.objObjPreimageIso K).symm ≪≫ asIso (Q.map q)
  have hI : Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn
      (structureSheafRing X) Z (Q.obj I) :=
    Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso
      (structureSheafRing X) Z e hK
  have hiso : IsIso (Q.map (supportedSectionsComplexShortComplex X Z hZ I).f) :=
    (Triangle.isZero₃_iff_isIso₁ _ (DerivedCategory.triangleOfSES_distinguished
      (supportedSectionsComplexShortExact X Z hZ I hInj))).mp
      (Stacks.Cohomology.PushforwardRestriction.isZero_Q_restrictPush_of_supported
        (structureSheafRing X) (openComplement Z hZ) Z (fun _ hx => hx) I hKI hI)
  let eI := asIso (Q.map (supportedSectionsComplexShortComplex X Z hZ I).f)
  refine ⟨DerivedCategory.Q.obj
    (((supportedSectionsOnClosedFunctor X Z hZ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I), ⟨?_⟩⟩
  exact ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategoryFactors.app
      (((supportedSectionsOnClosedFunctor X Z hZ).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)) ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
      (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ)
      (ComplexShape.up ℤ)).app I) ≪≫
    eI ≪≫ e.symm

end EssImage

/-! ### Part (2): the derived pushforward is an equivalence onto the supported complexes -/

/-- **Stacks 0AEF, part (2).** For `K` in `D(𝒪_X)` whose cohomology sheaves are supported on
the closed subset `Z`, the canonical map `i_* RH_Z(K) ⟶ K` — the counit of the adjunction
`i_*^D ⊣ RH_Z` of Stacks 0A3B (1) — is an isomorphism. -/
@[stacks 0AEF "part (2): the counit i_*RℋZ(K) ⟶ K is invertible at every K supported on Z, \
  which is the essential-image content of the equivalence"]
theorem isIso_derivedPushforwardAdjunction_counit_app_of_supported (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z)
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z K) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    IsIso ((derivedPushforwardAdjunction X Z hZ).counit.app K) := by
  let _ := pushforward_preservesFiniteLimits X Z
  let _ := pushforward_preservesFiniteColimits X Z hZ
  have _ := isIso_unit_derivedPushforwardAdjunction X Z hZ
  have _ := ((derivedPushforwardAdjunction X Z hZ).fullyFaithfulLOfIsIsoUnit).full
  have _ := ((derivedPushforwardAdjunction X Z hZ).fullyFaithfulLOfIsIsoUnit).faithful
  exact (Adjunction.isIso_counit_app_iff_mem_essImage _).mpr
    (essImage_derivedPushforward_of_supported X Z hZ K hK)

/-- **Stacks 0AEF, part (2), as an isomorphism.** For `K` in `D(𝒪_X)` with cohomology sheaves
supported on `Z`, the canonical map `i_* RH_Z(K) ⟶ K` is an isomorphism `i_* RH_Z(K) ≅ K`. -/
@[stacks 0AEF "part (2): the same invertible counit, as the isomorphism i_*RℋZ(K) ≅ K"]
def derivedPushforwardSupportedSectionsIso (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (hK : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X) Z K) :
    letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.obj
        ((derivedSupportedSectionsOnClosed X Z hZ).obj K) ≅ K :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  letI := isIso_derivedPushforwardAdjunction_counit_app_of_supported X Z hZ K hK
  asIso ((derivedPushforwardAdjunction X Z hZ).counit.app K)

/-- **Stacks 0AEF, part (2).** Derived pushforward along the inclusion of a closed subset `Z`
is an equivalence of `D(𝒪_X|_Z)` with the full subcategory `D_Z(𝒪_X)` of `D(𝒪_X)` of complexes
whose cohomology sheaves are supported on `Z`. -/
@[stacks 0AEF "part (2): i_* : D(𝒪_X|_Z) ⥤ D_Z(𝒪_X) is an equivalence"]
def closedSubsetDerivedPushforwardEquivalence (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) :
    DerivedCategory (_root_.SheafOfModules.{u}
        (structureSheafRing (closedSubsetRingedSpace X Z))) ≌
      SupportedDerivedCategory X Z :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  letI := isIso_unit_derivedPushforwardAdjunction X Z hZ
  equivalenceOfCounitIso (derivedPushforwardAdjunction X Z hZ)
    (supportedDerivedProperty X Z) (pushforward_supported X Z hZ)
    (isIso_derivedPushforwardAdjunction_counit_app_of_supported X Z hZ)

/-- **Stacks 0AEF, part (2).** The equivalence onto the supported complexes is induced by
`i_*`: composed with the inclusion of `D_Z(𝒪_X)` into `D(𝒪_X)` it is `i_*^D`. -/
@[stacks 0AEF "part (2): the functor of the equivalence is i_*"]
def closedSubsetDerivedPushforwardEquivalence_functor (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    (letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (closedSubsetDerivedPushforwardEquivalence X Z hZ).functor ⋙
        (supportedDerivedProperty X Z).ι ≅
      (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory) :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  ObjectProperty.liftCompιIso _ _ _

/-- **Stacks 0AEF, part (2).** The quasi-inverse of the equivalence is the derived functor
`RH_Z` of sections supported on `Z`, restricted to `D_Z(𝒪_X)`.

This is the `RH_Z` half of the source's `i^{-1}|_{D_Z(𝒪_X)} = RH_Z|_{D_Z(𝒪_X)}`; the `i^{-1}`
half is `closedSubsetDerivedPushforwardEquivalence_inverse_iso_derivedModulePullback` in
`ClosedSubsetDerivedPullback.lean`. -/
@[stacks 0AEF "part (2): the quasi-inverse is RℋZ restricted to D_Z"]
def closedSubsetDerivedPushforwardEquivalence_inverse (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    (closedSubsetDerivedPushforwardEquivalence X Z hZ).inverse ≅
      (supportedDerivedProperty X Z).ι ⋙ derivedSupportedSectionsOnClosed X Z hZ :=
  Iso.refl _

/-! ### Part (3): `i_* ∘ RH_Z` is right adjoint to the inclusion -/

/-- **Stacks 0AEF, part (3).** The functor `D(𝒪_X) ⥤ D_Z(𝒪_X)` given by `K ↦ i_* RH_Z(K)` —
`RH_Z` followed by derived pushforward, which lands in `D_Z(𝒪_X)` by part (1) — is right adjoint
to the inclusion `D_Z(𝒪_X) ⥤ D(𝒪_X)`.

This is the formal consequence of part (2) and Stacks 0A3B (1) that [Stacks, Tag 0AEF] says it
is: by part (2) the inclusion is the quasi-inverse of `i_*^D : D(𝒪_X|_Z) ≌ D_Z(𝒪_X)` followed by
`i_*^D`, so composing that equivalence with the adjunction `i_*^D ⊣ RH_Z` of Stacks 0A3B (1)
exhibits the inclusion as a left adjoint; see `iotaAdjunctionOfCounitIso`. -/
@[stacks 0AEF "part (3)"]
def derivedPushforwardSupportedSections_isRightAdjoint (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    (supportedDerivedProperty X Z).ι ⊣
      derivedSupportedSectionsOnClosed X Z hZ ⋙ derivedPushforwardToSupported X Z hZ :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  letI := isIso_unit_derivedPushforwardAdjunction X Z hZ
  iotaAdjunctionOfCounitIso (derivedPushforwardAdjunction X Z hZ)
    (supportedDerivedProperty X Z) (pushforward_supported X Z hZ)
    (isIso_derivedPushforwardAdjunction_counit_app_of_supported X Z hZ)

/-- **Stacks 0AEF, part (3).** The right adjoint of the inclusion really is `K ↦ i_* RH_Z(K)`:
composed with the inclusion of `D_Z(𝒪_X)` into `D(𝒪_X)` it is `RH_Z` followed by `i_*^D`.

The identification is definitional, by `CategoryTheory.ObjectProperty.liftCompιIso`. -/
def derivedPushforwardSupportedSections_comp_ι (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) :
    (letI := pushforward_preservesFiniteLimits X Z
    letI := pushforward_preservesFiniteColimits X Z hZ
    (derivedSupportedSectionsOnClosed X Z hZ ⋙ derivedPushforwardToSupported X Z hZ) ⋙
        (supportedDerivedProperty X Z).ι ≅
      derivedSupportedSectionsOnClosed X Z hZ ⋙
        (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory) :=
  Iso.refl _

end Stacks.Cohomology.SupportedComplexes

end
