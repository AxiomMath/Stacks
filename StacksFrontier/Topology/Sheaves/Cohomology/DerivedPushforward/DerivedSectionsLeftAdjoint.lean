module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LeftAdjointOfDerivedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointSectionsMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.SectionsOnASubsingletonSpace
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
import StacksCore.Tactic.StacksAttribute

/-!
# A left adjoint of derived global sections, on an arbitrary ringed space

Let `(S, 𝒪_S)` be a ringed space and `A = Γ(S, 𝒪_S)`.  This file constructs a left adjoint of

`RΓ(S, -) : D(𝒪_S) ⥤ D(A)`,

namely the derived pullback along the structure morphism `π : S ⟶ ({*}, A)` to the one-point
ringed space of [Stacks, Tag 01BH], read on `D(A)` through the identification of modules on the
point with `A`-modules.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.baseRestrict` — restriction of scalars along
  `π^♯` on the whole space, an equivalence `Mod(A) ≌ Mod(Γ({*}, 𝒪))`.
* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.derivedSectionsAdjunction` — **the adjunction**
  `L ⊣ RΓ(S, -)`, where `L` is the left adjoint
  `Stacks.Cohomology.DerivedSectionsLeftAdjoint.derivedBaseExtension`, namely `Lπ^*` read on
  `D(A)`.

## Main results

* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.baseRestrictIso` — derived sections over
  `π⁻¹ ⊤ = ⊤` with scalars restricted along `π^♯` are derived global sections with scalars
  restricted along `π^♯`: `RΓ(π⁻¹⊤, -) ≅ RΓ(S, -) ∘ Mod(π^♯)`.  Restriction of scalars is exact,
  so composing `RΓ(S, -)` with it is again a right derived functor of the composite, and the
  canonical comparison of the two is invertible.
* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.isIso_derivedSectionsAdjunction_unit` — the unit
  of `L ⊣ RΓ(S, -)` is invertible as soon as `Lπ^*` is fully faithful: the two other factors of
  `L` are equivalences.
* `Stacks.Cohomology.DerivedSectionsLeftAdjoint.isIso_derivedSectionsAdjunction_counit_app_iff` —
  and then the counit is invertible at `U` exactly when `U` lies in the essential image of `L`.

## Implementation notes

*Why the point intervenes.*  `RΓ(S, -)` takes values in complexes of `A`-modules, while the
derived adjunction `Lf^* ⊣ Rf_*` of [Stacks, Tag 079W] is available only for a morphism of ringed
*spaces*.  The one-point ringed space `({*}, A)` is the ringed space whose modules are
`A`-modules — `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointSectionsEquivalence` — and
`Stacks.AssociatedSheaf.toCoefficientPoint` is the morphism `π : S ⟶ ({*}, A)` that the identity
`A ⟶ Γ(S, 𝒪_S)` induces; the point and that morphism are `basePoint` and `toBasePoint`.  So
`Lπ^*` is a left adjoint of `Rπ_*`, and `Rπ_*` followed by sections on the point is `RΓ(S, -)`:
that is the Leray isomorphism of [Stacks, Tag 0D5W] at `V = ⊤`,
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso`, together with
`baseRestrictIso` to pass from the scalars `Γ({*}, 𝒪)` of the point to `A` itself.

*Three adjunctions are composed.*  The three are the one-point identification on derived
categories (`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointDerivedAdjunction`), the derived
adjunction of Tag 079W for `π`, and the equivalence `Mod(A) ≌ Mod(Γ({*}, 𝒪))` of restriction of
scalars along the ring isomorphism `π^♯`.

*The scalars of the point.*  `Γ({*}, 𝒪_{({*},A)})` is isomorphic to `A` but not equal to it: the
structure sheaf of the point is a skyscraper, and its sections on the whole space are `A` only
through `Stacks.AssociatedSheaf.coefficientRingEquiv`.  `pointStructureMap_eq` identifies `π^♯`
on the whole space with the inverse of that isomorphism, which is what makes `baseRestrict` an
equivalence.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedSectionsOnAPoint
open Stacks.Cohomology.GlobalKunneth

universe u

namespace Stacks.Cohomology.DerivedSectionsLeftAdjoint

attribute [local instance] HasDerivedCategory.standard

variable (S : RingedSpace.{u, u})

/-! ### Restriction of scalars along `π^♯` -/

/-- **Restriction of scalars along `π^♯` on the whole space**, a functor
`Mod(A) ⥤ Mod(Γ({*}, 𝒪))`. -/
abbrev baseRestrict :
    ModuleCat.{u} (baseRing S) ⥤ ModuleCat.{u} (baseRing (basePoint S)) :=
  ModuleCat.restrictScalars ((structureSheafHom (toBasePoint S)).hom.app (op ⊤)).hom

/-- `baseRestrict` is additive. -/
instance baseRestrict_additive : (baseRestrict S).Additive where map_add := rfl

/-- `baseRestrict` preserves finite limits. -/
instance baseRestrict_preservesFiniteLimits : PreservesFiniteLimits (baseRestrict S) :=
  Stacks.Cohomology.SubsingletonSections.preservesFiniteLimits_restrictScalars _

/-- `baseRestrict` preserves finite colimits. -/
instance baseRestrict_preservesFiniteColimits : PreservesFiniteColimits (baseRestrict S) :=
  Stacks.Cohomology.SubsingletonSections.preservesFiniteColimits_restrictScalars _

/-- Derived sections over `π⁻¹ ⊤` are global sections with scalars restricted along `π^♯`: the
two functors are the same, `π⁻¹ ⊤` being `⊤`. -/
def preimageSectionsBaseIso :
    sectionsOverOpen S ⊤ ⋙ baseRestrict S ≅ preimageSections (toBasePoint S) ⊤ :=
  Iso.refl _

/-- **`π^♯` on the whole space is the inverse of the identification of `A` with the sections of
the point's structure sheaf.**  The scalar map of Tag 01BH, construction (3), factors as that
identification followed by `π^♯`, and here it is the identity. -/
theorem pointStructureMap_eq :
    ((structureSheafHom (toBasePoint S)).hom.app (op ⊤)).hom =
      (coefficientRingEquiv (R := baseRing S)).symm.toRingHom := by
  refine RingHom.ext fun x => ?_
  have hx := DFunLike.congr_fun (globalSectionsMap_app_top_factors S (RingHom.id (baseRing S)))
    ((coefficientRingEquiv (R := baseRing S)).symm x)
  rw [globalSectionsMap_app_top_apply] at hx
  have hx2 : ((structureSheafHom (toBasePoint S)).hom.app (op ⊤)).hom
      ((coefficientRingEquiv (R := baseRing S))
        ((coefficientRingEquiv (R := baseRing S)).symm x)) =
      (coefficientRingEquiv (R := baseRing S)).symm x := hx.symm
  rw [RingEquiv.apply_symm_apply] at hx2
  exact hx2

/-- `baseRestrict` is restriction of scalars along a ring isomorphism. -/
theorem baseRestrict_eq :
    baseRestrict S =
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (coefficientRingEquiv (R := baseRing S)).symm).functor := by
  rw [baseRestrict, pointStructureMap_eq]
  rfl

/-- **Restriction of scalars along `π^♯` is an equivalence** `Mod(A) ≌ Mod(Γ({*}, 𝒪))`. -/
instance baseRestrict_isEquivalence : (baseRestrict S).IsEquivalence := by
  rw [baseRestrict_eq]
  infer_instance

/-! ### Derived sections over the inverse image of the point -/

/-- Sections over `⊤` followed by `baseRestrict` is additive. -/
instance sectionsComp_additive : (sectionsOverOpen S ⊤ ⋙ baseRestrict S).Additive where
  map_add := rfl

/-- Sections over `π⁻¹ ⊤` are additive. -/
instance preimageSectionsTop_additive : (preimageSections (toBasePoint S) ⊤).Additive where
  map_add := rfl

/-- On the homotopy category, sections over `π⁻¹ ⊤` followed by the localization are sections
over `⊤` followed by the localization and restriction of scalars along `π^♯`. -/
def baseRestrictUnitIso :
    homotopyPreimageSections (toBasePoint S) ⊤ ≅
      homotopySectionsOverOpen S ⊤ ⋙ (baseRestrict S).mapDerivedCategory := by
  letI : Preadditive (ModuleCat.{u} (baseRing (basePoint S))) := inferInstance
  letI : (baseRestrict S).Additive := baseRestrict_additive S
  letI : (sectionsOverOpen S ⊤).Additive := sectionsOverOpen_additive S ⊤
  letI : (preimageSections (toBasePoint S) ⊤).Additive := preimageSectionsTop_additive S
  exact Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (F := sectionsOverOpen S ⊤) (G := baseRestrict S)
        (H := preimageSections (toBasePoint S) ⊤) (preimageSectionsBaseIso S)
        (ComplexShape.up ℤ)).symm DerivedCategory.Qh ≪≫
    Functor.associator ((sectionsOverOpen S ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
      ((baseRestrict S).mapHomotopyCategory (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft ((sectionsOverOpen S ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
      (baseRestrict S).mapDerivedCategoryFactorsh.symm ≪≫
    (Functor.associator ((sectionsOverOpen S ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh (baseRestrict S).mapDerivedCategory).symm

/-- The comparison from termwise sections over `π⁻¹ ⊤` to derived global sections with scalars
restricted along `π^♯`. -/
def baseRestrictUnit :
    homotopyPreimageSections (toBasePoint S) ⊤ ⟶
      DerivedCategory.Qh ⋙ baseSections S ⋙ (baseRestrict S).mapDerivedCategory :=
  (baseRestrictUnitIso S).hom ≫
    Functor.whiskerRight (derivedSectionsOverOpenUnit S ⊤)
      (baseRestrict S).mapDerivedCategory ≫
    (Functor.associator DerivedCategory.Qh (baseSections S)
      (baseRestrict S).mapDerivedCategory).hom

/-- **Derived global sections with scalars restricted along `π^♯` are derived sections over
`π⁻¹ ⊤`.**  Restriction of scalars is exact, so `RΓ(S, -)` followed by it is again a right
derived functor of sections over `π⁻¹ ⊤ = ⊤` with restricted scalars: the comparison
`baseRestrictUnit` is invertible at a K-injective complex, where the unit of `RΓ(S, -)` is. -/
theorem isRightDerivedFunctor_baseRestrict :
    (baseSections S ⋙ (baseRestrict S).mapDerivedCategory).IsRightDerivedFunctor
      (baseRestrictUnit S)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S))
        (ComplexShape.up ℤ)) := by
  refine isRightDerivedFunctor_of_isIso_app_isKInjective.{u, u + 1, u + 1, u + 1, u + 1, u + 1}
    _ (exists_quasiIso_isKInjective S) DerivedCategory.Qh _ _ fun I hI => ?_
  have := hI
  have h : IsIso ((derivedSectionsOverOpenUnit S ⊤).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S))
        (ComplexShape.up ℤ)).obj I)) :=
    Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective
      (sectionsOverOpen S ⊤) I
  rw [baseRestrictUnit]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app]
  infer_instance

/-- The canonical comparison `RΓ(π⁻¹⊤, -) ⟶ RΓ(S, -) ∘ Mod(π^♯)`. -/
def baseRestrictComparison :
    derivedPreimageSections (toBasePoint S) ⊤ ⟶
      baseSections S ⋙ (baseRestrict S).mapDerivedCategory :=
  (derivedPreimageSections (toBasePoint S) ⊤).rightDerivedDesc
    (derivedPreimageSectionsUnit (toBasePoint S) ⊤)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S))
      (ComplexShape.up ℤ)) _
    (baseRestrictUnit S)

/-- The comparison `RΓ(π⁻¹⊤, -) ⟶ RΓ(S, -) ∘ Mod(π^♯)` is an isomorphism. -/
instance isIso_baseRestrictComparison : IsIso (baseRestrictComparison S) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _
      (derivedPreimageSectionsUnit (toBasePoint S) ⊤) _ _ (baseRestrictUnit S)).1
    (isRightDerivedFunctor_baseRestrict S)

/-- **`RΓ(π⁻¹⊤, -) ≅ RΓ(S, -) ∘ Mod(π^♯)`.** -/
def baseRestrictIso :
    derivedPreimageSections (toBasePoint S) ⊤ ≅
      baseSections S ⋙ (baseRestrict S).mapDerivedCategory :=
  asIso (baseRestrictComparison S)

/-! ### The left adjoint -/

/-- The functor of the equivalence `baseRestrict` is additive. -/
instance baseRestrict_asEquivalence_functor_additive :
    (baseRestrict S).asEquivalence.functor.Additive :=
  baseRestrict_additive S

/-- `Mod(A) ≌ Mod(Γ({*}, 𝒪))` read on derived categories. -/
abbrev baseRestrictDerivedEquivalence :
    DerivedCategory (ModuleCat.{u} (baseRing S)) ≌
      DerivedCategory (ModuleCat.{u} (baseRing (basePoint S))) :=
  Stacks.DerivedQCoh.Equivalence.mapDerivedCategory (baseRestrict S).asEquivalence

/-- The equivalence `Mod(A) ≌ Mod(Γ({*}, 𝒪))` cancels against its inverse. -/
def cancelBaseRestrictIso :
    (baseSections S ⋙ (baseRestrict S).mapDerivedCategory) ⋙
        (baseRestrictDerivedEquivalence S).inverse ≅ baseSections S :=
  Functor.isoWhiskerLeft (baseSections S)
      (baseRestrictDerivedEquivalence S).unitIso.symm ≪≫
    (baseSections S).rightUnitor

/-- **`RΓ(S, -)` has a left adjoint**, on an arbitrary ringed space: the adjunction
`L ⊣ RΓ(S, -)`.  It is the composite of the one-point identification on derived categories, the
derived adjunction `Lπ^* ⊣ Rπ_*` of [Stacks, Tag 079W], and restriction of scalars along `π^♯`,
read through the Leray isomorphism of [Stacks, Tag 0D5W]. -/
def derivedSectionsAdjunction : derivedBaseExtension S ⊣ baseSections S :=
  Adjunction.ofNatIsoRight
    ((baseRestrictDerivedEquivalence S).toAdjunction.comp
      (Adjunction.ofNatIsoRight
        (Adjunction.ofNatIsoRight
          ((onePointDerivedAdjunction (baseRing S)).comp (derivedAdjunction (toBasePoint S)))
          (derivedSectionsPushforwardIso (toBasePoint S) ⊤))
        (baseRestrictIso S)))
    (cancelBaseRestrictIso S)

/-! ### Full faithfulness of the left adjoint -/

/-- The left adjoint `L` of `RΓ(S, -)` is full when `Lπ^*` is fully faithful. -/
instance derivedSectionsLeftAdjoint_full
    [(derivedPullback (toBasePoint S)).Full] [(derivedPullback (toBasePoint S)).Faithful] :
    (derivedBaseExtension S).Full :=
  have : (onePointSectionsEquivalence (baseRing S)).functor.mapDerivedCategory.IsEquivalence :=
    Stacks.DerivedQCoh.isEquivalence_mapDerivedCategory (onePointSectionsEquivalence (baseRing S))
  inferInstanceAs (((Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (baseRestrict S).asEquivalence).functor ⋙
      (onePointSectionsEquivalence (baseRing S)).functor.mapDerivedCategory ⋙
        derivedPullback (toBasePoint S)).Full)

/-- The left adjoint `L` of `RΓ(S, -)` is faithful when `Lπ^*` is fully faithful. -/
instance derivedSectionsLeftAdjoint_faithful
    [(derivedPullback (toBasePoint S)).Full] [(derivedPullback (toBasePoint S)).Faithful] :
    (derivedBaseExtension S).Faithful :=
  have : (onePointSectionsEquivalence (baseRing S)).functor.mapDerivedCategory.IsEquivalence :=
    Stacks.DerivedQCoh.isEquivalence_mapDerivedCategory (onePointSectionsEquivalence (baseRing S))
  inferInstanceAs (((Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (baseRestrict S).asEquivalence).functor ⋙
      (onePointSectionsEquivalence (baseRing S)).functor.mapDerivedCategory ⋙
        derivedPullback (toBasePoint S)).Faithful)

/-- **The unit of `L ⊣ RΓ(S, -)` is invertible as soon as `Lπ^*` is fully faithful.**  The other
two factors of `L` are equivalences, so full faithfulness of `L` is that of the derived pullback
along the structure morphism to the point, and a left adjoint is fully faithful exactly when the
unit of its adjunction is invertible. -/
theorem isIso_derivedSectionsAdjunction_unit
    [(derivedPullback (toBasePoint S)).Full] [(derivedPullback (toBasePoint S)).Faithful] :
    IsIso (derivedSectionsAdjunction S).unit :=
  Adjunction.unit_isIso_of_L_fully_faithful (derivedSectionsAdjunction S)

/-- **The counit of `L ⊣ RΓ(S, -)` is invertible exactly on the essential image of `L`**, once
`Lπ^*` is fully faithful.  Over an affine base that essential image is the quasi-coherent part
of `D(𝒪_S)`, which is the content of the Spec–Γ equivalence of [Stacks, Tag 06Z0]. -/
theorem isIso_derivedSectionsAdjunction_counit_app_iff
    [(derivedPullback (toBasePoint S)).Full] [(derivedPullback (toBasePoint S)).Faithful]
    (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    IsIso ((derivedSectionsAdjunction S).counit.app U) ↔
      (derivedBaseExtension S).essImage U :=
  Adjunction.isIso_counit_app_iff_mem_essImage (derivedSectionsAdjunction S)

end Stacks.Cohomology.DerivedSectionsLeftAdjoint

end
