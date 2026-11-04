module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FlatPushforwardPreservesKInjectives
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.LocalizationAtPresheafHypercovering
public import StacksFrontier.CategoryTheory.Sites.PresheafOfElements
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDerivedGlobalSectionsUnconditional
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectCohomologyDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationDescentAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SectionsComplex
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationShriekExact
public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquareLocalization

/-!
# Cohomology of a presheaf of sets through a hypercovering of it

Let `C` be a site with equalizers and fibre products, given by a pretopology `J`, and let `G` be
a presheaf of sets on `C`. Stacks 09X6 transfers the results on hypercoverings of Section 85.25
from the final presheaf to `G`, by replacing the site `C` with its localization `C/G` of Stacks
0791, and spells out the instance it has in mind:

* for a hypercovering `K` of `G`, `RΓ(C/G, E) = RΓ((C/K)_total, a⁻¹E)`, where
  `a : Sh((C/K)_total) ⟶ Sh(C/G)` is the canonical augmentation (Stacks 0D8H for the site `C/G`);
* `RΓ(G, E) = RΓ(C/G, j⁻¹E)`, where `RΓ(G, -)` is the derived functor of
  `H⁰(G, -) = H⁰(G^#, -)`, maps out of `G` (Stacks 079X), and `j : C/G ⥤ C` is the localization
  functor (the analogue of Stacks 03F3);
* putting the two together, `RΓ(G, E) = RΓ((C/K)_total, a⁻¹j⁻¹E) = RΓ((C/K)_total, g⁻¹E)`, where
  `g : Sh((C/K)_total) ⟶ Sh(C)` is the composition of `a` and `j`.

This file proves the three statements.

## Main definitions

* `sectionsOverPresheaf`: `H⁰(G, -)` on abelian sheaves, the group `Hom(ℤ_G^#, F)` of maps out of
  the free abelian sheaf on `G`, whose underlying set is the set of maps of presheaves of sets
  `G ⟶ F` (`sectionsOverPresheafEquiv`).
* `derivedSectionsOverPresheaf`: `RΓ(G, -)`, its total right derived functor on the unbounded
  derived category.
* `localizationInverseImage`: `j⁻¹`, restriction of abelian sheaves along `C/G ⥤ C`.
* `compositeInverseImage`: `g⁻¹`, restriction of abelian sheaves along the composite of the
  localization functors `(C/K)_total ⥤ C/G ⥤ C` of `a` and `j`.

## Main results

* `extensionByZeroUnitIso`: extension by zero `j_!` takes the constant sheaf `ℤ` on `C/G` to the
  free abelian sheaf `ℤ_G^#`.
* `sectionsOverPresheafIso`: `H⁰(G, -) ≅ j⁻¹ ⋙ Γ(C/G, -)`.
* `derivedSectionsOverPresheafIso`: **Stacks 09X6**, `RΓ(G, E) = RΓ(C/G, j⁻¹E)`.
* `derivedGlobalSectionsLocalizationIso`: **Stacks 09X6**,
  `RΓ(C/G, E) = RΓ((C/K)_total, a⁻¹E)` for a hypercovering `K` of `G`.
* `derivedSectionsOverPresheafInverseImageIso`: **Stacks 09X6**,
  `RΓ(G, E) = RΓ((C/K)_total, a⁻¹j⁻¹E)`.
* `derivedSectionsOverPresheafCompositeIso`: **Stacks 09X6**,
  `RΓ(G, E) = RΓ((C/K)_total, g⁻¹E)`.

## Implementation notes

The site is small, as for Stacks 0D8H, which is what makes derived functors of abelian sheaves
available. The statements are isomorphisms of functors on the *unbounded* derived categories, so
they hold at every `E`, in particular on `D⁺`, the generality in which the source states them.

The comparison `RΓ(G, -) ≅ j⁻¹ ⋙ RΓ(C/G, -)` is stated over arbitrary models of the derived
categories (`HasDerivedCategory`), and for any topology on `C/G` equal to the one of Stacks 0791;
the statements involving the total site are seated at the standard model, because that is the
model of Stacks 0D8H (`derivedGlobalSectionsInverseImageIsoOfHypercovering'`), which they apply.

The underived comparison follows the proof of Stacks 03F3 and 07A0: `j⁻¹` has the exact left
adjoint `j_!` (Stacks 03DJ for a presheaf of sets,
`Stacks.Sites.LocalizationShriek.preservesFiniteLimits_sheafPullback`), so it carries K-injective
complexes to K-injective complexes, and `H⁰(G, -) = Hom(j_!ℤ, -) = Hom(ℤ, j⁻¹ -) = Γ(C/G, j⁻¹ -)`.
The identification `j_!ℤ ≅ ℤ_G^#` is the corepresentability argument of
`Stacks.Cohomology.SheafOfSets.extensionByZeroUnitIso`, which is stated for a *sheaf* of sets; it
uses nothing about `K` beyond its underlying presheaf and is redone here for a presheaf.

## References

* [Stacks Project, Tag 09X6](https://stacks.math.columbia.edu/tag/09X6)
* [Stacks Project, Tag 0D8H](https://stacks.math.columbia.edu/tag/0D8H)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 079X](https://stacks.math.columbia.edu/tag/079X)
* [Stacks Project, Tag 07A0](https://stacks.math.columbia.edu/tag/07A0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.CategoryTheory.Hypercovering.LocalizationAtPresheaf

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ Type u)

/-! ### `H⁰(G, -)` and `RΓ(G, -)` -/

section Sections

/-- **`H⁰(G, -)` of Stacks 079X on abelian sheaves:** `F ↦ Hom(ℤ_G^#, F)`, the group of maps out
of the free abelian sheaf on `G`. Its elements are the maps of presheaves of sets `G ⟶ F`
(`sectionsOverPresheafEquiv`), with the group structure of `F`. -/
abbrev sectionsOverPresheaf : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  preadditiveCoyoneda.obj (op ((Presheaf.freeAbelianSheaf J).obj G))

/-- The elements of `H⁰(G, F)` are the maps of presheaves of sets from `G` to `F`. -/
def sectionsOverPresheafEquiv (F : Sheaf J AddCommGrpCat.{u}) :
    ((sectionsOverPresheaf J G).obj F) ≃
      (G ⟶ (sheafToPresheaf J AddCommGrpCat.{u} ⋙ Presheaf.forgetAbelian).obj F) :=
  (Presheaf.freeAbelianSheafAdj J).homEquiv G F

/-- **`H⁰(G, -) = H⁰(G^#, -)`** (Stacks 079X, observation (1), quoted in Stacks 09X6): the free
abelian sheaf functor inverts the sheafification map `G ⟶ G^#`. -/
@[stacks 09X6 "`H⁰(G, -) = H⁰(G^#, -)`, the functor whose derived functor is `RΓ(G, -)`"]
def sectionsOverPresheafSheafifyIso :
    sectionsOverPresheaf J G ≅
      sectionsOverPresheaf J (sheafify J G) :=
  haveI := Presheaf.isIso_freeAbelianSheaf_map_of_W J (toSheafify J G) (J.W_toSheafify G)
  preadditiveCoyoneda.mapIso (asIso ((Presheaf.freeAbelianSheaf J).map (toSheafify J G))).op.symm

/-- **`RΓ(G, -)`:** the total right derived functor of `H⁰(G, -)` on the unbounded derived
category of abelian sheaves. -/
abbrev derivedSectionsOverPresheaf [HasDerivedCategory (Sheaf J AddCommGrpCat.{u})]
    [HasDerivedCategory AddCommGrpCat.{u}] :
    DerivedCategory (Sheaf J AddCommGrpCat.{u}) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  Stacks.DerivedFunctor.totalRightDerived (sectionsOverPresheaf J G)

end Sections

/-! ### The localization morphism `j` on abelian sheaves -/

section Localization

/-- The topology of Stacks 0791 on the localization `C/G`. -/
abbrev localizationTopology : GrothendieckTopology (CostructuredArrow (yoneda (C := C)) G) :=
  (CostructuredArrow.proj yoneda G).restrictedTopology J

open Stacks.Topos.Localized in
/-- Extension by zero `j_!` on abelian sheaves. -/
abbrev extensionByZero : Sheaf (localizationTopology J G) AddCommGrpCat.{u} ⥤
    Sheaf J AddCommGrpCat.{u} :=
  Functor.sheafPullbackConstruction.sheafPullback (CostructuredArrow.proj yoneda G)
    AddCommGrpCat.{u} (localizationTopology J G) J

open Stacks.Topos.Localized in
/-- `j_! ⊣ j⁻¹` on abelian sheaves. -/
abbrev extensionByZeroAdjunction : extensionByZero J G ⊣
    (CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u}
      (localizationTopology J G) J :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (CostructuredArrow.proj yoneda G)
    AddCommGrpCat.{u} (localizationTopology J G) J

/-- The free abelian presheaf on the final presheaf of sets of a category is the constant
presheaf `ℤ`. -/
def freeAbelianConstPUnitIso (D : Type u) [SmallCategory D] :
    (Presheaf.freeAbelian (C := D)).obj ((Functor.const _).obj PUnit.{u + 1}) ≅
      (Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  NatIso.ofComponents (fun _ ↦ Stacks.Sites.Elements.freeObjPUnitIso) (by
    intro X Y f
    have h : (Presheaf.freeAbelian.obj
        ((Functor.const Dᵒᵖ).obj PUnit.{u + 1})).map f = 𝟙 _ := AddCommGrpCat.free.map_id _
    rw [h, Category.id_comp]
    simp)

/-- The functor on abelian sheaves on `C` corepresented both by `j_!ℤ` and by `ℤ_G^#`: maps of
presheaves of sets out of `G`. -/
abbrev corepFunctor : Sheaf J AddCommGrpCat.{u} ⥤ Type u :=
  (sheafToPresheaf J AddCommGrpCat.{u} ⋙ Presheaf.forgetAbelian) ⋙ coyoneda.obj (op G)

/-- `ℤ_G^#` corepresents maps out of `G`: the free-abelian-sheaf adjunction. -/
def corepByFreeAbelianSheaf :
    (corepFunctor J G).CorepresentableBy ((Presheaf.freeAbelianSheaf J).obj G) :=
  (Presheaf.freeAbelianSheafAdj J).corepresentableBy G

open Stacks.Sites.Elements in
/-- `j_!ℤ` corepresents maps out of `G`: the composite of the free-abelian, sheafification and
`j_! ⊣ j⁻¹` adjunctions, followed by `elementsHomEquiv`. -/
def corepByExtensionByZeroUnit :
    (corepFunctor J G).CorepresentableBy
      ((extensionByZero J G).obj (integerSheaf (localizationTopology J G))) :=
  (((Presheaf.freeAbelianAdj.comp
      ((sheafificationAdjunction (localizationTopology J G) AddCommGrpCat.{u}).comp
        (extensionByZeroAdjunction J G))).corepresentableBy
      ((Functor.const _).obj PUnit.{u + 1})).ofIsoObj
    ((extensionByZero J G).mapIso ((presheafToSheaf (localizationTopology J G)
      AddCommGrpCat.{u}).mapIso (freeAbelianConstPUnitIso _))).symm).ofIso
    (NatIso.ofComponents
      (fun F ↦ (elementsHomEquiv G (Presheaf.forgetAbelian.obj F.obj)).toIso)
      (fun _ ↦ by ext θ; rfl))

/-- **Extension by zero of the constant sheaf `ℤ` on `C/G` is the free abelian sheaf `ℤ_G^#`.** -/
def extensionByZeroUnitIso :
    (extensionByZero J G).obj (integerSheaf (localizationTopology J G)) ≅
      (Presheaf.freeAbelianSheaf J).obj G :=
  (corepByExtensionByZeroUnit J G).uniqueUpToIso (corepByFreeAbelianSheaf J G)

/-- `j⁻¹` on abelian sheaves is additive. -/
instance additive_localizationInverseImage :
    ((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u}
      (localizationTopology J G) J).Additive :=
  have : PreservesLimitsOfSize.{0, 0} ((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous
      AddCommGrpCat.{u} (localizationTopology J G) J) :=
    (extensionByZeroAdjunction J G).rightAdjoint_preservesLimits
  Functor.additive_of_preserves_binary_products _

/-- Extension by zero `j_!` on abelian sheaves is additive. -/
instance additive_extensionByZero : (extensionByZero J G).Additive :=
  (extensionByZeroAdjunction J G).left_adjoint_additive

/-- Extension by zero `j_!` on abelian sheaves preserves finite limits. -/
instance preservesFiniteLimits_extensionByZero : PreservesFiniteLimits (extensionByZero J G) :=
  Stacks.Sites.LocalizationShriek.preservesFiniteLimits_sheafPullback G J

/-- Extension by zero `j_!` on abelian sheaves preserves finite colimits. -/
instance preservesFiniteColimits_extensionByZero :
    PreservesFiniteColimits (extensionByZero J G) :=
  have : PreservesColimitsOfSize.{0, 0} (extensionByZero J G) :=
    (extensionByZeroAdjunction J G).leftAdjoint_preservesColimits
  inferInstance

/-- `j⁻¹` on abelian sheaves preserves finite limits. -/
instance preservesFiniteLimits_localizationInverseImage :
    PreservesFiniteLimits ((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous
      AddCommGrpCat.{u} (localizationTopology J G) J) :=
  have : PreservesLimitsOfSize.{0, 0} ((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous
      AddCommGrpCat.{u} (localizationTopology J G) J) :=
    (extensionByZeroAdjunction J G).rightAdjoint_preservesLimits
  inferInstance

/-- `j⁻¹` on abelian sheaves preserves finite colimits. -/
instance preservesFiniteColimits_localizationInverseImage :
    PreservesFiniteColimits ((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous
      AddCommGrpCat.{u} (localizationTopology J G) J) :=
  have : ((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u}
      (localizationTopology J G) J).IsLeftAdjoint :=
    ((CostructuredArrow.proj yoneda G).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (localizationTopology J G) J).isLeftAdjoint
  inferInstance

/-- **`H⁰(G, -) = Γ(C/G, j⁻¹ -)`**, naturally in the abelian sheaf:
`Hom(ℤ_G^#, F) = Hom(j_!ℤ, F) = Hom(ℤ, j⁻¹F) = Γ(C/G, j⁻¹F)`. -/
def sectionsOverPresheafIso :
    sectionsOverPresheaf J G ≅
      (CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u}
          (localizationTopology J G) J ⋙
        Sheaf.Γ (localizationTopology J G) AddCommGrpCat.{u} :=
  preadditiveCoyoneda.mapIso (extensionByZeroUnitIso J G).op ≪≫
    (extensionByZeroAdjunction J G).preadditiveCoyonedaObjIso
      (integerSheaf (localizationTopology J G)) ≪≫
    Functor.isoWhiskerLeft _ (integerHomIsoGlobalSections (localizationTopology J G))

/-- `j⁻¹` carries K-injective complexes of abelian sheaves to K-injective complexes: it is the
right adjoint of the exact functor `j_!`. This is Stacks 03F3 (1) in its derived form, for the
localization at a presheaf of sets. -/
theorem isKInjective_localizationInverseImage
    (I : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      ((((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u}
        (localizationTopology J G) J).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  (Stacks.Cohomology.isKInjectiveHomotopyCategory_iff_isKInjective _).mp
    (_root_.rightAdjoint_preserves_isKInjective _ _ (extensionByZeroAdjunction J G) I
      ((Stacks.Cohomology.isKInjectiveHomotopyCategory_iff_isKInjective I).mpr hI))

end Localization


/-! ### `RΓ(G, E) = RΓ(C/G, j⁻¹E)` -/

section Derived

/-- Restriction of abelian sheaves along `C/G ⥤ C` is additive for any topology on `C/G` equal to
the one of Stacks 0791. -/
theorem additive_sheafPushforwardContinuous_of_eq
    (K : GrothendieckTopology (CostructuredArrow (yoneda (C := C)) G))
    (hK : K = localizationTopology J G) [(CostructuredArrow.proj yoneda G).IsContinuous K J] :
    ((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u} K
      J).Additive := by
  subst hK
  infer_instance

/-- Restriction of abelian sheaves along `C/G ⥤ C` preserves finite limits for any topology on
`C/G` equal to the one of Stacks 0791. -/
theorem preservesFiniteLimits_sheafPushforwardContinuous_of_eq
    (K : GrothendieckTopology (CostructuredArrow (yoneda (C := C)) G))
    (hK : K = localizationTopology J G) [(CostructuredArrow.proj yoneda G).IsContinuous K J] :
    PreservesFiniteLimits
      ((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u} K J) := by
  subst hK
  infer_instance

/-- Restriction of abelian sheaves along `C/G ⥤ C` preserves finite colimits for any topology on
`C/G` equal to the one of Stacks 0791. -/
theorem preservesFiniteColimits_sheafPushforwardContinuous_of_eq
    (K : GrothendieckTopology (CostructuredArrow (yoneda (C := C)) G))
    (hK : K = localizationTopology J G) [(CostructuredArrow.proj yoneda G).IsContinuous K J] :
    PreservesFiniteColimits
      ((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u} K J) := by
  subst hK
  infer_instance

/-- The global sections functor on abelian sheaves is additive. -/
instance additive_sheafΓ {D : Type u} [SmallCategory D] (K : GrothendieckTopology D) :
    (Sheaf.Γ K AddCommGrpCat.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

variable (K : GrothendieckTopology (CostructuredArrow (yoneda (C := C)) G))
  [(CostructuredArrow.proj yoneda G).IsContinuous K J]
  [((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u} K J).Additive]
  [PreservesFiniteLimits
    ((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u} K J)]
  [PreservesFiniteColimits
    ((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u} K J)]
  [HasDerivedCategory (Sheaf J AddCommGrpCat.{u})] [HasDerivedCategory (Sheaf K AddCommGrpCat.{u})]
  [HasDerivedCategory AddCommGrpCat.{u}]

/-- `RΓ(G, E) = RΓ(C/G, j⁻¹E)`, for any topology on `C/G` equal to the one of Stacks 0791. -/
def derivedSectionsOverPresheafIsoOfEq (hK : K = localizationTopology J G) :
    derivedSectionsOverPresheaf J G ≅
      ((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u} K
          J).mapDerivedCategory ⋙
        Stacks.DerivedFunctor.totalRightDerived (Sheaf.Γ K AddCommGrpCat.{u}) := by
  subst hK
  exact (Functor.isoWhiskerRight (Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
      ((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u}
        (localizationTopology J G) J)) _ ≪≫
    Stacks.Cohomology.LerayUnbounded.derivedCompIso _ _ _ (sectionsOverPresheafIso J G).symm
      (isKInjective_localizationInverseImage J G)).symm

end Derived

/-- **Stacks 09X6, `RΓ(G, E) = RΓ(C/G, j⁻¹E)`.** Let `C` be a site and `G` a presheaf of sets on
`C`, let `RΓ(G, -)` be the derived functor of `H⁰(G, -) = H⁰(G^#, -)`, maps out of `G` (Stacks
079X), and let `j : C/G ⥤ C` be the localization functor of Stacks 0791. Then

`RΓ(G, E) = RΓ(C/G, j⁻¹E)`

naturally in `E` in the unbounded derived category of abelian sheaves on `C`: the analogue of
Stacks 03F3 for the localization at `G`. -/
@[stacks 09X6 "`RΓ(G, E) = RΓ(C/G, j⁻¹E)` for the localization functor `j : C/G → C`, the analogue
  of Tag 03F3; an isomorphism of functors on the unbounded derived category"]
def derivedSectionsOverPresheafIso [HasDerivedCategory (Sheaf J AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf (localizationTopology J G) AddCommGrpCat.{u})]
    [HasDerivedCategory AddCommGrpCat.{u}] :
    derivedSectionsOverPresheaf J G ≅
      ((CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u}
          (localizationTopology J G) J).mapDerivedCategory ⋙
        Stacks.DerivedFunctor.totalRightDerived
          (Sheaf.Γ (localizationTopology J G) AddCommGrpCat.{u}) :=
  derivedSectionsOverPresheafIsoOfEq J G (localizationTopology J G) rfl


/-! ### Hypercoverings of `G` -/

section Hypercovering

open CategoryTheory.SimplicialSiteSituation CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard

variable [HasEqualizers C] [HasPullbacks C] (P : Pretopology C) (H : HypercoveringOf.{u, u} P G)

/-- The localization functor `C/G ⥤ C` is continuous for the localized pretopology on `C/G`. -/
instance isContinuous_proj_localizationPretopology :
    (CostructuredArrow.proj yoneda G).IsContinuous (localizationPretopology G P).toGrothendieck
      P.toGrothendieck := by
  rw [localizationPretopology_toGrothendieck]
  infer_instance

/-- The localization functor `C/G ⥤ C` is cocontinuous for the localized pretopology on `C/G`. -/
instance isCocontinuous_proj_localizationPretopology :
    (CostructuredArrow.proj yoneda G).IsCocontinuous (localizationPretopology G P).toGrothendieck
      P.toGrothendieck := by
  rw [localizationPretopology_toGrothendieck]
  infer_instance

/-- `j⁻¹ : Ab(C) ⥤ Ab(C/G)`, restriction of abelian sheaves along the localization functor. -/
abbrev localizationInverseImage :
    Sheaf P.toGrothendieck AddCommGrpCat.{u} ⥤
      Sheaf (localizationPretopology G P).toGrothendieck AddCommGrpCat.{u} :=
  (CostructuredArrow.proj yoneda G).sheafPushforwardContinuous AddCommGrpCat.{u}
    (localizationPretopology G P).toGrothendieck P.toGrothendieck

/-- `j⁻¹ : Ab(C) ⥤ Ab(C/G)` is additive. -/
instance additive_localizationInverseImage' : (localizationInverseImage G P).Additive :=
  additive_sheafPushforwardContinuous_of_eq P.toGrothendieck G _
    (localizationPretopology_toGrothendieck G P)

/-- `j⁻¹ : Ab(C) ⥤ Ab(C/G)` preserves finite limits. -/
instance preservesFiniteLimits_localizationInverseImage' :
    PreservesFiniteLimits (localizationInverseImage G P) :=
  preservesFiniteLimits_sheafPushforwardContinuous_of_eq P.toGrothendieck G _
    (localizationPretopology_toGrothendieck G P)

/-- `j⁻¹ : Ab(C) ⥤ Ab(C/G)` preserves finite colimits. -/
instance preservesFiniteColimits_localizationInverseImage' :
    PreservesFiniteColimits (localizationInverseImage G P) :=
  preservesFiniteColimits_sheafPushforwardContinuous_of_eq P.toGrothendieck G _
    (localizationPretopology_toGrothendieck G P)

/-- The hypercovering of the site `C/G` attached to the hypercovering `H` of `G` (Stacks 09X6). -/
abbrev localizedHypercovering : HypercoveringOfTerminal.{u, u} (localizationPretopology G P) :=
  hypercoveringOfEquivLocalization G P H

/-- **Stacks 09X6, `RΓ(C/G, E) = RΓ((C/K)_total, a⁻¹E)`.** For a hypercovering `K` of a presheaf
of sets `G` on a site `C` with equalizers and fibre products, regarded as a hypercovering of the
site `C/G`, and the canonical augmentation `a : Sh((C/K)_total) ⟶ Sh(C/G)`, derived global
sections on `C/G` are derived global sections on the total site of the inverse image. This is
Stacks 0D8H for the site `C/G`, as the remark says. -/
@[stacks 09X6 "for a hypercovering `K` of `G`, `RΓ(C/G, E) = RΓ((C/K)_total, a⁻¹E)` with `a` the
  canonical augmentation; an isomorphism of functors on the unbounded derived category, which
  contains `D⁺(C/G)`"]
def derivedGlobalSectionsLocalizationIso :
    Augmentation.derivedGlobalSectionsBase (Cat.of (CostructuredArrow (yoneda (C := C)) G))
        (localizationPretopology G P).toGrothendieck ≅
      Augmentation.derivedTotalInverseImage
          (hypercoveringSituation (localizationPretopology G P) (localizedHypercovering G P H))
          (Cat.of (CostructuredArrow (yoneda (C := C)) G))
          (localizationPretopology G P).toGrothendieck
          (hypercoveringAugmentation (localizationPretopology G P)
            (localizedHypercovering G P H)) ⋙
        Augmentation.derivedGlobalSectionsTotal
          (hypercoveringSituation (localizationPretopology G P) (localizedHypercovering G P H)) :=
  derivedGlobalSectionsInverseImageIsoOfHypercovering' (localizationPretopology G P)
    (localizedHypercovering G P H)

/-- **Stacks 09X6, `RΓ(G, E) = RΓ((C/K)_total, a⁻¹j⁻¹E)`.** -/
@[stacks 09X6 "`RΓ(G, E) = RΓ((C/K)_total, a⁻¹j⁻¹E)` for a hypercovering `K` of `G`"]
def derivedSectionsOverPresheafInverseImageIso :
    derivedSectionsOverPresheaf P.toGrothendieck G ≅
      (localizationInverseImage G P).mapDerivedCategory ⋙
        Augmentation.derivedTotalInverseImage
            (hypercoveringSituation (localizationPretopology G P) (localizedHypercovering G P H))
            (Cat.of (CostructuredArrow (yoneda (C := C)) G))
            (localizationPretopology G P).toGrothendieck
            (hypercoveringAugmentation (localizationPretopology G P)
              (localizedHypercovering G P H)) ⋙
          Augmentation.derivedGlobalSectionsTotal
            (hypercoveringSituation (localizationPretopology G P) (localizedHypercovering G P H)) :=
  derivedSectionsOverPresheafIsoOfEq P.toGrothendieck G _
      (localizationPretopology_toGrothendieck G P) ≪≫
    Functor.isoWhiskerLeft _ (derivedGlobalSectionsLocalizationIso G P H)


/-- The localization functor of the total site followed by the localization functor of `C/G`:
`(C/K)_total ⥤ C/G ⥤ C`. It defines the composite `g` of the augmentation `a` and of `j`. -/
abbrev compositeLocalizationFunctor :
    Grothendieck (slices (localizedHypercovering G P H).toSimplicialObject) ⥤ C :=
  totalForget (localizedHypercovering G P H).toSimplicialObject ⋙ CostructuredArrow.proj yoneda G

/-- The composite `(C/K)_total ⥤ C/G ⥤ C` is continuous for the total topology and the topology
of `C`. -/
instance isContinuous_compositeLocalizationFunctor :
    (compositeLocalizationFunctor G P H).IsContinuous
      (hypercoveringSituation (localizationPretopology G P)
        (localizedHypercovering G P H)).totalTopology P.toGrothendieck :=
  haveI : (totalForget (localizedHypercovering G P H).toSimplicialObject).IsContinuous
      (hypercoveringSituation (localizationPretopology G P)
        (localizedHypercovering G P H)).totalTopology
      (localizationPretopology G P).toGrothendieck :=
    totalForget_isContinuous _ _
  Functor.isContinuous_comp _ _ _ (localizationPretopology G P).toGrothendieck _

/-- **`g⁻¹`**, for `g : Sh((C/K)_total) ⟶ Sh(C)` the composition of the augmentation `a` and of
the localization morphism `j`: restriction of abelian sheaves along the composite
`(C/K)_total ⥤ C/G ⥤ C` of the functors defining `a` and `j`. -/
abbrev compositeInverseImage :
    Sheaf P.toGrothendieck AddCommGrpCat.{u} ⥤
      Sheaf (hypercoveringSituation (localizationPretopology G P)
        (localizedHypercovering G P H)).totalTopology AddCommGrpCat.{u} :=
  (compositeLocalizationFunctor G P H).sheafPushforwardContinuous AddCommGrpCat.{u}
    (hypercoveringSituation (localizationPretopology G P)
      (localizedHypercovering G P H)).totalTopology P.toGrothendieck

/-- `g⁻¹ = a⁻¹ ∘ j⁻¹` on abelian sheaves: the inverse image of the composite is the composite of
the inverse images. -/
def localizationInverseImageCompIso :
    localizationInverseImage G P ⋙
        Augmentation.totalInverseImageAb
          (hypercoveringSituation (localizationPretopology G P) (localizedHypercovering G P H))
          (Cat.of (CostructuredArrow (yoneda (C := C)) G))
          (localizationPretopology G P).toGrothendieck
          (hypercoveringAugmentation (localizationPretopology G P)
            (localizedHypercovering G P H)) ≅
      compositeInverseImage G P H :=
  Functor.isoWhiskerLeft (localizationInverseImage G P)
    (situationTotalInverseImageAbIso (localizationPretopology G P).toGrothendieck
      (localizedHypercovering G P H).toSimplicialObject)

/-- The inverse image `a⁻¹` of abelian sheaves along an augmentation is additive. -/
instance additive_totalInverseImageAb {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}}
    {K : GrothendieckTopology D} (a : Augmentation S D K) :
    (Augmentation.totalInverseImageAb S D K a).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse image `a⁻¹` of abelian sheaves along an augmentation preserves finite limits. -/
instance preservesFiniteLimits_totalInverseImageAb {S : SimplicialSiteSituation.{u}}
    {D : Cat.{u, u}} {K : GrothendieckTopology D} (a : Augmentation S D K) :
    PreservesFiniteLimits (Augmentation.totalInverseImageAb S D K a) :=
  inferInstanceAs (PreservesFiniteLimits (Sites.abelianInverseImage _))

/-- The inverse image `a⁻¹` of abelian sheaves along an augmentation preserves finite colimits. -/
instance preservesFiniteColimits_totalInverseImageAb {S : SimplicialSiteSituation.{u}}
    {D : Cat.{u, u}} {K : GrothendieckTopology D} (a : Augmentation S D K) :
    PreservesFiniteColimits (Augmentation.totalInverseImageAb S D K a) :=
  inferInstanceAs (PreservesFiniteColimits (Sites.abelianInverseImage _))

/-- `g⁻¹` on abelian sheaves is additive. -/
instance additive_compositeInverseImage : (compositeInverseImage G P H).Additive :=
  haveI := additive_totalInverseImageAb (hypercoveringAugmentation (localizationPretopology G P)
    (localizedHypercovering G P H))
  haveI := additive_localizationInverseImage' G P
  Functor.additive_of_iso (localizationInverseImageCompIso G P H)

/-- `g⁻¹` on abelian sheaves preserves finite limits. -/
instance preservesFiniteLimits_compositeInverseImage :
    PreservesFiniteLimits (compositeInverseImage G P H) :=
  haveI := preservesFiniteLimits_totalInverseImageAb (hypercoveringAugmentation
    (localizationPretopology G P) (localizedHypercovering G P H))
  haveI := preservesFiniteLimits_localizationInverseImage' G P
  preservesFiniteLimits_of_natIso (localizationInverseImageCompIso G P H)

/-- `g⁻¹` on abelian sheaves preserves finite colimits. -/
instance preservesFiniteColimits_compositeInverseImage :
    PreservesFiniteColimits (compositeInverseImage G P H) :=
  haveI := preservesFiniteColimits_totalInverseImageAb (hypercoveringAugmentation
    (localizationPretopology G P) (localizedHypercovering G P H))
  haveI := preservesFiniteColimits_localizationInverseImage' G P
  preservesFiniteColimits_of_natIso (localizationInverseImageCompIso G P H)

/-- `g⁻¹ = a⁻¹ ∘ j⁻¹` on the unbounded derived categories. -/
def derivedLocalizationInverseImageCompIso :
    (localizationInverseImage G P).mapDerivedCategory ⋙
        Augmentation.derivedTotalInverseImage
          (hypercoveringSituation (localizationPretopology G P) (localizedHypercovering G P H))
          (Cat.of (CostructuredArrow (yoneda (C := C)) G))
          (localizationPretopology G P).toGrothendieck
          (hypercoveringAugmentation (localizationPretopology G P)
            (localizedHypercovering G P H)) ≅
      (compositeInverseImage G P H).mapDerivedCategory :=
  haveI := additive_totalInverseImageAb (hypercoveringAugmentation (localizationPretopology G P)
    (localizedHypercovering G P H))
  haveI := preservesFiniteLimits_totalInverseImageAb (hypercoveringAugmentation
    (localizationPretopology G P) (localizedHypercovering G P H))
  haveI := preservesFiniteColimits_totalInverseImageAb (hypercoveringAugmentation
    (localizationPretopology G P) (localizedHypercovering G P H))
  Functor.isoWhiskerLeft _ (Augmentation.derivedTotalInverseImageIsoMapDerivedCategory _ _ _ _) ≪≫
    RingTheory.TorIndependence.mapDerivedCategoryCompNatIso _ _ _
      (localizationInverseImageCompIso G P H)

/-- **Stacks 09X6, `RΓ(G, E) = RΓ((C/K)_total, g⁻¹E)`.** Let `C` be a site with equalizers and
fibre products, `G` a presheaf of sets on `C` and `K` a hypercovering of `G`. Let
`g : Sh((C/K)_total) ⟶ Sh(C)` be the composition of the canonical augmentation
`a : Sh((C/K)_total) ⟶ Sh(C/G)` and of the localization morphism `j : Sh(C/G) ⟶ Sh(C)`. Then

`RΓ(G, E) = RΓ((C/K)_total, g⁻¹E)`

naturally in `E` in the unbounded derived category of abelian sheaves on `C`, in particular for
`E ∈ D⁺(C)`. -/
@[stacks 09X6 "for a hypercovering `K` of `G`, `RΓ(G, E) = RΓ((C/K)_total, g⁻¹E)` with `g` the
  composition of `a` and `j`; an isomorphism of functors on the unbounded derived category, which
  contains `D⁺(C)`"]
def derivedSectionsOverPresheafCompositeIso :
    derivedSectionsOverPresheaf P.toGrothendieck G ≅
      (compositeInverseImage G P H).mapDerivedCategory ⋙
        Augmentation.derivedGlobalSectionsTotal
          (hypercoveringSituation (localizationPretopology G P) (localizedHypercovering G P H)) :=
  derivedSectionsOverPresheafInverseImageIso G P H ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedLocalizationInverseImageCompIso G P H) _

end Hypercovering

end Stacks.CategoryTheory.Hypercovering.LocalizationAtPresheaf

end
