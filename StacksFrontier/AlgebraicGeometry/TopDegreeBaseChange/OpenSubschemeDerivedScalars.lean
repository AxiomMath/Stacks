module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayOpenSubschemeSectionsLE
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatPreimageRestrictSource
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OpenSubschemeDerivedSectionsImageTop
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismExactFunctorTransport

/-!
# The two readings of the scalars over an open subscheme, derived

Let `f : X ⟶ S` be a morphism of schemes, `V` an open of `S` and `U ≤ f⁻¹V` an open of `X`.
Sections over the open `U.ι ''ᵁ ⊤` of `X` are read over `Γ(V, 𝒪_S)` in two ways: through
`AlgebraicGeometry.Scheme.Opens.topIso` at `U`, restriction of sections from `f⁻¹V` to `U` and
`f^♯` at `V`; or through `(f.resLE V U e)^♯` at `⊤` and `topIso` at `V`. Both are restriction of
scalars along the one ring homomorphism `Γ(V, 𝒪_S) ⟶ Γ(U, 𝒪_U)` (`appLE_comp_topIso_inv_hom`).
This file identifies the two readings after derived sections over `U.ι ''ᵁ ⊤`, on the unbounded
derived categories, as `CategoryTheory.Functor.rightDerivedNatIso` at the degreewise
identification. Nothing is assumed of `f`, `V`, `U` or the module.

## Main definitions

* `resLETopRestrictScalars`: restriction of scalars along `(f.resLE V U e)^♯` at `⊤`.
* `baseTopRestrictScalars`: restriction of scalars along `topIso` at `V`.
* `restrictSourceScalars`: restriction of sections from `f⁻¹V` to `U`, then `f^♯` at `V`.
* `scalarsReconciliation`: the degreewise identification of the two readings.
* `scalarsUnitA`, `resLETopUnit` and `scalarsUnitB`: the units exhibiting the composites of
  derived sections with the restrictions of scalars as right derived functors.
* `derivedScalarsReconciliation`: the identification of the two readings on the derived
  categories.

## Main results

* `derivedScalarsReconciliation_hom_app_unit`: composed with the unit `scalarsUnitA`,
  `derivedScalarsReconciliation` is the localized degreewise identification followed by the unit
  `scalarsUnitB`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction (opensMap)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (exists_quasiIso_isKInjective)
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison
  (exactPostcomposeUnit isRightDerivedFunctor_exactPostcomposeUnit)
open Stacks.Cohomology.DerivedSectionsLeray
  (sectionsOverOpen derivedSectionsOverOpen derivedSectionsOverOpenUnit sectionsRestrictScalars)
open Stacks.EdgeCompat (preimageRestrictScalars)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-! ### Restrictions of scalars -/

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V)

/-- Restriction of scalars along `(f.resLE V U e)^♯` at `⊤`, from modules over
`Γ(U.ι ''ᵁ ⊤, 𝒪_X)` to modules over `Γ(⊤, 𝒪_V)`. -/
def resLETopRestrictScalars :
    ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj (op (U.ι ''ᵁ ⊤))) ⥤
      ModuleCat.{u} ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤)) :=
  preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤

/-- Restriction of scalars along `(f.resLE V U e)^♯` is additive. -/
instance resLETopRestrictScalars_additive : (resLETopRestrictScalars f V e).Additive :=
  inferInstanceAs ((preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤).Additive)

/-- Restriction of scalars along `(f.resLE V U e)^♯` is left exact. -/
instance resLETopRestrictScalars_preservesFiniteLimits :
    PreservesFiniteLimits (resLETopRestrictScalars f V e) :=
  inferInstanceAs (PreservesFiniteLimits
    (preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤))

/-- Restriction of scalars along `(f.resLE V U e)^♯` is right exact. -/
instance resLETopRestrictScalars_preservesFiniteColimits :
    PreservesFiniteColimits (resLETopRestrictScalars f V e) :=
  inferInstanceAs (PreservesFiniteColimits
    (preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤))

/-- Restriction of scalars along `AlgebraicGeometry.Scheme.Opens.topIso` at `V`, from modules
over `Γ(⊤, 𝒪_V)` to modules over `Γ(V, 𝒪_S)`. -/
def baseTopRestrictScalars :
    ModuleCat.{u} ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤)) ⥤
      ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V)) :=
  ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom

/-- Restriction of scalars along `topIso` at `V` is additive. -/
instance baseTopRestrictScalars_additive : (baseTopRestrictScalars (S := S) V).Additive :=
  inferInstanceAs ((ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).Additive)

/-- Restriction of scalars along `topIso` at `V` is left exact. -/
instance baseTopRestrictScalars_preservesFiniteLimits :
    PreservesFiniteLimits (baseTopRestrictScalars (S := S) V) :=
  inferInstanceAs (PreservesFiniteLimits
    (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom))

/-- Restriction of scalars along `topIso` at `V` is right exact. -/
instance baseTopRestrictScalars_preservesFiniteColimits :
    PreservesFiniteColimits (baseTopRestrictScalars (S := S) V) :=
  inferInstanceAs (PreservesFiniteColimits
    (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom))

/-- Restriction of scalars along the restriction of sections from `f⁻¹V` to `U` in `X`, followed
by restriction of scalars along `f^♯` at `V`. -/
abbrev restrictSourceScalars (hW : U ≤ (opensMap f.toLRSHom.toShHom).obj V) :
    ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj (op U)) ⥤
      ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V)) :=
  sectionsRestrictScalars X.toRingedSpace hW ⋙ preimageRestrictScalars f.toLRSHom.toShHom V

/-- The two readings of the ring homomorphism `Γ(V, 𝒪_S) ⟶ Γ(U, 𝒪_U)`, degreewise: restriction
of scalars along `topIso` at `U` followed by `restrictSourceScalars` is isomorphic to restriction
of scalars along `(f.resLE V U e)^♯` followed by restriction of scalars along `topIso` at `V`. -/
def scalarsReconciliation :
    imageTopRestrictScalarsOf X U ⋙ restrictSourceScalars f V e ≅
      resLETopRestrictScalars f V e ⋙ baseTopRestrictScalars V :=
  restrictScalarsSquareIso (f.appLE V U e).hom (Scheme.Opens.topIso U).inv.hom
    (Scheme.Opens.topIso V).inv.hom ((f.resLE V U e).appTop).hom
    (appLE_comp_topIso_inv_hom f V e)

/-! ### The two models of derived sections over `U.ι ''ᵁ ⊤`, read over `Γ(V, 𝒪_S)` -/

/-- The unit exhibiting `RΓ(U.ι ''ᵁ ⊤, -)`, read over `Γ(U, 𝒪_X)` through `topIso` at `U` and
then over `Γ(V, 𝒪_S)` through `restrictSourceScalars`, as a right derived functor. -/
def scalarsUnitA :
    ((sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙ imageTopRestrictScalarsOf X U) ⋙
          restrictSourceScalars f V e).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
        (imageTopRestrictScalarsOf X U).mapDerivedCategory) ⋙
          (restrictSourceScalars f V e).mapDerivedCategory :=
  exactPostcomposeUnit _ (restrictSourceScalars f V e) _ (imageTopCompUnit X U)

/-- `scalarsUnitA` exhibits a right derived functor. -/
instance isRightDerivedFunctor_scalarsUnitA :
    ((derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
        (imageTopRestrictScalarsOf X U).mapDerivedCategory) ⋙
          (restrictSourceScalars f V e).mapDerivedCategory).IsRightDerivedFunctor
      (scalarsUnitA f V e)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_exactPostcomposeUnit _ _ _ _ (exists_quasiIso_isKInjective X.toRingedSpace)

/-- The unit exhibiting `RΓ(U.ι ''ᵁ ⊤, -)` followed by restriction of scalars along
`(f.resLE V U e)^♯` as a right derived functor. -/
def resLETopUnit :
    (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
          resLETopRestrictScalars f V e).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
        (resLETopRestrictScalars f V e).mapDerivedCategory :=
  exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
    (resLETopRestrictScalars f V e) (derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
    (derivedSectionsOverOpenUnit X.toRingedSpace (U.ι ''ᵁ ⊤))

/-- `resLETopUnit` exhibits a right derived functor. -/
instance isRightDerivedFunctor_resLETopUnit :
    (derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
        (resLETopRestrictScalars f V e).mapDerivedCategory).IsRightDerivedFunctor
      (resLETopUnit f V e)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_exactPostcomposeUnit _ _ _ _ (exists_quasiIso_isKInjective X.toRingedSpace)

/-- The unit exhibiting `RΓ(U.ι ''ᵁ ⊤, -)` followed by restriction of scalars along
`(f.resLE V U e)^♯` and then along `topIso` at `V` as a right derived functor. -/
def scalarsUnitB :
    ((sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙ resLETopRestrictScalars f V e) ⋙
          baseTopRestrictScalars V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
        (resLETopRestrictScalars f V e).mapDerivedCategory) ⋙
          (baseTopRestrictScalars V).mapDerivedCategory :=
  exactPostcomposeUnit _ (baseTopRestrictScalars V) _ (resLETopUnit f V e)

/-- `scalarsUnitB` exhibits a right derived functor. -/
instance isRightDerivedFunctor_scalarsUnitB :
    ((derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
        (resLETopRestrictScalars f V e).mapDerivedCategory) ⋙
          (baseTopRestrictScalars V).mapDerivedCategory).IsRightDerivedFunctor
      (scalarsUnitB f V e)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_exactPostcomposeUnit _ _ _ _ (exists_quasiIso_isKInjective X.toRingedSpace)

/-! ### The derived identification -/

/-- **The two readings of the scalars agree on the unbounded derived category.** Derived sections
over `⊤` of the open subscheme `U`, read over `Γ(V, 𝒪_S)` through `topIso` at `U` and then down in
`X`, are the same as read through `(f.resLE V U e)^♯` and then `topIso` at `V`. -/
def derivedScalarsReconciliation :
    (derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
        (imageTopRestrictScalarsOf X U).mapDerivedCategory) ⋙
          (restrictSourceScalars f V e).mapDerivedCategory ≅
      (derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
        (resLETopRestrictScalars f V e).mapDerivedCategory) ⋙
          (baseTopRestrictScalars V).mapDerivedCategory :=
  Functor.rightDerivedNatIso _ _ (scalarsUnitA f V e) (scalarsUnitB f V e)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryNatIso
        (Functor.isoWhiskerLeft (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
          (scalarsReconciliation f V e)) (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- Composed with the unit `scalarsUnitA`, `derivedScalarsReconciliation` is the degreewise
identification `scalarsReconciliation` read on the homotopy category and localized, followed by
the unit `scalarsUnitB`. -/
theorem derivedScalarsReconciliation_hom_app_unit
    (L : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (scalarsUnitA f V e).app L ≫
        (derivedScalarsReconciliation f V e).hom.app (DerivedCategory.Qh.obj L) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryNatIso
            (Functor.isoWhiskerLeft (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
              (scalarsReconciliation f V e)) (ComplexShape.up ℤ)).hom.app L) ≫
        (scalarsUnitB f V e).app L :=
  Functor.rightDerivedNatTrans_app _ _ (scalarsUnitA f V e) (scalarsUnitB f V e)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _ L

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
