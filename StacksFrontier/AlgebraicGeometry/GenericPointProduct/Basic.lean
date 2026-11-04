module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.AlgebraicGeometry.GenericPointProduct.Comparison

/-!
# The generic-point product decomposition of the meromorphic functions

On a scheme whose weakly associated points are generic points of irreducible components, and whose
quasi-compact opens have finitely many irreducible components, the `𝒪_X`-module of meromorphic
functions is the product, over the generic points, of the pushed-forward structure sheaves of the
local schemes there.

## Main definitions

* `Stacks.AlgebraicGeometry.GenericPointProduct.comparison`: the comparison morphism of sheaves of
  commutative rings from the sheaf of total quotient rings to the generic-point product.
* `Stacks.AlgebraicGeometry.GenericPointProduct.germModuleHom`: its component at one generic point,
  as a morphism of `𝒪_X`-modules.
* `Stacks.AlgebraicGeometry.GenericPointProduct.decomposition`: the resulting morphism into the
  product in the category of `𝒪_X`-modules.

## Main results

* `Stacks.AlgebraicGeometry.GenericPointProduct.isIso_decomposition`: the decomposition is an
  isomorphism.
* `Stacks.AlgebraicGeometry.GenericPointProduct.meromorphicFunctionsIsoProduct`: the resulting
  isomorphism of the meromorphic functions with the generic-point product.

## Implementation notes

A morphism of `𝒪_X`-modules is built out of the comparison morphism of sheaves of rings for each
generic point separately, and these are assembled by the universal property of the product; this
avoids any description of the sections of the categorical product while the morphism is being
constructed. That description is needed only to check invertibility, where the sections of the
product are compared with the product of the sections through
`Stacks.AlgebraicGeometry.GenericPointSheaf.productSectionsIso`.

Both the scalar multiplication on the module of meromorphic functions and the one on a
generic-point contribution are definitionally multiplication in a ring of sections, by the image of
the scalar under the canonical map; the linearity of the comparison is therefore multiplicativity.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GenericPointProduct

open Stacks.AlgebraicGeometry.GenericPointDecomposition
open Stacks.AlgebraicGeometry.GenericPointSheaf

variable (X : Scheme.{u})

/-- The comparison morphism from the sheaf of total quotient rings to the generic-point product,
obtained from the comparison out of the total quotient presheaf by the universal property of
sheafification. -/
noncomputable abbrev comparison :
    sheafify (Opens.grothendieckTopology X) X.presheaf.totalQuotientPresheaf ⟶ piStalkPresheaf X :=
  sheafifyLift (Opens.grothendieckTopology X) (totalQuotientToPiStalk X)
    (piStalkSheaf X).property

/-- On the image of the regular functions, the comparison morphism is the family of pullbacks of
sections to the local schemes at the generic points. -/
theorem toTotalQuotientSheaf_comp_comparison :
    X.toTotalQuotientSheaf.hom ≫ comparison X = toPiStalkPresheaf X := by
  have e1 : X.toTotalQuotientSheaf.hom ≫ comparison X =
      X.presheaf.toTotalQuotientPresheaf ≫
        (toSheafify (Opens.grothendieckTopology X) X.presheaf.totalQuotientPresheaf ≫
          comparison X) :=
    (congrArg (fun g ↦ g ≫ comparison X) (Scheme.toTotalQuotientSheaf_hom X)).trans
      (Category.assoc _ _ _)
  have e2 : toSheafify (Opens.grothendieckTopology X) X.presheaf.totalQuotientPresheaf ≫
      comparison X = totalQuotientToPiStalk X := toSheafify_sheafifyLift _ _ _
  rw [e1, e2]
  exact NatTrans.ext (funext fun V ↦ CommRingCat.hom_ext
    (RingHom.ext fun s ↦ totalQuotientToPiStalkApp_apply_app X V s))

/-- On the image of the regular functions, the comparison morphism is the family of pullbacks of
sections, elementwise. -/
theorem comparison_app_toTotalQuotient (U : (Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj U) :
    (comparison X).app U ((toTotalQuotientRingCatSheaf X).hom.app U r) =
      (toPiStalkPresheaf X).app U r :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (toTotalQuotientSheaf_comp_comparison X) U) r

/-- The component of the comparison morphism at one generic point, as a morphism of
`𝒪_X`-modules from the sheaf of meromorphic functions to the generic-point contribution at
that point. -/
noncomputable def germModuleHom (η : genericPoints X) :
    meromorphicFunctions X ⟶ genericPointStalkModule X η :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom
        (X := (meromorphicFunctions X).val.obj U)
        (Y := (genericPointStalkModule X η).val.obj U)
        { toFun := fun t ↦ (comparison X).app U t η
          map_add' := fun t₁ t₂ ↦
            congrFun (map_add ((comparison X).app U).hom t₁ t₂) η
          map_smul' := fun r t ↦
            (congrFun (map_mul ((comparison X).app U).hom
                ((toTotalQuotientRingCatSheaf X).hom.app U r)
                (show (totalQuotientRingCatSheaf X).obj.obj U from t)) η).trans
              (congrArg (fun y ↦ y * ((comparison X).app U t η))
                (congrFun (comparison_app_toTotalQuotient X U r) η)) }
     naturality := fun {U V} f ↦ by
       ext t
       exact congrFun (ConcreteCategory.congr_hom ((comparison X).naturality f) t) η }⟩

/-- On sections over `U`, the component of the comparison morphism at `η` sends `t` to the
`η`-coordinate of its image under the comparison morphism. -/
theorem germModuleHom_val_app_apply (η : genericPoints X) (U : (Opens X)ᵒᵖ)
    (t : (meromorphicFunctions X).val.obj U) :
    (germModuleHom X η).val.app U t = (comparison X).app U t η := rfl

/-- The generic-point decomposition of the sheaf of meromorphic functions: the morphism into the
product, over the generic points, of the pushed-forward structure sheaves of the local schemes. -/
noncomputable def decomposition :
    meromorphicFunctions X ⟶ ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModule X η :=
  Pi.lift (germModuleHom X)

/-- The sections, over an open set, of a product of `𝒪_X`-modules, identified with the product of
the sections of the factors. -/
noncomputable def sectionsPi (F : genericPoints X → X.Modules) (U : X.Opens) :
    (sectionsFunctor X U).obj (∏ᶜ F) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op U))
        (∀ η : genericPoints X, (sectionsFunctor X U).obj (F η)) :=
  productSectionsIso F U ≪≫ ModuleCat.piIsoPi _

/-- The `η`-coordinate of the image of a section of a product under `sectionsPi` is its image
under the projection to the factor at `η`. -/
theorem sectionsPi_hom_apply (F : genericPoints X → X.Modules) (U : X.Opens)
    (x : (sectionsFunctor X U).obj (∏ᶜ F)) (η : genericPoints X) :
    (sectionsPi X F U).hom x η = (sectionsFunctor X U).map (Pi.π F η) x := by
  have h1 : (ModuleCat.piIsoPi fun η ↦ (sectionsFunctor X U).obj (F η)).hom
      ((productSectionsIso F U).hom x) η =
      (Pi.π (fun η ↦ (sectionsFunctor X U).obj (F η)) η) ((productSectionsIso F U).hom x) :=
    ConcreteCategory.congr_hom
      (ModuleCat.piIsoPi_hom_ker_subtype (fun η ↦ (sectionsFunctor X U).obj (F η)) η)
      ((productSectionsIso F U).hom x)
  have h2 : (productSectionsIso F U).hom ≫
      Pi.π (fun η ↦ (sectionsFunctor X U).obj (F η)) η =
      (sectionsFunctor X U).map (Pi.π F η) := by
    rw [productSectionsIso, PreservesProduct.iso_hom, piComparison, Pi.lift_π]
  exact h1.trans (by rw [← ConcreteCategory.comp_apply, h2])

/-- The `η`-coordinate of the image of a meromorphic function under the decomposition is the
`η`-coordinate of its image under the comparison morphism. -/
theorem sectionsPi_hom_decomposition (U : X.Opens)
    (t : (sectionsFunctor X U).obj (meromorphicFunctions X)) (η : genericPoints X) :
    (sectionsPi X (fun η ↦ genericPointStalkModule X η) U).hom
        ((sectionsFunctor X U).map (decomposition X) t) η =
      (comparison X).app (op U) t η := by
  rw [sectionsPi_hom_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp, decomposition,
    Pi.lift_π]
  exact germModuleHom_val_app_apply X η (op U) t

variable {X}

/-- The generic-point decomposition is an isomorphism of `𝒪_X`-modules. -/
theorem isIso_decomposition
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents (U : Set X)).Finite) :
    IsIso (decomposition X) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  have hcmp : IsIso ((comparison X).app (op U)) :=
    isIso_sheafifyLift_totalQuotientToPiStalk_app hass hfin U
  have hbij : Function.Bijective ((sectionsFunctor X U).map (decomposition X)) := by
    have key : (sectionsPi X (fun η ↦ genericPointStalkModule X η) U).hom ∘
        (sectionsFunctor X U).map (decomposition X) = (comparison X).app (op U) :=
      funext fun t ↦ funext fun η ↦ sectionsPi_hom_decomposition X U t η
    exact (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso
      (sectionsPi X (fun η ↦ genericPointStalkModule X η) U).hom) _).mp
        (key ▸ ConcreteCategory.bijective_of_isIso ((comparison X).app (op U)))
  have : IsIso ((sectionsFunctor X U).map (decomposition X)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact Functor.map_isIso (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op U))) _)
    ((sectionsFunctor X U).map (decomposition X))

/-- **Stacks Project, Tag 0EMF.** On a scheme whose weakly associated points are generic points of
irreducible components, and whose quasi-compact opens have finitely many irreducible components,
the `𝒪_X`-module of meromorphic functions is the product, over the generic points, of the
structure sheaves of the local schemes there, pushed forward to `X`. -/
noncomputable def meromorphicFunctionsIsoProduct
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfin : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents (U : Set X)).Finite) :
    meromorphicFunctions X ≅ ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModule X η :=
  letI := isIso_decomposition hass hfin
  asIso (decomposition X)

end Stacks.AlgebraicGeometry.GenericPointProduct
