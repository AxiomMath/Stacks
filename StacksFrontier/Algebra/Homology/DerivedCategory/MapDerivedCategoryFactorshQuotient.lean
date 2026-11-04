module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Crossing between the two localization functors onto the derived category

The derived category of an abelian category `C` is presented twice: as a localization of the
category of cochain complexes, by `DerivedCategory.Q`, and as a localization of the homotopy
category, by `DerivedCategory.Qh`. The two are identified by
`DerivedCategory.quotientCompQhIso : HomotopyCategory.quotient C _ ⋙ Qh ≅ Q`, and every
construction performed over one of them has to be read over the other before it can meet a
construction performed over the other.

This file holds the two crossings that such a reading needs: the comparison
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the degreewise action of an exact functor
with `DerivedCategory.Qh`, at the image of a cochain complex under the homotopy quotient, written
in terms of the comparison `CategoryTheory.Functor.mapDerivedCategoryFactors` with
`DerivedCategory.Q`; and the localization by `DerivedCategory.Qh` of the quotient of a morphism of
cochain complexes, written as its localization by `DerivedCategory.Q`.

Nothing here is specific to any geometry: everything is stated for an arbitrary exact additive
functor between abelian categories with derived categories.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app_quotient_obj`: the comparison over
  `DerivedCategory.Qh` at the quotient of a cochain complex is the comparison over
  `DerivedCategory.Q`, conjugated by `DerivedCategory.quotientCompQhIso`.
* `CategoryTheory.Functor.mapDerivedCategoryFactorsh_inv_app_quotient_obj`: the inverse half.
* `CategoryTheory.Functor.Qh_map_quotient_map`: the localization by `DerivedCategory.Qh` of the
  quotient of a morphism of complexes, read through `DerivedCategory.quotientCompQhIso`.

## Implementation notes

`HomologicalComplexUpToQuasiIso.Qh`, hence `DerivedCategory.Qh`, is not exposed, so the fact that
`DerivedCategory.Qh` is the lift of `DerivedCategory.Q` along the quotient functor — which would
make the components of `DerivedCategory.quotientCompQhIso` identities — is not available. The two
localization functors are therefore compared only through that isomorphism.
`CategoryTheory.Functor.mapHomotopyCategoryFactors` *is* exposed, and is an instance of
`CategoryTheory.Quotient.lift.isLift`, so its components are identities; that is what removes the
last factor from `CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]

/-- At the image of a cochain complex under `HomotopyCategory.quotient`, the comparison of the
degreewise action of an exact functor with `DerivedCategory.Qh` is its comparison with
`DerivedCategory.Q`, read through the identification `DerivedCategory.quotientCompQhIso` of
`DerivedCategory.Q` with the lift of `DerivedCategory.Qh` along the quotient functor. This is
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_hom_app` with its last factor — the
localization of a component of `CategoryTheory.Functor.mapHomotopyCategoryFactors`, which is an
identity — removed. -/
theorem mapDerivedCategoryFactorsh_hom_app_quotient_obj (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : CochainComplex C₁ ℤ) :
    F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app K ≫
          (DerivedCategory.quotientCompQhIso C₂).inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      F.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) := by
  have hid : DerivedCategory.Qh.map
      ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) = 𝟙 _ :=
    (congrArg DerivedCategory.Qh.map
      (CategoryTheory.Quotient.lift.isLift_inv _ _ _ K)).trans (DerivedCategory.Qh.map_id _)
  refine Eq.trans ?_ (F.mapDerivedCategoryFactorsh_hom_app K).symm
  exact congrArg (F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).hom.app K) ≫ ·)
    (congrArg (F.mapDerivedCategoryFactors.hom.app K ≫ ·)
      ((Category.comp_id _).symm.trans
        (congrArg ((DerivedCategory.quotientCompQhIso C₂).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ ·) hid.symm)))

/-- The inverse half of `mapDerivedCategoryFactorsh_hom_app_quotient_obj`: the inverse of a
composite of isomorphisms is the composite of the inverses in the opposite order. -/
theorem mapDerivedCategoryFactorsh_inv_app_quotient_obj (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : CochainComplex C₁ ℤ) :
    (DerivedCategory.quotientCompQhIso C₂).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        F.mapDerivedCategoryFactors.inv.app K ≫
          F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₁).inv.app K) =
      F.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) :=
  (Category.assoc _ _ _).symm.trans (congrArg Iso.inv
    (Iso.ext (α := F.mapDerivedCategory.mapIso ((DerivedCategory.quotientCompQhIso C₁).app K) ≪≫
        F.mapDerivedCategoryFactors.app K ≪≫
          ((DerivedCategory.quotientCompQhIso C₂).app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm)
      (β := F.mapDerivedCategoryFactorsh.app _)
      (mapDerivedCategoryFactorsh_hom_app_quotient_obj F K)))

/-- The localization by `DerivedCategory.Qh` of the quotient of a morphism of cochain complexes is
its localization by `DerivedCategory.Q`, read through `DerivedCategory.quotientCompQhIso`: that is
naturality of the identification. -/
theorem Qh_map_quotient_map {A B : CochainComplex C₁ ℤ} (f : A ⟶ B) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).map f) =
      (DerivedCategory.quotientCompQhIso C₁).hom.app A ≫
        DerivedCategory.Q.map f ≫ (DerivedCategory.quotientCompQhIso C₁).inv.app B := by
  rw [← Category.assoc, ← DerivedCategory.quotientCompQhIso_hom_naturality, Category.assoc,
    Iso.hom_inv_id_app]
  exact (Category.comp_id _).symm

end CategoryTheory.Functor

end
