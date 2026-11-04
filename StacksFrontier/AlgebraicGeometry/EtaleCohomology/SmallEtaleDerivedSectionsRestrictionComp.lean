module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedDescAlongPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedPushforwardStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SectionsTransitivityOverBase

/-!
# Transitivity of restriction of derived sections

For morphisms of schemes `a : X ⟶ Y` and `b : Y ⟶ Z`, restriction of unbounded derived global
sections of abelian étale sheaves along the composite `a ≫ b`,

`RΓ(Z, M) ⟶ RΓ(X, (a ≫ b)⁻¹M)`,

is restriction along `b` followed by restriction along `a`, read through the composition
isomorphism `a⁻¹b⁻¹M ≅ (a ≫ b)⁻¹M`. On abelian sheaves this is transitivity of restriction of
sections in the scheme over the base
(`Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_base`), and on derived categories it
follows from the uniqueness of a transformation out of the right derived functor `RΓ(Z, -)`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleGlobalSectionsRestrictionAb_comp` — restriction of global
  sections of abelian étale sheaves along a composite.
* `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction_comp_app` — restriction of
  unbounded derived global sections along a composite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- **Restriction of global sections along a composite.** For `a : X ⟶ Y` and `b : Y ⟶ Z`,
restriction of global sections of an abelian étale sheaf on `Z` along `a ≫ b` is restriction
along `b` followed by restriction along `a`, read through the composition isomorphism
`a⁻¹b⁻¹F ≅ (a ≫ b)⁻¹F`. -/
theorem smallEtaleGlobalSectionsRestrictionAb_comp :
    smallEtaleGlobalSectionsRestrictionAb (a ≫ b) =
      smallEtaleGlobalSectionsRestrictionAb b ≫
        Functor.whiskerLeft (smallEtalePullbackAb b) (smallEtaleGlobalSectionsRestrictionAb a) ≫
          (Functor.associator (smallEtalePullbackAb b) (smallEtalePullbackAb a)
              (Sheaf.Γ (smallEtaleTopology X) Ab.{u + 1})).inv ≫
            Functor.whiskerRight (smallEtalePullbackAbCompIso a b).hom
              (Sheaf.Γ (smallEtaleTopology X) Ab.{u + 1}) := by
  have h := smallEtaleSectionsPullbackAb_comp_base b a (Scheme.Etale.mk (𝟙 Z)) b
    (Category.comp_id b) (Category.comp_id (a ≫ b))
  refine (congrArg (fun σ => (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) Ab.{u + 1}
    (isTerminalEtaleMkId Z)).hom ≫ σ) h).trans ?_
  simp only [smallEtaleGlobalSectionsRestrictionAb, Category.assoc]

variable
  [((Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology Y) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology X) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))]

/-- **Restriction of derived sections along a composite.** For `a : X ⟶ Y` and `b : Y ⟶ Z`,
restriction of unbounded derived global sections along `a ≫ b` is restriction along `b` followed
by restriction along `a`, read through the composition isomorphism of derived inverse images. -/
theorem smallEtaleDerivedGlobalSectionsRestriction_comp :
    smallEtaleDerivedGlobalSectionsRestriction (a ≫ b) =
      smallEtaleDerivedGlobalSectionsRestriction b ≫
        Functor.whiskerLeft (smallEtaleDerivedPullbackAb b)
          (smallEtaleDerivedGlobalSectionsRestriction a) ≫
          (Functor.associator (smallEtaleDerivedPullbackAb b) (smallEtaleDerivedPullbackAb a)
              (smallEtaleDerivedGlobalSections X)).inv ≫
            Functor.whiskerRight
              (smallEtaleDerivedPullbackAbCompIsoQhLift (smallEtalePullbackAbCompIso a b)).hom
              (smallEtaleDerivedGlobalSections X) := by
  refine Functor.rightDerived_ext (smallEtaleDerivedGlobalSections Z)
    (smallEtaleDerivedGlobalSectionsUnit Z)
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) _ _ _ ?_
  ext J
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp]
  rw [smallEtaleDerivedGlobalSectionsRestriction_fac_app,
    reassoc_of% (smallEtaleDerivedGlobalSectionsRestriction_fac_app b J)]
  have hnat := (smallEtaleDerivedGlobalSectionsRestriction a).naturality
    ((smallEtalePullbackAb b).mapDerivedCategoryFactorsh.inv.app J)
  simp only [Functor.comp_map] at hnat
  rw [reassoc_of% hnat,
    reassoc_of% (smallEtaleDerivedGlobalSectionsRestriction_fac_app a
      (((smallEtalePullbackAb b).mapHomotopyCategory (.up ℤ)).obj J)),
    smallEtaleDerivedPullbackAbCompIsoQhLift_hom_app]
  have key : (smallEtalePullbackAb a).mapDerivedCategoryFactorsh.inv.app
        (((smallEtalePullbackAb b).mapHomotopyCategory (.up ℤ)).obj J) ≫
      (smallEtaleDerivedPullbackAb a).map
        ((smallEtalePullbackAb b).mapDerivedCategoryFactorsh.inv.app J ≫
          (smallEtalePullbackAb b).mapDerivedCategoryFactorsh.hom.app J) ≫
      (smallEtalePullbackAb a).mapDerivedCategoryFactorsh.hom.app
        (((smallEtalePullbackAb b).mapHomotopyCategory (.up ℤ)).obj J) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (smallEtalePullbackAbCompIso a b) (.up ℤ)).hom.app J) ≫
      (smallEtalePullbackAb (a ≫ b)).mapDerivedCategoryFactorsh.inv.app J =
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (smallEtalePullbackAbCompIso a b) (.up ℤ)).hom.app J) ≫
      (smallEtalePullbackAb (a ≫ b)).mapDerivedCategoryFactorsh.inv.app J := by
    rw [Iso.inv_hom_id_app]
    exact (congrArg (fun m => _ ≫ m ≫ _) ((smallEtaleDerivedPullbackAb a).map_id _)).trans
      (by rw [Category.id_comp, Iso.inv_hom_id_app_assoc])
  simp only [← Functor.map_comp, ← Functor.map_comp_assoc]
  rw [key, (smallEtaleDerivedGlobalSections X).map_comp]
  have hη := (smallEtaleDerivedGlobalSectionsUnit X).naturality
    ((Functor.mapHomotopyCategoryCompIso (smallEtalePullbackAbCompIso a b) (.up ℤ)).hom.app J)
  simp only [Functor.comp_map] at hη
  rw [← reassoc_of% hη, ← Functor.map_comp_assoc, Category.assoc,
    Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_trans,
    smallEtaleGlobalSectionsRestrictionAb_comp]

end Stacks.EtaleCohomology

end
