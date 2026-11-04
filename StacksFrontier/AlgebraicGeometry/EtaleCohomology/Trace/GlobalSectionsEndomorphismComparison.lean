module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTwistStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GlobalLefschetzNumberOfCtf
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ContinuousGlobalSectionsComp
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.RestrictionOfGlobalSections

/-!
# Endomorphisms of `RΓ(Y, M)` against endomorphisms of `RΓ(Z, Rg_* M)`

Let `g : Y ⟶ Z` be a morphism of schemes and `π : Y ⟶ Y` an endomorphism over `Z`, so
`π ≫ g = g`.  A morphism `γ : M ⟶ Rπ_* M` in `D⁺(Y_étale, Λ)` induces two endomorphisms:

* of `RΓ(Y, M)`: `RΓ(Y, γ)` followed by `RΓ(Y, Rπ_*(-)) ≅ RΓ(Y, -)`;
* of `RΓ(Z, Rg_* M)`: `RΓ(Z, Rg_*(γ))` followed by `Rg_* ∘ Rπ_* ≅ Rg_*`.

The comparison `RΓ(Y, -) ≅ RΓ(Z, Rg_*(-))` of
`Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsCompIso` intertwines them.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDirectImageCompGlobalSections_triangle`: the identifications
  `Γ(Z, g_* -) ≅ Γ(Y, -)`, `Γ(Y, π_* -) ≅ Γ(Y, -)` and `π_* ⋙ g_* ≅ g_*` are compatible.
* `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsCompIso_triangle`: the comparisons
  `RΓ(Y, -) ≅ RΓ(Z, Rg_* -)`, `RΓ(Y, -) ≅ RΓ(Y, Rπ_* -)` and `Rg_* ≅ Rg_* ∘ Rπ_*` are compatible.
* `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsCompIso_comm_endomorphism`: the
  comparison `RΓ(Y, M) ≅ RΓ(Z, Rg_* M)` intertwines the two endomorphisms induced by `γ`.

The proof is the coherence triangle of composition comparisons
(`Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso_triangle`); its underived input,
`Stacks.EtaleCohomology.etaleModuleDirectImageCompGlobalSections_triangle`, is checked on
sections over every étale `Z`-scheme, where all maps are restriction maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ]

/-- On a site with a terminal object `T`, the inverse of `Γ ≅ (-)(T)` followed by restriction to
`U` is restriction along the unique map `U ⟶ T`. -/
@[reassoc]
theorem ΓNatIsoSheafSections_inv_app_comp_ΓRes {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A : Type*} [Category A] [HasWeakSheafify J A] [HasTerminal C]
    {T : C} (hT : IsTerminal T) (F : Sheaf J A) (U : Cᵒᵖ) :
    (Sheaf.ΓNatIsoSheafSections J A hT).inv.app F ≫ F.ΓRes U =
      F.obj.map (hT.from U.unop).op := by
  rw [← F.ΓRes_map (hT.from U.unop).op, ← Sheaf.ΓNatIsoSheafSections_hom_app_general hT,
    Iso.inv_hom_id_app_assoc]

/-- The identification `Γ(Y, g_* N) ≅ Γ(X, N)` followed by restriction to `U` is restriction to the
base change of `U`. -/
@[reassoc]
theorem etaleModuleDirectImageCompGlobalSections_inv_app_comp_ΓRes {X Y : Scheme.{u}}
    (g : X ⟶ Y) (N : EtaleModules.{u, r} Λ X) (U : (Y.Etale)ᵒᵖ) :
    (etaleModuleDirectImageCompGlobalSections.{u, r} Λ g).inv.app N ≫
        Sheaf.ΓRes ((etaleModuleDirectImage.{u, r} Λ g).obj N) U =
      Sheaf.ΓRes N (op ((smallEtaleBaseChange g).obj U.unop)) := by
  have : IsIso (Scheme.Etale.mk (𝟙 Y)).hom := inferInstanceAs (IsIso (𝟙 Y))
  have : HasTerminal Y.Etale := (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Y))).hasTerminal
  have : IsIso (Scheme.Etale.mk (𝟙 X)).hom := inferInstanceAs (IsIso (𝟙 X))
  have : HasTerminal X.Etale := (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 X))).hasTerminal
  have e : (etaleModuleDirectImageCompGlobalSections.{u, r} Λ g).inv.app N =
      ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
          (isTerminalSmallEtaleBaseChangeObj g
            (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Y))))).hom.app N ≫ 𝟙 _) ≫
        (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
          (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Y)))).inv.app
            ((etaleModuleDirectImage.{u, r} Λ g).obj N) := rfl
  have h2 := ΓNatIsoSheafSections_inv_app_comp_ΓRes
    (J := Y.smallEtaleTopology) (A := ModuleCat.{max (u + 1) r} Λ)
    (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Y))) ((etaleModuleDirectImage.{u, r} Λ g).obj N) U
  have h3 := Sheaf.ΓNatIsoSheafSections_hom_app_general (J := X.smallEtaleTopology)
    (A := ModuleCat.{max (u + 1) r} Λ)
    (isTerminalSmallEtaleBaseChangeObj g (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Y)))) N
  rw [e, Category.comp_id]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) h2).trans ?_
  refine (congrArg (· ≫ _) h3).trans ?_
  exact Sheaf.ΓRes_map N _

/-- The underived triangle: for `π : Y ⟶ Y` over `g : Y ⟶ Z`, the identifications
`Γ(Z, g_* -) ≅ Γ(Y, -)`, `Γ(Y, π_* -) ≅ Γ(Y, -)` and `π_* ⋙ g_* ≅ g_*` are compatible. -/
theorem etaleModuleDirectImageCompGlobalSections_triangle {Y Z : Scheme.{u}} (π : Y ⟶ Y)
    (g : Y ⟶ Z) (hπ : π ≫ g = g) (N : EtaleModules.{u, r} Λ Y) :
    (etaleModuleDirectImageCompGlobalSections.{u, r} Λ g).inv.app N ≫
        (etaleModuleGlobalSections.{u, r} Λ Z).map
          ((etaleModuleDirectImageComp.{u, r} Λ π g g hπ.symm).inv.app N) =
      (etaleModuleDirectImageCompGlobalSections.{u, r} Λ π).inv.app N ≫
        (etaleModuleDirectImageCompGlobalSections.{u, r} Λ g).inv.app
          ((etaleModuleDirectImage.{u, r} Λ π).obj N) := by
  refine Sheaf.hom_ext_of_ΓRes fun U => ?_
  have h4 := etaleModuleDirectImageCompGlobalSections_inv_app_comp_ΓRes Λ g
    ((etaleModuleDirectImage.{u, r} Λ π).obj N) U
  have h5 := etaleModuleDirectImageCompGlobalSections_inv_app_comp_ΓRes Λ π N
    (op ((smallEtaleBaseChange g).obj U.unop))
  rw [Category.assoc, Category.assoc, Sheaf.ΓRes_naturality,
    etaleModuleDirectImageCompGlobalSections_inv_app_comp_ΓRes_assoc]
  refine Eq.trans ?_ (congrArg (_ ≫ ·) h4).symm
  refine Eq.trans ?_ h5.symm
  rw [etaleModuleDirectImageComp_inv_app_hom_app]
  exact Sheaf.ΓRes_map N _

/-- **The derived triangle**: for `π : Y ⟶ Y` over `g : Y ⟶ Z`, the comparisons
`RΓ(Y, -) ≅ RΓ(Z, Rg_* -)`, `RΓ(Y, -) ≅ RΓ(Y, Rπ_* -)` and `Rg_* ≅ Rg_* ∘ Rπ_*` are compatible. -/
theorem etaleModuleDerivedGlobalSectionsCompIso_triangle {Y Z : Scheme.{u}} (π : Y ⟶ Y)
    (g : Y ⟶ Z) (hπ : π ≫ g = g) (M : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y)) :
    (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ g).hom.app M ≫
        (etaleModuleDerivedGlobalSections.{u, r} Λ Z).map
          ((etaleModuleDerivedDirectImageEndomorphismComp.{u, r} Λ π g hπ).hom.app M) =
      (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ π).hom.app M ≫
        (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ g).hom.app
          ((etaleModuleDerivedDirectImage.{u, r} Λ π).obj M) :=
  rightDerivedFunctorPlusCompIsoOfIso_triangle
    (etaleModuleDirectImageCompGlobalSections.{u, r} Λ π)
    (etaleModuleDirectImageCompGlobalSections.{u, r} Λ g)
    (etaleModuleDirectImageCompGlobalSections.{u, r} Λ g)
    (etaleModuleDirectImageComp.{u, r} Λ π g g hπ.symm)
    (etaleModuleDirectImageCompGlobalSections_triangle Λ π g hπ) M

/-- **The endomorphism of `RΓ(Y, M)` induced by `π` is the endomorphism of `RΓ(Z, Rg_* M)`.**
For `π : Y ⟶ Y` over `g : Y ⟶ Z` and `γ : M ⟶ Rπ_* M`, the comparison
`RΓ(Y, M) ≅ RΓ(Z, Rg_* M)` intertwines `RΓ(Y, γ)` followed by `RΓ(Y, Rπ_* M) ≅ RΓ(Y, M)` with
`RΓ(Z, Rg_* γ)` followed by `Rg_* Rπ_* M ≅ Rg_* M`. -/
theorem etaleModuleDerivedGlobalSectionsCompIso_comm_endomorphism {Y Z : Scheme.{u}}
    (π : Y ⟶ Y) (g : Y ⟶ Z) (hπ : π ≫ g = g)
    {M : DerivedCategory.Plus (EtaleModules.{u, r} Λ Y)}
    (γ : M ⟶ (etaleModuleDerivedDirectImage.{u, r} Λ π).obj M) :
    (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ g).hom.app M ≫
        (etaleModuleDerivedGlobalSections.{u, r} Λ Z).map
          ((etaleModuleDerivedDirectImage.{u, r} Λ g).map γ ≫
            (etaleModuleDerivedDirectImageEndomorphismComp.{u, r} Λ π g hπ).inv.app M) =
      ((etaleModuleDerivedGlobalSections.{u, r} Λ Y).map γ ≫
          (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ π).inv.app M) ≫
        (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ g).hom.app M := by
  have T := etaleModuleDerivedGlobalSectionsCompIso_triangle Λ π g hπ M
  have hn := (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ g).hom.naturality γ
  have key : (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ g).hom.app
        ((etaleModuleDerivedDirectImage.{u, r} Λ π).obj M) ≫
      (etaleModuleDerivedGlobalSections.{u, r} Λ Z).map
        ((etaleModuleDerivedDirectImageEndomorphismComp.{u, r} Λ π g hπ).inv.app M) =
      (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ π).inv.app M ≫
        (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ g).hom.app M := by
    rw [← cancel_epi ((etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ π).hom.app M),
      Iso.hom_inv_id_app_assoc, ← reassoc_of% T, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
  dsimp only [Functor.comp_map] at hn
  rw [Functor.map_comp, ← Category.assoc, ← hn, Category.assoc, key, Category.assoc]

end Stacks.EtaleCohomology

end
