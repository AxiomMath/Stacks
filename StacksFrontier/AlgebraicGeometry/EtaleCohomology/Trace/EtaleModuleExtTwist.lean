module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExt
public import StacksFrontier.Algebra.Homology.RightDerivedEdgePostcompose
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionTwistEdge

/-!
# A twisted endomorphism of étale cohomology, read on `Ext` out of the constant sheaf

Let `Y` be a scheme, `Λ` a commutative ring, and let `Φ ⊣ Ψ` be an adjunction of exact
endofunctors of the sheaves of `Λ`-modules on `Y_étale`, with `Φ` lax monoidal for the sheaf
tensor product and `Ψ` preserving injectives (for instance `Φ = π̄⁻¹`, `Ψ = π̄_*` for a universal
homeomorphism `π̄`). Let `σ : Ψ ⋙ Γ(Y, -) ⟶ Γ(Y, -)` be compatible with the corepresentation of
global sections by the constant sheaf `Λ_Y` (hypothesis `hσ`: on maps out of `Λ_Y` it is
precomposition with the lax unit `ε : Λ_Y ⟶ Φ Λ_Y` after the adjunction). For a twist
`τ : N ⟶ Ψ N`, the endomorphism

`Hⁱ(Y, N) ⟶ Hⁱ(Y, Ψ N) ⟶ Rⁱ(Ψ ⋙ Γ)(N) ⟶ Hⁱ(Y, N)`

(`τ`, then the degreewise comparison of [Stacks, Tag 015M], then the map induced by `σ`) is, under
`Hⁱ(Y, M) ≅ Ext^i(Λ_Y, M)` (`Stacks.EtaleCohomology.etaleModuleRightDerivedPlusIsoExt`), the map
`b ↦ Stacks.ExtCup.adjunctionExtMap Φ Ψ adj N (b ∘ τ)`
(`etaleModuleRightDerivedPlusIsoExt_conj_edge`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.ExtCup

open ModuleSheafCohomology

section Generic

variable {C : Type*} [Category.{v} C] [Abelian C] [MonoidalCategory C] [HasExt.{v} C]
  [HasInjectiveResolutions C] [EnoughInjectives C] [HasDerivedCategory C]
  {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
  (Φ Ψ : C ⥤ C) [Φ.LaxMonoidal] [Φ.Additive] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ] (adj : Φ ⊣ Ψ) [Ψ.Additive] [PreservesFiniteLimits Ψ]
  [PreservesFiniteColimits Ψ] [Ψ.PreservesInjectiveObjects]
  (Γ : C ⥤ B) [Γ.Additive] (U : B ⥤ Ab.{v}) [U.Additive] [U.PreservesHomology]
  [PreservesFiniteLimits (Γ ⋙ U)] (α : Γ ⋙ U ≅ preadditiveCoyoneda.obj (op (𝟙_ C)))

/-- `Hⁱ ≅ Ext^i(𝟙, -)` assembled from the comparison of the two indexings, the extraction of `U`
from the right derived functors and the corepresentation `α`, as in
`Stacks.EtaleCohomology.etaleModuleRightDerivedPlusIsoExt`. -/
abbrev rightDerivedPlusIsoExt (M : C) (i : ℕ) :
    U.obj ((Γ.rightDerivedPlus (i : ℤ)).obj M) ≅ (extFunctorObj (𝟙_ C) i).obj M :=
  U.mapIso ((Stacks.DerivedIndexing.rightDerivedIso Γ i).app M).symm ≪≫
    ((extFunctorObjIsoRightDerived (Γ ⋙ U) (𝟙_ C) α i ≪≫ Γ.rightDerivedCompIso U i).app M).symm

/-- **A twisted endomorphism of `RⁱΓ`, read on `Ext` out of the unit**, generic form of
`Stacks.EtaleCohomology.etaleModuleRightDerivedPlusIsoExt_conj_edge`. -/
theorem rightDerivedPlusIsoExt_conj_edge (σ : Ψ ⋙ Γ ⟶ Γ)
    (hσ : Functor.whiskerRight σ U ≫ α.hom =
      (compCorepresentation Ψ (Γ ⋙ U) (𝟙_ C) α (Φ.obj (𝟙_ C)) (adjCorepresentation Φ Ψ adj)).hom ≫
        preadditiveCoyoneda.map (Functor.LaxMonoidal.ε Φ).op)
    (N : C) (τ : N ⟶ Ψ.obj N) (i : ℕ) (b : Ext.{v} (𝟙_ C) N i) :
    ((rightDerivedPlusIsoExt Γ U α N i).hom).hom
        ((U.map ((Γ.rightDerivedPlus (i : ℤ)).map τ ≫
            (Stacks.DerivedIndexing.rightDerivedPlusEdge Ψ Γ (i : ℤ)).app N ≫
            (Stacks.DerivedIndexing.rightDerivedPlusNatTrans σ (i : ℤ)).app N)).hom
          (((rightDerivedPlusIsoExt Γ U α N i).inv).hom b)) =
      adjunctionExtMap Φ Ψ adj N (b.comp (Ext.mk₀ τ) (add_zero i)) := by
  let e := extFunctorObjIsoRightDerived (Γ ⋙ U) (𝟙_ C) α i
  let c := Γ.rightDerivedCompIso U i
  let r := Stacks.DerivedIndexing.rightDerivedIso Γ i
  have hιinv : ∀ (M : C) (x : Ext.{v} (𝟙_ C) M i),
      ((rightDerivedPlusIsoExt Γ U α M i).inv).hom x =
        (U.map (r.hom.app M)).hom ((c.hom.app M).hom ((e.hom.app M).hom x)) := fun _ _ => rfl
  have hιhom : ∀ (M : C) y,
      ((rightDerivedPlusIsoExt Γ U α M i).hom).hom y =
        (e.inv.app M).hom ((c.inv.app M).hom ((U.map (r.inv.app M)).hom y)) := fun _ _ => rfl
  have happ : ∀ {A B C' : AddCommGrpCat.{v}} (f : A ⟶ B) (g : B ⟶ C') (x : A),
      (f ≫ g).hom x = g.hom (f.hom x) := fun _ _ _ => rfl
  have hn : (U.map ((Γ.rightDerivedPlus (i : ℤ)).map τ)).hom
      ((U.map (r.hom.app N)).hom ((c.hom.app N).hom ((e.hom.app N).hom b))) =
      (U.map (r.hom.app (Ψ.obj N))).hom ((c.hom.app (Ψ.obj N)).hom
        ((e.hom.app (Ψ.obj N)).hom (b.comp (Ext.mk₀ τ) (add_zero i)))) := by
    have hmap : ((extFunctorObj (𝟙_ C) i).map τ).hom b = b.comp (Ext.mk₀ τ) (add_zero i) := rfl
    have h1 := NatTrans.naturality_apply e.hom τ b
    rw [hmap] at h1
    have h2 := ConcreteCategory.congr_hom (c.hom.naturality τ) ((e.hom.app N).hom b)
    have h3 := congrArg U.map (r.hom.naturality τ)
    simp only [Functor.map_comp] at h3
    have h3' := ConcreteCategory.congr_hom h3 ((c.hom.app N).hom ((e.hom.app N).hom b))
    simp only [happ, Functor.comp_map] at h2 h3'
    rw [← h3', ← h2, h1]
  have hA := ConcreteCategory.congr_hom
    (Stacks.Cohomology.RightDerivedEdge.rightDerivedCompIso_hom_map_rightDerivedIso_edgePlus
      Ψ Γ U σ i N) ((e.hom.app (Ψ.obj N)).hom (b.comp (Ext.mk₀ τ) (add_zero i)))
  simp only [happ] at hA
  have hL2 := extFunctorObjIsoRightDerived_inv_edge_rightDerived Φ Ψ adj (Γ ⋙ U) α
    (Functor.whiskerRight σ U) hσ i N (b.comp (Ext.mk₀ τ) (add_zero i))
  have step : (U.map ((Γ.rightDerivedPlus (i : ℤ)).map τ ≫
        (Stacks.DerivedIndexing.rightDerivedPlusEdge Ψ Γ (i : ℤ)).app N ≫
        (Stacks.DerivedIndexing.rightDerivedPlusNatTrans σ (i : ℤ)).app N)).hom
        (((rightDerivedPlusIsoExt Γ U α N i).inv).hom b) =
      (U.map (r.hom.app N)).hom ((c.hom.app N).hom
        (((NatTrans.rightDerived (Functor.whiskerRight σ U) i).app N).hom
          (((Stacks.Cohomology.RightDerivedEdge.edge Ψ (Γ ⋙ U) i).app N).hom
            ((e.hom.app (Ψ.obj N)).hom (b.comp (Ext.mk₀ τ) (add_zero i)))))) := by
    rw [hιinv, Functor.map_comp, happ, hn]
    exact hA
  have hcancel : ∀ z, ((rightDerivedPlusIsoExt Γ U α N i).hom).hom
      ((U.map (r.hom.app N)).hom ((c.hom.app N).hom z)) = (e.inv.app N).hom z := by
    intro z
    rw [hιhom]
    change (c.hom.app N ≫ U.map (r.hom.app N) ≫ U.map (r.inv.app N) ≫ c.inv.app N ≫
      e.inv.app N).hom z = (e.inv.app N).hom z
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  rw [step, hcancel]
  exact hL2

end Generic

end Stacks.ExtCup

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory

variable (Λ : Type) [CommRing Λ] (Y : Scheme.{u})
  [(Y.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal]
  (Φ Ψ : EtaleModules.{u, 0} Λ Y ⥤ EtaleModules.{u, 0} Λ Y) [Φ.LaxMonoidal] [Φ.Additive]
  [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] (adj : Φ ⊣ Ψ) [Ψ.Additive]
  [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ] [Ψ.PreservesInjectiveObjects]

/-- **A twisted endomorphism of `Hⁱ(Y, -)`, read on `Ext` out of the constant sheaf.** -/
theorem etaleModuleRightDerivedPlusIsoExt_conj_edge
    (σ : Ψ ⋙ etaleModuleGlobalSections.{u, 0} Λ Y ⟶ etaleModuleGlobalSections.{u, 0} Λ Y)
    (hσ : Functor.whiskerRight σ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≫
        (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation Λ
          Y.smallEtaleTopology).hom =
      (ModuleSheafCohomology.compCorepresentation Ψ
          (etaleModuleGlobalSections.{u, 0} Λ Y ⋙
            forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
          (𝟙_ (EtaleModules.{u, 0} Λ Y))
          (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation Λ
            Y.smallEtaleTopology)
          (Φ.obj (𝟙_ _)) (Stacks.ExtCup.adjCorepresentation Φ Ψ adj)).hom ≫
        preadditiveCoyoneda.map (Functor.LaxMonoidal.ε Φ).op)
    (N : EtaleModules.{u, 0} Λ Y) (τ : N ⟶ Ψ.obj N) (i : ℕ)
    (b : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology)
      N i) :
    ((etaleModuleRightDerivedPlusIsoExt Λ Y N i).hom).hom
        (((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          (((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).map τ ≫
            (Stacks.DerivedIndexing.rightDerivedPlusEdge Ψ
              (etaleModuleGlobalSections.{u, 0} Λ Y) (i : ℤ)).app N ≫
            (Stacks.DerivedIndexing.rightDerivedPlusNatTrans σ (i : ℤ)).app N)).hom
          (((etaleModuleRightDerivedPlusIsoExt Λ Y N i).inv).hom b)) =
      Stacks.ExtCup.adjunctionExtMap Φ Ψ adj N (b.comp (Ext.mk₀ τ) (add_zero i)) := by
  have key := Stacks.ExtCup.rightDerivedPlusIsoExt_conj_edge Φ Ψ adj
    (etaleModuleGlobalSections.{u, 0} Λ Y) (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation Λ Y.smallEtaleTopology)
    σ hσ N τ i b
  have hι : ∀ M, etaleModuleRightDerivedPlusIsoExt Λ Y M i =
      Stacks.ExtCup.rightDerivedPlusIsoExt (etaleModuleGlobalSections.{u, 0} Λ Y)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
        (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation Λ
          Y.smallEtaleTopology) M i := fun _ => rfl
  rw [hι N]
  exact key

end Stacks.EtaleCohomology

end
