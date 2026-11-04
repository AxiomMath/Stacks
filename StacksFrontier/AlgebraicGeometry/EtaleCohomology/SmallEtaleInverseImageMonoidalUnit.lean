module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleExtTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedTwistEdge
public import StacksFrontier.CategoryTheory.Sites.SheafPullbackMonoidalUnit
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleGlobalSectionsAdjunctionTwist
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.RestrictionOfGlobalSections

/-!
# The unit of the monoidal inverse image of étale sheaves of modules

For a morphism of schemes `g : Y ⟶ X`, the lax unit `Λ_Y ⟶ g⁻¹ Λ_X` of the monoidal inverse image
`Stacks.EtaleCohomology.etaleModuleInverseImageSheafPullbackMonoidal` is the comparison
`Stacks.EtaleCohomology.etaleModuleInverseImageConstantIso` of constant sheaves
(`etaleModuleInverseImageMonoidal_ε`).

For a self-map `φ : Y ⟶ Y` over `g : Y ⟶ S`, the identification `Γ(Y, φ_* -) ≅ Γ(Y, -)` given by
`φ_* ⋙ g_* ≅ g_*` and `Γ(S, g_* -) ≅ Γ(Y, -)` is compatible, through the corepresentation of
global sections by `Λ_Y`, with that lax unit (`twistEdgeIso_whiskerRight_comp_corepresentation`).
This is the degree-zero hypothesis `hσ` of
`Stacks.EtaleCohomology.etaleModuleRightDerivedPlusIsoExt_conj_edge`, under which a twisted
endomorphism of `Hⁱ(Y, -)` is the twisted action `Stacks.ExtCup.adjunctionExtMap` on
`Ext^i(Λ_Y, -)`: for the base change of the geometric Frobenius it is what identifies the
canonical Frobenius on compactly supported cohomology with a twisted action commuting with cup
products, in the purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.etaleModuleInverseImageMonoidal_ε`.
* `Stacks.EtaleCohomology.twistEdgeIso_hom_app_comp_ΓNatIsoSheafSections`.
* `Stacks.EtaleCohomology.twistEdgeIso_whiskerRight_comp_corepresentation`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ]

/-- Modules in `Type (u + 1)` have colimits of size `u + 1`. -/
local instance : HasColimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} Λ) :=
  ModuleCat.hasColimitsOfSize.{u + 1, 0, u + 1, u + 1} Λ

attribute [local instance] Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal

/-- **The lax unit of the monoidal inverse image of étale sheaves of modules is the comparison of
constant sheaves**: `Λ_Y ⟶ g⁻¹ Λ_X` is `Stacks.EtaleCohomology.etaleModuleInverseImageConstantIso`
at `ULift Λ`. -/
theorem etaleModuleInverseImageMonoidal_ε {X Y : Scheme.{u}} (g : Y ⟶ X)
    [(X.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal]
    [(Y.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal] :
    Functor.LaxMonoidal.ε (etaleModuleInverseImage.{u, 0} Λ g) =
      (etaleModuleInverseImageConstantIso.{u, 0} Λ g).inv.app
        (ModuleCat.of Λ (ULift.{u + 1} Λ)) := by
  let : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  exact Functor.sheafPullbackMonoidal_ε (smallEtaleBaseChange g) (ModuleCat.{u + 1} Λ)
    X.smallEtaleTopology Y.smallEtaleTopology hT (hT.isTerminalObj (smallEtaleBaseChange g))

section Twist

/-- Global sections of étale sheaves of modules on a scheme, through the terminal object of the
small étale site. -/
local instance (Z : Scheme.{u}) :
    HasGlobalSectionsFunctor Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  hasGlobalSectionsFunctor_of_hasTerminal _ _

variable {Y S : Scheme.{u}} (φ : Y ⟶ Y) (g : Y ⟶ S) (hφ : g = φ ≫ g)

/-- **The identification `Γ(Y, φ_* -) ≅ Γ(Y, -)` for a self-map `φ` over `S`, read on sections.**
On sections over the terminal objects `T = Y ×_S S` and `φ⁻¹ T`, the isomorphism
`Γ(Y, φ_* M) ≅ Γ(S, g_* φ_* M) ≅ Γ(S, g_* M) ≅ Γ(Y, M)` built from `φ_* ⋙ g_* ≅ g_*` is the
identity of `M(φ⁻¹ T) = (φ_* M)(T)`. -/
theorem twistEdgeIso_hom_app_comp_ΓNatIsoSheafSections (M : EtaleModules.{u, 0} Λ Y) :
    (Functor.twistEdgeIso (etaleModuleDirectImage.{u, 0} Λ φ) (etaleModuleDirectImage.{u, 0} Λ g)
        (etaleModuleGlobalSections.{u, 0} Λ S) (etaleModuleGlobalSections.{u, 0} Λ Y)
        (etaleModuleDirectImageComp.{u, 0} Λ φ g g hφ)
        (etaleModuleGlobalSectionsDirectImageIso g Λ)).hom.app M ≫
      (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        ((IsTerminal.isTerminalObj (smallEtaleBaseChange g) _ terminalIsTerminal).isTerminalObj
          (smallEtaleBaseChange φ))).hom.app M =
      (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        (IsTerminal.isTerminalObj (smallEtaleBaseChange g) _ terminalIsTerminal)).hom.app
          ((etaleModuleDirectImage.{u, 0} Λ φ).obj M) := by
  let hT : IsTerminal ((smallEtaleBaseChange g).obj (⊤_ S.Etale)) :=
    IsTerminal.isTerminalObj (smallEtaleBaseChange g) _ terminalIsTerminal
  let hT' := hT.isTerminalObj (smallEtaleBaseChange φ)
  let ΓS := Sheaf.ΓNatIsoSheafSections S.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (terminalIsTerminal (C := S.Etale))
  let ΓY := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT
  let θ := etaleModuleDirectImageComp.{u, 0} Λ φ g g hφ
  -- `Γ(S, -)` read on sections over the terminal object `S`
  have hS : ΓS.inv.app
      ((etaleModuleDirectImage.{u, 0} Λ φ ⋙ etaleModuleDirectImage.{u, 0} Λ g).obj M) ≫
      (etaleModuleGlobalSections.{u, 0} Λ S).map (θ.hom.app M) ≫
      ΓS.hom.app ((etaleModuleDirectImage.{u, 0} Λ g).obj M) =
        (θ.hom.app M).hom.app (op (⊤_ S.Etale)) := by
    rw [ΓS.hom.naturality, Iso.inv_hom_id_app_assoc]
    rfl
  -- two terminal objects of `Y_et`
  have hY : ΓY.inv.app M ≫ (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) hT').hom.app M = M.obj.map (hT.from _).op := by
    have hY0 :
        (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT').hom.app M =
        ΓY.hom.app M ≫ M.obj.map (hT.from _).op :=
      ((Sheaf.ΓNatIsoSheafSections_hom_app_general hT' M).trans
        (Sheaf.ΓRes_map M (hT.from _).op).symm).trans
        (congrArg (· ≫ M.obj.map (hT.from _).op)
          (Sheaf.ΓNatIsoSheafSections_hom_app_general hT M).symm)
    rw [hY0, Iso.inv_hom_id_app_assoc]
  have hc' : hT.from _ ≫ (smallEtaleBaseChangeComp' φ g g hφ).hom.app (⊤_ S.Etale) = 𝟙 _ :=
    hT'.hom_ext _ _
  have hc : (θ.hom.app M).hom.app (op (⊤_ S.Etale)) ≫ M.obj.map (hT.from _).op = 𝟙 _ := by
    rw [etaleModuleDirectImageComp_hom_app_hom_app]
    exact (M.obj.map_comp _ _).symm.trans
      ((congrArg (fun f => M.obj.map f.op) hc').trans (M.obj.map_id _))
  have he : ∀ N, (etaleModuleGlobalSectionsDirectImageIso g Λ).hom.app N =
      ΓS.hom.app ((etaleModuleDirectImage.{u, 0} Λ g).obj N) ≫ ΓY.inv.app N := fun _ => rfl
  have he' : ∀ N, (etaleModuleGlobalSectionsDirectImageIso g Λ).inv.app N =
      ΓY.hom.app N ≫ ΓS.inv.app ((etaleModuleDirectImage.{u, 0} Λ g).obj N) := fun _ => rfl
  let a := ΓY.hom.app ((etaleModuleDirectImage.{u, 0} Λ φ).obj M)
  let b := ΓS.inv.app
    ((etaleModuleDirectImage.{u, 0} Λ φ ⋙ etaleModuleDirectImage.{u, 0} Λ g).obj M)
  let c := (etaleModuleGlobalSections.{u, 0} Λ S).map (θ.hom.app M)
  let d := ΓS.hom.app ((etaleModuleDirectImage.{u, 0} Λ g).obj M)
  let e := ΓY.inv.app M
  let f := (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT').hom.app M
  have key : a ≫ (b ≫ c ≫ d) ≫ (e ≫ f) = a :=
    ((congrArg (fun z => a ≫ z ≫ (e ≫ f)) hS).trans
      (congrArg (fun z => a ≫ (θ.hom.app M).hom.app (op (⊤_ S.Etale)) ≫ z) hY)).trans
      ((congrArg (a ≫ ·) hc).trans (Category.comp_id a))
  have assoc : (a ≫ b) ≫ c ≫ (d ≫ e) ≫ f = a ≫ (b ≫ c ≫ d) ≫ (e ≫ f) :=
    (Category.assoc a b _).trans (congrArg (a ≫ ·)
      ((congrArg (fun z => b ≫ c ≫ z) (Category.assoc d e f)).trans
        ((congrArg (b ≫ ·) (Category.assoc c d (e ≫ f))).symm.trans
          (Category.assoc b (c ≫ d) (e ≫ f)).symm)))
  have assoc' : ((a ≫ b) ≫ c ≫ (d ≫ e)) ≫ f = (a ≫ b) ≫ c ≫ (d ≫ e) ≫ f :=
    (Category.assoc (a ≫ b) (c ≫ (d ≫ e)) f).trans
      (congrArg ((a ≫ b) ≫ ·) (Category.assoc c (d ≫ e) f))
  have hT0 : (Functor.twistEdgeIso (etaleModuleDirectImage.{u, 0} Λ φ)
      (etaleModuleDirectImage.{u, 0} Λ g) (etaleModuleGlobalSections.{u, 0} Λ S)
      (etaleModuleGlobalSections.{u, 0} Λ Y) θ
      (etaleModuleGlobalSectionsDirectImageIso g Λ)).hom.app M = (a ≫ b) ≫ c ≫ (d ≫ e) := by
    rw [Functor.twistEdgeIso_hom_app, he, he']
    rfl
  exact (congrArg (· ≫ f) hT0).trans (assoc'.trans (assoc.trans key))

attribute [local instance] HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **The degree-zero compatibility `hσ` for a self-map over a base.** Let `φ : Y ⟶ Y` be a
morphism over `g : Y ⟶ S` whose direct image is right exact. The identification
`Γ(Y, φ_* -) ≅ Γ(Y, -)` built from `φ_* ⋙ g_* ≅ g_*` and `Γ(S, g_* -) ≅ Γ(Y, -)`, read through the
corepresentation of global sections by `Λ_Y`, is precomposition with the lax unit
`Λ_Y ⟶ φ⁻¹ Λ_Y` after the `φ⁻¹ ⊣ φ_*` transpose. This is the hypothesis `hσ` of
`Stacks.EtaleCohomology.etaleModuleRightDerivedPlusIsoExt_conj_edge`. -/
theorem twistEdgeIso_whiskerRight_comp_corepresentation
    [(Y.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal]
    [PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} Λ φ)] :
    Functor.whiskerRight (Functor.twistEdgeIso (etaleModuleDirectImage.{u, 0} Λ φ)
          (etaleModuleDirectImage.{u, 0} Λ g) (etaleModuleGlobalSections.{u, 0} Λ S)
          (etaleModuleGlobalSections.{u, 0} Λ Y) (etaleModuleDirectImageComp.{u, 0} Λ φ g g hφ)
          (etaleModuleGlobalSectionsDirectImageIso g Λ)).hom
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≫
        (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation Λ
          Y.smallEtaleTopology).hom =
      (ModuleSheafCohomology.compCorepresentation (etaleModuleDirectImage.{u, 0} Λ φ)
          (etaleModuleGlobalSections.{u, 0} Λ Y ⋙
            forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
          (𝟙_ (EtaleModules.{u, 0} Λ Y))
          (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation Λ
            Y.smallEtaleTopology)
          ((etaleModuleInverseImage.{u, 0} Λ φ).obj (𝟙_ _))
          (Stacks.ExtCup.adjCorepresentation _ _ (etaleModuleInverseImageAdj.{u, 0} Λ φ))).hom ≫
        preadditiveCoyoneda.map
          (Functor.LaxMonoidal.ε (etaleModuleInverseImage.{u, 0} Λ φ)).op := by
  let hT : IsTerminal ((smallEtaleBaseChange g).obj (⊤_ S.Etale)) :=
    IsTerminal.isTerminalObj (smallEtaleBaseChange g) _ terminalIsTerminal
  let hT' := hT.isTerminalObj (smallEtaleBaseChange φ)
  have hε : Functor.LaxMonoidal.ε (etaleModuleInverseImage.{u, 0} Λ φ) =
      (((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).comp
        (etaleModuleInverseImageAdj.{u, 0} Λ φ)).leftAdjointUniq
          (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT')).inv.app
        (𝟙_ (ModuleCat.{u + 1} Λ)) :=
    Functor.sheafPullbackMonoidal_ε (smallEtaleBaseChange φ) (ModuleCat.{u + 1} Λ)
      Y.smallEtaleTopology Y.smallEtaleTopology hT hT'
  ext M s
  have hL : ((Functor.whiskerRight (Functor.twistEdgeIso (etaleModuleDirectImage.{u, 0} Λ φ)
          (etaleModuleDirectImage.{u, 0} Λ g) (etaleModuleGlobalSections.{u, 0} Λ S)
          (etaleModuleGlobalSections.{u, 0} Λ Y) (etaleModuleDirectImageComp.{u, 0} Λ φ g g hφ)
          (etaleModuleGlobalSectionsDirectImageIso g Λ)).hom
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≫
        (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation Λ
          Y.smallEtaleTopology).hom).app M).hom s =
      ((Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation Λ
          Y.smallEtaleTopology).hom.app M).hom ((Functor.twistEdgeIso
          (etaleModuleDirectImage.{u, 0} Λ φ)
          (etaleModuleDirectImage.{u, 0} Λ g) (etaleModuleGlobalSections.{u, 0} Λ S)
          (etaleModuleGlobalSections.{u, 0} Λ Y) (etaleModuleDirectImageComp.{u, 0} Λ φ g g hφ)
          (etaleModuleGlobalSectionsDirectImageIso g Λ)).hom.app M s) := rfl
  have hR : (((ModuleSheafCohomology.compCorepresentation (etaleModuleDirectImage.{u, 0} Λ φ)
          (etaleModuleGlobalSections.{u, 0} Λ Y ⋙
            forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
          (𝟙_ (EtaleModules.{u, 0} Λ Y))
          (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation Λ
            Y.smallEtaleTopology)
          ((etaleModuleInverseImage.{u, 0} Λ φ).obj (𝟙_ _))
          (Stacks.ExtCup.adjCorepresentation _ _ (etaleModuleInverseImageAdj.{u, 0} Λ φ))).hom ≫
        preadditiveCoyoneda.map
          (Functor.LaxMonoidal.ε (etaleModuleInverseImage.{u, 0} Λ φ)).op).app M).hom s =
      Functor.LaxMonoidal.ε (etaleModuleInverseImage.{u, 0} Λ φ) ≫
        ((etaleModuleInverseImageAdj.{u, 0} Λ φ).homEquiv _ _).symm
          (((Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation Λ
            Y.smallEtaleTopology).hom.app ((etaleModuleDirectImage.{u, 0} Λ φ).obj M)).hom s) :=
    rfl
  refine hL.trans (Eq.trans ?_ hR.symm)
  have h2 := Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation_hom_app_twist
    Λ Y.smallEtaleTopology (smallEtaleBaseChange φ) (etaleModuleInverseImageAdj.{u, 0} Λ φ)
    (Functor.twistEdgeIso (etaleModuleDirectImage.{u, 0} Λ φ)
      (etaleModuleDirectImage.{u, 0} Λ g) (etaleModuleGlobalSections.{u, 0} Λ S)
      (etaleModuleGlobalSections.{u, 0} Λ Y) (etaleModuleDirectImageComp.{u, 0} Λ φ g g hφ)
      (etaleModuleGlobalSectionsDirectImageIso g Λ)).hom hT hT'
    (twistEdgeIso_hom_app_comp_ΓNatIsoSheafSections Λ φ g hφ) M s
  exact h2.trans (congrArg (· ≫ _) hε.symm)

end Twist

end Stacks.EtaleCohomology

end
