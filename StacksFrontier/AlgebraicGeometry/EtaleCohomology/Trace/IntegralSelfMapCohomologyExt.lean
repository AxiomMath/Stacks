module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralSelfMapCohomologyEndo
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralLerayEdge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExtTwist
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactUnitSingle

/-!
# Pullback along an integral self-map, read on `Ext`

For an integral morphism `g : A ⟶ B` the identification `Hⁱ(B, g_* H) ≅ Hⁱ(A, H)`
(`Stacks.EtaleCohomology.integralDirectImageCohomologyIso`) is the degreewise comparison
`Stacks.DerivedIndexing.rightDerivedPlusEdge g_* Γ(B, -)` followed by the map induced by
`Γ(B, g_* -) ≅ Γ(A, -)` (`integralDirectImageCohomologyIso_hom_eq_edge`). For an integral self-map
`φ : Y ⟶ Y` and a commutative coefficient ring `Λ` this puts the pullback action
`Stacks.EtaleCohomology.integralSelfMapCohomologyEndo` in the shape of
`Stacks.EtaleCohomology.etaleModuleRightDerivedPlusIsoExt_conj_edge`, whose degree-zero hypothesis
for `Γ(Y, φ_* -) ≅ Γ(Y, -)` is `directImageCompGlobalSections_whiskerRight_comp_corepresentation`.
So on `Ext^i(Λ_Y, N)` the action is `b ↦ θ(b ∘ α)`, `θ` the map of the adjunction
`φ^{-1} ⊣ φ_*`, and on `Hⁱ(Y, U N)` it is the restriction map along `φ` followed by the adjoint of
`α` (`extForgetSheafH_integralSelfMapCohomologyEndo`). This is the analogue for
`integralSelfMapCohomologyEndo` of
`Stacks.EtaleCohomology.extForgetSheafH_selfMapCohomologyEndo`, and is proved along the same lines.

## Main results

* `Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso_inv_eq_ofPreservesInjectives`.
* `Stacks.EtaleCohomology.rightDerivedPlusEdge_app_comp_rightDerivedPlusNatTrans_app`.
* `Stacks.EtaleCohomology.integralDirectImageCohomologyIso_hom_eq_edge`.
* `Stacks.EtaleCohomology.directImageCompGlobalSections_whiskerRight_comp_corepresentation`.
* `Stacks.EtaleCohomology.etaleModuleRightDerivedPlusIsoExt_integralSelfMapCohomologyEndo`.
* `Stacks.EtaleCohomology.extForgetSheafH_integralSelfMapCohomologyEndo`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w w' w'' v v' v'' u u' u'' r

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.EtaleCohomology

section Generic

variable {A : Type u} {B : Type u'} {C : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] [HasDerivedCategory.{w'} C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C) [F.Additive] [G.Additive] [H.Additive]
  [F.PreservesInjectiveObjects] (e : F ⋙ G ≅ H)

/-- **The two composition comparisons for a first factor preserving injectives agree**: the
inverse of `RH ≅ RF ⋙ RG` (`Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso`) is the
comparison `RF ⋙ RG ≅ RH` of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives`. Both are
characterized by the derived-functor units. -/
theorem rightDerivedFunctorPlusCompIsoOfIso_inv_eq_ofPreservesInjectives :
    (rightDerivedFunctorPlusCompIsoOfIso F G H e).inv =
      (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G H e).hom := by
  refine Iso.inv_ext ?_
  refine Functor.rightDerived_ext H.rightDerivedFunctorPlus H.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso A) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app]
  rw [← Category.assoc, unit_comp_rightDerivedFunctorPlusCompIsoOfIso_hom, Category.assoc,
    Category.assoc, Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_fac,
    ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end Generic

section Edge

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D] [HasDerivedCategory.{w''} E]
  [EnoughInjectives C] [EnoughInjectives D]
  (L : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [L.Additive] [G.Additive] [H.Additive]
  [L.PreservesInjectiveObjects] (c : L ⋙ G ≅ H)

/-- **The degreewise comparison of a composite, transported along `c : L ⋙ G ≅ H`**: it is the
degree-`q` cohomology of the canonical map `(Lℱ)[0] ⟶ RL(ℱ[0])` followed by the comparison
`RL ⋙ RG ≅ RH` of `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives`. -/
theorem rightDerivedPlusEdge_app_comp_rightDerivedPlusNatTrans_app (q : ℤ) (X : C) :
    (Stacks.DerivedIndexing.rightDerivedPlusEdge L G q).app X ≫
        (Stacks.DerivedIndexing.rightDerivedPlusNatTrans c.hom q).app X =
      (DerivedCategory.Plus.homologyFunctor E q).map
        (G.rightDerivedFunctorPlus.map
            ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle L).app X) ≫
          (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives L G H c).hom.app
            ((DerivedCategory.Plus.singleFunctor C 0).obj X)) := by
  have e1 : (Stacks.DerivedIndexing.rightDerivedPlusCompIso L G).inv.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
        (Functor.rightDerivedFunctorPlusNatIso c).hom.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj X) =
      (Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives L G H c).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) := by
    rw [Functor.rightDerivedPlusCompIso_eq,
      Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom]
    exact (NatTrans.comp_app _ _ _).symm
  have key : (Stacks.DerivedIndexing.rightDerivedPlusEdge L G q).app X ≫
        (Stacks.DerivedIndexing.rightDerivedPlusNatTrans c.hom q).app X =
      (DerivedCategory.Plus.homologyFunctor E q).map
        (G.rightDerivedFunctorPlus.map
            ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle L).app X) ≫
          (Stacks.DerivedIndexing.rightDerivedPlusCompIso L G).inv.app
              ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
            (Functor.rightDerivedFunctorPlusNatIso c).hom.app
              ((DerivedCategory.Plus.singleFunctor C 0).obj X)) :=
    (congrArg (fun z => z ≫ (Stacks.DerivedIndexing.rightDerivedPlusNatTrans c.hom q).app X)
        (Stacks.DerivedIndexing.rightDerivedPlusEdge_app L G q X)).trans
      (Stacks.DerivedIndexing.assocMap (DerivedCategory.Plus.homologyFunctor E q) _ _ _)
  rw [key, e1]

end Edge

section Integral

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ]

/-- **`H^i(B, g_* H) ≅ H^i(A, H)` is the degreewise comparison of the composite**: for an
integral `g : A ⟶ B` it is `Stacks.DerivedIndexing.rightDerivedPlusEdge g_* Γ(B, -)` followed by
the map induced by `Γ(B, g_* -) ≅ Γ(A, -)`. -/
theorem integralDirectImageCohomologyIso_hom_eq_edge {A B : Scheme.{u}} (g : A ⟶ B)
    [IsIntegralHom g] (H : EtaleModules.{u, r} Λ A) (i : ℤ) :
    (integralDirectImageCohomologyIso Λ g H i).hom =
      (Stacks.DerivedIndexing.rightDerivedPlusEdge (etaleModuleDirectImage.{u, r} Λ g)
          (etaleModuleGlobalSections.{u, r} Λ B) i).app H ≫
        (Stacks.DerivedIndexing.rightDerivedPlusNatTrans
          (etaleModuleDirectImageCompGlobalSections.{u, r} Λ g).hom i).app H := by
  have := (etaleModuleDirectImage_exact_of_isIntegralHom Λ g).1
  have := (etaleModuleDirectImage_exact_of_isIntegralHom Λ g).2
  rw [rightDerivedPlusEdge_app_comp_rightDerivedPlusNatTrans_app,
    integralDirectImageCohomologyIso_hom_eq,
    Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_hom]
  exact congrArg (fun t => (DerivedCategory.Plus.homologyFunctor _ i).map
    ((etaleModuleDerivedGlobalSections.{u, r} Λ B).map
      ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle (etaleModuleDirectImage.{u, r} Λ g)).app
        H) ≫ NatTrans.app t ((DerivedCategory.Plus.singleFunctor _ 0).obj H)))
    (rightDerivedFunctorPlusCompIsoOfIso_inv_eq_ofPreservesInjectives
      (etaleModuleDirectImage.{u, r} Λ g) (etaleModuleGlobalSections.{u, r} Λ B)
      (etaleModuleGlobalSections.{u, r} Λ A) (etaleModuleDirectImageCompGlobalSections.{u, r} Λ g))

end Integral

section Corepresentation

variable (Λ : Type) [CommRing Λ]

local instance : HasColimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} Λ) :=
  ModuleCat.hasColimitsOfSize.{u + 1, 0, u + 1, u + 1} Λ

local instance (Z : Scheme.{u}) :
    HasGlobalSectionsFunctor Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  hasGlobalSectionsFunctor_of_hasTerminal _ _

attribute [local instance] Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable {Y : Scheme.{u}} (φ : Y ⟶ Y)

/-- **`Γ(Y, φ_* -) ≅ Γ(Y, -)` read on sections**: on sections over the terminal objects `T` and
`φ⁻¹ T` of `Y_étale`, it is the identity of `M(φ⁻¹ T) = (φ_* M)(T)`. -/
theorem directImageCompGlobalSections_hom_app_comp_ΓNatIsoSheafSections
    (M : EtaleModules.{u, 0} Λ Y) :
    (etaleModuleDirectImageCompGlobalSections.{u, 0} Λ φ).hom.app M ≫
        (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
          (IsTerminal.isTerminalObj (smallEtaleBaseChange φ) _ terminalIsTerminal)).hom.app M =
      (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        (terminalIsTerminal (C := Y.Etale))).hom.app
          ((etaleModuleDirectImage.{u, 0} Λ φ).obj M) := by
  rw [Sheaf.ΓNatIsoSheafSections_hom_app_general, Sheaf.ΓNatIsoSheafSections_hom_app_general,
    ← etaleModuleDirectImageCompGlobalSections_inv_app_comp_ΓRes Λ φ M (op (⊤_ Y.Etale))]
  exact Iso.hom_inv_id_app_assoc _ _ _

/-- **The degree-zero compatibility `hσ` for `Γ(Y, φ_* -) ≅ Γ(Y, -)`**: read through the
corepresentation of global sections by `Λ_Y`, the identification
`Stacks.EtaleCohomology.etaleModuleDirectImageCompGlobalSections` for `φ` is precomposition with
the lax unit `Λ_Y ⟶ φ⁻¹ Λ_Y` after the `φ⁻¹ ⊣ φ_*` transpose. This is the hypothesis `hσ` of
`Stacks.EtaleCohomology.etaleModuleRightDerivedPlusIsoExt_conj_edge`. -/
theorem directImageCompGlobalSections_whiskerRight_comp_corepresentation
    [(Y.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal] :
    Functor.whiskerRight (etaleModuleDirectImageCompGlobalSections.{u, 0} Λ φ).hom
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
  let hT : IsTerminal (⊤_ Y.Etale) := terminalIsTerminal
  let hT' : IsTerminal ((smallEtaleBaseChange φ).obj (⊤_ Y.Etale)) :=
    IsTerminal.isTerminalObj (smallEtaleBaseChange φ) _ terminalIsTerminal
  have hε : Functor.LaxMonoidal.ε (etaleModuleInverseImage.{u, 0} Λ φ) =
      (((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).comp
        (etaleModuleInverseImageAdj.{u, 0} Λ φ)).leftAdjointUniq
          (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT')).inv.app
        (𝟙_ (ModuleCat.{u + 1} Λ)) :=
    Functor.sheafPullbackMonoidal_ε (smallEtaleBaseChange φ) (ModuleCat.{u + 1} Λ)
      Y.smallEtaleTopology Y.smallEtaleTopology hT hT'
  ext M s
  have hL : ((Functor.whiskerRight (etaleModuleDirectImageCompGlobalSections.{u, 0} Λ φ).hom
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≫
        (Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation Λ
          Y.smallEtaleTopology).hom).app M).hom s =
      ((Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation Λ
          Y.smallEtaleTopology).hom.app M).hom
        ((etaleModuleDirectImageCompGlobalSections.{u, 0} Λ φ).hom.app M s) := rfl
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
    (etaleModuleDirectImageCompGlobalSections.{u, 0} Λ φ).hom hT hT'
    (directImageCompGlobalSections_hom_app_comp_ΓNatIsoSheafSections Λ φ) M s
  exact h2.trans (congrArg (· ≫ _) hε.symm)

variable [IsIntegralHom φ] [(Y.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal]

/-- **The pullback action of an integral self-map on `Ext^i(Λ_Y, N)` is `b ↦ θ(b ∘ α)`**, for
`θ` the map `Ext^i(Λ_Y, φ_* N) ⟶ Ext^i(Λ_Y, N)`, `b ↦ ε_N ∘ φ^{-1}(b)` of the adjunction
`φ^{-1} ⊣ φ_*` (`Stacks.ExtCup.adjunctionExtMap`) and `α : N ⟶ φ_* N` the linearization. -/
theorem etaleModuleRightDerivedPlusIsoExt_integralSelfMapCohomologyEndo
    (N : EtaleModules.{u, 0} Λ Y) (α : N ⟶ (etaleModuleDirectImage.{u, 0} Λ φ).obj N) (i : ℕ)
    (b : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology)
      N i) :
    ((etaleModuleRightDerivedPlusIsoExt Λ Y N i).hom).hom
        (((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          (integralSelfMapCohomologyEndo Λ φ N α i)).hom
          (((etaleModuleRightDerivedPlusIsoExt Λ Y N i).inv).hom b)) =
      Stacks.ExtCup.adjunctionExtMap (etaleModuleInverseImage.{u, 0} Λ φ)
        (etaleModuleDirectImage.{u, 0} Λ φ) (etaleModuleInverseImageAdj.{u, 0} Λ φ) N
        (b.comp (Ext.mk₀ α) (add_zero i)) := by
  have := (etaleModuleDirectImage_exact_of_isIntegralHom Λ φ).1
  have := (etaleModuleDirectImage_exact_of_isIntegralHom Λ φ).2
  rw [integralSelfMapCohomologyEndo, integralDirectImageCohomologyIso_hom_eq_edge]
  exact etaleModuleRightDerivedPlusIsoExt_conj_edge Λ Y (etaleModuleInverseImage.{u, 0} Λ φ)
    (etaleModuleDirectImage.{u, 0} Λ φ) (etaleModuleInverseImageAdj.{u, 0} Λ φ)
    (etaleModuleDirectImageCompGlobalSections.{u, 0} Λ φ).hom
    (directImageCompGlobalSections_whiskerRight_comp_corepresentation Λ φ) N α i b

variable [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The pullback action of an integral self-map on `Hⁱ(Y, U N)` is the restriction map along
`φ`**: under `Hⁱ(Y, N) ≅ Ext^i(Λ_Y, N) ⟶ Hⁱ(Y, U N)`, the action
`Stacks.EtaleCohomology.integralSelfMapCohomologyEndo` of `φ` with linearization `α` is
`etaleCohomologyRestrictionMap φ` followed by `φ^{-1}(U N) ≅ U(φ^{-1} N) ⟶ U N`, the second map
being the adjoint `φ^{-1}(α) ≫ ε` of `α`. -/
theorem extForgetSheafH_integralSelfMapCohomologyEndo
    (N : EtaleModules.{u, 0} Λ Y) (α : N ⟶ (etaleModuleDirectImage.{u, 0} Λ φ).obj N) (i : ℕ)
    (b : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology)
      N i) :
    extForgetSheafH Λ Y N i (((etaleModuleRightDerivedPlusIsoExt Λ Y N i).hom).hom
        (((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          (integralSelfMapCohomologyEndo Λ φ N α i)).hom
          (((etaleModuleRightDerivedPlusIsoExt Λ Y N i).inv).hom b))) =
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} φ ((etaleModuleUnderlyingAbelian Y Λ).obj N) i
          (extForgetSheafH Λ Y N i b)).comp
        (Ext.mk₀ ((etaleModuleUnderlyingAbelianInverseImageIso Λ φ).hom.app N ≫
          (etaleModuleUnderlyingAbelian Y Λ).map
            ((etaleModuleInverseImage.{u, 0} Λ φ).map α ≫
              (etaleModuleInverseImageAdj.{u, 0} Λ φ).counit.app N))) (add_zero i) := by
  have := (etaleModuleDirectImage_exact_of_isIntegralHom Λ φ).2
  rw [etaleModuleRightDerivedPlusIsoExt_integralSelfMapCohomologyEndo Λ φ N α i b,
    adjunctionExtMap_eq_etaleModuleExtRestriction Λ φ, etaleModuleExtRestriction_comp_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, extForgetSheafH_comp_mk₀,
    extForgetSheafH_etaleModuleExtRestriction, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

end Corepresentation

end Stacks.EtaleCohomology

end
