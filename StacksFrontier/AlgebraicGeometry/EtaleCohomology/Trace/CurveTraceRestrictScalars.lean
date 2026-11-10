module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveExtensionByZeroSheafTrace
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantModuleTraceGaloisTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteSectionPullbackTransfer

/-!
# The trace of a curve does not depend on the coefficient ring

Let `C` be a smooth proper curve over an algebraically closed field `K`, `j : U ⟶ C` an open
immersion with finite complement, and `ψ : R →+* Λ` a morphism of finite rings with
`#R = #Λ = n` invertible in `K` (in the Trace Formula chapter, `R = ℤ/n` and `Λ` an arbitrary,
possibly noncommutative, finite ring of order `n`). For a sheaf `G` of `Λ`-modules on `U`
constant on its global sections, the trace `H²(C, j_! G) ≅ Γ(U, G)` of
`Stacks.EtaleCohomology.curveExtensionByZeroSheafTrace` computed over `Λ` is the trace computed
over `R` after restricting scalars, and more generally the trace is natural for `R`-linear maps
`res_ψ G ⟶ G'` into a constant sheaf `G'` of `R`-modules.

The comparison of cohomology is read on the underlying abelian sheaf: `res_ψ` does not change the
underlying sheaf of abelian groups, and the cohomology over any ring is the cohomology of the
underlying abelian sheaf (`Stacks.EtaleCohomology.etaleModuleCohomologyAddEquivSheafH`).

## Main definitions

* `Stacks.EtaleCohomology.constantSheafRestrictScalarsIso` — `res_ψ (E_Y) ≅ (res_ψ E)_Y`.
* `Stacks.EtaleCohomology.etaleModuleCohomologyRestrictScalars` — `Hⁱ(Y, N) ≃+ Hⁱ(Y, res_ψ N)`
  through the underlying abelian sheaf.

## Main results

* `Stacks.EtaleCohomology.underlyingConstantSheafIso_restrictScalars` — the comparison with the
  constant abelian sheaf is compatible with `res_ψ`.
* `Stacks.EtaleCohomology.restrictScalars_map_constantSheafΓAdj_counit` — `res_ψ` of the counit
  `Γ(G)_Y ⟶ G` is the counit for `res_ψ G`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.EtaleCohomology.etaleModulesEnoughInjectivesZeroTraceTwist
  Stacks.EtaleCohomology.moduleCatHasColimitsOfSizeSmallEtale
  Stacks.EtaleCohomology.hasGlobalSectionsFunctorSmallEtaleModuleCat

namespace Stacks.ConstantSheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {D B : Type*} [Category* D]
  [Category* B] (U : D ⥤ B) [HasWeakSheafify J D] [HasWeakSheafify J B]
  [J.PreservesSheafification U] [J.HasSheafCompose U]

/-- **`constantCommuteCompose` carries constant sections to constant sections**: the comparison
`U(E_C) ≅ (U E)_C` sends the image under `U` of the constant section of `E` over `V` to the
constant section of `U E` over `V`. -/
theorem map_constantSheafSection_comp_constantCommuteCompose (E : D) (V : C) :
    U.map (constantSheafSection J D E V) ≫
        ((constantCommuteCompose J U).hom.app E).hom.app (op V) =
      constantSheafSection J B (U.obj E) V := by
  rw [constantCommuteCompose_hom_app_hom, NatTrans.comp_app]
  have h1 := congrArg (fun t => t.app (op V))
    (sheafComposeIso_inv_fac J U ((Functor.const Cᵒᵖ).obj E))
  have h2 := congrArg (fun t => t.app (op V))
    (toSheafify_naturality J (Functor.constComp Cᵒᵖ E U).hom)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at h1 h2
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans
    (h2.symm.trans (Category.id_comp _)))

end Stacks.ConstantSheaf

namespace Stacks.EtaleCohomology

section Constant

variable {R Λ : Type} [Ring R] [Ring Λ] (ψ : R →+* Λ) (Y : Scheme.{u})

/-- **`res_ψ (E_Y) ≅ (res_ψ E)_Y`**: restriction of scalars of the constant sheaf of
`Λ`-modules on `E` is the constant sheaf of `R`-modules on `res_ψ E`
(`CategoryTheory.constantCommuteCompose`). -/
abbrev constantSheafRestrictScalarsIso (E : ModuleCat.{u + 1} Λ) :
    (etaleModuleRestrictScalars ψ Y).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) ≅
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
        ((ModuleCat.restrictScalars.{u + 1} ψ).obj E) :=
  (constantCommuteCompose Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ψ)).app E

/-- `res_ψ (E_Y) ≅ (res_ψ E)_Y` carries constant sections to constant sections. -/
theorem constantSheafSection_comp_constantSheafRestrictScalarsIso (E : ModuleCat.{u + 1} Λ)
    (V : Y.Etale) :
    (ModuleCat.restrictScalars.{u + 1} ψ).map (constantSheafSection Λ E V) ≫
        (constantSheafRestrictScalarsIso ψ Y E).hom.hom.app (op V) =
      constantSheafSection R ((ModuleCat.restrictScalars.{u + 1} ψ).obj E) V :=
  Stacks.ConstantSheaf.map_constantSheafSection_comp_constantCommuteCompose
    Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ψ) E V

/-- The inverse of `res_ψ (E_Y) ≅ (res_ψ E)_Y` carries constant sections to constant sections. -/
theorem constantSheafSection_comp_constantSheafRestrictScalarsIso_inv (E : ModuleCat.{u + 1} Λ)
    (V : Y.Etale) :
    constantSheafSection R ((ModuleCat.restrictScalars.{u + 1} ψ).obj E) V ≫
        (constantSheafRestrictScalarsIso ψ Y E).inv.hom.app (op V) =
      (ModuleCat.restrictScalars.{u + 1} ψ).map (constantSheafSection Λ E V) := by
  have h := constantSheafSection_comp_constantSheafRestrictScalarsIso ψ Y E V
  have hi : (constantSheafRestrictScalarsIso ψ Y E).hom.hom.app (op V) ≫
      (constantSheafRestrictScalarsIso ψ Y E).inv.hom.app (op V) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id]
    rfl
  exact (congrArg (· ≫ (constantSheafRestrictScalarsIso ψ Y E).inv.hom.app (op V)) h).symm.trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hi).trans (Category.comp_id _)))

/-- **`res_ψ` does not change the underlying abelian sheaf**: the abelian sheaf underlying
`res_ψ N` is the abelian sheaf underlying `N`, on the nose. -/
def underlyingAbelianRestrictScalarsIso (N : EtaleModules.{u, 0} Λ Y) :
    (etaleModuleUnderlyingAbelian Y ℤ).obj ((etaleModuleRestrictScalars (Int.castRingHom R) Y).obj
        ((etaleModuleRestrictScalars ψ Y).obj N)) ≅
      (etaleModuleUnderlyingAbelian Y ℤ).obj
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).obj N) :=
  Iso.refl _

/-- `underlyingAbelianRestrictScalarsIso` is natural in the sheaf. -/
@[reassoc]
theorem underlyingAbelianRestrictScalarsIso_hom_naturality {N N' : EtaleModules.{u, 0} Λ Y}
    (g : N ⟶ N') :
    (etaleModuleUnderlyingAbelian Y ℤ).map ((etaleModuleRestrictScalars (Int.castRingHom R) Y).map
        ((etaleModuleRestrictScalars ψ Y).map g)) ≫
        (underlyingAbelianRestrictScalarsIso ψ Y N').hom =
      (underlyingAbelianRestrictScalarsIso ψ Y N).hom ≫
        (etaleModuleUnderlyingAbelian Y ℤ).map
          ((etaleModuleRestrictScalars (Int.castRingHom Λ) Y).map g) :=
  rfl

/-- The constant section of `E_Y` over `V`, read in the underlying abelian sheaf. -/
abbrev underlyingConstantSheafSection {S : Type} [Ring S] (E : ModuleCat.{u + 1} S)
    (V : Y.Etale) :
    AddCommGrpCat.of E ⟶ ((etaleModuleUnderlyingAbelian Y ℤ).obj
      ((etaleModuleRestrictScalars (Int.castRingHom S) Y).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S)).obj E))).obj.obj (op V) :=
  (forget₂ (ModuleCat.{u + 1} S) AddCommGrpCat.{u + 1}).map (constantSheafSection S E V)

omit [Ring R] [Ring Λ] in
/-- The inverse of the comparison `U(E_Y) ≅ E₀,Y` carries constant sections to constant
sections. -/
theorem constantSheafSection_comp_underlyingConstantSheafIso_inv {S : Type} [Ring S]
    (E : ModuleCat.{u + 1} S) {E₀ : Type} [AddCommGroup E₀] (e : E ≃+ E₀) (V : Y.Etale) :
    Stacks.ConstantSheaf.constantSheafSection Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} E₀)) V ≫
      (underlyingConstantSheafIso Y E e).inv.hom.app (op V) =
      (AddEquiv.toAddCommGrpIso (X := AddCommGrpCat.of E) (Y := AddCommGrpCat.of (ULift.{u + 1} E₀))
        (e.trans (AddEquiv.ulift.{0, u + 1} (α := E₀)).symm)).inv ≫
        underlyingConstantSheafSection Y E V := by
  have h : underlyingConstantSheafSection Y E V ≫
      (underlyingConstantSheafIso Y E e).hom.hom.app (op V) =
      (AddEquiv.toAddCommGrpIso (X := AddCommGrpCat.of E) (Y := AddCommGrpCat.of (ULift.{u + 1} E₀))
        (e.trans (AddEquiv.ulift.{0, u + 1} (α := E₀)).symm)).hom ≫
        Stacks.ConstantSheaf.constantSheafSection Y.smallEtaleTopology AddCommGrpCat.{u + 1}
          (AddCommGrpCat.of (ULift.{u + 1} E₀)) V :=
    forget₂_constantSheafSection_comp_underlyingConstantSheafIso Y E e V
  rw [← Iso.inv_comp_eq] at h
  rw [← h, Category.assoc, Category.assoc, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, Category.comp_id]

/-- `res_ψ (E_Y) ≅ (res_ψ E)_Y`, read in the underlying abelian sheaves, carries constant
sections to constant sections. -/
theorem underlyingConstantSheafSection_comp_constantSheafRestrictScalarsIso
    (E : ModuleCat.{u + 1} Λ) (V : Y.Etale) :
    underlyingConstantSheafSection Y E V ≫
        (underlyingAbelianRestrictScalarsIso ψ Y
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)).inv.hom.app (op V) ≫
        ((etaleModuleUnderlyingAbelian Y ℤ).map
          ((etaleModuleRestrictScalars (Int.castRingHom R) Y).map
            (constantSheafRestrictScalarsIso ψ Y E).hom)).hom.app (op V) =
      underlyingConstantSheafSection Y ((ModuleCat.restrictScalars.{u + 1} ψ).obj E) V :=
  (Functor.map_comp (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) _ _).symm.trans
    (congrArg (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
      (constantSheafSection_comp_constantSheafRestrictScalarsIso ψ Y E V))

/-- **The comparison with the constant abelian sheaf is compatible with `res_ψ`.** Through the
abelian sheaf underlying `res_ψ (E_Y)`, which is the abelian sheaf underlying `E_Y`,
`res_ψ (E_Y) ≅ (res_ψ E)_Y` followed by the comparison `U((res_ψ E)_Y) ≅ E₀,Y` is the comparison
`U(E_Y) ≅ E₀,Y`. -/
theorem underlyingConstantSheafIso_restrictScalars (E : ModuleCat.{u + 1} Λ) {E₀ : Type}
    [AddCommGroup E₀] (e : E ≃+ E₀) :
    (underlyingAbelianRestrictScalarsIso ψ Y
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)).inv ≫
      (etaleModuleUnderlyingAbelian Y ℤ).map ((etaleModuleRestrictScalars (Int.castRingHom R) Y).map
        (constantSheafRestrictScalarsIso ψ Y E).hom) ≫
      (underlyingConstantSheafIso Y ((ModuleCat.restrictScalars.{u + 1} ψ).obj E) e).hom =
      (underlyingConstantSheafIso Y E e).hom := by
  refine (cancel_epi (underlyingConstantSheafIso Y E e).inv).mp ?_
  rw [Iso.inv_hom_id]
  refine ((constantSheafAdj _ _ (etaleSiteTerminalIsTerminal Y)).homEquiv _ _).injective ?_
  rw [Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply_eq,
    Stacks.ConstantSheaf.constantSheafAdj_homEquiv_apply_eq,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app, Category.comp_id,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, NatTrans.comp_app,
    NatTrans.comp_app,
    reassoc_of% (constantSheafSection_comp_underlyingConstantSheafIso_inv Y E e
      (etaleSiteTerminal Y)),
    reassoc_of% (underlyingConstantSheafSection_comp_constantSheafRestrictScalarsIso ψ Y E
      (etaleSiteTerminal Y))]
  have hR := forget₂_constantSheafSection_comp_underlyingConstantSheafIso Y
    ((ModuleCat.restrictScalars.{u + 1} ψ).obj E) e (etaleSiteTerminal Y)
  exact (congrArg (_ ≫ ·) hR).trans (Iso.inv_hom_id_assoc _ _)

/-- The comparison `res_ψ Γ(Y, G) ≅ Γ(Y, res_ψ G)` followed by the identification of global
sections with the sections over the final object is `res_ψ` of that identification. -/
theorem etaleModuleGlobalSectionsRestrictScalars_hom_app_comp_ΓNatIso
    (G : EtaleModules.{u, 0} Λ Y) :
    ((etaleModuleGlobalSectionsRestrictScalars ψ Y).app G).hom ≫
        (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} R)
          terminalIsTerminal).hom.app ((etaleModuleRestrictScalars ψ Y).obj G) =
      (ModuleCat.restrictScalars.{u + 1} ψ).map
        ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
          terminalIsTerminal).hom.app G) := by
  simp only [etaleModuleGlobalSectionsRestrictScalars, Iso.app_hom, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_app]
  rfl

/-- **`res_ψ` of the counit `Γ(Y, G)_Y ⟶ G` is the counit for `res_ψ G`**, through
`res_ψ (E_Y) ≅ (res_ψ E)_Y` and `res_ψ Γ(Y, G) ≅ Γ(Y, res_ψ G)`. -/
theorem restrictScalars_map_constantSheafΓAdj_counit (G : EtaleModules.{u, 0} Λ Y) :
    (etaleModuleRestrictScalars ψ Y).map
        ((constantSheafΓAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G) =
      (constantSheafRestrictScalarsIso ψ Y
          ((etaleModuleGlobalSections.{u, 0} Λ Y).obj G)).hom ≫
        (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).map
          ((etaleModuleGlobalSectionsRestrictScalars ψ Y).app G).hom ≫
        (constantSheafΓAdj Y.smallEtaleTopology (ModuleCat.{u + 1} R)).counit.app
          ((etaleModuleRestrictScalars ψ Y).obj G) := by
  have hΛ := Adjunction.rightAdjointUniq_hom_app_counit
    (constantSheafΓAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal) G
  have hR := Adjunction.rightAdjointUniq_hom_app_counit
    (constantSheafΓAdj Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} R) terminalIsTerminal)
    ((etaleModuleRestrictScalars ψ Y).obj G)
  have hw := constantSheafAdj_counit_w Y.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ψ)
    G terminalIsTerminal
  have hnat := (constantCommuteCompose Y.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1} ψ)).hom.naturality
      ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        terminalIsTerminal).hom.app G)
  have hγ := etaleModuleGlobalSectionsRestrictScalars_hom_app_comp_ΓNatIso ψ Y G
  have hγ' : (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).map
        ((etaleModuleGlobalSectionsRestrictScalars ψ Y).app G).hom ≫
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).map
        ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} R)
          terminalIsTerminal).hom.app ((etaleModuleRestrictScalars ψ Y).obj G)) =
      (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).map
        ((ModuleCat.restrictScalars.{u + 1} ψ).map
          ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
            terminalIsTerminal).hom.app G)) := by
    rw [← Functor.map_comp, hγ]
    rfl
  calc (etaleModuleRestrictScalars ψ Y).map
        ((constantSheafΓAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)
      = (etaleModuleRestrictScalars ψ Y).map
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
            ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
              terminalIsTerminal).hom.app G)) ≫
          (etaleModuleRestrictScalars ψ Y).map
            ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
              terminalIsTerminal).counit.app G) :=
        (congrArg (etaleModuleRestrictScalars ψ Y).map hΛ.symm).trans (Functor.map_comp _ _ _)
    _ = (etaleModuleRestrictScalars ψ Y).map
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
            ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
              terminalIsTerminal).hom.app G)) ≫
          (constantCommuteCompose Y.smallEtaleTopology
            (ModuleCat.restrictScalars.{u + 1} ψ)).hom.app (G.obj.obj (op (⊤_ Y.Etale))) ≫
          (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} R)
            terminalIsTerminal).counit.app ((etaleModuleRestrictScalars ψ Y).obj G) :=
        congrArg (_ ≫ ·) hw.symm
    _ = (constantSheafRestrictScalarsIso ψ Y
          ((etaleModuleGlobalSections.{u, 0} Λ Y).obj G)).hom ≫
          (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).map
            ((ModuleCat.restrictScalars.{u + 1} ψ).map
              ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
                terminalIsTerminal).hom.app G)) ≫
          (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} R)
            terminalIsTerminal).counit.app ((etaleModuleRestrictScalars ψ Y).obj G) :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hnat).trans (Category.assoc _ _ _))
    _ = _ := congrArg (_ ≫ ·) ((congrArg (· ≫ _) hγ'.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hR)))

/-- **`Γ(Y, G) ⟶ Γ(Y, G')` induced by an `R`-linear `φ : res_ψ G ⟶ G'`**, as an additive map:
`res_ψ Γ(Y, G) = Γ(Y, res_ψ G)` followed by `Γ(φ)`. -/
def globalSectionsRestrictScalarsAddHom (G : EtaleModules.{u, 0} Λ Y) (G' : EtaleModules.{u, 0} R Y)
    (φ : (etaleModuleRestrictScalars ψ Y).obj G ⟶ G') :
    (etaleModuleGlobalSections.{u, 0} Λ Y).obj G →+ (etaleModuleGlobalSections.{u, 0} R Y).obj G' :=
  (((etaleModuleGlobalSectionsRestrictScalars ψ Y).app G).hom ≫
    (etaleModuleGlobalSections.{u, 0} R Y).map φ).hom.toAddMonoidHom

/-- `globalSectionsRestrictScalarsAddHom ψ Y G G' φ` maps a global section `x` to its image under
the identification `res_ψ Γ(Y, G) = Γ(Y, res_ψ G)` followed by `Γ(φ)`. -/
theorem globalSectionsRestrictScalarsAddHom_apply (G : EtaleModules.{u, 0} Λ Y)
    (G' : EtaleModules.{u, 0} R Y) (φ : (etaleModuleRestrictScalars ψ Y).obj G ⟶ G')
    (x : (etaleModuleGlobalSections.{u, 0} Λ Y).obj G) :
    globalSectionsRestrictScalarsAddHom ψ Y G G' φ x =
      (((etaleModuleGlobalSectionsRestrictScalars ψ Y).app G).hom ≫
        (etaleModuleGlobalSections.{u, 0} R Y).map φ).hom x :=
  rfl

end Constant

section Restriction

variable (S : Type) [Ring S] {U C : Scheme.{u}} (j : U ⟶ C) [Etale j]

/-- **`E_U ≅ j^{-1}(E_C)`** for an étale `j : U ⟶ C`: the inverse image of a constant sheaf is
the constant sheaf, read through the restriction functor `j^{-1}`. This is the identification
entering `Stacks.EtaleCohomology.curveExtensionByZeroConstantTrace`. -/
abbrev restrictionConstantSheafIso (E : ModuleCat.{u + 1} S) :
    (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} S)).obj E ≅
      (etaleModuleRestriction.{u, 0} S j).obj
        ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} S)).obj E) :=
  ((etaleModuleInverseImageConstantIso.{u, 0} S j).app E).symm ≪≫
    (etaleModuleInverseImageRestrictionIso.{u, 0} S j).app _

/-- **`E_U ≅ j^{-1}(E_C)` carries the constant section over `U` to the constant section of `E_C`
over `U`.** -/
theorem constantSheafSection_comp_restrictionConstantSheafIso (E : ModuleCat.{u + 1} S) :
    constantSheafSection S E (Scheme.Etale.mk (𝟙 U)) ≫
        (restrictionConstantSheafIso S j E).hom.hom.app (op (Scheme.Etale.mk (𝟙 U))) =
      constantSheafSection S E
        ((Scheme.Etale.smallEtaleCompose j).obj (Scheme.Etale.mk (𝟙 U))) := by
  let F := (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} S)).obj E
  let hGT := (isTerminalEtaleMkId C).isTerminalObj (smallEtaleBaseChange j)
  let ρ : Scheme.Etale.mk (𝟙 U) ⟶ (smallEtaleBaseChange j).obj (Scheme.Etale.mk (𝟙 C)) :=
    hGT.from _
  have h1 := constantSheafSection_comp_inverseImageConstantIso_inv S E j ρ
  have h2 := ((etaleModuleInverseImageRestrictionIso.{u, 0} S j).hom.app F).hom.naturality ρ.op
  have h3 := congrArg (fun t => t.hom.app (op (Scheme.Etale.mk (𝟙 C))))
    (Adjunction.unit_leftAdjointUniq_hom_app (etaleModuleInverseImageAdj.{u, 0} S j)
      (etaleModuleRestrictionDirectImageAdj.{u, 0} S j) F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h3
  have h4 := constantSheafSection_comp_map S E
    ((Scheme.Etale.smallEtaleCompose j).map ρ ≫
      (Scheme.Etale.smallEtaleComposeBaseChangeAdj j).counit.app (Scheme.Etale.mk (𝟙 C)))
  rw [op_comp, Functor.map_comp] at h4
  refine Eq.trans ?_ h4
  calc constantSheafSection S E (Scheme.Etale.mk (𝟙 U)) ≫
        (restrictionConstantSheafIso S j E).hom.hom.app (op (Scheme.Etale.mk (𝟙 U)))
      = (constantSheafSection S E (Scheme.Etale.mk (𝟙 U)) ≫
          ((etaleModuleInverseImageConstantIso.{u, 0} S j).app E).inv.hom.app
            (op (Scheme.Etale.mk (𝟙 U)))) ≫
          ((etaleModuleInverseImageRestrictionIso.{u, 0} S j).hom.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 U))) := (Category.assoc _ _ _).symm
    _ = pulledBackConstantSection S E j ≫
          ((etaleModuleInverseImageRestrictionIso.{u, 0} S j).hom.app F).hom.app
            (op ((smallEtaleBaseChange j).obj (Scheme.Etale.mk (𝟙 C)))) ≫
          ((etaleModuleRestriction.{u, 0} S j).obj F).obj.map ρ.op := by
        rw [h1, Category.assoc]
        exact congrArg (_ ≫ ·) h2
    _ = constantSheafSection S E (Scheme.Etale.mk (𝟙 C)) ≫
          ((etaleModuleRestrictionDirectImageAdj.{u, 0} S j).unit.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 C))) ≫
          ((etaleModuleRestriction.{u, 0} S j).obj F).obj.map ρ.op :=
        (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h3)))
    _ = _ := rfl

end Restriction

section CrossRestriction

variable {R Λ : Type} [Ring R] [Ring Λ] (ψ : R →+* Λ) {U C : Scheme.{u}} (j : U ⟶ C) [Etale j]

/-- **`res_ψ` commutes with `j^{-1}` on the nose.** -/
def restrictionRestrictScalarsIso (X : EtaleModules.{u, 0} Λ C) :
    (etaleModuleRestrictScalars ψ U).obj ((etaleModuleRestriction.{u, 0} Λ j).obj X) ≅
      (etaleModuleRestriction.{u, 0} R j).obj ((etaleModuleRestrictScalars ψ C).obj X) :=
  Iso.refl _

/-- `restrictionRestrictScalarsIso` is natural. -/
@[reassoc]
theorem restrictionRestrictScalarsIso_hom_naturality {X X' : EtaleModules.{u, 0} Λ C}
    (g : X ⟶ X') :
    (etaleModuleRestrictScalars ψ U).map ((etaleModuleRestriction.{u, 0} Λ j).map g) ≫
        (restrictionRestrictScalarsIso ψ j X').hom =
      (restrictionRestrictScalarsIso ψ j X).hom ≫
        (etaleModuleRestriction.{u, 0} R j).map ((etaleModuleRestrictScalars ψ C).map g) :=
  rfl

/-- **`E_U ≅ j^{-1}(E_C)` is compatible with `res_ψ`**: through `res_ψ (E_V) ≅ (res_ψ E)_V` on
`U` and on `C`, `res_ψ` of the identification for `E` is the identification for `res_ψ E`. -/
theorem restrictScalars_restrictionConstantSheafIso (E : ModuleCat.{u + 1} Λ) :
    (constantSheafRestrictScalarsIso ψ U E).inv ≫
        (etaleModuleRestrictScalars ψ U).map (restrictionConstantSheafIso Λ j E).hom ≫
        (restrictionRestrictScalarsIso ψ j _).hom ≫
        (etaleModuleRestriction.{u, 0} R j).map (constantSheafRestrictScalarsIso ψ C E).hom =
      (restrictionConstantSheafIso R j ((ModuleCat.restrictScalars.{u + 1} ψ).obj E)).hom := by
  refine constantSheaf_hom_ext R ((ModuleCat.restrictScalars.{u + 1} ψ).obj E) ?_
  have hκU := constantSheafSection_comp_constantSheafRestrictScalarsIso_inv ψ U E
    (Scheme.Etale.mk (𝟙 U))
  have hΛ := congrArg (ModuleCat.restrictScalars.{u + 1} ψ).map
    (constantSheafSection_comp_restrictionConstantSheafIso Λ j E)
  have hκC := constantSheafSection_comp_constantSheafRestrictScalarsIso ψ C E
    ((Scheme.Etale.smallEtaleCompose j).obj (Scheme.Etale.mk (𝟙 U)))
  have hR := constantSheafSection_comp_restrictionConstantSheafIso R j
    ((ModuleCat.restrictScalars.{u + 1} ψ).obj E)
  refine Eq.trans ?_ hR.symm
  refine Eq.trans ?_ hκC
  have e1 : constantSheafSection R ((ModuleCat.restrictScalars.{u + 1} ψ).obj E)
          (Scheme.Etale.mk (𝟙 U)) ≫
        ((constantSheafRestrictScalarsIso ψ U E).inv ≫
          (etaleModuleRestrictScalars ψ U).map (restrictionConstantSheafIso Λ j E).hom ≫
          (restrictionRestrictScalarsIso ψ j _).hom ≫
          (etaleModuleRestriction.{u, 0} R j).map
            (constantSheafRestrictScalarsIso ψ C E).hom).hom.app (op (Scheme.Etale.mk (𝟙 U))) =
      (constantSheafSection R ((ModuleCat.restrictScalars.{u + 1} ψ).obj E)
            (Scheme.Etale.mk (𝟙 U)) ≫
          (constantSheafRestrictScalarsIso ψ U E).inv.hom.app (op (Scheme.Etale.mk (𝟙 U)))) ≫
          (ModuleCat.restrictScalars.{u + 1} ψ).map
            ((restrictionConstantSheafIso Λ j E).hom.hom.app (op (Scheme.Etale.mk (𝟙 U)))) ≫
          (constantSheafRestrictScalarsIso ψ C E).hom.hom.app
            (op ((Scheme.Etale.smallEtaleCompose j).obj (Scheme.Etale.mk (𝟙 U)))) := by
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc]
    rfl
  refine e1.trans ?_
  rw [hκU]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) ((Functor.map_comp _ _ _).symm.trans hΛ))

/-- **The unit of `j_! ⊣ j^{-1}` is compatible with `res_ψ`**
(`Stacks.Sites.coefficientPullbackTwoSquare_unit`). -/
theorem extensionByZeroAdj_unit_comp_restrictScalars (G : EtaleModules.{u, 0} Λ U) :
    (etaleModuleExtensionByZeroAdj.{u, 0} R j).unit.app ((etaleModuleRestrictScalars ψ U).obj G) ≫
        (etaleModuleRestriction.{u, 0} R j).map
          ((etaleModuleExtensionByZeroRestrictScalars ψ j).hom.app G) =
      (etaleModuleRestrictScalars ψ U).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app G) ≫
        (restrictionRestrictScalarsIso ψ j _).hom :=
  (Stacks.Sites.coefficientPullbackTwoSquare_unit (Scheme.Etale.smallEtaleCompose j)
    U.smallEtaleTopology C.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} ψ) G).trans
      (Category.comp_id _).symm

/-- **The map `j_!(E_U) ⟶ E_C` entering the trace is compatible with `res_ψ`.** The map
`j_!(E_U) ≅ j_! j^{-1}(E_C) ⟶ E_C` of `Stacks.EtaleCohomology.curveExtensionByZeroConstantTrace`
for `res_ψ E`, precomposed with `j_!(res_ψ (E_U) ≅ (res_ψ E)_U)`, is `res_ψ` of the map for `E`,
read through `j_! ∘ res_ψ ≅ res_ψ ∘ j_!` and `res_ψ (E_C) ≅ (res_ψ E)_C`. -/
theorem extensionByZero_restrictionConstantSheafIso_restrictScalars (E : ModuleCat.{u + 1} Λ) :
    (etaleModuleExtensionByZero.{u, 0} R j).map (constantSheafRestrictScalarsIso ψ U E).hom ≫
        (etaleModuleExtensionByZero.{u, 0} R j).map
          (restrictionConstantSheafIso R j ((ModuleCat.restrictScalars.{u + 1} ψ).obj E)).hom ≫
        (etaleModuleExtensionByZeroAdj.{u, 0} R j).counit.app
          ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
            ((ModuleCat.restrictScalars.{u + 1} ψ).obj E)) =
      (etaleModuleExtensionByZeroRestrictScalars ψ j).hom.app
          ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) ≫
        (etaleModuleRestrictScalars ψ C).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j).map (restrictionConstantSheafIso Λ j E).hom ≫
            (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app
              ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) ≫
        (constantSheafRestrictScalarsIso ψ C E).hom := by
  apply ((etaleModuleExtensionByZeroAdj.{u, 0} R j).homEquiv _ _).injective
  have hL : ((etaleModuleExtensionByZeroAdj.{u, 0} R j).homEquiv _ _)
      ((etaleModuleExtensionByZero.{u, 0} R j).map (constantSheafRestrictScalarsIso ψ U E).hom ≫
        (etaleModuleExtensionByZero.{u, 0} R j).map
          (restrictionConstantSheafIso R j ((ModuleCat.restrictScalars.{u + 1} ψ).obj E)).hom ≫
        (etaleModuleExtensionByZeroAdj.{u, 0} R j).counit.app _) =
      (constantSheafRestrictScalarsIso ψ U E).hom ≫
        (restrictionConstantSheafIso R j ((ModuleCat.restrictScalars.{u + 1} ψ).obj E)).hom := by
    rw [Adjunction.homEquiv_apply_eq, Adjunction.homEquiv_counit, Functor.map_comp_assoc]
    rfl
  have hΛ : ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _)
      ((etaleModuleExtensionByZero.{u, 0} Λ j).map (restrictionConstantSheafIso Λ j E).hom ≫
        (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app _) =
      (restrictionConstantSheafIso Λ j E).hom := by
    rw [Adjunction.homEquiv_apply_eq, Adjunction.homEquiv_counit]
    rfl
  rw [Adjunction.homEquiv_unit] at hΛ
  have h6 := extensionByZeroAdj_unit_comp_restrictScalars ψ j
    ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)
  have h5 := restrictScalars_restrictionConstantSheafIso ψ j E
  rw [hL, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp, reassoc_of% h6]
  rw [← h5]
  simp only [Iso.hom_inv_id_assoc]
  rw [← reassoc_of% (restrictionRestrictScalarsIso_hom_naturality ψ j
    ((etaleModuleExtensionByZero.{u, 0} Λ j).map (restrictionConstantSheafIso Λ j E).hom ≫
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app _)),
    ← Functor.map_comp_assoc, hΛ]

/-- **The counit of `j_! ⊣ j^{-1}` is compatible with `res_ψ`**: via
`j_! ∘ res_ψ ≅ res_ψ ∘ j_!` and `res_ψ j^{-1} = j^{-1} res_ψ`, `res_ψ` of the counit at `H` is
the counit at `res_ψ H`. -/
theorem restrictScalars_extensionByZeroAdj_counit (H : EtaleModules.{u, 0} Λ C) :
    (etaleModuleExtensionByZeroRestrictScalars ψ j).hom.app
          ((etaleModuleRestriction.{u, 0} Λ j).obj H) ≫
        (etaleModuleRestrictScalars ψ C).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app H) =
      (etaleModuleExtensionByZero.{u, 0} R j).map (restrictionRestrictScalarsIso ψ j H).hom ≫
        (etaleModuleExtensionByZeroAdj.{u, 0} R j).counit.app
          ((etaleModuleRestrictScalars ψ C).obj H) := by
  symm
  refine ((etaleModuleExtensionByZeroAdj.{u, 0} R j).homEquiv_counit
    (g := (restrictionRestrictScalarsIso ψ j H).hom)).symm.trans ?_
  rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit, Functor.map_comp,
    reassoc_of% (extensionByZeroAdj_unit_comp_restrictScalars ψ j
      ((etaleModuleRestriction.{u, 0} Λ j).obj H)),
    ← restrictionRestrictScalarsIso_hom_naturality, ← Functor.map_comp_assoc,
    Adjunction.right_triangle_components, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end CrossRestriction

section Cohomology

variable {R Λ : Type} [Ring R] [Ring Λ] (ψ : R →+* Λ) (Y : Scheme.{u})

/-- **`Hⁱ(Y, N) ≃+ Hⁱ(Y, res_ψ N)`**, the cohomology computed over `Λ` and over `R`, through the
cohomology of the underlying abelian sheaf, which `res_ψ` does not change. -/
def etaleModuleCohomologyRestrictScalars (N : EtaleModules.{u, 0} Λ Y) (i : ℕ) :
    ((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj N ≃+
      ((etaleModuleGlobalSections.{u, 0} R Y).rightDerivedPlus (i : ℤ)).obj
        ((etaleModuleRestrictScalars ψ Y).obj N) :=
  (etaleModuleCohomologyAddEquivSheafH Y N i).trans
    ((sheafHAddEquivOfIso (underlyingAbelianRestrictScalarsIso ψ Y N).symm i).trans
      (etaleModuleCohomologyAddEquivSheafH Y ((etaleModuleRestrictScalars ψ Y).obj N) i).symm)

/-- `Hⁱ(Y, N) ≃+ Hⁱ(Y, res_ψ N)` is the identity on the cohomology of the underlying abelian
sheaf. -/
theorem etaleModuleCohomologyAddEquivSheafH_restrictScalars (N : EtaleModules.{u, 0} Λ Y) (i : ℕ)
    (x : ((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj N) :
    etaleModuleCohomologyAddEquivSheafH Y ((etaleModuleRestrictScalars ψ Y).obj N) i
        (etaleModuleCohomologyRestrictScalars ψ Y N i x) =
      Sheaf.H.map (underlyingAbelianRestrictScalarsIso ψ Y N).inv i
        (etaleModuleCohomologyAddEquivSheafH Y N i x) := by
  simp only [etaleModuleCohomologyRestrictScalars, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply, sheafHAddEquivOfIso_apply, Iso.symm_hom]

/-- **`Hⁱ(Y, N) ≃+ Hⁱ(Y, res_ψ N)` is natural in `N`.** -/
theorem etaleModuleCohomologyRestrictScalars_naturality {N N' : EtaleModules.{u, 0} Λ Y}
    (g : N ⟶ N') (i : ℕ)
    (x : ((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).obj N) :
    etaleModuleCohomologyRestrictScalars ψ Y N' i
        ((((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus (i : ℤ)).map g).hom x) =
      (((etaleModuleGlobalSections.{u, 0} R Y).rightDerivedPlus (i : ℤ)).map
        ((etaleModuleRestrictScalars ψ Y).map g)).hom
          (etaleModuleCohomologyRestrictScalars ψ Y N i x) := by
  apply (etaleModuleCohomologyAddEquivSheafH Y
    ((etaleModuleRestrictScalars ψ Y).obj N') i).injective
  rw [etaleModuleCohomologyAddEquivSheafH_restrictScalars,
    etaleModuleCohomologyAddEquivSheafH_naturality, etaleModuleCohomologyAddEquivSheafH_naturality,
    etaleModuleCohomologyAddEquivSheafH_restrictScalars, ← Sheaf.H.map_comp_apply,
    ← Sheaf.H.map_comp_apply]
  rfl

/-- `Hⁱ(Y, -)` of a composite, evaluated at a class. -/
private theorem rightDerivedPlus_map_comp_apply {S : Type} [Ring S]
    {N N' N'' : EtaleModules.{u, 0} S Y} (f : N ⟶ N') (g : N' ⟶ N'') (i : ℕ)
    (x : ((etaleModuleGlobalSections.{u, 0} S Y).rightDerivedPlus (i : ℤ)).obj N) :
    (((etaleModuleGlobalSections.{u, 0} S Y).rightDerivedPlus (i : ℤ)).map g).hom
        ((((etaleModuleGlobalSections.{u, 0} S Y).rightDerivedPlus (i : ℤ)).map f).hom x) =
      (((etaleModuleGlobalSections.{u, 0} S Y).rightDerivedPlus (i : ℤ)).map (f ≫ g)).hom x := by
  rw [Functor.map_comp]
  rfl

end Cohomology

section ClassCongr

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] {ζ : K}

/-- The inverse of `Hom(ℤ/n, A) ≅ H²(C, A)` followed by evaluation at `1` depends only on `n`, not
on the proofs of its hypotheses. -/
theorem zmodEvalAddEquiv_curveConstantClass_symm_congr {A : Type} [AddCommGroup A] {n m : ℕ}
    (h : n = m) (hn₁ : IsUnit (n : K)) (hζ₁ : IsPrimitiveRoot ζ n) (hm₁ : IsUnit (m : K))
    (hζm : IsPrimitiveRoot ζ m) (hA : ∀ a : A, n • a = 0) (hAm : ∀ a : A, m • a = 0)
    (hb : Function.Bijective (curveConstantClass q hn₁ hζ₁ A))
    (hbm : Function.Bijective (curveConstantClass q hm₁ hζm A))
    (x : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C A) 2) :
    zmodEvalAddEquiv hA ((AddEquiv.ofBijective _ hb).symm x) =
      zmodEvalAddEquiv hAm ((AddEquiv.ofBijective _ hbm).symm x) := by
  subst h
  rfl

end ClassCongr

section TraceCompare

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] {R Λ : Type} [Ring R] [Ring Λ] [Fintype R] [Fintype Λ]
  (ψ : R →+* Λ) (hn : IsUnit ((Fintype.card Λ : ℕ) : K)) {ζ : K}
  (hζ : IsPrimitiveRoot ζ (Fintype.card Λ)) (hnR : IsUnit ((Fintype.card R : ℕ) : K))
  (hζR : IsPrimitiveRoot ζ (Fintype.card R))

/-- **The trace `H²(C, E_C) ≅ E` does not depend on the coefficient ring.** For a finite
`Λ`-module `E`, a finite `R`-module `E'` and an `R`-linear `h : res_ψ E ⟶ E'`, the trace over `R`
of the image of `w ∈ H²(C, E_C)` under `H²(C, E_C) ≃+ H²(C, res_ψ (E_C)) ⟶ H²(C, E'_C)` (through
`res_ψ (E_C) ≅ (res_ψ E)_C` and `h`) is `h` of the trace of `w` over `Λ`. -/
theorem curveConstantModuleTraceAddEquiv_restrictScalars (hcard : Fintype.card R = Fintype.card Λ)
    (E : ModuleCat.{u + 1} Λ) [Finite E] (E' : ModuleCat.{u + 1} R) [Finite E']
    (h : (ModuleCat.restrictScalars.{u + 1} ψ).obj E ⟶ E')
    (w : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
      ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) :
    curveConstantModuleTraceAddEquiv q R hnR hζR E'
        ((((etaleModuleGlobalSections.{u, 0} R C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((constantSheafRestrictScalarsIso ψ C E).hom ≫
            (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).map h)).hom
          (etaleModuleCohomologyRestrictScalars ψ C _ 2 w)) =
      h.hom (curveConstantModuleTraceAddEquiv q Λ hn hζ E w) := by
  let e : ((ModuleCat.restrictScalars.{u + 1} ψ).obj E) ≃+ Shrink.{0} E :=
    (Shrink.addEquiv.{0} (α := E)).symm
  let h' : Shrink.{0} E →+ Shrink.{0} E' :=
    (Shrink.addEquiv.{0} (α := E')).symm.toAddMonoidHom.comp
      (h.hom.toAddMonoidHom.comp e.symm.toAddMonoidHom)
  have key : (underlyingAbelianRestrictScalarsIso ψ C
        ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)).inv ≫
      (etaleModuleUnderlyingAbelian C ℤ).map ((etaleModuleRestrictScalars (Int.castRingHom R) C).map
        ((constantSheafRestrictScalarsIso ψ C E).hom ≫
          (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).map h)) ≫
      (underlyingConstantSheafIso C E' Shrink.addEquiv.symm).hom =
      (underlyingConstantSheafIso C E Shrink.addEquiv.symm).hom ≫ etaleConstantSheafMap C h' := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc,
      underlyingConstantSheafIso_hom_naturality C h e (Shrink.addEquiv.{0} (α := E')).symm,
      ← Category.assoc,
      ← Category.assoc, Category.assoc _ _ (underlyingConstantSheafIso C _ e).hom,
      underlyingConstantSheafIso_restrictScalars ψ C E e]
  have hR : ∀ a : Shrink.{0} E, Fintype.card R • a = 0 := fun a => by
    rw [hcard]
    exact shrink_card_nsmul_eq_zero Λ E a
  simp only [curveConstantModuleTraceAddEquiv, AddEquiv.trans_apply]
  rw [etaleModuleCohomologyAddEquivSheafH_naturality,
    etaleModuleCohomologyAddEquivSheafH_restrictScalars, sheafHAddEquivOfIso_apply,
    sheafHAddEquivOfIso_apply, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, key,
    Sheaf.H.map_comp_apply]
  generalize Sheaf.H.map (underlyingConstantSheafIso C E Shrink.addEquiv.symm).hom 2
    (etaleModuleCohomologyAddEquivSheafH C _ 2 w) = x
  let Θ := AddEquiv.ofBijective (curveConstantClass q hnR hζR (Shrink.{0} E))
    (bijective_curveConstantClass q hnR hζR hR)
  let Θ' := AddEquiv.ofBijective (curveConstantClass q hnR hζR (Shrink.{0} E'))
    (bijective_curveConstantClass q hnR hζR (shrink_card_nsmul_eq_zero R E'))
  obtain ⟨φ, rfl⟩ := Θ.surjective x
  have hΘ : ∀ φ, Θ φ = curveConstantClass q hnR hζR (Shrink.{0} E) φ := fun _ => rfl
  have hΘ' : ∀ φ, Θ' φ = curveConstantClass q hnR hζR (Shrink.{0} E') φ := fun _ => rfl
  rw [← zmodEvalAddEquiv_curveConstantClass_symm_congr q hcard hnR hζR hn hζ hR
    (shrink_card_nsmul_eq_zero Λ E) (bijective_curveConstantClass q hnR hζR hR), hΘ,
    ← curveConstantClass_naturality, ← hΘ', ← hΘ, Θ'.symm_apply_apply, Θ.symm_apply_apply]
  change Shrink.addEquiv.{0} (α := E') (h' (φ 1)) = h.hom (Shrink.addEquiv.{0} (α := E) (φ 1))
  simp [h', e]
  rfl

end TraceCompare

section SheafTraceCompare

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] {R Λ : Type} [Ring R] [Ring Λ] [Fintype R] [Fintype Λ]
  (ψ : R →+* Λ) (hn : IsUnit ((Fintype.card Λ : ℕ) : K)) {ζ : K}
  (hζ : IsPrimitiveRoot ζ (Fintype.card Λ)) (hnR : IsUnit ((Fintype.card R : ℕ) : K))
  (hζR : IsPrimitiveRoot ζ (Fintype.card R))
  {U : Scheme.{u}} (jC : U ⟶ C) [IsOpenImmersion jC] (hfin : ((Set.range jC.base)ᶜ).Finite)

omit [Fintype R] in
/-- `Stacks.EtaleCohomology.curveExtensionByZeroConstantTrace` is the trace of `E_C` after the map
`j_!(E_U) ≅ j_! j^{-1}(E_C) ⟶ E_C`. -/
theorem curveExtensionByZeroConstantTrace_eq (E : ModuleCat.{u + 1} Λ) [Finite E]
    (z : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))) :
    curveExtensionByZeroConstantTrace q Λ hn hζ jC hfin E z =
      curveConstantModuleTraceAddEquiv q Λ hn hζ E
        ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map (restrictionConstantSheafIso Λ jC E).hom ≫
            (etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app
              ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))).hom z) := by
  rw [curveExtensionByZeroConstantTrace, LinearEquiv.trans_apply]
  refine congrArg (curveConstantModuleTraceAddEquiv q Λ hn hζ E) ?_
  rw [Iso.toLinearEquiv_apply, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Functor.mapIso_hom,
    Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

omit [Fintype R] [Fintype Λ] in
/-- `E_U ≅ j^{-1}(E_C)` is natural in `E`. -/
@[reassoc]
theorem restrictionConstantSheafIso_hom_naturality (S : Type) [Ring S] {E E' : ModuleCat.{u + 1} S}
    (g : E ⟶ E') :
    (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} S)).map g ≫
        (restrictionConstantSheafIso S jC E').hom =
      (restrictionConstantSheafIso S jC E).hom ≫
        (etaleModuleRestriction.{u, 0} S jC).map
          ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} S)).map g) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Category.assoc]
  rw [← (etaleModuleInverseImageRestrictionIso.{u, 0} S jC).hom.naturality,
    NatTrans.naturality_assoc]
  rfl

/-- **The trace of a constant sheaf does not depend on the coefficient ring**, in the form
entering the trace on `H²(C, j_! G)`: for `h : res_ψ E ⟶ E'` with `E` a finite `Λ`-module and `E'`
a finite `R`-module, the trace over `R` of the image of `z ∈ H²(C, j_!(E_U))` under
`H²(C, j_! E_U) ≃+ H²(C, res_ψ j_! E_U) ≅ H²(C, j_!((res_ψ E)_U)) ⟶ H²(C, j_!(E'_U))` is `h` of the
trace of `z` over `Λ`. -/
theorem curveExtensionByZeroConstantTrace_restrictScalars (hcard : Fintype.card R = Fintype.card Λ)
    (E : ModuleCat.{u + 1} Λ) [Finite E] (E' : ModuleCat.{u + 1} R) [Finite E']
    (h : (ModuleCat.restrictScalars.{u + 1} ψ).obj E ⟶ E')
    (z : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))) :
    curveExtensionByZeroConstantTrace q R hnR hζR jC hfin E'
        ((((etaleModuleGlobalSections.{u, 0} R C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.app
              ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) ≫
            (etaleModuleExtensionByZero.{u, 0} R jC).map
              ((constantSheafRestrictScalarsIso ψ U E).hom ≫
                (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).map h))).hom
          (etaleModuleCohomologyRestrictScalars ψ C _ 2 z)) =
      h.hom (curveExtensionByZeroConstantTrace q Λ hn hζ jC hfin E z) := by
  have hK := extensionByZero_restrictionConstantSheafIso_restrictScalars ψ jC E
  have hmap : (etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.app
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) ≫
      (etaleModuleExtensionByZero.{u, 0} R jC).map
        ((constantSheafRestrictScalarsIso ψ U E).hom ≫
          (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).map h) ≫
      (etaleModuleExtensionByZero.{u, 0} R jC).map (restrictionConstantSheafIso R jC E').hom ≫
      (etaleModuleExtensionByZeroAdj.{u, 0} R jC).counit.app
        ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).obj E') =
      (etaleModuleRestrictScalars ψ C).map
          ((etaleModuleExtensionByZero.{u, 0} Λ jC).map (restrictionConstantSheafIso Λ jC E).hom ≫
            (etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app
              ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)) ≫
        (constantSheafRestrictScalarsIso ψ C E).hom ≫
        (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).map h := by
    have hn₁ := restrictionConstantSheafIso_hom_naturality jC R h
    have hn₂ := (etaleModuleExtensionByZeroAdj.{u, 0} R jC).counit_naturality
      ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).map h)
    calc _ = (etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.app
            ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) ≫
          ((etaleModuleExtensionByZero.{u, 0} R jC).map
              (constantSheafRestrictScalarsIso ψ U E).hom ≫
            (etaleModuleExtensionByZero.{u, 0} R jC).map
              (restrictionConstantSheafIso R jC ((ModuleCat.restrictScalars.{u + 1} ψ).obj E)).hom ≫
            (etaleModuleExtensionByZeroAdj.{u, 0} R jC).counit.app
              ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
                ((ModuleCat.restrictScalars.{u + 1} ψ).obj E))) ≫
          (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).map h := by
          rw [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc
            (etaleModuleExtensionByZero.{u, 0} R jC)
            ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).map h), hn₁,
            Functor.map_comp, Category.assoc, hn₂]
          simp only [Category.assoc]
      _ = _ := by
          rw [hK]
          simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  have hz : (((etaleModuleGlobalSections.{u, 0} R C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
        ((etaleModuleExtensionByZero.{u, 0} R jC).map (restrictionConstantSheafIso R jC E').hom ≫
          (etaleModuleExtensionByZeroAdj.{u, 0} R jC).counit.app
            ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).obj E'))).hom
        ((((etaleModuleGlobalSections.{u, 0} R C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.app
              ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) ≫
            (etaleModuleExtensionByZero.{u, 0} R jC).map
              ((constantSheafRestrictScalarsIso ψ U E).hom ≫
                (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).map h))).hom
          (etaleModuleCohomologyRestrictScalars ψ C _ 2 z)) =
      (((etaleModuleGlobalSections.{u, 0} R C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((constantSheafRestrictScalarsIso ψ C E).hom ≫
            (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R)).map h)).hom
        (etaleModuleCohomologyRestrictScalars ψ C _ 2
          ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ jC).map (restrictionConstantSheafIso Λ jC E).hom ≫
              (etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app
                ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E))).hom z)) := by
    rw [rightDerivedPlus_map_comp_apply, Category.assoc, hmap,
      ← rightDerivedPlus_map_comp_apply, ← etaleModuleCohomologyRestrictScalars_naturality]
    dsimp only [Functor.id_obj]
  rw [curveExtensionByZeroConstantTrace_eq, curveExtensionByZeroConstantTrace_eq, hz]
  exact curveConstantModuleTraceAddEquiv_restrictScalars q ψ hn hζ hnR hζR hcard E E' h _

omit [Fintype R] [Fintype Λ] in
/-- **A map `res_ψ G ⟶ G'` read on the constant sheaves of global sections.** Through the counits
`Γ(U, G)_U ⟶ G` and `Γ(U, G')_U ⟶ G'`, an `R`-linear `φ : res_ψ G ⟶ G'` is the constant sheaf
of `Γ(φ) : res_ψ Γ(U, G) = Γ(U, res_ψ G) ⟶ Γ(U, G')`. -/
theorem restrictScalars_map_counit_comp (G : EtaleModules.{u, 0} Λ U)
    (G' : EtaleModules.{u, 0} R U) (φ : (etaleModuleRestrictScalars ψ U).obj G ⟶ G') :
    (etaleModuleRestrictScalars ψ U).map
        ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G) ≫ φ =
      (constantSheafRestrictScalarsIso ψ U ((etaleModuleGlobalSections.{u, 0} Λ U).obj G)).hom ≫
        (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).map
          (((etaleModuleGlobalSectionsRestrictScalars ψ U).app G).hom ≫
            (etaleModuleGlobalSections.{u, 0} R U).map φ) ≫
        (constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} R)).counit.app G' := by
  rw [restrictScalars_map_constantSheafΓAdj_counit, Category.assoc, Category.assoc,
    ← (constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} R)).counit_naturality φ,
    Functor.map_comp, Category.assoc]

/-- **The trace of `H²(C, j_! G)` does not depend on the coefficient ring.** Let `G` be a sheaf of
`Λ`-modules and `G'` a sheaf of `R`-modules on `U`, both constant on their (finite) global
sections, and `φ : res_ψ G ⟶ G'` an `R`-linear map. Then the trace over `R` of the image of
`y ∈ H²(C, j_! G)` under `H²(C, j_! G) ≃+ H²(C, res_ψ j_! G) ≅ H²(C, j_!(res_ψ G)) ⟶ H²(C, j_! G')`
is `Γ(φ)` of the trace of `y` over `Λ`. -/
theorem curveExtensionByZeroSheafTrace_restrictScalars (hcard : Fintype.card R = Fintype.card Λ)
    (G : EtaleModules.{u, 0} Λ U)
    (hG : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} Λ U).obj G)) (G' : EtaleModules.{u, 0} R U)
    (hG' : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} R)).counit.app G'))
    (hE' : Finite ((etaleModuleGlobalSections.{u, 0} R U).obj G'))
    (φ : (etaleModuleRestrictScalars ψ U).obj G ⟶ G')
    (y : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj G)) :
    curveExtensionByZeroSheafTrace q R hnR hζR jC hfin G' hG' hE'
        ((((etaleModuleGlobalSections.{u, 0} R C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.app G ≫
            (etaleModuleExtensionByZero.{u, 0} R jC).map φ)).hom
          (etaleModuleCohomologyRestrictScalars ψ C _ 2 y)) =
      (((etaleModuleGlobalSectionsRestrictScalars ψ U).app G).hom ≫
        (etaleModuleGlobalSections.{u, 0} R U).map φ).hom
        (curveExtensionByZeroSheafTrace q Λ hn hζ jC hfin G hG hE y) := by
  have := hG
  have := hG'
  have := hE
  have := hE'
  have hφ : φ ≫ inv ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} R)).counit.app G') =
      (etaleModuleRestrictScalars ψ U).map
          (inv ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)) ≫
        (constantSheafRestrictScalarsIso ψ U ((etaleModuleGlobalSections.{u, 0} Λ U).obj G)).hom ≫
        (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).map
          (((etaleModuleGlobalSectionsRestrictScalars ψ U).app G).hom ≫
          (etaleModuleGlobalSections.{u, 0} R U).map φ) := by
    have hc := restrictScalars_map_counit_comp ψ G G' φ
    rw [← cancel_epi ((etaleModuleRestrictScalars ψ U).map
      ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)),
      ← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
      reassoc_of% hc, IsIso.hom_inv_id, Category.comp_id]
  have hS : (etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.app G ≫
        (etaleModuleExtensionByZero.{u, 0} R jC).map φ ≫
        (etaleModuleExtensionByZero.{u, 0} R jC).map
          (inv ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} R)).counit.app G')) =
      (etaleModuleRestrictScalars ψ C).map ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
          (inv ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))) ≫
        (etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.app
          ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            ((etaleModuleGlobalSections.{u, 0} Λ U).obj G)) ≫
        (etaleModuleExtensionByZero.{u, 0} R jC).map
          ((constantSheafRestrictScalarsIso ψ U
              ((etaleModuleGlobalSections.{u, 0} Λ U).obj G)).hom ≫
            (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).map
          (((etaleModuleGlobalSectionsRestrictScalars ψ U).app G).hom ≫
          (etaleModuleGlobalSections.{u, 0} R U).map φ)) := by
    have hv := (etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.naturality
      (inv ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))
    simp only [Functor.comp_map] at hv
    rw [← Functor.map_comp, hφ, reassoc_of% hv, Functor.map_comp]
  have hz : (((etaleModuleGlobalSections.{u, 0} R C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
        ((etaleModuleExtensionByZero.{u, 0} R jC).map
          (inv ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} R)).counit.app G')))).hom
        ((((etaleModuleGlobalSections.{u, 0} R C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.app G ≫
            (etaleModuleExtensionByZero.{u, 0} R jC).map φ)).hom
          (etaleModuleCohomologyRestrictScalars ψ C _ 2 y)) =
      (((etaleModuleGlobalSections.{u, 0} R C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.app
              ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
                ((etaleModuleGlobalSections.{u, 0} Λ U).obj G)) ≫
            (etaleModuleExtensionByZero.{u, 0} R jC).map
              ((constantSheafRestrictScalarsIso ψ U
                  ((etaleModuleGlobalSections.{u, 0} Λ U).obj G)).hom ≫
                (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).map
          (((etaleModuleGlobalSectionsRestrictScalars ψ U).app G).hom ≫
          (etaleModuleGlobalSections.{u, 0} R U).map φ)))).hom
        (etaleModuleCohomologyRestrictScalars ψ C ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
            ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
              ((etaleModuleGlobalSections.{u, 0} Λ U).obj G))) 2
          ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
            ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
              (inv ((constantSheafΓAdj U.smallEtaleTopology
                (ModuleCat.{u + 1} Λ)).counit.app G)))).hom y)) := by
    rw [etaleModuleCohomologyRestrictScalars_naturality, rightDerivedPlus_map_comp_apply,
      rightDerivedPlus_map_comp_apply, Category.assoc, hS]
    dsimp only [Functor.id_obj]
  have key := curveExtensionByZeroConstantTrace_restrictScalars q ψ hn hζ hnR hζR jC hfin hcard
    ((etaleModuleGlobalSections.{u, 0} Λ U).obj G) ((etaleModuleGlobalSections.{u, 0} R U).obj G')
    (((etaleModuleGlobalSectionsRestrictScalars ψ U).app G).hom ≫
      (etaleModuleGlobalSections.{u, 0} R U).map φ)
    ((((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).map
        (inv ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G)))).hom y)
  rw [curveExtensionByZeroSheafTrace_apply, curveExtensionByZeroSheafTrace_apply, hz]
  convert key using 2

omit [IsCurve K q] [IsProper q] [Fintype R] [Fintype Λ] in
include q hfin in
/-- `H²(C, j_! j^{-1} H) ≅ H²(C, H)` through the counit, as a surjection. -/
theorem exists_rightDerivedPlus_two_counit_eq (S : Type) [Ring S] (H : EtaleModules.{u, 0} S C)
    (v : ((etaleModuleGlobalSections.{u, 0} S C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj H) :
    ∃ w : ((etaleModuleGlobalSections.{u, 0} S C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} S jC).obj ((etaleModuleRestriction.{u, 0} S jC).obj H)),
      (((etaleModuleGlobalSections.{u, 0} S C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
        ((etaleModuleExtensionByZeroAdj.{u, 0} S jC).counit.app H)).hom w = v := by
  have := isIso_rightDerivedPlus_two_counit_of_finite_compl' q S jC hfin H
  exact ⟨(inv (((etaleModuleGlobalSections.{u, 0} S C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} S jC).counit.app H))).hom v,
    IsIso.inv_hom_id_apply _ _⟩

omit [Fintype R] [Fintype Λ] in
/-- The trace `H²(C, H) ≅ Γ(U, G)` after the counit `H²(C, j_! j^{-1} H) ⟶ H²(C, H)` is the trace
of `H²(C, j_! G)` after `j_!(l)`. -/
theorem curveExtensionByZeroRestrictionTrace_counit (S : Type) [Ring S] [Fintype S]
    (hnS : IsUnit ((Fintype.card S : ℕ) : K)) (hζS : IsPrimitiveRoot ζ (Fintype.card S))
    (H : EtaleModules.{u, 0} S C) (G : EtaleModules.{u, 0} S U)
    (l : (etaleModuleRestriction.{u, 0} S jC).obj H ≅ G)
    (hG : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} S)).counit.app G))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} S U).obj G))
    (w : ((etaleModuleGlobalSections.{u, 0} S C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
      ((etaleModuleExtensionByZero.{u, 0} S jC).obj ((etaleModuleRestriction.{u, 0} S jC).obj H))) :
    curveExtensionByZeroRestrictionTrace q S hnS hζS jC hfin H G l hG hE
        ((((etaleModuleGlobalSections.{u, 0} S C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} S jC).counit.app H)).hom w) =
      curveExtensionByZeroSheafTrace q S hnS hζS jC hfin G hG hE
        ((((etaleModuleGlobalSections.{u, 0} S C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
          ((etaleModuleExtensionByZero.{u, 0} S jC).map l.hom)).hom w) := by
  have := isIso_rightDerivedPlus_two_counit_of_finite_compl' q S jC hfin H
  have hinv : (inv (((etaleModuleGlobalSections.{u, 0} S C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
      ((etaleModuleExtensionByZeroAdj.{u, 0} S jC).counit.app H))).hom
      ((((etaleModuleGlobalSections.{u, 0} S C).rightDerivedPlus ((2 : ℕ) : ℤ)).map
        ((etaleModuleExtensionByZeroAdj.{u, 0} S jC).counit.app H)).hom w) = w := by
    exact IsIso.hom_inv_id_apply _ _
  rw [curveExtensionByZeroRestrictionTrace_apply, hinv]

/-- **The trace `H²(C, H) ≅ Γ(U, G)` does not depend on the coefficient ring.** Let `H` be a sheaf
of `Λ`-modules and `H'` a sheaf of `R`-modules on `C`, with identifications `l : j^{-1} H ≅ G` and
`l' : j^{-1} H' ≅ G'` with sheaves constant on their (finite) global sections, and let
`Φ : res_ψ H ⟶ H'` and `φ : res_ψ G ⟶ G'` be `R`-linear maps compatible with `l` and `l'`. Then
the trace over `R` of the image of `v ∈ H²(C, H)` under `H²(C, H) ≃+ H²(C, res_ψ H) ⟶ H²(C, H')`
is `Γ(φ)` of the trace of `v` over `Λ`. -/
theorem curveExtensionByZeroRestrictionTrace_restrictScalars
    (hcard : Fintype.card R = Fintype.card Λ) (H : EtaleModules.{u, 0} Λ C)
    (G : EtaleModules.{u, 0} Λ U) (l : (etaleModuleRestriction.{u, 0} Λ jC).obj H ≅ G)
    (hG : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).counit.app G))
    (hE : Finite ((etaleModuleGlobalSections.{u, 0} Λ U).obj G)) (H' : EtaleModules.{u, 0} R C)
    (G' : EtaleModules.{u, 0} R U) (l' : (etaleModuleRestriction.{u, 0} R jC).obj H' ≅ G')
    (hG' : IsIso ((constantSheafΓAdj U.smallEtaleTopology (ModuleCat.{u + 1} R)).counit.app G'))
    (hE' : Finite ((etaleModuleGlobalSections.{u, 0} R U).obj G'))
    (Φ : (etaleModuleRestrictScalars ψ C).obj H ⟶ H')
    (φ : (etaleModuleRestrictScalars ψ U).obj G ⟶ G')
    (hΦ : (restrictionRestrictScalarsIso ψ jC H).hom ≫ (etaleModuleRestriction.{u, 0} R jC).map Φ ≫
        l'.hom = (etaleModuleRestrictScalars ψ U).map l.hom ≫ φ)
    (v : ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj H) :
    curveExtensionByZeroRestrictionTrace q R hnR hζR jC hfin H' G' l' hG' hE'
        ((((etaleModuleGlobalSections.{u, 0} R C).rightDerivedPlus ((2 : ℕ) : ℤ)).map Φ).hom
          (etaleModuleCohomologyRestrictScalars ψ C _ 2 v)) =
      globalSectionsRestrictScalarsAddHom ψ U G G' φ
        (curveExtensionByZeroRestrictionTrace q Λ hn hζ jC hfin H G l hG hE v) := by
  obtain ⟨w, rfl⟩ := exists_rightDerivedPlus_two_counit_eq (q := q) (jC := jC) (hfin := hfin) Λ H v
  have h1 : (etaleModuleRestrictScalars ψ C).map
        ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H) =
      (etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.app
          ((etaleModuleRestriction.{u, 0} Λ jC).obj H) ≫
        (etaleModuleExtensionByZero.{u, 0} R jC).map (restrictionRestrictScalarsIso ψ jC H).hom ≫
        (etaleModuleExtensionByZeroAdj.{u, 0} R jC).counit.app
          ((etaleModuleRestrictScalars ψ C).obj H) := by
    rw [← Iso.app_inv, Iso.eq_inv_comp, Iso.app_hom]
    exact restrictScalars_extensionByZeroAdj_counit ψ jC H
  have hv := (etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.naturality l.hom
  simp only [Functor.comp_map] at hv
  have key : (etaleModuleRestrictScalars ψ C).map
        ((etaleModuleExtensionByZeroAdj.{u, 0} Λ jC).counit.app H) ≫ Φ =
      ((etaleModuleRestrictScalars ψ C).map ((etaleModuleExtensionByZero.{u, 0} Λ jC).map l.hom) ≫
        (etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.app G ≫
        (etaleModuleExtensionByZero.{u, 0} R jC).map φ ≫
        (etaleModuleExtensionByZero.{u, 0} R jC).map l'.inv) ≫
        (etaleModuleExtensionByZeroAdj.{u, 0} R jC).counit.app H' := by
    have hΦ' : (restrictionRestrictScalarsIso ψ jC H).hom ≫
          (etaleModuleRestriction.{u, 0} R jC).map Φ =
        (etaleModuleRestrictScalars ψ U).map l.hom ≫ φ ≫ l'.inv := by
      rw [← reassoc_of% hΦ, Iso.hom_inv_id, Category.comp_id]
    rw [h1, Category.assoc, Category.assoc,
      ← (etaleModuleExtensionByZeroAdj.{u, 0} R jC).counit_naturality Φ, ← Functor.map_comp_assoc,
      hΦ', Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% hv]
  rw [curveExtensionByZeroRestrictionTrace_counit, etaleModuleCohomologyRestrictScalars_naturality,
    rightDerivedPlus_map_comp_apply, key, ← rightDerivedPlus_map_comp_apply,
    curveExtensionByZeroRestrictionTrace_counit, rightDerivedPlus_map_comp_apply]
  have hl : ((etaleModuleRestrictScalars ψ C).map
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).map l.hom) ≫
        (etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.app G ≫
        (etaleModuleExtensionByZero.{u, 0} R jC).map φ ≫
        (etaleModuleExtensionByZero.{u, 0} R jC).map l'.inv) ≫
        (etaleModuleExtensionByZero.{u, 0} R jC).map l'.hom =
      (etaleModuleRestrictScalars ψ C).map ((etaleModuleExtensionByZero.{u, 0} Λ jC).map l.hom) ≫
        (etaleModuleExtensionByZeroRestrictScalars ψ jC).inv.app G ≫
        (etaleModuleExtensionByZero.{u, 0} R jC).map φ := by
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]
  rw [hl, ← rightDerivedPlus_map_comp_apply]
  dsimp only [Functor.comp_obj]
  rw [← etaleModuleCohomologyRestrictScalars_naturality]
  convert curveExtensionByZeroSheafTrace_restrictScalars q ψ hn hζ hnR hζR jC hfin hcard G hG hE G'
    hG' hE' φ _ using 2
  exact globalSectionsRestrictScalarsAddHom_apply ψ U G G' φ _

end SheafTraceCompare

end Stacks.EtaleCohomology

end
