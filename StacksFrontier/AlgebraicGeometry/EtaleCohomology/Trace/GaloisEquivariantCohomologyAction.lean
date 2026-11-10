module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldBaseChangeGlobalSectionsGaloisAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportActionNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GlobalLefschetzNumberOfCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactDerivedTrace
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.CochainComplexPlusDerivedUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RightDerivedRestrictionUnit

/-!
# The Galois action on `RΓ^Gal(X_k̄, -)` is the action of Remark 03UI (2)

Let `k` be a field, `k̄` a separable algebraic extension, `Y` a quasi-compact and quasi-separated
`k`-scheme and `σ ∈ Aut_k(k̄)`. The Galois-equivariant `RΓ^Gal(Y_k̄, -)` with values in discrete
`Λ[Aut_k(k̄)]`-modules (`Stacks.EtaleCohomology.galoisDerivedGlobalSections`) has, forgetting the
action, the underlying complex `RΓ(Y_k̄, -|_{Y_k̄})`
(`Stacks.EtaleCohomology.galoisDerivedGlobalSectionsForgetIso`). The base defines an action of
`σ` on `RΓ(Y_k̄, C|_{Y_k̄})` through the derived category: `RΓ` of the twist
`C|_{Y_k̄} ⟶ R(s_σ)_*(C|_{Y_k̄})` for `s_σ = id_Y × Spec σ`
(`Stacks.EtaleCohomology.galoisRestrictionCohomologyEndo`), and on `RΓ_c(X_k̄, K)` and
`H^i_c(X_k̄, K)` through a compactification (`Stacks.EtaleCohomology.galoisCompactSupportAction`,
`Stacks.EtaleCohomology.galoisCompactSupportGroupAction`). This file proves that the comparison
carries the action of `σ` coming from the Galois-module structure to that action.

## Main definitions

* `Stacks.EtaleCohomology.galoisModuleAction` — `σ` acting on underlying modules of discrete
  Galois modules, an endomorphism of the forgetful functor `U`.
* `Stacks.EtaleCohomology.galoisForgetAction` — its derived version on `D⁺`.
* `Stacks.EtaleCohomology.galoisRestrictionCohomologyNatTrans` — the base's action of `σ` on
  `RΓ(Y_k̄, -|)`, descended to `D⁺(Y_étale)`.

## Main results

* `Stacks.EtaleCohomology.galoisForgetAction_comp_galoisDerivedGlobalSectionsForgetIso` and
  `Stacks.EtaleCohomology.galoisForgetAction_app_comp_galoisDerivedGlobalSectionsForgetIso` — the
  comparison is Galois-equivariant.
* `Stacks.EtaleCohomology.galoisForgetAction_app_comp_galoisCompactSupportForgetIso` — the same
  for `RΓ^Gal_c(X_k̄, K)` and `Stacks.EtaleCohomology.galoisCompactSupportAction`.
* `Stacks.EtaleCohomology.galoisCompactSupportGroupForgetIso_hom_galoisAction` — the same for the
  Galois modules `H^i(RΓ^Gal_c(X_k̄, K))` and
  `Stacks.EtaleCohomology.galoisCompactSupportGroupAction`.
* `Stacks.EtaleCohomology.mapCochainComplexPlusDerivedUnit_comp_galoisRestrictionCohomologyEndo` —
  the unit `Γ(Y_k̄, C|) ⟶ RΓ(Y_k̄, C|)` carries the degreewise action of `σ` to the base's action.
* `Stacks.EtaleCohomology.etaleModuleDirectImageCompGlobalSections_eq` — the base's two
  identifications `Γ(Y, g_* -) ≅ Γ(X, -)` agree.
* `Stacks.EtaleCohomology.rightDerivedFunctorPlus_comp_ext` — transformations out of `RF ⋙ G` are
  determined after the unit on complexes.

## Implementation notes

Both sides are right derived functors of `F ↦ Γ(Y_k̄, F|_{Y_k̄})`, with the degreewise action of
`σ` on it; the two actions are compared after the units, on complexes
(`Stacks.EtaleCohomology.rightDerivedFunctorPlus_comp_ext`). On the base side the computation is
`CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit_app_comp_twist`. No isomorphism is chosen,
and `AlgebraicGeometry.representationSheafPullbackIso` is not used.

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (2).
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius Opposite

universe u w₁ w₂

namespace Stacks.EtaleCohomology

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Exact functors on `D⁺`, on the image of a complex -/

section ExactQ

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- **The comparison `RF ≅ F̄` of an exact functor, against the unit, on a complex**: the unit
`Q(F(M)) ⟶ RF(Q M)` followed by the comparison is the inverse of the commutation
`Q ⋙ F̄ ≅ F ⋙ Q`. -/
theorem mapCochainComplexPlusDerivedUnit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (M : CochainComplex.Plus A) :
    F.mapCochainComplexPlusDerivedUnit.app M ≫
        F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app (DerivedCategory.Plus.Q.obj M) =
      (Functor.mapDerivedCategoryPlusQIso F).inv.app M := by
  have h1 := F.unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app
    ((HomotopyCategory.Plus.quotient A).obj M)
  have h2 := F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.naturality
    ((DerivedCategory.Plus.quotientCompQhIso A).hom.app M)
  rw [Functor.mapCochainComplexPlusDerivedUnit_app]
  simp only [Functor.mapDerivedCategoryPlusQIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Iso.symm_inv]
  have hm0 : (AlgebraicGeometry.Tag01XLDerivedIso.mapHomotopyCategoryPlusFactors F).inv.app M =
      𝟙 _ := by
    apply ObjectProperty.hom_ext
    refine ((HomotopyCategory.Plus.ι B).map_preimage _).trans ?_
    simp [Functor.mapHomotopyCategoryFactors]
    rfl
  have hm : DerivedCategory.Plus.Qh.map
      ((AlgebraicGeometry.Tag01XLDerivedIso.mapHomotopyCategoryPlusFactors F).inv.app M) = 𝟙 _ := by
    rw [hm0]
    exact DerivedCategory.Plus.Qh.map_id _
  rw [hm]
  simp only [Category.comp_id, Category.assoc]
  refine congrArg (_ ≫ ·) ?_
  exact (congrArg (_ ≫ ·) h2).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun x => x ≫ F.mapDerivedCategoryPlus.map
      ((DerivedCategory.Plus.quotientCompQhIso A).hom.app M)) h1).trans
        (Category.id_comp _).symm))

/-- **The inverse comparison `F̄ ≅ RF` of an exact functor, on a complex**: it is the commutation
`F̄(Q M) ≅ Q(F(M))` followed by the unit `Q(F(M)) ⟶ RF(Q M)`. -/
private theorem rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_inv_app_Q
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (M : CochainComplex.Plus A) :
    F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app (DerivedCategory.Plus.Q.obj M) =
      (Functor.mapDerivedCategoryPlusQIso F).hom.app M ≫
        F.mapCochainComplexPlusDerivedUnit.app M := by
  have e1 : ((Functor.mapDerivedCategoryPlusQIso F).hom.app M ≫
      F.mapCochainComplexPlusDerivedUnit.app M) ≫
        F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
          (DerivedCategory.Plus.Q.obj M) = 𝟙 _ := by
    rw [Category.assoc,
      mapCochainComplexPlusDerivedUnit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom,
      Iso.hom_inv_id_app]
  exact ((Category.comp_id _).symm.trans ((congrArg (_ ≫ ·)
    (F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom_inv_id_app _).symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e1).trans
        (Category.id_comp _))))).symm

/-- **The transformation of `D⁺` induced by a transformation of exact functors, on a complex**:
it is the degreewise transformation, through the commutations `Q ⋙ T̄ ≅ T ⋙ Q`. -/
theorem mapDerivedCategoryPlusNatTrans_app_Q {T S : A ⥤ B} [T.Additive] [S.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S] (τ : T ⟶ S)
    (M : CochainComplex.Plus A) :
    (Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans τ).app (DerivedCategory.Plus.Q.obj M) ≫
        (Functor.mapDerivedCategoryPlusQIso S).hom.app M =
      (Functor.mapDerivedCategoryPlusQIso T).hom.app M ≫
        DerivedCategory.Plus.Q.map (ObjectProperty.homMk
          (X := T.mapCochainComplexPlus.obj M) (Y := S.mapCochainComplexPlus.obj M)
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app M.obj)) := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [Functor.map_comp, Functor.map_comp,
    Stacks.DerivedFunctor.ι_map_mapDerivedCategoryPlusNatTrans_app,
    Functor.ι_map_mapDerivedCategoryPlusQIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusQIso_hom_app]
  exact Stacks.DerivedFunctor.mapDerivedNatTrans_factors_app τ M.obj

/-- **Transformations out of `RF ⋙ G` are determined on complexes**: two transformations
`RF ⋙ G ⟶ K` agree as soon as they agree after `G` of the unit `Q(F(C)) ⟶ RF(Q C)`, for every
bounded below complex `C`. This is the universal property of the right derived functor, read on
complexes rather than on the homotopy category. -/
theorem rightDerivedFunctorPlus_comp_ext {H : Type*} [Category* H] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (G : DerivedCategory.Plus B ⥤ H) {K : DerivedCategory.Plus A ⥤ H}
    (γ₁ γ₂ : F.rightDerivedFunctorPlus ⋙ G ⟶ K)
    (h : ∀ C : CochainComplex.Plus A,
      G.map (F.mapCochainComplexPlusDerivedUnit.app C) ≫ γ₁.app (DerivedCategory.Plus.Q.obj C) =
        G.map (F.mapCochainComplexPlusDerivedUnit.app C) ≫ γ₂.app (DerivedCategory.Plus.Q.obj C)) :
    γ₁ = γ₂ := by
  refine Functor.rightDerived_ext (F.rightDerivedFunctorPlus ⋙ G)
    (Functor.whiskerRight F.rightDerivedFunctorPlusUnith G) (HomotopyCategory.Plus.quasiIso A) K
    γ₁ γ₂ ?_
  ext N
  obtain ⟨C, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective N
  let e := (DerivedCategory.Plus.quotientCompQhIso A).hom.app C
  let eB := (DerivedCategory.Plus.quotientCompQhIso B).inv.app (F.mapCochainComplexPlus.obj C)
  let u := F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj C)
  have key : ∀ γ : F.rightDerivedFunctorPlus ⋙ G ⟶ K,
      G.map eB ≫ (G.map u ≫ γ.app (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient A).obj C))) ≫ K.map e =
      G.map (F.mapCochainComplexPlusDerivedUnit.app C) ≫ γ.app (DerivedCategory.Plus.Q.obj C) := by
    intro γ
    exact (congrArg (G.map eB ≫ ·) ((Category.assoc _ _ _).trans ((congrArg (G.map u ≫ ·)
      (γ.naturality e).symm).trans (Category.assoc _ _ _).symm))).trans
        ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ γ.app (DerivedCategory.Plus.Q.obj C))
          ((congrArg (G.map eB ≫ ·) (G.map_comp u (F.rightDerivedFunctorPlus.map e)).symm).trans
            (G.map_comp eB (u ≫ F.rightDerivedFunctorPlus.map e)).symm)))
  exact (cancel_mono (K.map e)).1 ((cancel_epi (G.map eB)).1
    ((key γ₁).trans ((h C).trans (key γ₂).symm)))

end ExactQ

/-! ### The two identifications `Γ(Y, g_* -) ≅ Γ(X, -)` agree -/

section GlobalSectionsDirectImage

/-- Sheaves of `ModuleCat.{u + 1} Λ` on a small étale site have a global sections functor, the
site having a terminal object; pinned at the object universe. -/
local instance (priority := 3000) hasGlobalSectionsFunctor_galoisAction (Λ : Type) [Ring Λ]
    (Z : Scheme.{u}) : HasGlobalSectionsFunctor Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  hasGlobalSectionsFunctor_of_hasTerminal _ _

variable (Λ : Type) [Ring Λ]


/-- The component at a sheaf `F` of
    `Stacks.EtaleCohomology.etaleModuleDirectImageCompGlobalSections_eq`. -/
theorem etaleModuleDirectImageCompGlobalSections_hom_app {X Y : Scheme.{u}} (g : X ⟶ Y)
    (F : EtaleModules.{u, 0} Λ X) :
    (etaleModuleDirectImageCompGlobalSections.{u, 0} Λ g).hom.app F =
      (etaleModuleGlobalSectionsDirectImageIso g Λ).hom.app F := by
  let hT1 : IsTerminal ((smallEtaleBaseChange g).obj (⊤_ Y.Etale)) :=
    IsTerminal.isTerminalObj (smallEtaleBaseChange g) _ terminalIsTerminal
  have : IsIso (Scheme.Etale.mk (𝟙 Y)).hom := inferInstanceAs (IsIso (𝟙 Y))
  have : IsIso (Scheme.Etale.mk (𝟙 X)).hom := inferInstanceAs (IsIso (𝟙 X))
  have : HasTerminal Y.Etale := (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Y))).hasTerminal
  have : HasTerminal X.Etale := (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 X))).hasTerminal
  let hT2 : IsTerminal ((smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 Y))) :=
    isTerminalSmallEtaleBaseChangeObj g (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Y)))
  let ΓY₁ := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (terminalIsTerminal (C := Y.Etale))
  let ΓX₁ := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT1
  let ΓY₂ := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (isTerminalOfIsIsoHom (Scheme.Etale.mk (𝟙 Y)))
  let ΓX₂ := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT2
  have hiso : IsIso (F.ΓRes (op ((smallEtaleBaseChange g).obj (⊤_ Y.Etale)))) := by
    rw [← Sheaf.ΓNatIsoSheafSections_hom_app_general hT1 F]
    infer_instance
  have hmono : Mono (F.ΓRes (op ((smallEtaleBaseChange g).obj (⊤_ Y.Etale)))) :=
    @IsIso.mono_of_iso _ _ _ _ _ hiso
  refine (@cancel_mono _ _ _ _ _ _ hmono _ _).1 ?_
  let k : ⊤_ Y.Etale ⟶ Scheme.Etale.mk (𝟙 Y) := (isTerminalEtaleMkId Y).from _
  have r1 := Sheaf.ΓRes_map F ((smallEtaleBaseChange g).map k).op
  have r2 := Sheaf.ΓRes_map ((etaleModuleDirectImage.{u, 0} Λ g).obj F) k.op
  have cR : (etaleModuleGlobalSectionsDirectImageIso g Λ).hom.app F ≫ ΓX₁.hom.app F =
      ΓY₁.hom.app ((etaleModuleDirectImage.{u, 0} Λ g).obj F) := by
    change (ΓY₁.hom.app ((etaleModuleDirectImage.{u, 0} Λ g).obj F) ≫ ΓX₁.inv.app F) ≫
      ΓX₁.hom.app F = _
    exact (Category.assoc _ _ _).trans ((congrArg _ (Iso.inv_hom_id_app ΓX₁ F)).trans
      (Category.comp_id _))
  have cL : (etaleModuleDirectImageCompGlobalSections.{u, 0} Λ g).hom.app F ≫ ΓX₂.hom.app F =
      ΓY₂.hom.app ((etaleModuleDirectImage.{u, 0} Λ g).obj F) := by
    change (ΓY₂.hom.app ((etaleModuleDirectImage.{u, 0} Λ g).obj F) ≫ 𝟙 _ ≫ ΓX₂.inv.app F) ≫
      ΓX₂.hom.app F = _
    exact (Category.assoc _ _ _).trans ((congrArg _ ((Category.assoc _ _ _).trans
      ((Category.id_comp _).trans (Iso.inv_hom_id_app ΓX₂ F)))).trans (Category.comp_id _))
  rw [Sheaf.ΓNatIsoSheafSections_hom_app_general] at cR cL
  have eR : (etaleModuleGlobalSectionsDirectImageIso g Λ).hom.app F ≫
      F.ΓRes (op ((smallEtaleBaseChange g).obj (⊤_ Y.Etale))) =
      ((etaleModuleDirectImage.{u, 0} Λ g).obj F).ΓRes (op (⊤_ Y.Etale)) :=
    cR.trans (Sheaf.ΓNatIsoSheafSections_hom_app_general _ _)
  have eL : (etaleModuleDirectImageCompGlobalSections.{u, 0} Λ g).hom.app F ≫
      F.ΓRes (op ((smallEtaleBaseChange g).obj (⊤_ Y.Etale))) =
      ((etaleModuleDirectImage.{u, 0} Λ g).obj F).ΓRes (op (⊤_ Y.Etale)) :=
    (congrArg (_ ≫ ·) r1.symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ F.obj.map ((smallEtaleBaseChange g).map k).op)
        (cL.trans (Sheaf.ΓNatIsoSheafSections_hom_app_general _ _))).trans r2))
  exact eL.trans eR.symm

/-- **The two identifications `Γ(Y, g_*F) ≅ Γ(X, F)` of the base agree**: both are restriction of
global sections to a final object followed by the inverse of restriction to its base change, and
they differ only in the final object chosen. -/
theorem etaleModuleDirectImageCompGlobalSections_eq {X Y : Scheme.{u}} (g : X ⟶ Y) :
    etaleModuleDirectImageCompGlobalSections.{u, 0} Λ g =
      etaleModuleGlobalSectionsDirectImageIso g Λ :=
  Iso.ext (NatTrans.ext (funext fun F => etaleModuleDirectImageCompGlobalSections_hom_app Λ g F))

end GlobalSectionsDirectImage

/-! ### The Galois action on `RΓ(Y_k̄, C|_{Y_k̄})` against the unit -/

section Core

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (σ : kbar ≃ₐ[k] kbar)

/-- **The action of `σ` on `Γ(Y_k̄, -|_{Y_k̄})`**, as an endomorphism of the functor
`G ↦ Γ(Y_k̄, G|_{Y_k̄})`: its component at `G` is
`Stacks.EtaleCohomology.fieldBaseChangeGlobalSectionsGaloisAction`. -/
def fieldBaseChangeGlobalSectionsGaloisNatTrans :
    etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar) ⋙
        etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar) ⟶
      etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar) ⋙
        etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar) where
  app G := fieldBaseChangeGlobalSectionsGaloisAction.{u, 0} Λ Y kbar σ G
  naturality _ _ v := (fieldBaseChangeGlobalSectionsGaloisAction_naturality Λ Y kbar σ v).symm

/-- **The action of `σ` on `RΓ(Y_k̄, C|_{Y_k̄})` against the unit `Γ(Y_k̄, C|) ⟶ RΓ(Y_k̄, C|)`**:
    the
unit carries the degreewise action of `σ` on the complex `Γ(Y_k̄, C|_{Y_k̄})` to
`Stacks.EtaleCohomology.galoisRestrictionCohomologyEndo`. -/
theorem mapCochainComplexPlusDerivedUnit_comp_galoisRestrictionCohomologyEndo
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)) :
    (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y
        kbar)).mapCochainComplexPlusDerivedUnit.app
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            C) ≫
      galoisRestrictionCohomologyEndo.{u, 0} Λ Y kbar σ C =
    DerivedCategory.Plus.Q.map (ObjectProperty.homMk
        (X := (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y
            kbar)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y
              kbar)).mapCochainComplexPlus.obj C))
        (Y := (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y
            kbar)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y
              kbar)).mapCochainComplexPlus.obj C))
        ((NatTrans.mapHomologicalComplex (fieldBaseChangeGlobalSectionsGaloisNatTrans Λ Y kbar σ)
          (ComplexShape.up ℤ)).app C.obj)) ≫
      (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y
          kbar)).mapCochainComplexPlusDerivedUnit.app
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            C) := by
  have h := Functor.mapCochainComplexPlusDerivedUnit_app_comp_twist
    (etaleModuleDirectImage.{u, 0} Λ (galoisBaseChange Y kbar σ))
    (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar))
    (etaleModuleDirectImageCompGlobalSections.{u, 0} Λ (galoisBaseChange Y kbar σ))
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C)
    (selfMapComplexTwist.{u, 0} Λ (fieldBaseChangeProj Y kbar) (galoisBaseChange Y kbar σ)
      (galoisBaseChange_comp_fst Y kbar σ) C)
  refine h.trans (congrArg (· ≫ _) (congrArg DerivedCategory.Plus.Q.map ?_))
  ext n : 2
  change (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).map
      ((selfMapTwist.{u, 0} Λ (fieldBaseChangeProj Y kbar) (galoisBaseChange Y kbar σ)
        (galoisBaseChange_comp_fst Y kbar σ)).app (C.obj.X n)) ≫
    (etaleModuleDirectImageCompGlobalSections.{u, 0} Λ (galoisBaseChange Y kbar σ)).hom.app
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj (C.obj.X n)) = _
  rw [etaleModuleDirectImageCompGlobalSections_hom_app]
  rfl

end Core

/-! ### The comparison `RΓ^Gal ⋙ U ≅ RΓ(Y_k̄, -|)` on complexes -/

section ForgetFac

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned. -/
local instance (priority := 3000) etaleModules_enoughInjectives_galoisAction (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- Enough injectives for discrete Galois modules, pinned. -/
local instance (priority := 3000) galoisModules_enoughInjectives_galoisAction (Λ : Type) [Ring Λ]
    (k : Type u) [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar] :
    EnoughInjectives (GaloisModules Λ k kbar) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar]

/-- **The comparison `RΓ^Gal(Y_k̄, -) ⋙ U ≅ RΓ(Y_k̄, -|_{Y_k̄})` against the units, on a complex**:
`U` of the unit `Q(Γ^Gal(C)) ⟶ RΓ^Gal(Q C)` followed by the comparison is the unit
`Q(Γ(Y_k̄, C|)) ⟶ RΓ(Y_k̄, Q(C|))`, read through the commutations of `Q` with `U` and with `-|`. -/
theorem galoisDerivedGlobalSectionsForgetIso_fac
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)) :
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
        (kbar ≃ₐ[k] kbar)).mapDerivedCategoryPlus.map
        ((galoisGlobalSections Λ Y kbar).mapCochainComplexPlusDerivedUnit.app C) ≫
      (galoisDerivedGlobalSectionsForgetIso Λ Y kbar).hom.app (DerivedCategory.Plus.Q.obj C) =
    (Functor.mapDerivedCategoryPlusQIso (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1}
        Λ (kbar ≃ₐ[k] kbar))).hom.app ((galoisGlobalSections Λ Y kbar).mapCochainComplexPlus.obj C)
            ≫
      (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y
          kbar)).mapCochainComplexPlusDerivedUnit.app
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            C) ≫
      (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus.map
        ((Functor.mapDerivedCategoryPlusQIso
          (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))).inv.app C) := by
  let U := Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)
  let Γg := galoisGlobalSections Λ Y kbar
  let res := etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)
  let Γ := etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)
  have hRres :=
      mapCochainComplexPlusDerivedUnit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom
    res C
  have h1 := Functor.mapCochainComplexPlusDerivedUnit_comp Γg U
      (Functor.rightDerivedFunctorPlusComp Γg U)
    (Functor.rightDerivedFunctorPlusComp_fac Γg U) C
  have h2 := Functor.mapCochainComplexPlusDerivedUnit_comp res Γ
    (Functor.rightDerivedFunctorPlusComp res Γ) (Functor.rightDerivedFunctorPlusComp_fac res Γ) C
  have hn := U.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.naturality
    (Γg.mapCochainComplexPlusDerivedUnit.app C)
  dsimp only [Functor.comp_obj] at hn
  let c₁ := Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic Γg U
    (fun I _ => U.rightAcyclic_of_exact (Γg.obj I))
  let c₂ := Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic res Γ
    (fun I _ => rightAcyclic_etaleModuleGlobalSections_fieldBaseChange Λ Y kbar I)
  have h1' : U.mapCochainComplexPlusDerivedUnit.app (Γg.mapCochainComplexPlus.obj C) ≫
      U.rightDerivedFunctorPlus.map (Γg.mapCochainComplexPlusDerivedUnit.app C) ≫
        c₁.inv.app (DerivedCategory.Plus.Q.obj C) =
      (Γg ⋙ U).mapCochainComplexPlusDerivedUnit.app C := by
    rw [← Category.assoc, ← h1]
    exact (Category.assoc _ _ _).trans ((congrArg _ (c₁.hom_inv_id_app _)).trans
      (Category.comp_id _))
  change U.mapDerivedCategoryPlus.map (Γg.mapCochainComplexPlusDerivedUnit.app C) ≫
      U.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
        (Γg.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj C)) ≫
      c₁.inv.app (DerivedCategory.Plus.Q.obj C) ≫ c₂.hom.app (DerivedCategory.Plus.Q.obj C) ≫
      Γ.rightDerivedFunctorPlus.map
        (res.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app (DerivedCategory.Plus.Q.obj
            C)) = _
  rw [reassoc_of% hn,
    rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_inv_app_Q U (Γg.mapCochainComplexPlus.obj C),
    Category.assoc, reassoc_of% h1']
  exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h2).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      ((Γ.rightDerivedFunctorPlus.map_comp _ _).symm.trans
        (congrArg Γ.rightDerivedFunctorPlus.map hRres))))))

end ForgetFac

/-! ### The two Galois actions -/

section Actions

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned. -/
local instance (priority := 3000) etaleModules_enoughInjectives_galoisActions (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- Enough injectives for discrete Galois modules, pinned. -/
local instance (priority := 3000) galoisModules_enoughInjectives_galoisActions (Λ : Type) [Ring Λ]
    (k : Type u) [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar] :
    EnoughInjectives (GaloisModules Λ k kbar) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)

/-- `Q : C⁺(𝒜) ⥤ D⁺(𝒜)` is a localization at the quasi-isomorphisms. -/
local instance isLocalization_plusQ_galoisAction (𝒜 : Type*) [Category* 𝒜] [Abelian 𝒜] :
    (DerivedCategory.Plus.Q (C := 𝒜)).IsLocalization (CochainComplex.Plus.quasiIso 𝒜) :=
  Functor.IsLocalization.of_iso _ (DerivedCategory.Plus.quotientCompQhIso 𝒜)

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The action of `σ` on the underlying module of a discrete Galois module**, as an
endomorphism of the forgetful functor `U : GaloisModules Λ k k̄ ⥤ ModuleCat Λ`: its component at
`M` is `ρ_M(σ)`, natural because morphisms of Galois modules are equivariant. -/
def galoisModuleAction (σ : kbar ≃ₐ[k] kbar) :
    Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar) ⟶
      Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar) where
  app M := (M.obj.obj.ρ σ).asHom
  naturality _ _ f := (f.hom.hom.comm σ).symm

/-- **The action of `σ` on the underlying complex of an object of `D⁺(GaloisModules Λ k k̄)`**: the
endomorphism of the forgetful functor `D⁺(GaloisModules Λ k k̄) ⥤ D⁺(Λ)` induced by
`Stacks.EtaleCohomology.galoisModuleAction`. -/
def galoisForgetAction (σ : kbar ≃ₐ[k] kbar) :
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
        (kbar ≃ₐ[k] kbar)).mapDerivedCategoryPlus ⟶
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
        (kbar ≃ₐ[k] kbar)).mapDerivedCategoryPlus :=
  Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans (galoisModuleAction Λ kbar σ)

/-- **The action of `σ` on `RΓ(Y_k̄, C|_{Y_k̄})`, as an endomorphism of
`C ↦ RΓ(Y_k̄, C|_{Y_k̄})` on `D⁺(Y_étale)`**: the descent along `Q` of
`Stacks.EtaleCohomology.galoisRestrictionCohomologyEndo`, which is natural in the complex. -/
def galoisRestrictionCohomologyNatTrans (σ : kbar ≃ₐ[k] kbar) :
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapDerivedCategoryPlus ⋙
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus ⟶
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapDerivedCategoryPlus ⋙
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus :=
  Localization.liftNatTrans DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso _)
    (DerivedCategory.Plus.Q ⋙
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapDerivedCategoryPlus ⋙
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus)
    (DerivedCategory.Plus.Q ⋙
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapDerivedCategoryPlus ⋙
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus)
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapDerivedCategoryPlus ⋙
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus)
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapDerivedCategoryPlus ⋙
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus)
    { app := fun C =>
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus.map
            ((Functor.mapDerivedCategoryPlusQIso
              (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))).hom.app C) ≫
          galoisRestrictionCohomologyEndo.{u, 0} Λ Y kbar σ C ≫
          (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus.map
            ((Functor.mapDerivedCategoryPlusQIso
              (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))).inv.app C)
      naturality := fun C C' ψ => by
        have q1 := (Functor.mapDerivedCategoryPlusQIso
          (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))).hom.naturality ψ
        have q2 := (Functor.mapDerivedCategoryPlusQIso
          (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))).inv.naturality ψ
        have e := galoisRestrictionCohomologyEndo_naturality Λ Y kbar σ ψ
        dsimp only [Functor.comp_map, Functor.comp_obj, etaleModuleDerivedGlobalSections]
          at q1 q2 e ⊢
        rw [← Functor.map_comp_assoc, q1, Functor.map_comp_assoc, ← reassoc_of% e,
          ← Functor.map_comp, q2, Functor.map_comp]
        simp only [Category.assoc] }

/-- The action of `σ` on `RΓ(Y_k̄, -|)` at the image of a complex is
`Stacks.EtaleCohomology.galoisRestrictionCohomologyEndo`, through `Q ⋙ (-|) ≅ (-|) ⋙ Q`. -/
theorem galoisRestrictionCohomologyNatTrans_app (σ : kbar ≃ₐ[k] kbar)
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)) :
    (galoisRestrictionCohomologyNatTrans Λ Y kbar σ).app (DerivedCategory.Plus.Q.obj C) =
      (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusQIso
            (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))).hom.app C) ≫
        galoisRestrictionCohomologyEndo.{u, 0} Λ Y kbar σ C ≫
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusQIso
            (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))).inv.app C) := by
  rw [galoisRestrictionCohomologyNatTrans, Localization.liftNatTrans_app]
  simp

/-- **The action of `σ` on `RΓ(Y_k̄, -|)` against the unit, on a complex**: the unit followed by
the commutation `(-|) ⋙ Q ≅ Q ⋙ (-|)` carries the degreewise action of `σ` on
`Γ(Y_k̄, C|_{Y_k̄})` to `Stacks.EtaleCohomology.galoisRestrictionCohomologyNatTrans`. -/
private theorem mapCochainComplexPlusDerivedUnit_comp_galoisRestrictionCohomologyNatTrans_app
    (σ : kbar ≃ₐ[k] kbar) (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)) :
    (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y
        kbar)).mapCochainComplexPlusDerivedUnit.app
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y
            kbar)).mapCochainComplexPlus.obj C) ≫
      (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus.map
        ((Functor.mapDerivedCategoryPlusQIso
          (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))).inv.app C) ≫
      (galoisRestrictionCohomologyNatTrans Λ Y kbar σ).app (DerivedCategory.Plus.Q.obj C) =
    DerivedCategory.Plus.Q.map (ObjectProperty.homMk
        (X := (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y
            kbar)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y
              kbar)).mapCochainComplexPlus.obj C))
        (Y := (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y
            kbar)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y
              kbar)).mapCochainComplexPlus.obj C))
        ((NatTrans.mapHomologicalComplex (fieldBaseChangeGlobalSectionsGaloisNatTrans Λ Y kbar σ)
          (ComplexShape.up ℤ)).app C.obj)) ≫
      (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y
          kbar)).mapCochainComplexPlusDerivedUnit.app
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y
            kbar)).mapCochainComplexPlus.obj C) ≫
      (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus.map
        ((Functor.mapDerivedCategoryPlusQIso
          (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))).inv.app C) := by
  rw [galoisRestrictionCohomologyNatTrans_app, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of%
    mapCochainComplexPlusDerivedUnit_comp_galoisRestrictionCohomologyEndo Λ Y kbar σ C]

end Actions

/-! ### The comparison is Galois-equivariant -/

section Equivariance

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned. -/
local instance (priority := 3000) etaleModules_enoughInjectives_galoisEquiv (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- Enough injectives for discrete Galois modules, pinned. -/
local instance (priority := 3000) galoisModules_enoughInjectives_galoisEquiv (Λ : Type) [Ring Λ]
    (k : Type u) [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar] :
    EnoughInjectives (GaloisModules Λ k kbar) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  [QuasiCompact Y.hom] [QuasiSeparated Y.hom] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [Algebra.IsSeparable k kbar]

/-- **The Galois action on `RΓ^Gal(Y_k̄, -)` is the action of Remark 03UI (2)**: forgetting the
action, `RΓ^Gal(Y_k̄, -) ⋙ U ≅ RΓ(Y_k̄, -|_{Y_k̄})`
(`Stacks.EtaleCohomology.galoisDerivedGlobalSectionsForgetIso`) carries the action of `σ` coming
from the Galois-module structure to the action induced by `id_Y × Spec σ`. -/
theorem galoisForgetAction_comp_galoisDerivedGlobalSectionsForgetIso (σ : kbar ≃ₐ[k] kbar) :
    Functor.whiskerLeft (galoisDerivedGlobalSections Λ Y kbar) (galoisForgetAction Λ kbar σ) ≫
        (galoisDerivedGlobalSectionsForgetIso Λ Y kbar).hom =
      (galoisDerivedGlobalSectionsForgetIso Λ Y kbar).hom ≫
        galoisRestrictionCohomologyNatTrans Λ Y kbar σ := by
  apply rightDerivedFunctorPlus_comp_ext (galoisGlobalSections Λ Y kbar)
  intro C
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app]
  have hnat := (galoisForgetAction Λ kbar σ).naturality
    ((galoisGlobalSections Λ Y kbar).mapCochainComplexPlusDerivedUnit.app C)
  have hfac := galoisDerivedGlobalSectionsForgetIso_fac Λ Y kbar C
  have hD := mapDerivedCategoryPlusNatTrans_app_Q (galoisModuleAction Λ kbar σ)
    ((galoisGlobalSections Λ Y kbar).mapCochainComplexPlus.obj C)
  have e1 := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫
      (galoisDerivedGlobalSectionsForgetIso Λ Y kbar).hom.app (DerivedCategory.Plus.Q.obj C))
          hnat).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hfac)))
  have e2 := (Category.assoc _ _ _).symm.trans (congrArg (· ≫
      (galoisRestrictionCohomologyNatTrans Λ Y kbar σ).app (DerivedCategory.Plus.Q.obj C)) hfac)
  have e3 := ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hD).trans
    (Category.assoc _ _ _))).trans ((congrArg (_ ≫ ·)
      (mapCochainComplexPlusDerivedUnit_comp_galoisRestrictionCohomologyNatTrans_app
        Λ Y kbar σ C).symm).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm)
  exact e1.trans (e3.trans e2.symm)

/-- **The Galois action on `RΓ^Gal(Y_k̄, C)`, at a complex**: through the identification of its
underlying complex with `RΓ(Y_k̄, C|_{Y_k̄})`, the action of `σ` from the Galois-module structure
is `Stacks.EtaleCohomology.galoisRestrictionCohomologyEndo`. -/
theorem galoisForgetAction_app_comp_galoisDerivedGlobalSectionsForgetIso (σ : kbar ≃ₐ[k] kbar)
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)) :
    (galoisForgetAction Λ kbar σ).app
        ((galoisDerivedGlobalSections Λ Y kbar).obj (DerivedCategory.Plus.Q.obj C)) ≫
      (galoisDerivedGlobalSectionsForgetIso Λ Y kbar).hom.app (DerivedCategory.Plus.Q.obj C) ≫
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusQIso
            (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))).hom.app C) =
    ((galoisDerivedGlobalSectionsForgetIso Λ Y kbar).hom.app (DerivedCategory.Plus.Q.obj C) ≫
        (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusQIso
            (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))).hom.app C)) ≫
      galoisRestrictionCohomologyEndo.{u, 0} Λ Y kbar σ C := by
  have h := congrArg (fun τ => τ.app (DerivedCategory.Plus.Q.obj C))
    (galoisForgetAction_comp_galoisDerivedGlobalSectionsForgetIso Λ Y kbar σ)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  have hβ : (galoisRestrictionCohomologyNatTrans Λ Y kbar σ).app (DerivedCategory.Plus.Q.obj C) ≫
      (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus.map
        ((Functor.mapDerivedCategoryPlusQIso
          (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))).hom.app C) =
      (etaleModuleGlobalSections.{u, 0} Λ (fieldBaseChange Y kbar)).rightDerivedFunctorPlus.map
        ((Functor.mapDerivedCategoryPlusQIso
          (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))).hom.app C) ≫
        galoisRestrictionCohomologyEndo.{u, 0} Λ Y kbar σ C := by
    rw [galoisRestrictionCohomologyNatTrans_app, Category.assoc, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    exact congrArg (_ ≫ ·) (Category.comp_id _)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hβ).trans (Category.assoc _ _ _).symm)))

end Equivariance

/-! ### The Galois action on `RΓ_c(X_k̄, -)` and `H^i_c(X_k̄, -)` -/

section CompactSupport

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned. -/
local instance (priority := 3000) etaleModules_enoughInjectives_galoisCompact (Λ : Type) [Ring Λ]
    (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- Enough injectives for discrete Galois modules, pinned. -/
local instance (priority := 3000) galoisModules_enoughInjectives_galoisCompact (Λ : Type) [Ring Λ]
    (k : Type u) [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar] :
    EnoughInjectives (GaloisModules Λ k kbar) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsSeparable k kbar]

/-- **The Galois action on `RΓ^Gal_c(X_k̄, K)` is the action of Remark 03UI (2)**: through
`Stacks.EtaleCohomology.galoisCompactSupportForgetIso`, the action of `σ ∈ Aut_k(k̄)` from the
Galois-module structure of `RΓ^Gal_c(X_k̄, K)` is
`Stacks.EtaleCohomology.galoisCompactSupportAction`, induced by `id_{X̄} × Spec σ`. -/
theorem galoisForgetAction_app_comp_galoisCompactSupportForgetIso (σ : kbar ≃ₐ[k] kbar)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    (galoisForgetAction Λ kbar σ).app (galoisDerivedCompactSupport Λ f j kbar K) ≫
        (galoisCompactSupportForgetIso Λ f j kbar K).hom =
      (galoisCompactSupportForgetIso Λ f j kbar K).hom ≫
        galoisCompactSupportAction.{u, 0} Λ f j kbar σ K := by
  have h := galoisForgetAction_app_comp_galoisDerivedGlobalSectionsForgetIso Λ (Over.mk j.toBase)
    kbar σ ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K)
  have e : (galoisCompactSupportForgetIso Λ f j kbar K).hom =
      (galoisDerivedGlobalSectionsForgetIso Λ (Over.mk j.toBase) kbar).hom.app
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K)) ≫
        (etaleModuleGlobalSections.{u, 0} Λ
            (fieldBaseChange (Over.mk j.toBase) kbar)).rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusQIso (etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar))).hom.app
              ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K)) := by
    simp only [galoisCompactSupportForgetIso, galoisCompactSupportForgetNatIso, Iso.app_hom,
      Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Iso.symm_hom, Category.id_comp, Category.comp_id]
  exact (congrArg (_ ≫ ·) e).trans (h.trans (congrArg (· ≫ _) e.symm))

/-- **`H^i_c(X_k̄, K)` as a Galois module carries the action of Remark 03UI (2)**: the action of
`σ` on the Galois module `H^i(RΓ^Gal_c(X_k̄, K))` corresponds, through
`Stacks.EtaleCohomology.galoisCompactSupportGroupForgetIso`, to
`Stacks.EtaleCohomology.galoisCompactSupportGroupAction`. -/
theorem galoisCompactSupportGroupForgetIso_hom_galoisAction (σ : kbar ≃ₐ[k] kbar)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (i : ℤ) :
    (((DerivedCategory.Plus.homologyFunctor (GaloisModules Λ k kbar) i).obj
          (galoisDerivedCompactSupport Λ f j kbar K)).obj.obj.ρ σ).asHom ≫
        (galoisCompactSupportGroupForgetIso Λ f j kbar K i).hom =
      (galoisCompactSupportGroupForgetIso Λ f j kbar K i).hom ≫
        galoisCompactSupportGroupAction.{u, 0} Λ f j kbar σ K i := by
  let M := galoisDerivedCompactSupport Λ f j kbar K
  have hnat := congr_app (Stacks.DerivedFunctor.derivedHomologyIso_naturality
    (galoisModuleAction Λ kbar σ) i) (DerivedCategory.Plus.ι.obj M)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hnat
  have hinv : (galoisModuleAction Λ kbar σ).app
        ((DerivedCategory.homologyFunctor (GaloisModules Λ k kbar) i).obj
          (DerivedCategory.Plus.ι.obj M)) ≫
      (Stacks.DerivedFunctor.derivedHomologyIso (Stacks.Injectives.continuousModuleUnderlying.{0,
          u, u + 1}
        Λ (kbar ≃ₐ[k] kbar)) i).inv.app (DerivedCategory.Plus.ι.obj M) =
      (Stacks.DerivedFunctor.derivedHomologyIso (Stacks.Injectives.continuousModuleUnderlying.{0,
          u, u + 1}
        Λ (kbar ≃ₐ[k] kbar)) i).inv.app (DerivedCategory.Plus.ι.obj M) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
          ((Stacks.DerivedFunctor.mapDerivedNatTrans (galoisModuleAction Λ kbar σ)).app
            (DerivedCategory.Plus.ι.obj M)) := by
    have h := congrArg (fun t => (Stacks.DerivedFunctor.derivedHomologyIso
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)) i).inv.app
        (DerivedCategory.Plus.ι.obj M) ≫ t ≫ (Stacks.DerivedFunctor.derivedHomologyIso
      (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)) i).inv.app
        (DerivedCategory.Plus.ι.obj M)) hnat
    simp only [Category.assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc, Category.comp_id] at h
    exact h.symm
  have hC := congrArg (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
    (galoisForgetAction_app_comp_galoisCompactSupportForgetIso Λ f j kbar σ K)
  rw [Functor.map_comp, Functor.map_comp] at hC
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hinv).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hC))) |>.trans (Category.assoc _ _ _).symm

end CompactSupport

end Stacks.EtaleCohomology

end
