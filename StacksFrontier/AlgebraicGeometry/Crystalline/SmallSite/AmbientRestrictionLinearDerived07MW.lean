module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedPushTransBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientRestrictionDerived
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientRestrictionLinear07MW
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.InjectiveModuleCatGlobalSections
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.RestrictionOfGlobalSections

/-!
# Restricting `A`-linear crystalline cohomology classes to an object of `Cris(X/S)`

Fix a global crystalline situation `(p, (S, I, γ), X)`, write `A = Γ(S, 𝒪_S)`, and let
`B = (U, T, δ)` be an object of `Cris(X/S)`.  The restriction of global cohomology classes
`RΓ(Cris(X/S), K) ⟶ RΓ(T, K_T)` of [Stacks, Equation 07LP] is
`...SmallSite.CrystallineThickening.derivedGlobalSectionsToAmbient`, between derived categories
of abelian groups.  This file builds its `A`-linear counterpart, for complexes of sheaves of
`A`-modules (`...SmallSite.BaseModuleSheaf`), and shows that it is an isomorphism wherever the
abelian one is, at the underlying complex of abelian sheaves.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `CrystallineThickening.AmbientModuleSheaf B` — sheaves of `A`-modules on `T_Zar`.
* `CrystallineThickening.ambientLinearGlobalSections B` — `Γ(T, -)` on them, valued in
  `A`-modules.
* `CrystallineThickening.linearGlobalSectionsToAmbient B` — the `A`-linear restriction
  `Γ(Cris(X/S), G) ⟶ Γ(T, G_T)`.
* `CrystallineThickening.derivedLinearGlobalSectionsToAmbient B` — its derived form
  `RΓ_A(Cris(X/S), K) ⟶ RΓ_A(T, K_T)`.

## Main results

* `rightAcyclic_globalSections_baseForget_obj_of_injective` and
  `CrystallineThickening.rightAcyclic_ambientGlobalSections_ambientForget_obj_of_injective` —
  the underlying abelian sheaf of an injective sheaf of `A`-modules (on `Cris(X/S)`, resp. on
  `T_Zar`) is acyclic for abelian global sections.
* `CrystallineThickening.derivedGlobalSectionsToAmbient_eq_derivedPushTrans` — the abelian
  restriction is the derived transformation of `globalSectionsToAmbient`.
* `CrystallineThickening.isIso_derivedLinearGlobalSectionsToAmbient_app` — **the `A`-linear
  restriction at `K` is an isomorphism if the abelian one is at the complex of abelian sheaves
  underlying `K`.**

## References

* [Stacks Project, Tag 07LP](https://stacks.math.columbia.edu/tag/07LP)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe w₁ w₂ w₃ w₄ w₅ w₆ u

noncomputable section

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### Forgetting the `A`-action on `Cris(X/S)` -/

/-- Forgetting the `A`-action on sheaves of `A`-modules on `Cris(X/S)` preserves finite limits. -/
instance preservesFiniteLimits_baseForget : PreservesFiniteLimits (baseForget S) :=
  Stacks.Cohomology.ModuleSheaf.preservesFiniteLimits_sheafCompose_forget₂.{u + 1, u, _, _}
    (smallTopology S) Γ(S.S.scheme, ⊤)

/-- Forgetting the `A`-action on sheaves of `A`-modules on `Cris(X/S)` preserves finite
colimits. -/
instance preservesFiniteColimits_baseForget : PreservesFiniteColimits (baseForget S) :=
  Stacks.Cohomology.ModuleSheaf.preservesFiniteColimits_sheafCompose_forget₂.{u + 1, u, _, _}
    (smallTopology S) Γ(S.S.scheme, ⊤)

/-- **The underlying abelian sheaf of an injective sheaf of `A`-modules on `Cris(X/S)` is acyclic
for `Γ(Cris(X/S), -)`.** -/
theorem rightAcyclic_globalSections_baseForget_obj_of_injective
    [HasDerivedCategory.{w₁} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w₂} AddCommGrpCat.{u + 1}] (I : BaseModuleSheaf S) [Injective I] :
    (globalSections S).rightAcyclic ((baseForget S).obj I) :=
  Stacks.Cohomology.GlobalSections.rightAcyclic_Γ_sheafCompose_forget₂_obj_of_injective.{w₁, w₂, u}
    (smallTopology S) Γ(S.S.scheme, ⊤) I

namespace CrystallineThickening

variable {S} (B : CrystallineThickening S)

/-! ### Sheaves of `A`-modules on the ambient scheme -/

/-- **Sheaves of `A`-modules on the small Zariski site of the ambient scheme `T` of `B`**, at the
coefficient universe `u + 1`. -/
abbrev AmbientModuleSheaf : Type (u + 2) :=
  Sheaf (Opens.grothendieckTopology B.obj.thickening.target.scheme)
    (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))

/-- Presheaves of `A`-modules on `T_Zar` admit sheafification. -/
instance instHasSheafifyAmbientModuleSheaf :
    HasSheafify (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  Stacks.ModuleSheaf.hasSheafify_moduleCat.{u + 1} _ _

/-- Sheaves of `A`-modules on `T_Zar` have enough injectives. -/
instance instEnoughInjectivesAmbientModuleSheaf : EnoughInjectives (AmbientModuleSheaf B) :=
  Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u, u, u + 2} _ _

/-- `Ext`-groups of abelian sheaves on `T_Zar` exist in `Type (u + 1)`. -/
local instance hasExtAmbient :
    HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology B.obj.thickening.target.scheme) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

/-- **The abelian sheaf underlying a sheaf of `A`-modules on `T_Zar`.** -/
abbrev ambientForget : AmbientModuleSheaf B ⥤
    Sheaf (Opens.grothendieckTopology B.obj.thickening.target.scheme) AddCommGrpCat.{u + 1} :=
  sheafCompose _ (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1})

/-- Forgetting the `A`-action on `T_Zar` preserves finite limits. -/
instance preservesFiniteLimits_ambientForget : PreservesFiniteLimits (ambientForget B) :=
  Stacks.Cohomology.ModuleSheaf.preservesFiniteLimits_sheafCompose_forget₂.{u + 1, u, _, _}
    (Opens.grothendieckTopology B.obj.thickening.target.scheme) Γ(S.S.scheme, ⊤)

/-- Forgetting the `A`-action on `T_Zar` preserves finite colimits. -/
instance preservesFiniteColimits_ambientForget : PreservesFiniteColimits (ambientForget B) :=
  Stacks.Cohomology.ModuleSheaf.preservesFiniteColimits_sheafCompose_forget₂.{u + 1, u, _, _}
    (Opens.grothendieckTopology B.obj.thickening.target.scheme) Γ(S.S.scheme, ⊤)

/-- Forgetting the `A`-action on `T_Zar` reflects finite limits. -/
instance reflectsFiniteLimits_ambientForget : ReflectsFiniteLimits (ambientForget B) :=
  reflectsFiniteLimits_of_reflectsIsomorphisms _

/-- Forgetting the `A`-action on `T_Zar` reflects finite colimits. -/
instance reflectsFiniteColimits_ambientForget : ReflectsFiniteColimits (ambientForget B) where
  reflects _ _ _ := reflectsColimitsOfShape_of_reflectsIsomorphisms

/-- `G ↦ G_T` on sheaves of `A`-modules preserves finite limits: forgetting the `A`-action
after it is the exact abelian restriction after forgetting, and forgetting reflects them. -/
instance preservesFiniteLimits_linearAmbientRestriction :
    PreservesFiniteLimits (linearAmbientRestriction B) :=
  have : PreservesFiniteLimits (linearAmbientRestriction B ⋙ ambientForget B) :=
    inferInstanceAs (PreservesFiniteLimits (baseForget S ⋙ abelianAmbientRestriction B))
  preservesFiniteLimits_of_reflects_of_preserves _ (ambientForget B)

/-- `G ↦ G_T` on sheaves of `A`-modules preserves finite colimits. -/
instance preservesFiniteColimits_linearAmbientRestriction :
    PreservesFiniteColimits (linearAmbientRestriction B) :=
  have : PreservesFiniteColimits (linearAmbientRestriction B ⋙ ambientForget B) :=
    inferInstanceAs (PreservesFiniteColimits (baseForget S ⋙ abelianAmbientRestriction B))
  preservesFiniteColimits_of_reflects_of_preserves _ (ambientForget B)

/-- **The underlying abelian sheaf of an injective sheaf of `A`-modules on `T_Zar` is acyclic for
`Γ(T, -)`.** -/
theorem rightAcyclic_ambientGlobalSections_ambientForget_obj_of_injective
    [HasDerivedCategory.{w₁}
      (Sheaf (Opens.grothendieckTopology B.obj.thickening.target.scheme) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w₂} AddCommGrpCat.{u + 1}] (I : AmbientModuleSheaf B) [Injective I] :
    (ambientGlobalSections B).rightAcyclic ((ambientForget B).obj I) :=
  Stacks.Cohomology.GlobalSections.rightAcyclic_Γ_sheafCompose_forget₂_obj_of_injective.{w₁, w₂,
    u + 1} (Opens.grothendieckTopology B.obj.thickening.target.scheme) Γ(S.S.scheme, ⊤) I

/-! ### `A`-linear global sections on the ambient scheme -/

/-- `A`-modules at the universe `u + 1` have the limits indexed by the opens of `T`. -/
instance instHasLimitsOfShapeAmbientModuleCat :
    HasLimitsOfShape (B.obj.thickening.target.scheme.Opens)ᵒᵖ
      (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  have := ModuleCat.hasLimitsOfSize.{u, u, u + 1} (R := Γ(S.S.scheme, ⊤))
  inferInstance

/-- Forgetting the `A`-action preserves the limits indexed by the opens of `T`. -/
instance instPreservesLimitsOfShapeAmbientForget₂ :
    PreservesLimitsOfShape (B.obj.thickening.target.scheme.Opens)ᵒᵖ
      (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}) :=
  have := ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{u, u, u + 1}
    (R := Γ(S.S.scheme, ⊤))
  inferInstance

/-- **`Γ(T, -)` on sheaves of `A`-modules on `T_Zar`**, valued in `A`-modules. -/
abbrev ambientLinearGlobalSections : AmbientModuleSheaf B ⥤ ModuleCat.{u + 1} Γ(S.S.scheme, ⊤) :=
  Sheaf.Γ _ _

/-- `Γ(T, -)` over `A` is additive, being a right adjoint. -/
instance additive_ambientLinearGlobalSections : (ambientLinearGlobalSections B).Additive :=
  have : PreservesLimitsOfSize.{0, 0} (ambientLinearGlobalSections B) :=
    (constantSheafΓAdj (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))).rightAdjoint_preservesLimits
  Functor.additive_of_preserves_binary_products _

/-- The comparison of `Γ_A(T, N)` with the abelian `Γ(T, -)` of the abelian sheaf underlying
`N`: both are limits of the sections. -/
def ambientLinearGlobalSectionsForgetIsoApp (N : AmbientModuleSheaf B) :
    (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}).obj
        ((ambientLinearGlobalSections B).obj N) ≅
      (ambientGlobalSections B).obj ((ambientForget B).obj N) :=
  (isLimitOfPreserves (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1})
    (Sheaf.isLimitConeΓ N)).conePointUniqueUpToIso (Sheaf.isLimitConeΓ ((ambientForget B).obj N))

/-- `ambientLinearGlobalSectionsForgetIsoApp` commutes with restriction to an open. -/
theorem ambientLinearGlobalSectionsForgetIsoApp_hom_ΓRes (N : AmbientModuleSheaf B)
    (W : (B.obj.thickening.target.scheme.Opens)ᵒᵖ) :
    (ambientLinearGlobalSectionsForgetIsoApp B N).hom ≫
        Sheaf.ΓRes ((ambientForget B).obj N) W =
      (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}).map
        (Sheaf.ΓRes N W) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ W

/-- **`Γ_A(T, -)` forgets to the abelian `Γ(T, -)`**, naturally. -/
def ambientLinearGlobalSectionsForgetIso :
    ambientLinearGlobalSections B ⋙
        forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1} ≅
      ambientForget B ⋙ ambientGlobalSections B :=
  NatIso.ofComponents (ambientLinearGlobalSectionsForgetIsoApp B)
    (fun {N N'} f => by
      refine (Sheaf.isLimitConeΓ ((ambientForget B).obj N')).hom_ext fun W => ?_
      change ((forget₂ _ _).map ((ambientLinearGlobalSections B).map f) ≫
          (ambientLinearGlobalSectionsForgetIsoApp B N').hom) ≫ Sheaf.ΓRes _ W =
        ((ambientLinearGlobalSectionsForgetIsoApp B N).hom ≫
          (ambientGlobalSections B).map ((ambientForget B).map f)) ≫ Sheaf.ΓRes _ W
      simp only [Category.assoc, ambientLinearGlobalSectionsForgetIsoApp_hom_ΓRes,
        Sheaf.ΓRes_naturality]
      simp only [← Category.assoc, ambientLinearGlobalSectionsForgetIsoApp_hom_ΓRes]
      exact ((forget₂ _ _).map_comp _ _).symm.trans
        ((congrArg (forget₂ _ _).map (Sheaf.ΓRes_naturality f W)).trans
          ((forget₂ _ _).map_comp _ _)))

/-! ### The `A`-linear restriction of global sections -/

/-- The cone over the sections of `G_T` whose point is `Γ_A(Cris(X/S), G)` and whose components
are the restrictions to the objects `B|_W`. -/
def linearGlobalSectionsToAmbientCone (G : BaseModuleSheaf S) :
    Cone ((linearAmbientRestriction B).obj G).obj where
  pt := (baseLinearGlobalSections S).obj G
  π :=
    { app W := Sheaf.ΓRes G (op (B.restrictOpen W.unop))
      naturality W W' f := by
        refine (Category.id_comp _).trans ?_
        exact ((Sheaf.coneΓ G).w ((restrictOpenFunctor B).op.map f)).symm }

/-- The component at `G` of `linearGlobalSectionsToAmbient`. -/
def linearGlobalSectionsToAmbientApp (G : BaseModuleSheaf S) :
    (baseLinearGlobalSections S).obj G ⟶
      (ambientLinearGlobalSections B).obj ((linearAmbientRestriction B).obj G) :=
  (Sheaf.isLimitConeΓ ((linearAmbientRestriction B).obj G)).lift
    (linearGlobalSectionsToAmbientCone B G)

/-- `linearGlobalSectionsToAmbientApp` followed by the restriction to an open `W` of `T` is the
restriction to `B|_W`. -/
@[reassoc]
theorem linearGlobalSectionsToAmbientApp_ΓRes (G : BaseModuleSheaf S)
    (W : (B.obj.thickening.target.scheme.Opens)ᵒᵖ) :
    linearGlobalSectionsToAmbientApp B G ≫ Sheaf.ΓRes ((linearAmbientRestriction B).obj G) W =
      Sheaf.ΓRes G (op (B.restrictOpen W.unop)) :=
  (Sheaf.isLimitConeΓ ((linearAmbientRestriction B).obj G)).fac _ W

/-- **The `A`-linear restriction `Γ(Cris(X/S), G) ⟶ Γ(T, G_T)`**, for sheaves of `A`-modules:
a global section is sent to its values at the restrictions `B|_W`. -/
def linearGlobalSectionsToAmbient :
    baseLinearGlobalSections S ⟶ linearAmbientRestriction B ⋙ ambientLinearGlobalSections B where
  app G := linearGlobalSectionsToAmbientApp B G
  naturality G G' φ := by
    refine (Sheaf.isLimitConeΓ ((linearAmbientRestriction B).obj G')).hom_ext fun W => ?_
    change ((baseLinearGlobalSections S).map φ ≫ linearGlobalSectionsToAmbientApp B G') ≫
        Sheaf.ΓRes _ W =
      (linearGlobalSectionsToAmbientApp B G ≫
        (ambientLinearGlobalSections B).map ((linearAmbientRestriction B).map φ)) ≫
        Sheaf.ΓRes _ W
    have h1 := linearGlobalSectionsToAmbientApp_ΓRes B G' W
    have h2 := linearGlobalSectionsToAmbientApp_ΓRes B G W
    have h3 := Sheaf.ΓRes_naturality φ (op (B.restrictOpen W.unop))
    have h4 := Sheaf.ΓRes_naturality ((linearAmbientRestriction B).map φ) W
    rw [Category.assoc, h1, Category.assoc, h4, ← Category.assoc, h2]
    exact h3

/-- The `A`-linear restriction followed by the restriction to an open `W` of `T` is the restriction
to `B|_W`. -/
@[reassoc]
theorem linearGlobalSectionsToAmbient_app_ΓRes (G : BaseModuleSheaf S)
    (W : (B.obj.thickening.target.scheme.Opens)ᵒᵖ) :
    (linearGlobalSectionsToAmbient B).app G ≫ Sheaf.ΓRes ((linearAmbientRestriction B).obj G) W =
      Sheaf.ΓRes G (op (B.restrictOpen W.unop)) :=
  linearGlobalSectionsToAmbientApp_ΓRes B G W

/-- The abelian restriction followed by the restriction to an open `W` of `T` is the restriction
to `B|_W`. -/
@[reassoc]
theorem globalSectionsToAmbient_app_ΓRes (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (W : (B.obj.thickening.target.scheme.Opens)ᵒᵖ) :
    (globalSectionsToAmbient B).app G ≫ Sheaf.ΓRes ((abelianAmbientRestriction B).obj G) W =
      Sheaf.ΓRes G (op (B.restrictOpen W.unop)) := by
  rw [← Sheaf.ΓNatIsoLim_hom_app_comp_π, ← Sheaf.ΓNatIsoLim_hom_app_comp_π]
  exact globalSectionsToAmbient_app_comp B G W.unop

/-- **The `A`-linear restriction forgets to the abelian one**: the square formed with the two
identifications of `A`-linear global sections with abelian ones commutes. -/
theorem forget₂_map_linearGlobalSectionsToAmbient_app (G : BaseModuleSheaf S) :
    (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}).map
        ((linearGlobalSectionsToAmbient B).app G) ≫
      (ambientLinearGlobalSectionsForgetIso B).hom.app ((linearAmbientRestriction B).obj G) =
      (baseLinearGlobalSectionsForgetIso S).hom.app G ≫
        (globalSectionsToAmbient B).app ((baseForget S).obj G) := by
  refine (Sheaf.isLimitConeΓ ((abelianAmbientRestriction B).obj ((baseForget S).obj G))).hom_ext
    fun W => ?_
  have h1 := ambientLinearGlobalSectionsForgetIsoApp_hom_ΓRes B
    ((linearAmbientRestriction B).obj G) W
  have h2 := linearGlobalSectionsToAmbient_app_ΓRes B G W
  have h3 := globalSectionsToAmbient_app_ΓRes B ((baseForget S).obj G) W
  have h4 := baseLinearGlobalSectionsForgetIsoApp_hom_ΓRes S G (op (B.restrictOpen W.unop))
  exact (Category.assoc _ _ _).trans ((whisker_eq _ h1).trans
    (((forget₂ _ _).map_comp _ _).symm.trans ((congrArg (forget₂ _ _).map h2).trans
      (h4.symm.trans ((whisker_eq _ h3).symm.trans (Category.assoc _ _ _).symm)))))

/-- The identification of `G ↦ G_T` on sheaves of `A`-modules, followed by forgetting the
`A`-action, with forgetting followed by the abelian `G ↦ G_T`; the two functors are equal. -/
def linearAmbientRestrictionForgetHom :
    linearAmbientRestriction B ⋙ ambientForget B ⟶ baseForget S ⋙ abelianAmbientRestriction B :=
  eqToHom (linearAmbientRestriction_comp_forget B)

/-- `linearAmbientRestrictionForgetHom` is invertible. -/
instance isIso_linearAmbientRestrictionForgetHom : IsIso (linearAmbientRestrictionForgetHom B) :=
  inferInstanceAs (IsIso (eqToHom _))

/-- `forget₂_map_linearGlobalSectionsToAmbient_app` in the form of the compatibility hypothesis of
`Stacks.Cohomology.DerivedBaseChangePlus.derivedPushTrans_baseChange`. -/
theorem forget₂_map_linearGlobalSectionsToAmbient_app' (G : BaseModuleSheaf S) :
    (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}).map
        ((linearGlobalSectionsToAmbient B).app G) ≫
      (ambientLinearGlobalSectionsForgetIso B).hom.app ((linearAmbientRestriction B).obj G) ≫
        (ambientGlobalSections B).map
          ((linearAmbientRestrictionForgetHom B).app G) =
      (baseLinearGlobalSectionsForgetIso S).hom.app G ≫
        (globalSectionsToAmbient B).app ((baseForget S).obj G) := by
  refine Eq.trans ?_ (forget₂_map_linearGlobalSectionsToAmbient_app B G)
  refine whisker_eq _ ?_
  simp only [linearAmbientRestrictionForgetHom, eqToHom_app, eqToHom_map]
  exact Category.comp_id _

/-! ### The derived `A`-linear restriction -/

section Derived

variable [HasDerivedCategory.{w₁} (BaseModuleSheaf S)]
  [HasDerivedCategory.{w₂} (AmbientModuleSheaf B)]
  [HasDerivedCategory.{w₃} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{w₄} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₅}
    (Sheaf (Opens.grothendieckTopology B.obj.thickening.target.scheme) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₆} AddCommGrpCat.{u + 1}]

/-- **The `A`-linear restriction of global cohomology classes to `T`**,
`RΓ_A(Cris(X/S), K) ⟶ RΓ_A(T, K_T)`: the derived transformation of
`linearGlobalSectionsToAmbient`. -/
def derivedLinearGlobalSectionsToAmbient :
    derivedBaseLinearGlobalSectionsFunctor S ⟶
      (linearAmbientRestriction B).mapDerivedCategoryPlus ⋙
        (ambientLinearGlobalSections B).rightDerivedFunctorPlus :=
  Stacks.Cohomology.DerivedBaseChangePlus.derivedPushTrans _ (linearGlobalSectionsToAmbient B)

omit [HasDerivedCategory (BaseModuleSheaf S)] [HasDerivedCategory (AmbientModuleSheaf B)]
  [HasDerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))] in
/-- **The abelian restriction of global cohomology classes is the derived transformation of
`globalSectionsToAmbient`.** -/
theorem derivedGlobalSectionsToAmbient_eq_derivedPushTrans :
    derivedGlobalSectionsToAmbient B =
      Stacks.Cohomology.DerivedBaseChangePlus.derivedPushTrans _ (globalSectionsToAmbient B) :=
  rfl

/-- **The `A`-linear restriction is an isomorphism where the abelian one is.**  If the abelian
restriction `RΓ(Cris(X/S), K_ab) ⟶ RΓ(T, (K_ab)_T)` is an isomorphism at the complex of abelian
sheaves underlying `K`, the `A`-linear restriction is an isomorphism at `K`: forgetting the
`A`-module structure carries the latter to the former up to the base change isomorphisms, and
forgetting is conservative on `D⁺`. -/
theorem isIso_derivedLinearGlobalSectionsToAmbient_app
    (X : DerivedCategory.Plus (BaseModuleSheaf S))
    (h : IsIso ((derivedGlobalSectionsToAmbient B).app
      ((baseForget S).mapDerivedCategoryPlus.obj X))) :
    IsIso ((derivedLinearGlobalSectionsToAmbient B).app X) := by
  have hsq := Stacks.Cohomology.DerivedBaseChangePlus.derivedPushTrans_baseChange
    (linearAmbientRestriction B) (ambientForget B) (baseForget S) (abelianAmbientRestriction B)
    (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1})
    (linearGlobalSectionsToAmbient B) (globalSectionsToAmbient B)
    (baseLinearGlobalSectionsForgetIso S).hom (ambientLinearGlobalSectionsForgetIso B).hom
    (linearAmbientRestrictionForgetHom B)
    (forget₂_map_linearGlobalSectionsToAmbient_app' B) X
  have h₀ : IsIso ((Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus
      (baseLinearGlobalSections S) (globalSections S)
      (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}) (baseForget S)
      (baseLinearGlobalSectionsForgetIso S).hom).app X) := by
    have e := Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlusIso_inv (baseForget S)
      (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1})
      (baseLinearGlobalSections S) (globalSections S) (baseLinearGlobalSectionsForgetIso S).symm
      (fun I _ => rightAcyclic_globalSections_baseForget_obj_of_injective S I)
    rw [Iso.symm_inv] at e
    rw [← e]
    infer_instance
  have h₁ : IsIso ((Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus
      (ambientLinearGlobalSections B) (ambientGlobalSections B)
      (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}) (ambientForget B)
      (ambientLinearGlobalSectionsForgetIso B).hom).app
        ((linearAmbientRestriction B).mapDerivedCategoryPlus.obj X)) := by
    have e := Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlusIso_inv
      (ambientForget B) (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1})
      (ambientLinearGlobalSections B) (ambientGlobalSections B)
      (ambientLinearGlobalSectionsForgetIso B).symm
      (fun I _ => rightAcyclic_ambientGlobalSections_ambientForget_obj_of_injective B I)
    rw [Iso.symm_inv] at e
    rw [← e]
    infer_instance
  have h₂ := Stacks.Cohomology.DerivedBaseChangePlus.isIso_derivedCompTrans_app
    (linearAmbientRestriction B) (ambientForget B) (baseForget S) (abelianAmbientRestriction B)
    (linearAmbientRestrictionForgetHom B) X
  rw [← derivedGlobalSectionsToAmbient_eq_derivedPushTrans] at hsq
  have : IsIso ((forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))
      AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus.map
        ((derivedLinearGlobalSectionsToAmbient B).app X)) := by
    change IsIso ((forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))
      AddCommGrpCat.{u + 1}).mapDerivedCategoryPlus.map
        ((Stacks.Cohomology.DerivedBaseChangePlus.derivedPushTrans _
          (linearGlobalSectionsToAmbient B)).app X))
    have h' := (congrArg IsIso hsq).mpr (@IsIso.comp_isIso _ _ _ _ _ _ _ h₀ h)
    let g := (Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus
          (ambientLinearGlobalSections B) (ambientGlobalSections B)
          (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}) (ambientForget B)
          (ambientLinearGlobalSectionsForgetIso B).hom).app
            ((linearAmbientRestriction B).mapDerivedCategoryPlus.obj X) ≫
          (ambientGlobalSections B).rightDerivedFunctorPlus.map
            ((Stacks.Cohomology.DerivedBaseChangePlus.derivedCompTrans
              (linearAmbientRestriction B) (ambientForget B) (baseForget S)
              (abelianAmbientRestriction B) (linearAmbientRestrictionForgetHom B)).app X)
    have : IsIso g := @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ (Functor.map_isIso _ _)
    exact IsIso.of_isIso_comp_right _ g
  exact (Stacks.Cohomology.isIso_forget₂_mapDerivedCategoryPlus_map_iff _).1 this

end Derived

end CrystallineThickening

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
