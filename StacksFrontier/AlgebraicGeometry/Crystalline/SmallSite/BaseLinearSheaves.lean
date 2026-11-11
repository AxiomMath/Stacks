module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleCohomology

/-!
# Sheaves of `A`-modules on the small crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] and write
`A = Γ(S, 𝒪_S)`.  The de Rham complex `F ⊗_{𝒪_{X/S}} Ω^•_{X/S}` of a crystal is not a complex of
`𝒪_{X/S}`-modules — its differentials are only `A`-linear — so the assertion
`RΓ(Cris(X/S), F) = RΓ(Cris(X/S), F ⊗ Ω^•_{X/S})` *in `D(A)`* has to be formed in a category of
sheaves of `A`-modules on `Cris(X/S)`.  This file sets that category up.

The category is `Sheaf (smallTopology S) (ModuleCat A)`, the sheaves on `Cris(X/S)` with values
in `A`-modules.  By `Stacks.SheafOfModules.ConstantRing.sheafifiedConstRingModulesEquivalence` this
is, on a site where the constant sheaf of rings exists, the category of sheaves of modules over the
constant sheaf of rings `A̲`; the `ModuleCat`-valued form is used because the constant sheaf of
rings in `RingCat.{u}` is not available on `Cris(X/S)` (the site has its objects in
`Type (u + 1)`), while `ModuleCat.{u + 1} A`-valued sheaves exist at the coefficient universe
`u + 1` of the abelian theory of `SmallSite/Cohomology.lean`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `BaseModuleSheaf S` — sheaves of `A`-modules on `Cris(X/S)`, at the coefficient universe `u + 1`.
* `baseForget S` — the underlying abelian sheaf, landing in the coefficient category
  `Sheaf (smallTopology S) AddCommGrpCat.{u + 1}` of the abelian theory.
* `baseLinearGlobalSections S` — **`Γ(Cris(X/S), -)` on sheaves of `A`-modules**, valued in
  `A`-modules (Mathlib's `CategoryTheory.Sheaf.Γ`, the right adjoint of the constant sheaf
  functor).
* `derivedBaseLinearGlobalSectionsFunctor S` — **`RΓ_A(Cris(X/S), -)`**, its right derived functor
  `D⁺(Mod_A(Cris(X/S))) ⥤ D⁺(Mod_A)`, and `plusOfCochainComplex` the object of the source of a
  complex concentrated in degrees `≥ 0`.
* `toBaseModuleSheaf S` — a sheaf of `𝒪_{X/S}`-modules (at the raised module universe of
  `SmallSite/ModuleCohomology.lean`) read as a sheaf of `A`-modules through
  `...SmallSite.baseSmulRingHom`.

## Main results

* `instEnoughInjectivesBaseModuleSheaf` — the category is abelian (Mathlib's `sheafIsAbelian`)
  and has enough injectives, so `RΓ_A` exists.
* `baseLinearGlobalSectionsForgetIso` — **`Γ_A` forgets to the abelian `Γ`**:
  `baseLinearGlobalSections S ⋙ forget₂ ≅ baseForget S ⋙ globalSections S`.
* `toBaseModuleSheaf_comp_baseForget` — the abelian sheaf underlying `toBaseModuleSheaf M` is
  `toAbelianSheaf M`, on the nose.
* `toBaseModuleSheafGlobalSectionsIso` — **`Γ_A` of `M` read as a sheaf of `A`-modules is the
  module-valued global sections of `SmallSite/ModuleCohomology.lean`**:
  `toBaseModuleSheaf S ⋙ baseLinearGlobalSections S ≅ baseModuleGlobalSections S`, as
  `A`-modules.  This is what lets `RΓ_A(Cris(X/S), -)` of a complex be compared with
  `...SmallSite.moduleULiftDerivedGlobalSections`.

## What is not proved here

Exactness of `baseForget S` and of `toBaseModuleSheaf S`, and the comparison of the derived
functors along them (that injective sheaves of `𝒪_{X/S}`-modules, and injective sheaves of
`A`-modules, are acyclic for `Γ_A`), are not proved in this file; the comparison is in
`SmallSite/CrystalDeRhamLinearDerived07MW.lean`.

## References

* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
* [Stacks Project, Tag 07MW](https://stacks.math.columbia.edu/tag/07MW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe w w' r v u

noncomputable section

/-- `Λ`-modules in a universe into which `Λ` embeds form a Grothendieck abelian category: AB5 is
reflected by the exact forgetful functor to abelian groups. -/
private theorem isGrothendieckAbelian_moduleCat_of_univLE (Λ : Type r) [Ring Λ]
    [UnivLE.{r, v}] : IsGrothendieckAbelian.{v} (ModuleCat.{v} Λ) := by
  refine { ab5OfSize := ⟨fun D _ _ => ?_⟩ }
  exact HasExactColimitsOfShape.domain_of_functor D (forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v})

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- A linear map between the carriers of two bundled `A`-modules, as a morphism of `ModuleCat`.
The module structures are read off the bundled objects, so none has to be synthesized on a carrier
that has been unfolded (the carrier of a restriction of scalars, for instance). -/
abbrev moduleCatHomMk {M N : ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)}
    (f : M →ₗ[Γ(S.S.scheme, ⊤)] N) : M ⟶ N :=
  ModuleCat.ofHom f

/-! ### The category -/

/-- **Sheaves of `A`-modules on the small crystalline site**, `A = Γ(S, 𝒪_S)`, with the sections
in `Type (u + 1)`: the sheaves on `Cris(X/S)` with values in `ModuleCat.{u + 1} A`. -/
abbrev BaseModuleSheaf : Type (u + 2) :=
  Sheaf (smallTopology S) (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))

/-- Presheaves of `A`-modules on the small crystalline site admit sheafification, at the
coefficient universe `u + 1` of the objects of the site. -/
instance instHasSheafifyBaseModuleSheaf :
    HasSheafify (smallTopology S) (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  Stacks.ModuleSheaf.hasSheafify_moduleCat.{u + 1} _ _

/-- Forgetting the `A`-action carries sheaves of `A`-modules to abelian sheaves. -/
instance instHasSheafComposeForget₂ : (smallTopology S).HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}) :=
  Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} _ _

/-- **Sheaves of `A`-modules on the small crystalline site have enough injectives**: they form a
Grothendieck abelian category at the universe `u + 1` of the objects of the site. -/
instance instEnoughInjectivesBaseModuleSheaf : EnoughInjectives (BaseModuleSheaf S) :=
  have := isGrothendieckAbelian_moduleCat_of_univLE.{u, u + 1} Γ(S.S.scheme, ⊤)
  Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u, u + 1, u + 2} (smallTopology S)
    (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))

/-- **The abelian sheaf underlying a sheaf of `A`-modules.** -/
abbrev baseForget : BaseModuleSheaf S ⥤ Sheaf (smallTopology S) AddCommGrpCat.{u + 1} :=
  sheafCompose (smallTopology S)
    (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1})

/-- Forgetting the `A`-action is additive. -/
instance instAdditiveBaseForget : (baseForget S).Additive where
  map_add := by intros; rfl

/-! ### `Γ(Cris(X/S), -)` and `RΓ(Cris(X/S), -)` over `A` -/

/-- `A`-modules at the universe `u + 1` have all limits of size `u + 1`.  Recorded with the
universes pinned, since instance search is otherwise stuck on `u + 1 =?= max (u + 1) ?v`. -/
instance instHasLimitsModuleCat : HasLimits (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1}

/-- `A`-modules at the universe `u + 1` have the limits indexed by `Cris(X/S)`. -/
instance instHasLimitsOfShapeModuleCat :
    HasLimitsOfShape (CrystallineThickening S)ᵒᵖ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  have := ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1} (R := Γ(S.S.scheme, ⊤))
  inferInstance

/-- Forgetting the `A`-action preserves the limits indexed by `Cris(X/S)`. -/
instance instPreservesLimitsOfShapeForget₂ : PreservesLimitsOfShape (CrystallineThickening S)ᵒᵖ
    (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}) :=
  have := ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{u, u + 1, u + 1}
    (R := Γ(S.S.scheme, ⊤))
  inferInstance

/-- **The global sections `Γ(Cris(X/S), -)` of sheaves of `A`-modules**, valued in `A`-modules:
Mathlib's `CategoryTheory.Sheaf.Γ`, the right adjoint of the constant sheaf functor. -/
abbrev baseLinearGlobalSections :
    BaseModuleSheaf S ⥤ ModuleCat.{u + 1} Γ(S.S.scheme, ⊤) :=
  Sheaf.Γ (smallTopology S) (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))

/-- `Γ(Cris(X/S), -)` over `A` is additive, being a right adjoint. -/
instance instAdditiveBaseLinearGlobalSections : (baseLinearGlobalSections S).Additive :=
  have : PreservesLimitsOfSize.{0, 0} (baseLinearGlobalSections S) :=
    (constantSheafΓAdj (smallTopology S)
      (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))).rightAdjoint_preservesLimits
  Functor.additive_of_preserves_binary_products _

/-- The comparison of `Γ_A(N)` with the abelian `Γ` of the abelian sheaf underlying `N`: both
are limits of the sections over the objects of `Cris(X/S)` (`CategoryTheory.Sheaf.isLimitConeΓ`),
and forgetting the `A`-action preserves those limits. -/
def baseLinearGlobalSectionsForgetIsoApp (N : BaseModuleSheaf S) :
    (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}).obj
        ((baseLinearGlobalSections S).obj N) ≅
      (globalSections S).obj ((baseForget S).obj N) :=
  (isLimitOfPreserves (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1})
    (Sheaf.isLimitConeΓ N)).conePointUniqueUpToIso (Sheaf.isLimitConeΓ ((baseForget S).obj N))

/-- `baseLinearGlobalSectionsForgetIsoApp` commutes with restriction to an object. -/
theorem baseLinearGlobalSectionsForgetIsoApp_hom_ΓRes (N : BaseModuleSheaf S)
    (X : (CrystallineThickening S)ᵒᵖ) :
    (baseLinearGlobalSectionsForgetIsoApp S N).hom ≫ Sheaf.ΓRes ((baseForget S).obj N) X =
      (forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1}).map
        (Sheaf.ΓRes N X) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ X

/-- **`Γ_A` forgets to the abelian `Γ`**: the abelian group underlying the `A`-module
`Γ(Cris(X/S), N)` is the global sections of the abelian sheaf underlying `N`, naturally in `N`. -/
def baseLinearGlobalSectionsForgetIso :
    baseLinearGlobalSections S ⋙
        forget₂ (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) AddCommGrpCat.{u + 1} ≅
      baseForget S ⋙ globalSections S :=
  NatIso.ofComponents (baseLinearGlobalSectionsForgetIsoApp S)
    (fun {N N'} f => by
      refine (Sheaf.isLimitConeΓ ((baseForget S).obj N')).hom_ext fun X => ?_
      change ((forget₂ _ _).map ((baseLinearGlobalSections S).map f) ≫
          (baseLinearGlobalSectionsForgetIsoApp S N').hom) ≫ Sheaf.ΓRes _ X =
        ((baseLinearGlobalSectionsForgetIsoApp S N).hom ≫
          (globalSections S).map ((baseForget S).map f)) ≫ Sheaf.ΓRes _ X
      simp only [Category.assoc, baseLinearGlobalSectionsForgetIsoApp_hom_ΓRes,
        Sheaf.ΓRes_naturality]
      simp only [← Category.assoc, baseLinearGlobalSectionsForgetIsoApp_hom_ΓRes]
      exact ((forget₂ _ _).map_comp _ _).symm.trans
        ((congrArg (forget₂ _ _).map (Sheaf.ΓRes_naturality f X)).trans
          ((forget₂ _ _).map_comp _ _)))

section Derived

variable [HasDerivedCategory.{w} (BaseModuleSheaf S)]
  [HasDerivedCategory.{w'} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]

/-- **`RΓ_A(Cris(X/S), -)`**: the right derived functor of the `A`-module-valued global sections,
between bounded below derived categories. -/
def derivedBaseLinearGlobalSectionsFunctor :
    DerivedCategory.Plus (BaseModuleSheaf S) ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  (baseLinearGlobalSections S).rightDerivedFunctorPlus

/-- A complex of sheaves of `A`-modules concentrated in degrees `≥ 0`, as an object of the bounded
below derived category. -/
def plusOfCochainComplex (K : CochainComplex (BaseModuleSheaf S) ℤ) [K.IsStrictlyGE 0] :
    DerivedCategory.Plus (BaseModuleSheaf S) :=
  DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient (BaseModuleSheaf S)).obj
    ⟨K, ⟨0, inferInstance⟩⟩)

end Derived

/-! ### Sheaves of `𝒪_{X/S}`-modules as sheaves of `A`-modules -/

/-- The action of `A` on the abelian sheaf underlying a sheaf of `𝒪_{X/S}`-modules, through
`...SmallSite.baseSmulRingHom`. -/
def toAbelianSheafBaseAction (M : ModuleSheaf S) :
    Γ(S.S.scheme, ⊤) →+* End ((toAbelianSheaf S).obj M) :=
  (Stacks.ModuleCatLift.mapEndRingHom (toAbelianSheaf S) M).comp (baseSmulRingHom S M)

/-- **A sheaf of `𝒪_{X/S}`-modules read as a sheaf of `A`-modules**, `A` acting through the
structure morphisms `T ⟶ S`. -/
def toBaseModuleSheaf : ModuleSheaf S ⥤ BaseModuleSheaf S where
  obj M := Stacks.ModuleCatLift.sheafOfEndAction Γ(S.S.scheme, ⊤) (smallTopology S)
    ((toAbelianSheaf S).obj M) (toAbelianSheafBaseAction S M)
  map {M M'} f := ObjectProperty.homMk (Stacks.ModuleCatLift.ofEndActionMap Γ(S.S.scheme, ⊤) _ _
    ((toAbelianSheaf S).map f).hom fun a => by
      change ((toAbelianSheaf S).map (baseSmul S a M) ≫ (toAbelianSheaf S).map f).hom = _
      rw [← Functor.map_comp, baseSmul, ← Stacks.Cohomology.SiteModules.comp_globalSmul,
        Functor.map_comp]
      rfl)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The abelian sheaf underlying `toBaseModuleSheaf M` is the abelian sheaf underlying `M`**, on
the nose. -/
theorem toBaseModuleSheaf_comp_baseForget :
    toBaseModuleSheaf S ⋙ baseForget S = toAbelianSheaf S :=
  rfl

/-- An element of `A` acts on the sections of `toBaseModuleSheaf M` over `(U, T, δ)` as its
pullback to `Γ(T, 𝒪_T)`. -/
theorem toBaseModuleSheaf_smul (M : ModuleSheaf S) (X : (CrystallineThickening S)ᵒᵖ)
    (a : Γ(S.S.scheme, ⊤)) (x : ((toBaseModuleSheaf S).obj M).obj.obj X) :
    a • x = (show M.val.obj X from (baseRingHom S a).val X • (show M.val.obj X from x)) :=
  baseSmul_val_app S a M X x

/-- The cone over the sections of `toBaseModuleSheaf M` whose point is the module-valued global
sections `baseModuleGlobalSections M` and whose components evaluate a compatible family. -/
def baseModuleGlobalSectionsCone (M : ModuleSheaf S) :
    Cone ((toBaseModuleSheaf S).obj M).obj where
  pt := (baseModuleGlobalSections S).obj M
  π :=
    { app X := moduleCatHomMk S (M := (baseModuleGlobalSections S).obj M)
        (N := ((toBaseModuleSheaf S).obj M).obj.obj X)
        { toFun s := (show M.sections from s).eval X
          map_add' _ _ := rfl
          map_smul' a s := (toBaseModuleSheaf_smul S M X a _).symm }
      naturality X Y f := by
        ext s
        exact ((show M.sections from s).2 f).symm }

/-- **The module-valued global sections are the limit of the sections**, as `A`-modules. -/
def isLimitBaseModuleGlobalSectionsCone (M : ModuleSheaf S) :
    IsLimit (baseModuleGlobalSectionsCone S M) where
  lift c := moduleCatHomMk S (M := c.pt) (N := (baseModuleGlobalSections S).obj M) {
      toFun x := (show (baseModuleGlobalSections S).obj M from
        M.val.sectionsMk (fun X => (c.π.app X).hom x)
          (fun _ _ f => ConcreteCategory.congr_hom (c.w f) x))
      map_add' x y := PresheafOfModules.sections_ext _ _ fun X => map_add (c.π.app X).hom x y
      map_smul' a x := PresheafOfModules.sections_ext _ _ fun X =>
        ((c.π.app X).hom.map_smul a x).trans (toBaseModuleSheaf_smul S M X a _) }
  fac c X := by
    ext x
    rfl
  uniq c m hm := by
    ext x
    refine PresheafOfModules.sections_ext _ _ fun X => ?_
    exact ConcreteCategory.congr_hom (hm X) x

/-- Evaluating a global section commutes with the map induced by a morphism of sheaves of
`𝒪_{X/S}`-modules. -/
theorem baseModuleGlobalSections_map_comp_π {M M' : ModuleSheaf S} (f : M ⟶ M')
    (X : (CrystallineThickening S)ᵒᵖ) :
    (baseModuleGlobalSections S).map f ≫ (baseModuleGlobalSectionsCone S M').π.app X =
      (baseModuleGlobalSectionsCone S M).π.app X ≫ ((toBaseModuleSheaf S).map f).hom.app X := by
  ext s
  rfl

/-- **`Γ_A` of a sheaf of `𝒪_{X/S}`-modules, read as a sheaf of `A`-modules, is its module-valued
global sections**: `toBaseModuleSheaf S ⋙ baseLinearGlobalSections S ≅ baseModuleGlobalSections S`
as functors to `A`-modules.  Both are limits of the sections over the objects of `Cris(X/S)`. -/
def toBaseModuleSheafGlobalSectionsIso :
    toBaseModuleSheaf S ⋙ baseLinearGlobalSections S ≅ baseModuleGlobalSections S :=
  NatIso.ofComponents
    (fun M => (Sheaf.isLimitConeΓ ((toBaseModuleSheaf S).obj M)).conePointUniqueUpToIso
      (isLimitBaseModuleGlobalSectionsCone S M))
    (fun {M M'} f => by
      refine (isLimitBaseModuleGlobalSectionsCone S M').hom_ext fun X => ?_
      simp only [Functor.comp_map]
      exact Sheaf.ΓRes_naturality ((toBaseModuleSheaf S).map f) X)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
