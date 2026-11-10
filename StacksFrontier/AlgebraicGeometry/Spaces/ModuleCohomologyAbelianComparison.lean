module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapseUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SectionsOnALocallySmallSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ConstantSheafCorepresentation
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftColimits
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftInjective
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftInjectives
import all StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of modules and of abelian sheaves on an algebraic space

Let `X` be an algebraic space and `ℱ` an `𝒪_X`-module on the small étale site of `X`.  The
cohomology `H^n(X, ℱ)` may be computed in the category of `𝒪_X`-modules — the right derived
functors of the global sections of modules — or in the category of abelian sheaves, after
forgetting the module structure.  [Stacks, Tag 03FD] says that the two agree.  This file proves
it for the small étale site of an algebraic space, where the module sections live in the
universe `u` of the schemes while the objects of the site live in `u + 1`, so that abelian
sheaves are taken with coefficients in `Ab.{u + 1}`, the universe in which their cohomology is
studied in this library (for instance by [Stacks, Tag 073E]).

As a consequence, the cohomology of modules on a quasi-compact and quasi-separated algebraic
space commutes with filtered colimits, which is [Stacks, Tag 073E] read for `𝒪_X`-modules.

## Main definitions

* `AlgebraicGeometry.Space.moduleToAbelianSheaf`: the underlying abelian sheaf of an
  `𝒪_X`-module, with its sections raised to the universe `u + 1`.
* `AlgebraicGeometry.Space.moduleCohomologyForgetIso`: **[Stacks, Tag 03FD]**,
  `H^n(X, ℱ) = H^n(X_étale, ℱ)` naturally in the `𝒪_X`-module `ℱ`, as abelian groups.

## Main results

* `AlgebraicGeometry.Space.isIso_colimit_post_moduleCohomology`: on a quasi-compact and
  quasi-separated algebraic space, the cohomology of `𝒪_X`-modules commutes with filtered
  colimits, after forgetting to abelian groups.

## Implementation notes

The comparison is the `δ`-functor argument of [Stacks, Tag 03FD],
`ModuleSheafCohomology.comparisonIso`, applied to the exact functor
`moduleToAbelianSheaf` and to the global sections of abelian sheaves, corepresented by the
constant sheaf `ℤ`.  Its acyclicity input — `Ext^{n+1}(ℤ, ℱ) = 0` for the underlying abelian
sheaf of an injective `𝒪_X`-module `ℱ` — is known with coefficients in `Ab.{u}`
(`Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree`); it is carried to `Ab.{u + 1}`
because raising the universe of the coefficients is exact, fully faithful and preserves
injective objects on the essentially small étale site
(`CategoryTheory.sheafCompose_preservesInjectiveObjects`,
`CategoryTheory.Functor.ext_eq_zero_of_forall_ext_eq_zero`).

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

/-! ### Postcomposition preserves injective sheaves on an essentially small site -/

namespace CategoryTheory

/-- Postcomposition on a functor category over an essentially small category with a
limit-preserving functor which preserves injective objects again preserves injective objects.
The category is replaced by its small model, along which the functor categories are
equivalent compatibly with postcomposition. -/
lemma whiskeringRight_preservesInjectiveObjects
    {C : Type*} [Category.{u} C] [EssentiallySmall.{u} C] {A D : Type*} [Category* A]
    [Category* D] [HasLimitsOfSize.{u, u} A] [HasLimitsOfSize.{u, u} D] [EnoughInjectives A]
    (G : A ⥤ D) [G.PreservesInjectiveObjects] [PreservesLimitsOfSize.{u, u} G] :
    ((Functor.whiskeringRight C A D).obj G).PreservesInjectiveObjects := by
  have := AlgebraicGeometry.Space.whiskeringRight_preservesInjectiveObjects
    (C := SmallModel.{u} C) G
  let e : C ≌ SmallModel.{u} C := equivSmallModel C
  refine ⟨fun {F} hF ↦ ?_⟩
  let E := e.congrLeft (E := A)
  have : Injective (E.functor.obj F) := E.symm.toAdjunction.map_injective _ hF
  have h1 : Injective ((E.functor.obj F) ⋙ G) :=
    ((Functor.whiskeringRight _ A D).obj G).injective_obj (E.functor.obj F)
  let E' := e.congrLeft (E := D)
  have : Injective (E'.inverse.obj ((E.functor.obj F) ⋙ G)) :=
    E'.toAdjunction.map_injective _ h1
  exact Injective.of_iso (Functor.isoWhiskerRight (E.unitIso.app F).symm G) this

/-- Postcomposition on sheaves over an essentially small site with a limit-preserving functor
which preserves injective objects again preserves injective objects: an injective sheaf is
injective as a presheaf, and injectivity of a presheaf is preserved by postcomposition. -/
lemma sheafCompose_preservesInjectiveObjects
    {C : Type*} [Category.{u} C] [EssentiallySmall.{u} C] (J : GrothendieckTopology C)
    {A D : Type*} [Category* A] [Category* D]
    [HasLimitsOfSize.{u, u} A] [HasLimitsOfSize.{u, u} D] [EnoughInjectives A]
    [HasSheafify J A] [HasSheafify J D]
    (G : A ⥤ D) [J.HasSheafCompose G] [G.PreservesInjectiveObjects]
    [PreservesLimitsOfSize.{u, u} G] :
    (sheafCompose J G).PreservesInjectiveObjects := by
  have := CategoryTheory.whiskeringRight_preservesInjectiveObjects (C := Cᵒᵖ) G
  refine ⟨fun {F} hF ↦ ?_⟩
  have : Injective F.obj := (sheafificationAdjunction J A).map_injective _ hF
  have : Injective (F.obj ⋙ G) :=
    ((Functor.whiskeringRight Cᵒᵖ A D).obj G).injective_obj F.obj
  exact Functor.injective_of_map_injective (sheafToPresheaf J D)
    (show Injective (F.obj ⋙ G) from inferInstance)

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

attribute [local instance 5000] SmallEtale.instHasSheafify

set_option synthInstance.maxHeartbeats 400000 in
-- the limits needed for global sections of sheaves on the small étale site take a deep search
/-- The global sections functor of abelian sheaves with coefficients in `u + 1` on the small
étale site (instance search times out without this shortcut). -/
local instance hasGlobalSectionsFunctor_moduleCohomologyAbelianComparison :
    HasGlobalSectionsFunctor (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} :=
  hasGlobalSectionsFunctor_of_hasLimitsOfShape _ _

/-- The underlying abelian sheaf of an `𝒪_X`-module, with its sections raised to the universe
`u + 1` of the objects of the small étale site. -/
abbrev moduleToAbelianSheaf :
    Modules.{u, u} B S hS X.1 X.2 ⥤ Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⋙
    sheafCompose (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u}

/-! ### Global sections, as a limit -/

/-- The global sections of an `𝒪_X`-module, read as an abelian group, as a cone over the diagram
of the sections of its underlying abelian sheaf with sections raised to `u + 1`. -/
def moduleSectionsCone (M : Modules.{u, u} B S hS X.1 X.2) :
    Cone ((moduleToAbelianSheaf B S hS X).obj M).obj where
  pt := (globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⋙
        forget₂ _ AddCommGrpCat.{u + 1}).obj M
  π :=
    { app U := AddCommGrpCat.ofHom
        { toFun := fun (s : M.sections) => ULift.up (s.eval U)
          map_zero' := rfl
          map_add' _ _ := rfl }
      naturality := by
        intro U V f
        ext (s : M.sections)
        exact congrArg ULift.up (M.val.sections_property s f).symm }

/-- `moduleSectionsCone` is a limit cone: a compatible family of sections is a point of the
limit of the sections over the site. -/
def isLimitModuleSectionsCone (M : Modules.{u, u} B S hS X.1 X.2) :
    IsLimit (moduleSectionsCone B S hS X M) where
  lift c := AddCommGrpCat.ofHom
    { toFun x := (M.val.sectionsMk (fun U => ULift.down (c.π.app U x))
        (fun U V f => congrArg ULift.down (ConcreteCategory.congr_hom (c.w f) x)) : M.sections)
      map_zero' := PresheafOfModules.sections_ext _ _ fun U =>
        congrArg ULift.down (c.π.app U).hom.map_zero
      map_add' _ _ := PresheafOfModules.sections_ext _ _ fun U =>
        congrArg ULift.down ((c.π.app U).hom.map_add _ _) }
  fac c U := by ext x; rfl
  uniq c m hm := AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun x =>
    PresheafOfModules.sections_ext _ _ fun U =>
      congrArg ULift.down (ConcreteCategory.congr_hom (hm U) x)

/-- **Global sections of `𝒪_X`-modules, read in abelian groups, are the global sections of the
underlying abelian sheaves.**  Both are limits of the sections over the objects of the site. -/
def globalSectionsForgetIsoModuleToAbelianSheaf :
    globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⋙
        forget₂ _ AddCommGrpCat.{u + 1} ≅
      moduleToAbelianSheaf B S hS X ⋙
        Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} := by
  refine NatIso.ofComponents (fun M =>
    (isLimitModuleSectionsCone B S hS X M).conePointUniqueUpToIso
      (Sheaf.isLimitConeΓ ((moduleToAbelianSheaf B S hS X).obj M))) ?_
  intro M N f
  let T := moduleToAbelianSheaf B S hS X
  let hM := isLimitModuleSectionsCone B S hS X M
  let hN := isLimitModuleSectionsCone B S hS X N
  let qM := Sheaf.isLimitConeΓ (T.obj M)
  let qN := Sheaf.isLimitConeΓ (T.obj N)
  apply qN.hom_ext
  intro U
  have h1 := IsLimit.conePointUniqueUpToIso_hom_comp hN qN U
  have h2 := IsLimit.conePointUniqueUpToIso_hom_comp hM qM U
  have hnat := Sheaf.ΓRes_naturality (T.map f) U
  have h3 : (globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⋙
        forget₂ _ AddCommGrpCat.{u + 1}).map f ≫ (moduleSectionsCone B S hS X N).π.app U =
      (moduleSectionsCone B S hS X M).π.app U ≫ (T.map f).hom.app U := by
    ext s
    rfl
  let F := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⋙
      forget₂ _ AddCommGrpCat.{u + 1}
  let eM := hM.conePointUniqueUpToIso qM
  let eN := hN.conePointUniqueUpToIso qN
  have e1 : (F.map f ≫ eN.hom) ≫ (Sheaf.coneΓ (T.obj N)).π.app U =
      F.map f ≫ (moduleSectionsCone B S hS X N).π.app U :=
    (Category.assoc _ _ _).trans (congrArg (fun g => F.map f ≫ g) h1)
  have e3 : (moduleSectionsCone B S hS X M).π.app U ≫ (T.map f).hom.app U =
      (eM.hom ≫ (Sheaf.coneΓ (T.obj M)).π.app U) ≫ (T.map f).hom.app U :=
    congrArg (fun g => g ≫ (T.map f).hom.app U) h2.symm
  have e4 : (eM.hom ≫ (Sheaf.coneΓ (T.obj M)).π.app U) ≫ (T.map f).hom.app U =
      (eM.hom ≫ (T ⋙ Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).map f) ≫
        (Sheaf.coneΓ (T.obj N)).π.app U :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun g => eM.hom ≫ g) hnat.symm).trans (Category.assoc _ _ _).symm)
  exact e1.trans (h3.trans (e3.trans e4))

/-! ### The homological inputs -/

/-- Abelian sheaves on the small étale site of an algebraic space, with coefficients in the
universe `u` of the structure rings, have enough injectives: the site is essentially small
there. -/
local instance enoughInjectives_sheaf_u :
    EnoughInjectives (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :=
  have : IsGrothendieckAbelian.{u}
      (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u} _ _
  inferInstance

/-- `Ext` groups in the universe `u + 1` between abelian sheaves on the small étale site with
coefficients in `u`. -/
local instance hasExt_sheaf_u :
    HasExt.{u + 1} (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :=
  HasExt.standard _

set_option synthInstance.maxHeartbeats 400000 in
-- `HasExt` from the Grothendieck abelian structure on étale sheaves takes a deep search
/-- `Ext` groups in the universe `u + 1` between abelian sheaves on the small étale site with
coefficients in `u + 1`: the category of these sheaves is Grothendieck abelian, the site being
essentially small. -/
local instance hasExt_sheaf_succ :
    HasExt.{u + 1} (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) :=
  have : IsGrothendieckAbelian.{u + 1}
      (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} _ _
  inferInstance

/-- The `𝒪_X`-modules on the small étale site of an algebraic space have enough injectives. -/
local instance enoughInjectives_modules_u : EnoughInjectives (Modules.{u, u} B S hS X.1 X.2) :=
  enoughInjectives_modules B S hS X.1 X.2

/-- The universe lift of abelian sheaves on the small étale site preserves sheafification. -/
local instance preservesSheafification_ulift :
    (SmallEtale.topology B S hS X.1).PreservesSheafification
      AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  Stacks.Sheaves.UniverseLift.preservesSheafification_uliftFunctor

/-- The universe lift of abelian sheaves on the small étale site preserves finite colimits. -/
local instance uliftSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (sheafCompose (SmallEtale.topology B S hS X.1)
      AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
  ⟨fun _ _ _ => sheafCompose_preservesColimitsOfShape _ _⟩

/-- The universe lift of abelian sheaves on the small étale site preserves finite limits. -/
local instance uliftSheaf_preservesFiniteLimits :
    PreservesFiniteLimits (sheafCompose (SmallEtale.topology B S hS X.1)
      AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
  ⟨fun _ _ _ => sheafCompose_preservesLimitsOfShape _ _⟩

/-- The universe lift of abelian sheaves on the small étale site preserves injective objects. -/
local instance uliftSheaf_preservesInjectiveObjects :
    (sheafCompose (SmallEtale.topology B S hS X.1)
      AddCommGrpCat.uliftFunctor.{u + 1, u}).PreservesInjectiveObjects :=
  CategoryTheory.sheafCompose_preservesInjectiveObjects _ _

/-- The underlying abelian sheaf of an `𝒪_X`-module, with sections raised to `u + 1`, preserves
finite limits. -/
local instance moduleToAbelianSheaf_preservesFiniteLimits :
    PreservesFiniteLimits (moduleToAbelianSheaf B S hS X) :=
  @comp_preservesFiniteLimits _ _ _ _ _ _
    (SheafOfModules.toSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (sheafCompose (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u})
    inferInstance (uliftSheaf_preservesFiniteLimits B S hS X)

/-- The underlying abelian sheaf of an `𝒪_X`-module, with sections raised to `u + 1`, preserves
finite colimits. -/
local instance moduleToAbelianSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (moduleToAbelianSheaf B S hS X) :=
  @comp_preservesFiniteColimits _ _ _ _ _ _
    (SheafOfModules.toSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (sheafCompose (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u})
    (Stacks.Cohomology.ObjectSections.toSheaf_preservesFiniteColimits
      (SmallEtale.topology B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (uliftSheaf_preservesFiniteColimits B S hS X)

/-- The constant sheaf `ℤ` with coefficients in `u + 1` is the universe lift of the constant
sheaf `ℤ` with coefficients in `u`. -/
def uliftConstantSheafIso :
    (sheafCompose (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        ((constantSheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      (constantSheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) :=
  (sheafComposeNatIso (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u}
      (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)).symm.app _ ≪≫
    (presheafToSheaf _ _).mapIso (NatIso.ofComponents (fun _ =>
      AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans
        (AddEquiv.ulift.trans AddEquiv.ulift.symm))) (fun _ => rfl))

/-- The universe lift of the constant sheaf `ℤ`, which corepresents global sections of abelian
sheaves with coefficients in `u + 1`. -/
abbrev liftedConstantSheaf : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} :=
  (sheafCompose (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    ((constantSheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))

/-- Global sections of abelian sheaves with coefficients in `u + 1` are corepresented by the
universe lift of the constant sheaf `ℤ`. -/
def globalSectionsCorepresentation :
    Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} ≅
      preadditiveCoyoneda.obj (op (liftedConstantSheaf B S hS X)) :=
  ModuleSheafCohomology.globalSectionsIsoCoyonedaConstantSheaf _ ≪≫
    preadditiveCoyoneda.mapIso (uliftConstantSheafIso B S hS X).op

/-- Global sections of an `𝒪_X`-module, read in abelian groups, are corepresented by the
structure sheaf. -/
def unitCorepresentation :
    preadditiveCoyoneda.obj (op (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) ≅
      globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⋙
        forget₂ _ AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents (fun M => AddEquiv.toAddCommGrpIso
    { SheafOfModules.unitHomEquiv M with
      map_add' := fun _ _ => rfl })
    (fun {M N} f => by
      ext g
      exact SheafOfModules.unitHomEquiv_comp_apply g f)

/-- The identification of maps out of the structure sheaf with maps out of the constant sheaf
`ℤ` after `moduleToAbelianSheaf`: both are global sections. -/
def unitCorepresentationComp :
    preadditiveCoyoneda.obj (op (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) ≅
      moduleToAbelianSheaf B S hS X ⋙
        preadditiveCoyoneda.obj (op (liftedConstantSheaf B S hS X)) :=
  unitCorepresentation B S hS X ≪≫ globalSectionsForgetIsoModuleToAbelianSheaf B S hS X ≪≫
    Functor.isoWhiskerLeft _ (globalSectionsCorepresentation B S hS X)

/-- **The acyclicity input of Stacks 03FD.**  The underlying abelian sheaf of an injective
`𝒪_X`-module, with sections raised to `u + 1`, has no positive-degree `Ext` out of the constant
sheaf `ℤ`.  With coefficients in `u` this is
`Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree`, the constant sheaf `ℤ` being
sectionwise torsion free; it is carried to `u + 1` by the universe lift, which is exact, fully
faithful and preserves injective objects. -/
theorem ext_liftedConstantSheaf_moduleToAbelianSheaf_eq_zero
    (I : Modules.{u, u} B S hS X.1 X.2) [Injective I] (n : ℕ)
    (e : Abelian.Ext.{u + 1} (liftedConstantSheaf B S hS X)
      ((moduleToAbelianSheaf B S hS X).obj I) (n + 1)) : e = 0 := by
  let L := sheafCompose (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u}
  have hL := Stacks.Sheaves.UniverseLift.fullyFaithfulUliftSheafFunctor.{u + 1, u}
    (SmallEtale.topology B S hS X.1)
  have : L.Full := hL.full
  have : L.Faithful := hL.faithful
  have : L.Additive := ⟨fun {_ _ _ _} => rfl⟩
  refine Functor.ext_eq_zero_of_forall_ext_eq_zero.{u + 1} L n (fun e' => ?_) e
  exact @Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree _ _
    (SmallEtale.topology B S hS X.1) _ _ _ _
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) I
    (by assumption) _
    (ModuleSheafCohomology.isTorsionFree_sheafify _ _ (fun _ => by
      change Module.IsTorsionFree ℤ (ULift.{u} ℤ)
      exact Module.Flat.isTorsionFree)) n e'

/-- The universe lift of abelian sheaves is additive. -/
instance uliftSheaf_additive : (sheafCompose (SmallEtale.topology B S hS X.1)
    AddCommGrpCat.uliftFunctor.{u + 1, u}).Additive := ⟨fun {_ _ _ _} => rfl⟩

/-- The underlying abelian sheaf of an `𝒪_X`-module depends additively on it. -/
instance moduleToAbelianSheaf_additive : (moduleToAbelianSheaf B S hS X).Additive where
  map_add {_M _N f g} :=
    (congrArg (sheafCompose (SmallEtale.topology B S hS X.1)
      AddCommGrpCat.uliftFunctor.{u + 1, u}).map
        (Functor.map_add (SheafOfModules.toSheaf _) (f := f) (g := g))).trans rfl

/-- **Stacks 03FD on the small étale site of an algebraic space.**  The cohomology of an
`𝒪_X`-module `ℱ`, computed in `𝒪_X`-modules and read in abelian groups, is the cohomology of its
underlying abelian sheaf (with sections raised to `u + 1`), naturally in `ℱ`. -/
@[stacks 03FD "on the small étale site of an algebraic space"]
def moduleCohomologyForgetIso (n : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived n ⋙
        forget₂ _ AddCommGrpCat.{u + 1} ≅
      moduleToAbelianSheaf B S hS X ⋙
        (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).rightDerived n :=
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS X.1 X.2
  letI : HasExt.{u + 1} (Modules.{u, u} B S hS X.1 X.2) := HasExt.standard _
  (Functor.rightDerivedCompIso _ _ n).symm ≪≫
    Functor.rightDerivedIsoOfNatIso (globalSectionsForgetIsoModuleToAbelianSheaf B S hS X) n ≪≫
    ModuleSheafCohomology.comparisonIso (moduleToAbelianSheaf B S hS X)
      (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1})
      (liftedConstantSheaf B S hS X) (globalSectionsCorepresentation B S hS X)
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
      (unitCorepresentationComp B S hS X)
      (fun I _ n e => ext_liftedConstantSheaf_moduleToAbelianSheaf_eq_zero B S hS X I n e) n

/-- The underlying abelian sheaf of `𝒪_X`-modules, with sections raised to `u + 1`, commutes
with colimits indexed by a category in the universe `u`. -/
theorem moduleToAbelianSheaf_preservesColimitsOfShape (I : Type u) [SmallCategory I] :
    PreservesColimitsOfShape I (moduleToAbelianSheaf B S hS X) := by
  have hT : PreservesColimitsOfShape I (SheafOfModules.toSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) := by
    rw [(PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj)).preservesColimitsOfShape_iff]
    exact preservesColimitsOfShape_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O).obj)).symm
  have : PreservesColimitsOfShape I AddCommGrpCat.uliftFunctor.{u + 1, u} := inferInstance
  have hL : PreservesColimitsOfShape I (sheafCompose (SmallEtale.topology B S hS X.1)
      AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
    sheafCompose_preservesColimitsOfShape _ _
  exact @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _
    (SheafOfModules.toSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (sheafCompose (SmallEtale.topology B S hS X.1) AddCommGrpCat.uliftFunctor.{u + 1, u})
    hT hL

/-- **Stacks 073E for `𝒪_X`-modules.**  On a quasi-compact and quasi-separated algebraic space
`X`, the canonical map `colim_i H^p(X, ℱ_i) ⟶ H^p(X, colim_i ℱ_i)` is an isomorphism for every
filtered system of `𝒪_X`-modules, the cohomology being read in abelian groups.

By `moduleCohomologyForgetIso` the cohomology of an `𝒪_X`-module is that of its underlying
abelian sheaf, which commutes with colimits, and the statement for abelian sheaves is
`AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_globalSections`. -/
theorem isIso_colimit_post_moduleCohomology (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactSpace B S hS X.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (p : ℕ) {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Modules.{u, u} B S hS X.1 X.2) [HasColimit F] :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsIso (colimit.post F ((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived p ⋙
        forget₂ _ AddCommGrpCat.{u + 1})) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := moduleToAbelianSheaf_preservesColimitsOfShape B S hS X I
  let H := (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).rightDerived p
  have h1 : IsIso (colimit.post (F ⋙ moduleToAbelianSheaf B S hS X) H) :=
    isIso_colimit_post_rightDerived_globalSections B S hS hZ X.1 X.2 hqc hqs p _
  have h2 : IsIso (colimit.post F (moduleToAbelianSheaf B S hS X ⋙ H)) := by
    rw [← colimit.post_post]
    infer_instance
  exact Stacks.Cohomology.isIso_colimit_post_of_natIso F _ _
    (moduleCohomologyForgetIso B S hS X p).symm

end AlgebraicGeometry.Space

end
