module

public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleModuleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardFormula
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgettingTheModuleStructureUnivLE
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekCocontinuousSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedModuleLowerShriekLargeSections
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07AV for sheaves of modules on the flat-fppf sites

This is the flat-fppf twin of
`StacksFrontier/AlgebraicGeometry/Stacks/LisseEtaleModuleDerivedBaseChange.lean`.

Let `f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic stacks, `f'` its restriction to the
flat-fppf sites, and `g`, `g'` the inclusions of the flat-fppf sites of `𝒴` and `𝒳`, with the
structure sheaves of **Stacks 06TV** on the fppf sites and their restrictions on the flat-fppf
sites, so that `g^* = g⁻¹` and `(g')^* = (g')⁻¹` are restriction (**Stacks 0788** (1)(f)). This
file proves, with no hypothesis, the module case of the first identity of **Stacks 07AV**:

`Rf'_* ∘ (g')^* ≅ g^* ∘ Rf_*` on the unbounded derived categories of sheaves of modules.

## The argument

The source: "since cohomology of abelian groups and sheaves of modules agree we also conclude".
Two inputs feed `Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit`:

* the degree-zero square on sheaves of modules: the canonical comparison
  `Stacks.SheafOfModules.squareComparison` is invertible, because its underlying map of abelian
  presheaves is the base change of right Kan extensions, invertible at every sheaf by
  `AlgebraicGeometry.Stack.FlatFppf.isIso_ranBaseChange_app_of_isSheaf`;
* for a K-injective complex `I` of `𝒪_𝒳`-modules, `(g')^* I` computes `Rf'_*`: quasi-isomorphy
  of the direct image of a K-injective resolution is checked on underlying abelian complexes,
  where the direct image of modules is the direct image of abelian sheaves on the nose; the
  sections of the latter over a flat object `y` of `𝒴` are corepresented by a sectionwise
  torsion-free sheaf; the underlying abelian complex of a K-injective complex of modules computes
  `RHom` out of every sectionwise torsion-free sheaf (Stacks 0D6J,
  `Stacks.Cohomology.ForgetModuleUnivLE.qh_map_bijective_single_of_isKInjective`); and by
  `AlgebraicGeometry.Stack.FlatFppf.qh_map_bijective_directImageCorep_restriction` so does its
  restriction to the flat-fppf site, out of the corepresenting sheaves.

## The second identity

`L(g')_! ∘ (f')^{-1} = f^{-1} ∘ Lg_!` is the conjugate of the first identity across the
composed adjunctions `Lg_! ⊣ g^*` (07BA's `derivedModuleLowerShriekSucc`) and `f^{-1} ⊣ Rf_*`. The
latter is derived from an adjunction of exact functors on sheaves of modules: `f^{-1}` is the
inverse image of Stacks 06WE, restriction along `f` read through the identification Stacks 06TW of
the restricted structure sheaf, and the structure map of `f_*` is the transpose of that
identification, so `Stacks.SheafOfModules.RestrictRan.restrictionAdjunctionOfEq` applies; on the
flat-fppf sites the structure map of `f'_*` is again such a transpose
(`Stacks.SheafOfModules.structureMapSquare_homEquiv_eqToHom`).

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.isIso_moduleSquareComparison`: **Stacks 07AT** (2) on
  sheaves of modules.
* restricted K-injective complexes of modules compute `Rf'_*`: this is
  `Stacks.SheafOfModules.isIso_derivedPushforwardUnit_inverseImage` (in the lisse-étale twin)
  fed with `AlgebraicGeometry.Stack.FlatFppf.qh_map_bijective_directImageCorep_restriction`.
* `AlgebraicGeometry.Stack.FlatFppf.moduleDerivedRestrictionBaseChangeIso`: **Stacks 07AV**,
  first identity, for sheaves of modules.
* `AlgebraicGeometry.Stack.FlatFppf.modulePullbackPushforwardAdjunction` and
  `AlgebraicGeometry.Stack.FlatFppf.moduleSubsiteInverseImageAdjunction`: `f^{-1} ⊣ f_*` and
  `(f')^{-1} ⊣ f'_*` on sheaves of modules.
* `AlgebraicGeometry.Stack.FlatFppf.moduleDerivedLowerShriekBaseChangeIso`: **Stacks 07AV**,
  second identity, for sheaves of modules.

## References

* [Stacks Project, Tag 07AV](https://stacks.math.columbia.edu/tag/07AV)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules
open Stacks.Cohomology.DerivedLowerShriek
  (alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    exists_quasiIso_isKInjective_of_isGrothendieckAbelian)
open Stacks.Cohomology.SupportedComplexes (derivedAdjunctionOfExactLeftAdjoint)

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat
  isContinuous_inclusion_topology isCocontinuous_inclusion_topology
  AlgebraicGeometry.Stack.instHasPointwiseRightKanExtensionRingCat
  AlgebraicGeometry.Stack.instHasPointwiseRightKanExtensionAddCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsFlat B S hS f)

/-- The restriction `f'` of `f` commutes, on the nose, with the two inclusions of the flat-fppf
sites. -/
theorem primedSiteFunctor_comp_ι :
    primedSiteFunctor B S hS f hf ⋙ (objectProperty B S hS 𝒴).ι =
      (objectProperty B S hS 𝒳).ι ⋙ f.hom.hom.toFunctor := rfl

/-- The direct image `f'_*` of sheaves of modules along the restriction `f'` of a flat
1-morphism to the flat-fppf sites, for the structure map forced by the square of
**Stacks 07AT** (2). -/
abbrev moduleSubsitePushforward :
    _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳) ⥤
      _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴) :=
  haveI := isCocontinuous_subsiteFunctor_topology B S hS f hf
  pushforwardCocontinuous.{u + 1} (primedSiteFunctor B S hS f hf)
    (restrictedStructureMap B S hS B.topology le_rfl f
      (flatObject B S hS 𝒳.val) (flatObject B S hS 𝒴.val)
      (topology B S hS 𝒳) (topology B S hS 𝒴) (primedSiteFunctor B S hS f hf)
      (primedSiteFunctor_comp_ι B S hS f hf))

/-- **Stacks 07AT** (2) on sheaves of modules: the canonical comparison
`f_* ∘ g^* ⟶ (g')^* ∘ f'_*` of `Stacks.SheafOfModules.squareComparison` is invertible. Its
underlying map of abelian presheaves at a sheaf of modules is the base change of right Kan
extensions, invertible by `AlgebraicGeometry.Stack.FlatFppf.isIso_ranBaseChange_app_of_isSheaf`,
and the forgetful functors to abelian sheaves and to abelian presheaves reflect isomorphisms. -/
theorem isIso_moduleSquareComparison :
    haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
    haveI := isCocontinuous_subsiteFunctor_topology B S hS f hf
    IsIso (squareComparison (J' := topology B S hS 𝒳) (K' := topology B S hS 𝒴)
      (structureMapHomFunctor B S hS B.topology le_rfl f)
      (primedSiteFunctor_comp_ι B S hS f hf)) := by
  have := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
  have := isCocontinuous_subsiteFunctor_topology B S hS f hf
  suffices ∀ N, IsIso ((squareComparison (J' := topology B S hS 𝒳) (K' := topology B S hS 𝒴)
      (structureMapHomFunctor B S hS B.topology le_rfl f)
      (primedSiteFunctor_comp_ι B S hS f hf)).app N) from NatIso.isIso_of_isIso_app _
  intro N
  have hsq : (Stacks.Sites.CocontinuousExchange.twoSquare
      (primedSiteFunctor_comp_ι B S hS f hf)).op =
      SubsitePushforward.subsiteRanSquare f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
        (flatObject_map B S hS f hf) := by
    ext X
    simp [Stacks.Sites.CocontinuousExchange.twoSquare, SubsitePushforward.subsiteRanSquare]
    rfl
  have h1 : IsIso (((Stacks.Sites.CocontinuousExchange.twoSquare
      (primedSiteFunctor_comp_ι B S hS f hf)).op.ranBaseChange
          (D := AddCommGrpCat.{u + 1})).app N.val.presheaf) := by
    rw [hsq]
    exact isIso_ranBaseChange_app_of_isSheaf B S hS f hf N.val.presheaf N.isSheaf
  rw [← isIso_iff_of_reflects_iso _
      (_root_.SheafOfModules.toSheaf.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴)),
    ← isIso_iff_of_reflects_iso _ (sheafToPresheaf (topology B S hS 𝒴) AddCommGrpCat.{u + 1})]
  exact h1

section Derived

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- **Stacks 07AV, first identity, for sheaves of modules on the flat-fppf sites:
`g^* ∘ Rf_* = Rf'_* ∘ (g')^*`.** For a flat 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, total
right derived functors `Rf_*`, `Rf'_*` of the direct images of sheaves of modules along `f` and
along its restriction `f'` to the flat-fppf sites, and `g^*`, `(g')^*` the restrictions of
sheaves of modules to the flat-fppf sites (which are `g⁻¹`, `(g')⁻¹`),

`(g')^* ⋙ Rf'_* ≅ Rf_* ⋙ g^*`

on the unbounded derived categories, with no further hypothesis. It is
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit` at the degree-zero square
`AlgebraicGeometry.Stack.FlatFppf.isIso_moduleSquareComparison` and at
`Stacks.SheafOfModules.isIso_derivedPushforwardUnit_inverseImage`, fed with
`AlgebraicGeometry.Stack.FlatFppf.qh_map_bijective_directImageCorep_restriction`. -/
@[stacks 07AV "the module case for the flat-fppf sites, first identity: \
g⁻¹ ∘ Rf_* = Rf'_* ∘ (g')⁻¹ on the unbounded derived categories of sheaves of modules, as an \
isomorphism (g')^* ⋙ Rf'_* ≅ Rf_* ⋙ g^* for any total right derived \
functors Rf_*, Rf'_* of the two \
direct images, with no further hypothesis: the degree-zero square of Stacks 07AT (2) on modules \
and the fact that restricted K-injective complexes of modules compute Rf'_* (Stacks 0D6J with \
Stacks 07AK at the 2-fibre products V ×_y 𝒳) are proved, not assumed"]
def moduleDerivedRestrictionBaseChangeIso
    (Rf : DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴)))
    (Rf' : DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴)))
    (αf : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    (αf' : (moduleSubsitePushforward B S hS f hf).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf')
    [hRf : Rf.IsRightDerivedFunctor αf (HomotopyCategory.quasiIso
      (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) (ComplexShape.up ℤ))]
    [hRf' : Rf'.IsRightDerivedFunctor αf' (HomotopyCategory.quasiIso
      (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) (ComplexShape.up ℤ))] :
    (moduleInverseImage B S hS 𝒳).mapDerivedCategory ⋙ Rf' ≅
      Rf ⋙ (moduleInverseImage B S hS 𝒴).mapDerivedCategory :=
  haveI : IsGrothendieckAbelian.{u + 1}
      (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u, u} _
  haveI : IsGrothendieckAbelian.{u + 1}
      (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u, u} _
  haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
  haveI := isCocontinuous_subsiteFunctor_topology B S hS f hf
  haveI := isIso_moduleSquareComparison B S hS f hf
  Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit
    (moduleInverseImage B S hS 𝒳) (moduleInverseImage B S hS 𝒴)
    (modulePushforward B S hS f) (moduleSubsitePushforward B S hS f hf) Rf Rf' αf αf'
    (asIso (squareComparison (J' := topology B S hS 𝒳) (K' := topology B S hS 𝒴)
      (structureMapHomFunctor B S hS B.topology le_rfl f)
      (primedSiteFunctor_comp_ι B S hS f hf))).symm
    (fun I hI => haveI := hI
      isIso_derivedPushforwardUnit_inverseImage (ambientRingStructureSheaf B S hS 𝒳)
        (topology B S hS 𝒳) (topology B S hS 𝒴) (subsiteRingStructureSheaf B S hS 𝒴)
        (primedSiteFunctor B S hS f hf)
        (restrictedStructureMap B S hS B.topology le_rfl f
          (flatObject B S hS 𝒳.val) (flatObject B S hS 𝒴.val)
          (topology B S hS 𝒳) (topology B S hS 𝒴) (primedSiteFunctor B S hS f hf)
          (primedSiteFunctor_comp_ι B S hS f hf)) Rf' αf'
        (fun y Z hZ n => qh_map_bijective_directImageCorep_restriction B S hS f hf
          (topology B S hS 𝒳) (inclusionTopology_eq_topology B S hS 𝒳) y Z hZ n) I)

/-- **Stacks 06TW on the flat-fppf sites.** The restriction along the restriction `f'` of a
flat 1-morphism of the structure sheaf of the flat-fppf site of `𝒴` is the structure sheaf of
the flat-fppf site of `𝒳`: both are restrictions of the structure sheaf of `𝒴`, along
`f' ⋙ g = g' ⋙ f`, and the restriction of that of `𝒴` along `f` is that of `𝒳`. -/
theorem subsiteRingStructureSheaf_inverseImageRing :
    haveI := isContinuous_subsiteFunctor_topology B S hS f hf
    inverseImageRing (topology B S hS 𝒳) (topology B S hS 𝒴)
        (primedSiteFunctor B S hS f hf) (subsiteRingStructureSheaf B S hS 𝒴) =
      subsiteRingStructureSheaf B S hS 𝒳 :=
  congrArg (inverseImageRing (topology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (objectProperty B S hS 𝒳).ι)
    (sheafPushforwardContinuous_ringStructureSheafCore B S hS B.topology
      le_rfl f)

/-- The inverse image `(f')^{-1}` of sheaves of modules along the restriction `f'` of a flat
1-morphism to the flat-fppf sites: restriction along `f'`, read over the structure sheaf of the
flat-fppf site of `𝒳` through
`AlgebraicGeometry.Stack.FlatFppf.subsiteRingStructureSheaf_inverseImageRing`. -/
abbrev moduleSubsiteInverseImage :
    _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴) ⥤
      _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳) :=
  haveI := isContinuous_subsiteFunctor_topology B S hS f hf
  _root_.SheafOfModules.pushforward.{u + 1} (F := primedSiteFunctor B S hS f hf)
    (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm)

/-- **The inverse image `f^{-1}` of sheaves of modules of Stacks 06WE is left adjoint to the
direct image `f_*` of the morphism of fppf topoi.** The direct image is
`Stacks.SheafOfModules.pushforwardCocontinuous` over the transpose of the identification
**Stacks 06TW** of the restricted structure sheaf, so this is
`Stacks.SheafOfModules.RestrictRan.restrictionAdjunctionOfEq`, the inverse image of 06WE being
restriction along `f` read through the same identification. -/
@[sga "4 Vbis 1.3.6" "special case"]
def modulePullbackPushforwardAdjunction :
    AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS 𝒳.val.val.p
        𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
        f.hom.hom.w B.topology le_rfl ⊣
      modulePushforward B S hS f :=
  haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).1
  haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
  (RestrictRan.restrictionAdjunctionOfEq.{u + 1} f.hom.hom.toFunctor
    (associatedTopology B S hS 𝒳.val.val.p B.topology)
    (associatedTopology B S hS 𝒴.val.val.p B.topology) (ambientRingStructureSheaf B S hS 𝒴)
    (sheafPushforwardContinuous_ringStructureSheafCore B S hS B.topology
      le_rfl f)).ofNatIsoLeft
    (_root_.SheafOfModules.pushforwardCongr (ObjectProperty.hom_ext _
      (eqToHom_map (sheafToPresheaf _ RingCat.{u}) _)))

/-- **The inverse image `(f')^{-1}` of sheaves of modules on the flat-fppf sites is left
adjoint to the direct image `f'_*`.** The structure map of `f'_*` is the restriction of that of
`f_*` (`Stacks.SheafOfModules.structureMapSquare`), which is again the transpose of an equality of
restricted structure sheaves (`Stacks.SheafOfModules.structureMapSquare_homEquiv_eqToHom`), so
`Stacks.SheafOfModules.RestrictRan.restrictionAdjunctionOfEq` applies. -/
def moduleSubsiteInverseImageAdjunction :
    moduleSubsiteInverseImage B S hS f hf ⊣ moduleSubsitePushforward B S hS f hf := by
  haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).1
  haveI := (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
  haveI := isContinuous_subsiteFunctor_topology B S hS f hf
  haveI := isCocontinuous_subsiteFunctor_topology B S hS f hf
  have e := structureMapSquare_homEquiv_eqToHom (J' := topology B S hS 𝒳)
    (K' := topology B S hS 𝒴) (J := associatedTopology B S hS 𝒳.val.val.p B.topology)
    (K := associatedTopology B S hS 𝒴.val.val.p B.topology) (primedSiteFunctor_comp_ι B S hS f hf)
    (sheafPushforwardContinuous_ringStructureSheafCore B S hS B.topology
      le_rfl f)
    (subsiteRingStructureSheaf_inverseImageRing B S hS f hf)
  change _ ⊣ pushforwardCocontinuous.{u + 1} (primedSiteFunctor B S hS f hf)
    (structureMapSquare (J' := topology B S hS 𝒳) (K' := topology B S hS 𝒴)
      (structureMapHomFunctor B S hS B.topology le_rfl f)
      (primedSiteFunctor_comp_ι B S hS f hf))
  rw [structureMapHomFunctor, e]
  exact RestrictRan.restrictionAdjunctionOfEq.{u + 1} (primedSiteFunctor B S hS f hf)
    (topology B S hS 𝒳) (topology B S hS 𝒴) (subsiteRingStructureSheaf B S hS 𝒴)
    (subsiteRingStructureSheaf_inverseImageRing B S hS f hf)


/-- The inverse image `f^{-1}` of sheaves of modules of **Stacks 06WE** along a 1-morphism of
algebraic stacks, for the fppf sites, on the unbounded derived categories. It is exact
(`AlgebraicGeometry.Stack.preservesFiniteLimits_modulePullback` and
`AlgebraicGeometry.Stack.preservesFiniteColimits_modulePullback`), so it needs no deriving. -/
abbrev derivedModulePullback :
    DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :=
  haveI := preservesFiniteLimits_modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    f.hom.hom.toFunctor f.hom.hom.w B.topology le_rfl
  haveI := preservesFiniteColimits_modulePullback.{u, u + 1, u, u, u + 1, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    f.hom.hom.toFunctor f.hom.hom.w B.topology le_rfl
  haveI : (AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
      𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      f.hom.hom.toFunctor f.hom.hom.w B.topology
      le_rfl).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  (AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS 𝒳.val.val.p
    𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
    f.hom.hom.w B.topology le_rfl).mapDerivedCategory

/-- The inverse image `(f')^{-1}` of sheaves of modules along the restriction `f'` of a flat
1-morphism to the flat-fppf sites, on the unbounded derived categories. It is exact, `f'` being
continuous and cocontinuous (`SheafOfModules.exactFunctor_pushforward_of_isCocontinuous`). -/
abbrev derivedModuleSubsiteInverseImage :
    DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) :=
  haveI := isContinuous_subsiteFunctor_topology B S hS f hf
  haveI := isCocontinuous_subsiteFunctor_topology B S hS f hf
  haveI : PreservesFiniteLimits (moduleSubsiteInverseImage B S hS f hf) :=
    (_root_.SheafOfModules.exactFunctor_pushforward_of_isCocontinuous.{u + 1, u, u + 1, u, u, u + 1}
      (primedSiteFunctor B S hS f hf)
      (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm)).1
  haveI : PreservesFiniteColimits (moduleSubsiteInverseImage B S hS f hf) :=
    (_root_.SheafOfModules.exactFunctor_pushforward_of_isCocontinuous.{u + 1, u, u + 1, u, u, u + 1}
      (primedSiteFunctor B S hS f hf)
      (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm)).2
  (moduleSubsiteInverseImage B S hS f hf).mapDerivedCategory

/-- **Stacks 07AV, the module case for the flat-fppf sites, second identity.** Let
`f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic stacks, `f'` its restriction to the flat-fppf
sites, and `Lg_!`, `L(g')_!` the derived lower shrieks of sheaves of modules along the inclusions
of the flat-fppf sites (`AlgebraicGeometry.Stack.FlatFppf.derivedModuleLowerShriekSucc`). Then

`Lg_! ⋙ f^{-1} ≅ (f')^{-1} ⋙ L(g')_!`

on the unbounded derived categories of sheaves of modules, that is,
`L(g')_! ∘ (f')^{-1} = f^{-1} ∘ Lg_!`. Here `f^{-1}`, `(f')^{-1}` are the exact inverse images
(Stacks 06WE, and restriction along `f'`), left adjoint to the canonical total right derived
direct images `Rf_*`, `Rf'_*` (`derivedAdjunctionOfExactLeftAdjoint` on
`AlgebraicGeometry.Stack.FlatFppf.modulePullbackPushforwardAdjunction` and
`AlgebraicGeometry.Stack.FlatFppf.moduleSubsiteInverseImageAdjunction`), and the isomorphism
is the conjugate, across the composed adjunctions, of the first identity
`AlgebraicGeometry.Stack.FlatFppf.moduleDerivedRestrictionBaseChangeIso`. -/
@[stacks 07AV "the module case for the flat-fppf sites, second identity: \
L(g')_! ∘ (f')⁻¹ = f⁻¹ ∘ Lg_! on the unbounded derived categories of sheaves of modules, as an \
isomorphism Lg_! ⋙ f⁻¹ ≅ (f')⁻¹ ⋙ L(g')_! for the actual derived lower shrieks and the exact \
inverse images, with no hypothesis: the adjunctions Lg_! ⊣ g⁻¹, f⁻¹ ⊣ Rf_* and their primed \
versions are constructed, and the first identity is proved"]
def moduleDerivedLowerShriekBaseChangeIso :
    derivedModuleLowerShriekSucc B S hS 𝒴 ⋙ derivedModulePullback B S hS f ≅
      derivedModuleSubsiteInverseImage B S hS f hf ⋙ derivedModuleLowerShriekSucc B S hS 𝒳 :=
  haveI : IsGrothendieckAbelian.{u + 1}
      (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u, u} _
  haveI : IsGrothendieckAbelian.{u + 1}
      (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u, u} _
  haveI := preservesFiniteLimits_modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    f.hom.hom.toFunctor f.hom.hom.w B.topology le_rfl
  haveI := preservesFiniteColimits_modulePullback.{u, u + 1, u, u, u + 1, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    f.hom.hom.toFunctor f.hom.hom.w B.topology le_rfl
  haveI : (AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
      𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      f.hom.hom.toFunctor f.hom.hom.w B.topology
      le_rfl).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  haveI := isContinuous_subsiteFunctor_topology B S hS f hf
  haveI := isCocontinuous_subsiteFunctor_topology B S hS f hf
  haveI : PreservesFiniteLimits (moduleSubsiteInverseImage B S hS f hf) :=
    (_root_.SheafOfModules.exactFunctor_pushforward_of_isCocontinuous.{u + 1, u, u + 1, u, u, u + 1}
      (primedSiteFunctor B S hS f hf)
      (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm)).1
  haveI : PreservesFiniteColimits (moduleSubsiteInverseImage B S hS f hf) :=
    (_root_.SheafOfModules.exactFunctor_pushforward_of_isCocontinuous.{u + 1, u, u + 1, u, u, u + 1}
      (primedSiteFunctor B S hS f hf)
      (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm)).2
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  haveI := alongFunctor_hasRightDerivedFunctor_of_isGrothendieckAbelian
    ((moduleSubsitePushforward B S hS f hf).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
  let Rf := ((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let αf := ((modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let Rf' := ((moduleSubsitePushforward B S hS f hf).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let αf' := ((moduleSubsitePushforward B S hS f hf).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let adjf := derivedAdjunctionOfExactLeftAdjoint (modulePullbackPushforwardAdjunction B S hS f)
    Rf αf exists_quasiIso_isKInjective_of_isGrothendieckAbelian
  let adjf' := derivedAdjunctionOfExactLeftAdjoint
    (moduleSubsiteInverseImageAdjunction B S hS f hf) Rf' αf'
    exists_quasiIso_isKInjective_of_isGrothendieckAbelian
  (conjugateIsoEquiv (adjf'.comp (derivedModuleLowerShriekSuccAdjunction B S hS 𝒳))
    ((derivedModuleLowerShriekSuccAdjunction B S hS 𝒴).comp adjf)).symm
    (moduleDerivedRestrictionBaseChangeIso B S hS f hf Rf Rf' αf αf')


end Derived

end AlgebraicGeometry.Stack.FlatFppf
