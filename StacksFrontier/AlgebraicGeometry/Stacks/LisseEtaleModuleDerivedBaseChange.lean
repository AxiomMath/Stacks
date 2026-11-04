module

public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardFormula
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.ForgettingTheModuleStructureUnivLE
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekCocontinuousSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictionAdjointOfRingEquality
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleDerivedModuleLowerShriekLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasicoherentPullbackExactness
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07AV for sheaves of modules on the lisse-étale sites

Let `f : 𝒳 ⟶ 𝒴` be a smooth 1-morphism of algebraic stacks, `f'` its restriction to the
lisse-étale sites, and `g`, `g'` the inclusions of the lisse-étale sites of `𝒴` and `𝒳`, with the
structure sheaves of **Stacks 06TV** on the étale sites and their restrictions on the lisse-étale
sites, so that `g^* = g⁻¹` and `(g')^* = (g')⁻¹` are restriction (**Stacks 0788** (1)(f)). This
file proves, with no hypothesis, the module case of the first identity of **Stacks 07AV**:

`Rf'_* ∘ (g')^* ≅ g^* ∘ Rf_*` on the unbounded derived categories of sheaves of modules.

## The argument

The source: "since cohomology of abelian groups and sheaves of modules agree we also conclude".
Two inputs feed `Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit`:

* the degree-zero square on sheaves of modules: the canonical comparison
  `Stacks.SheafOfModules.squareComparison` is invertible, because its underlying map of abelian
  presheaves is the base change of right Kan extensions, invertible at every sheaf by
  `AlgebraicGeometry.Stack.LisseEtale.isIso_ranBaseChange_app_of_isSheaf`;
* for a K-injective complex `I` of `𝒪_𝒳`-modules, `(g')^* I` computes `Rf'_*`: quasi-isomorphy
  of the direct image of a K-injective resolution is checked on underlying abelian complexes,
  where the direct image of modules is the direct image of abelian sheaves on the nose; the
  sections of the latter over a smooth object `y` of `𝒴` are corepresented by a sectionwise
  torsion-free sheaf; the underlying abelian complex of a K-injective complex of modules computes
  `RHom` out of every sectionwise torsion-free sheaf (Stacks 0D6J,
  `Stacks.Cohomology.ForgetModuleUnivLE.qh_map_bijective_single_of_isKInjective`); and by
  `AlgebraicGeometry.Stack.LisseEtale.qh_map_bijective_directImageCorep_restriction` so does its
  restriction to the lisse-étale site, out of the corepresenting sheaves.

## The second identity

`L(g')_! ∘ (f')^{-1} = f^{-1} ∘ Lg_!` is the conjugate of the first identity across the
composed adjunctions `Lg_! ⊣ g^*` (07BA's `derivedModuleLowerShriekSucc`) and `f^{-1} ⊣ Rf_*`. The
latter is derived from an adjunction of exact functors on sheaves of modules: `f^{-1}` is the
inverse image of Stacks 06WE, restriction along `f` read through the identification Stacks 06TW of
the restricted structure sheaf, and the structure map of `f_*` is the transpose of that
identification, so `Stacks.SheafOfModules.RestrictRan.restrictionAdjunctionOfEq` applies; on the
lisse-étale sites the structure map of `f'_*` is again such a transpose
(`Stacks.SheafOfModules.structureMapSquare_homEquiv_eqToHom`).

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.isIso_moduleSquareComparison`: **Stacks 07AT** (1) on
  sheaves of modules.
* `Stacks.SheafOfModules.isIso_derivedPushforwardUnit_inverseImage`: restricted K-injective
  complexes of modules compute the derived direct image along a cocontinuous functor out of a
  full subsite, granted that restricted K-injective complexes of abelian sheaves compute `RHom`
  out of the sheaves corepresenting its sections; the flat-fppf twin
  `StacksFrontier/AlgebraicGeometry/Stacks/FlatFppfModuleDerivedBaseChange.lean` uses it too.
* `AlgebraicGeometry.Stack.LisseEtale.moduleDerivedRestrictionBaseChangeIso`: **Stacks 07AV**,
  first identity, for sheaves of modules.
* `AlgebraicGeometry.Stack.LisseEtale.modulePullbackPushforwardAdjunction` and
  `AlgebraicGeometry.Stack.LisseEtale.moduleSubsiteInverseImageAdjunction`: `f^{-1} ⊣ f_*` and
  `(f')^{-1} ⊣ f'_*` on sheaves of modules.
* `AlgebraicGeometry.Stack.LisseEtale.moduleDerivedLowerShriekBaseChangeIso`: **Stacks 07AV**,
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

namespace AlgebraicGeometry.Stack.LisseEtale

universe u w

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat
  isContinuous_inclusion_topology' isCocontinuous_inclusion_topology'
  AlgebraicGeometry.Stack.instHasPointwiseRightKanExtensionRingCat
  AlgebraicGeometry.Stack.instHasPointwiseRightKanExtensionAddCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsSmooth B S hS f)

/-- The restriction `f'` of `f` commutes, on the nose, with the two inclusions of the lisse-étale
sites. -/
theorem primedSiteFunctor_comp_ι :
    primedSiteFunctor B S hS f hf ⋙ (smoothObject.{u, w} B S hS 𝒴).ι =
      (smoothObject.{u, w} B S hS 𝒳).ι ⋙ f.hom.hom.toFunctor := rfl

/-- The direct image `f'_*` of sheaves of modules along the restriction `f'` of a smooth
1-morphism to the lisse-étale sites, for the structure map forced by the square of
**Stacks 07AT** (1). -/
abbrev moduleSubsitePushforward :
    _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳) ⥤
      _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴) :=
  haveI := isCocontinuous_subsiteFunctor_topology.{u, w} B S hS f hf
  pushforwardCocontinuous.{u + 1} (primedSiteFunctor B S hS f hf)
    (restrictedStructureMap B S hS (etaleTopology B) (etaleTopology_le_topology B) f
      (smoothObject.{u, w} B S hS 𝒳) (smoothObject.{u, w} B S hS 𝒴)
      (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴) (primedSiteFunctor B S hS f hf)
      (primedSiteFunctor_comp_ι B S hS f hf))

/-- **Stacks 07AT** (1) on sheaves of modules: the canonical comparison
`f_* ∘ g^* ⟶ (g')^* ∘ f'_*` of `Stacks.SheafOfModules.squareComparison` is invertible. Its
underlying map of abelian presheaves at a sheaf of modules is the base change of right Kan
extensions, invertible by `AlgebraicGeometry.Stack.LisseEtale.isIso_ranBaseChange_app_of_isSheaf`,
and the forgetful functors to abelian sheaves and to abelian presheaves reflect isomorphisms. -/
theorem isIso_moduleSquareComparison :
    haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
      (etaleTopology B)).2
    haveI := isCocontinuous_subsiteFunctor_topology.{u, w} B S hS f hf
    IsIso (squareComparison (J' := topology.{u, w} B S hS 𝒳) (K' := topology.{u, w} B S hS 𝒴)
      (structureMapHomFunctor B S hS (etaleTopology B) (etaleTopology_le_topology B) f)
      (primedSiteFunctor_comp_ι B S hS f hf)) := by
  have := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).2
  have := isCocontinuous_subsiteFunctor_topology.{u, w} B S hS f hf
  have h : ∀ N : _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳),
      IsIso ((squareComparison (J' := topology.{u, w} B S hS 𝒳) (K' := topology.{u, w} B S hS 𝒴)
        (structureMapHomFunctor B S hS (etaleTopology B) (etaleTopology_le_topology B) f)
        (primedSiteFunctor_comp_ι B S hS f hf)).app N) := by
    intro N
    have hsq : (Stacks.Sites.CocontinuousExchange.twoSquare
        (primedSiteFunctor_comp_ι B S hS f hf)).op =
        SubsitePushforward.subsiteRanSquare f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
          (smoothObject_map.{u, w} B S hS f hf) := by
      ext X
      simp [Stacks.Sites.CocontinuousExchange.twoSquare, SubsitePushforward.subsiteRanSquare]
      rfl
    have h1 : IsIso (((Stacks.Sites.CocontinuousExchange.twoSquare
        (primedSiteFunctor_comp_ι B S hS f hf)).op.ranBaseChange
            (D := AddCommGrpCat.{u + 1})).app N.val.presheaf) := by
      rw [hsq]
      exact isIso_ranBaseChange_app_of_isSheaf B S hS f hf N.val.presheaf N.isSheaf
    exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (_root_.SheafOfModules.toSheaf.{u + 1}
      (subsiteRingStructureSheaf B S hS 𝒴) ⋙ sheafToPresheaf (topology.{u, w} B S hS 𝒴)
        AddCommGrpCat.{u + 1}) h1 inferInstance
  exact NatIso.isIso_of_isIso_app _

section Derived

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- **Restricted K-injective complexes of modules compute the derived direct image along a
cocontinuous functor out of a full subsite.** Let `P` cut out a full subsite of a site `(C, J)`
whose inclusion `g'` is continuous and cocontinuous, let `R` be a sheaf of rings on `C` and
`(g')^* R` its restriction, and let `u'` be a cocontinuous functor from the subsite to a site
`(D, K)` carrying a sheaf of rings `R'` with a structure map `φ : R' ⟶ u'_*((g')^* R)`. Suppose
(`hres`) that whenever a complex `Z` of abelian sheaves on `C` computes `RHom` in the homotopy
category out of every sectionwise torsion-free sheaf, its restriction `(g')^{-1} Z` computes `RHom`
out of each sheaf `pushforwardCorep J' u' y` corepresenting the sections over `y` of `u'_*`. Then
for a total right derived functor `Ru'_*` of the direct image of sheaves of modules along `u'` and
a K-injective complex `I` of `R`-modules, the comparison `u'_*((g')^* I) ⟶ Ru'_*((g')^* I)` is
an isomorphism.

Quasi-isomorphy of the direct image of a K-injective resolution `(g')^* I ⟶ J` is checked on the
underlying complexes of abelian sheaves, where the direct image of modules is the direct image of
abelian sheaves on the nose (`Stacks.SheafOfModules.pushforwardCocontinuous_comp_toSheaf`), and
then on sections over the objects `y` of `D`, which are corepresented by sectionwise torsion-free
sheaves. Morphisms out of those into the shifts of the underlying abelian complex of `J` are
computed in the homotopy category by **Stacks 0D6J**
(`Stacks.Cohomology.ForgetModuleUnivLE.qh_map_bijective_single_of_isKInjective`), and into the
shifts of the underlying abelian complex of `(g')^* I`, the restriction of that of `I`, by `hres`
fed with Stacks 0D6J on `C`. The lisse-étale and flat-fppf instances of `hres` are
`AlgebraicGeometry.Stack.LisseEtale.qh_map_bijective_directImageCorep_restriction` and
`AlgebraicGeometry.Stack.FlatFppf.qh_map_bijective_directImageCorep_restriction`. -/
theorem _root_.Stacks.SheafOfModules.isIso_derivedPushforwardUnit_inverseImage
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    {P : ObjectProperty C} [EssentiallySmall.{u} P.FullSubcategory]
    (J' : GrothendieckTopology P.FullSubcategory)
    [P.ι.IsContinuous J' J] [P.ι.IsCocontinuous J' J]
    {D : Type (u + 1)} [Category.{u} D] [EssentiallySmall.{u} D] (K : GrothendieckTopology D)
    (R' : Sheaf K RingCat.{u}) (u' : P.FullSubcategory ⥤ D) [u'.IsCocontinuous J' K]
    (φ : R' ⟶ (u'.sheafPushforwardCocontinuous RingCat.{u} J' K).obj (inverseImageRing J' J P.ι R))
    (Rf' : DerivedCategory (_root_.SheafOfModules.{u + 1} (inverseImageRing J' J P.ι R)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u + 1} R'))
    (αf' : (pushforwardCocontinuous.{u + 1} u' φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf')
    [hRf' : Rf'.IsRightDerivedFunctor αf' (HomotopyCategory.quasiIso
      (_root_.SheafOfModules.{u + 1} (inverseImageRing J' J P.ι R)) (ComplexShape.up ℤ))]
    (hres : ∀ (y : D) (Z : CochainComplex (Sheaf J AddCommGrpCat.{u + 1}) ℤ),
      (∀ (A₀ : Sheaf J AddCommGrpCat.{u + 1}), (∀ V, Module.IsTorsionFree ℤ (A₀.obj.obj V)) →
        ∀ m : ℤ, Function.Bijective (DerivedCategory.Qh.map :
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
              ((CochainComplex.singleFunctor _ 0).obj A₀) ⟶
            (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (Z⟦m⟧)) → _)) →
      ∀ n : ℤ, Function.Bijective (DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor _ 0).obj
              (Stacks.Cohomology.CocontinuousPushforwardCorep.pushforwardCorep.{u} J' u' y)) ⟶
          (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((P.ι.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J' J).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj Z⟦n⟧)) → _))
    (I : CochainComplex (_root_.SheafOfModules.{u + 1} R) ℤ) [hI : I.IsKInjective] :
    IsIso (αf'.app (((inverseImage.{u + 1} J' J P.ι R).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have : HasExt.{u + 1} (Sheaf J' AddCommGrpCat.{u + 1}) :=
    Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, u + 1}
  have : HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1}) :=
    Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, u + 1}
  have : IsGrothendieckAbelian.{u + 1}
      (_root_.SheafOfModules.{u + 1} (inverseImageRing J' J P.ι R)) :=
    Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u, u} _
  have : IsGrothendieckAbelian.{u + 1}
      (_root_.SheafOfModules.{u + 1} R) :=
    Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u, u} _
  have : IsGrothendieckAbelian.{u + 1} (Sheaf J' AddCommGrpCat.{u + 1}) :=
    Stacks.Cohomology.SiteModules.site_isGrothendieckAbelian_addCommGrp.{u + 1, u, u + 1}
  have : IsGrothendieckAbelian.{u + 1} (Sheaf J AddCommGrpCat.{u + 1}) :=
    Stacks.Cohomology.SiteModules.site_isGrothendieckAbelian_addCommGrp.{u + 1, u, u + 1}
  have : EnoughInjectives (Sheaf J' AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.enoughInjectives
  have : EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.enoughInjectives
  have : EnoughInjectives (_root_.SheafOfModules.{u + 1} (inverseImageRing J' J P.ι R)) :=
    IsGrothendieckAbelian.enoughInjectives
  have : EnoughInjectives (_root_.SheafOfModules.{u + 1} R) :=
    IsGrothendieckAbelian.enoughInjectives
  let M := ((inverseImage.{u + 1} J' J P.ι R).mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let Jc := (Stacks.Injectives.kInjectiveResolutionFunctor
    (_root_.SheafOfModules.{u + 1} (inverseImageRing J' J P.ι R))).obj M
  let q : M ⟶ Jc := (Stacks.Injectives.kInjectiveResolutionInclusion
    (_root_.SheafOfModules.{u + 1} (inverseImageRing J' J P.ι R))).app M
  have hq : QuasiIso q :=
    inferInstanceAs (QuasiIso ((Stacks.Injectives.kInjectiveResolutionInclusion
    (_root_.SheafOfModules.{u + 1} (inverseImageRing J' J P.ι R))).app M))
  have hJc : Jc.IsKInjective :=
    inferInstanceAs ((Stacks.Injectives.kInjectiveResolutionFunctor
    (_root_.SheafOfModules.{u + 1} (inverseImageRing J' J P.ι R))).obj M).IsKInjective
  have key : ∀ X : Type (u + 1), Module.IsTorsionFree ℤ (FreeAbelianGroup X) :=
    fun _ => Module.Flat.isTorsionFree
  have hqi : QuasiIso (((pushforwardCocontinuous.{u + 1} u' φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map q) := by
    rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
      (_root_.SheafOfModules.toSheaf.{u + 1} R')]
    show QuasiIso (((u'.sheafPushforwardCocontinuous
      AddCommGrpCat.{u + 1} J'
      K).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((_root_.SheafOfModules.toSheaf.{u + 1} (inverseImageRing J' J P.ι R)
          ).mapHomologicalComplex (ComplexShape.up ℤ)).map q))
    apply Stacks.Cohomology.CocontinuousPushforwardCorep.quasiIso_of_quasiIso_sheafToPresheaf
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro t
    have : ((sheafSections K AddCommGrpCat.{u + 1}).obj t).Additive :=
      ⟨fun {_ _ _ _} => rfl⟩
    show QuasiIso ((((u'.sheafPushforwardCocontinuous
      AddCommGrpCat.{u + 1} J' K) ⋙
        (sheafSections K AddCommGrpCat.{u + 1}).obj t
      ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((_root_.SheafOfModules.toSheaf.{u + 1} (inverseImageRing J' J P.ι R)
          ).mapHomologicalComplex (ComplexShape.up ℤ)).map q))
    refine Stacks.Cohomology.DerivedLowerShriek.quasiIso_mapHomologicalComplex_of_corepresentable
      _ _ (Stacks.Cohomology.CocontinuousPushforwardCorep.pushforwardCorepRepresentation.{u}
        J' K u'
          t.unop).symm _ (fun n => ?_)
    have : QuasiIso (((_root_.SheafOfModules.toSheaf.{u + 1} (inverseImageRing J' J P.ι R)
          ).mapHomologicalComplex (ComplexShape.up ℤ)).map q) := inferInstance
    have hP : ∀ V, Module.IsTorsionFree ℤ
        ((Stacks.Cohomology.CocontinuousPushforwardCorep.pushforwardCorep.{u}
          J' u' t.unop).obj.obj V) :=
      fun V => ModuleSheafCohomology.isTorsionFree_sheafify _ _ (fun W => key _) V
    refine Stacks.Cohomology.DerivedLowerShriek.bijective_postcomp_of_qh_bijective _ ?_
      (Stacks.Cohomology.ForgetModuleUnivLE.qh_map_bijective_single_of_isKInjective.{u, u, u, u + 1}
        J' (inverseImageRing J' J P.ι R) _ hP Jc n)
    exact hres t.unop (((_root_.SheafOfModules.toSheaf.{u + 1} R).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)
      (fun A₀ hA₀ m =>
        Stacks.Cohomology.ForgetModuleUnivLE.qh_map_bijective_single_of_isKInjective.{u, u, u,
          u + 1}
          J R A₀ hA₀ I m) n
  have hF : IsIso (((pushforwardCocontinuous.{u + 1} u' φ).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)) := by
    show IsIso (DerivedCategory.Qh.map
      (((pushforwardCocontinuous.{u + 1} u' φ).mapHomotopyCategory
        (ComplexShape.up ℤ)).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)))
    rw [Functor.mapHomotopyCategory_map]
    exact _root_.isIso_Qh_map_quotient_map_of_quasiIso _
  have hJ : IsIso (αf'.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Jc)) :=
    Stacks.Cohomology.DerivedLowerShriek.alongFunctor_rightDerivedUnit_isIso_at_kInjective _ Rf'
      αf' Jc
  have hR : IsIso ((DerivedCategory.Qh ⋙ Rf').map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)) := by
    exact inferInstanceAs (IsIso (Rf'.map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q))))
  have hnat := αf'.naturality ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)
  have : IsIso (αf'.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M) ≫
      (DerivedCategory.Qh ⋙ Rf').map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)) := by
    rw [← hnat]
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hR this

/-- **Stacks 07AV, first identity, for sheaves of modules on the lisse-étale sites:
`g^* ∘ Rf_* = Rf'_* ∘ (g')^*`.** For a smooth 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, total
right derived functors `Rf_*`, `Rf'_*` of the direct images of sheaves of modules along `f` and
along its restriction `f'` to the lisse-étale sites, and `g^*`, `(g')^*` the restrictions of
sheaves of modules to the lisse-étale sites (which are `g⁻¹`, `(g')⁻¹`),

`(g')^* ⋙ Rf'_* ≅ Rf_* ⋙ g^*`

on the unbounded derived categories, with no further hypothesis. It is
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit` at the degree-zero square
`AlgebraicGeometry.Stack.LisseEtale.isIso_moduleSquareComparison` and at
`Stacks.SheafOfModules.isIso_derivedPushforwardUnit_inverseImage`, fed with
`AlgebraicGeometry.Stack.LisseEtale.qh_map_bijective_directImageCorep_restriction`. -/
@[stacks 07AV "the module case for the lisse-étale sites, first identity: \
g⁻¹ ∘ Rf_* = Rf'_* ∘ (g')⁻¹ on the unbounded derived categories of sheaves of modules, as an \
isomorphism (g')^* ⋙ Rf'_* ≅ Rf_* ⋙ g^* for any total right derived functors Rf_*, Rf'_* of the two \
direct images, with no further hypothesis: the degree-zero square of Stacks 07AT (1) on modules \
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
  haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).2
  haveI := isCocontinuous_subsiteFunctor_topology.{u, w} B S hS f hf
  haveI := isIso_moduleSquareComparison B S hS f hf
  Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeIsoOfUnit
    (moduleInverseImage B S hS 𝒳) (moduleInverseImage B S hS 𝒴)
    (modulePushforward B S hS f) (moduleSubsitePushforward B S hS f hf) Rf Rf' αf αf'
    (asIso (squareComparison (J' := topology.{u, w} B S hS 𝒳) (K' := topology.{u, w} B S hS 𝒴)
      (structureMapHomFunctor B S hS (etaleTopology B) (etaleTopology_le_topology B) f)
      (primedSiteFunctor_comp_ι B S hS f hf))).symm
    (fun I hI => haveI := hI
      isIso_derivedPushforwardUnit_inverseImage (ambientRingStructureSheaf B S hS 𝒳)
        (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴)
        (subsiteRingStructureSheaf B S hS 𝒴) (primedSiteFunctor B S hS f hf)
        (restrictedStructureMap B S hS (etaleTopology B) (etaleTopology_le_topology B) f
          (smoothObject.{u, w} B S hS 𝒳) (smoothObject.{u, w} B S hS 𝒴)
          (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴) (primedSiteFunctor B S hS f hf)
          (primedSiteFunctor_comp_ι B S hS f hf)) Rf' αf'
        (fun y Z hZ n => qh_map_bijective_directImageCorep_restriction B S hS f hf
          (topology.{u, w} B S hS 𝒳)
          (inclusionTopology_eq_topology.{u, w} B S hS 𝒳
            (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)) y Z hZ n) I)

/-- **Stacks 06TW on the lisse-étale sites.** The restriction along the restriction `f'` of a
smooth 1-morphism of the structure sheaf of the lisse-étale site of `𝒴` is the structure sheaf of
the lisse-étale site of `𝒳`: both are restrictions of the structure sheaf of `𝒴`, along
`f' ⋙ g = g' ⋙ f`, and the restriction of that of `𝒴` along `f` is that of `𝒳`. -/
theorem subsiteRingStructureSheaf_inverseImageRing :
    haveI := isContinuous_subsiteFunctor_topology.{u, w} B S hS f hf
    inverseImageRing (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴)
        (primedSiteFunctor B S hS f hf) (subsiteRingStructureSheaf B S hS 𝒴) =
      subsiteRingStructureSheaf B S hS 𝒳 :=
  congrArg (inverseImageRing (topology.{u, w} B S hS 𝒳) (ambientTopology B S hS 𝒳)
      (smoothObject.{u, w} B S hS 𝒳).ι)
    (sheafPushforwardContinuous_ringStructureSheafCore B S hS (etaleTopology B)
      (etaleTopology_le_topology B) f)

/-- The inverse image `(f')^{-1}` of sheaves of modules along the restriction `f'` of a smooth
1-morphism to the lisse-étale sites: restriction along `f'`, read over the structure sheaf of the
lisse-étale site of `𝒳` through
`AlgebraicGeometry.Stack.LisseEtale.subsiteRingStructureSheaf_inverseImageRing`. -/
abbrev moduleSubsiteInverseImage :
    _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴) ⥤
      _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳) :=
  haveI := isContinuous_subsiteFunctor_topology.{u, w} B S hS f hf
  _root_.SheafOfModules.pushforward.{u + 1} (F := primedSiteFunctor B S hS f hf)
    (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm)

/-- **The inverse image `f^{-1}` of sheaves of modules of Stacks 06WE is left adjoint to the
direct image `f_*` of the morphism of étale topoi.** The direct image is
`Stacks.SheafOfModules.pushforwardCocontinuous` over the transpose of the identification
**Stacks 06TW** of the restricted structure sheaf, so this is
`Stacks.SheafOfModules.RestrictRan.restrictionAdjunctionOfEq`, the inverse image of 06WE being
restriction along `f` read through the same identification. -/
@[sga "4 Vbis 1.3.6" "special case"]
def modulePullbackPushforwardAdjunction :
    AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS 𝒳.val.val.p
      𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor f.hom.hom.w
        (etaleTopology B) (etaleTopology_le_topology B) ⊣
      modulePushforward B S hS f :=
  haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).1
  haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).2
  (RestrictRan.restrictionAdjunctionOfEq.{u + 1} f.hom.hom.toFunctor (ambientTopology B S hS 𝒳)
    (ambientTopology B S hS 𝒴) (ambientRingStructureSheaf B S hS 𝒴)
    (sheafPushforwardContinuous_ringStructureSheafCore B S hS (etaleTopology B)
      (etaleTopology_le_topology B) f)).ofNatIsoLeft
    (_root_.SheafOfModules.pushforwardCongr (ObjectProperty.hom_ext _
      (eqToHom_map (sheafToPresheaf _ RingCat.{u}) _)))

/-- **The inverse image `(f')^{-1}` of sheaves of modules on the lisse-étale sites is left
adjoint to the direct image `f'_*`.** The structure map of `f'_*` is the restriction of that of
`f_*` (`Stacks.SheafOfModules.structureMapSquare`), which is again the transpose of an equality of
restricted structure sheaves (`Stacks.SheafOfModules.structureMapSquare_homEquiv_eqToHom`), so
`Stacks.SheafOfModules.RestrictRan.restrictionAdjunctionOfEq` applies. -/
def moduleSubsiteInverseImageAdjunction :
    moduleSubsiteInverseImage B S hS f hf ⊣ moduleSubsitePushforward B S hS f hf := by
  haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).1
  haveI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
    (etaleTopology B)).2
  haveI := isContinuous_subsiteFunctor_topology.{u, w} B S hS f hf
  haveI := isCocontinuous_subsiteFunctor_topology.{u, w} B S hS f hf
  have e := structureMapSquare_homEquiv_eqToHom (J' := topology.{u, w} B S hS 𝒳)
    (K' := topology.{u, w} B S hS 𝒴) (J := ambientTopology B S hS 𝒳)
    (K := ambientTopology B S hS 𝒴) (primedSiteFunctor_comp_ι B S hS f hf)
    (sheafPushforwardContinuous_ringStructureSheafCore B S hS (etaleTopology B)
      (etaleTopology_le_topology B) f)
    (subsiteRingStructureSheaf_inverseImageRing B S hS f hf)
  change _ ⊣ pushforwardCocontinuous.{u + 1} (primedSiteFunctor B S hS f hf)
    (structureMapSquare (J' := topology.{u, w} B S hS 𝒳) (K' := topology.{u, w} B S hS 𝒴)
      (structureMapHomFunctor B S hS (etaleTopology B) (etaleTopology_le_topology B) f)
      (primedSiteFunctor_comp_ι B S hS f hf))
  rw [structureMapHomFunctor, e]
  exact RestrictRan.restrictionAdjunctionOfEq.{u + 1} (primedSiteFunctor B S hS f hf)
    (topology.{u, w} B S hS 𝒳) (topology.{u, w} B S hS 𝒴) (subsiteRingStructureSheaf B S hS 𝒴)
    (subsiteRingStructureSheaf_inverseImageRing B S hS f hf)


/-- The inverse image `f^{-1}` of sheaves of modules of **Stacks 06WE** along a 1-morphism of
algebraic stacks, for the étale sites, on the unbounded derived categories. It is exact
(`AlgebraicGeometry.Stack.preservesFiniteLimits_modulePullback` and
`AlgebraicGeometry.Stack.preservesFiniteColimits_modulePullback`), so it needs no deriving. -/
abbrev derivedModulePullback :
    DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒴)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) :=
  haveI := preservesFiniteLimits_modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    f.hom.hom.toFunctor f.hom.hom.w (etaleTopology B) (etaleTopology_le_topology B)
  haveI := preservesFiniteColimits_modulePullback.{u, u + 1, u, u, u + 1, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    f.hom.hom.toFunctor f.hom.hom.w (etaleTopology B) (etaleTopology_le_topology B)
  haveI : (AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
      𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      f.hom.hom.toFunctor f.hom.hom.w (etaleTopology B)
      (etaleTopology_le_topology B)).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  (AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS 𝒳.val.val.p
    𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
    f.hom.hom.w (etaleTopology B) (etaleTopology_le_topology B)).mapDerivedCategory

/-- The inverse image `(f')^{-1}` of sheaves of modules along the restriction `f'` of a smooth
1-morphism to the lisse-étale sites, on the unbounded derived categories. It is exact, `f'` being
continuous and cocontinuous (`SheafOfModules.exactFunctor_pushforward_of_isCocontinuous`). -/
abbrev derivedModuleSubsiteInverseImage :
    DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) :=
  haveI := isContinuous_subsiteFunctor_topology.{u, w} B S hS f hf
  haveI := isCocontinuous_subsiteFunctor_topology.{u, w} B S hS f hf
  haveI : PreservesFiniteLimits (moduleSubsiteInverseImage B S hS f hf) :=
    (_root_.SheafOfModules.exactFunctor_pushforward_of_isCocontinuous.{u + 1, u, u + 1, u, u, u + 1}
      (primedSiteFunctor B S hS f hf)
      (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm)).1
  haveI : PreservesFiniteColimits (moduleSubsiteInverseImage B S hS f hf) :=
    (_root_.SheafOfModules.exactFunctor_pushforward_of_isCocontinuous.{u + 1, u, u + 1, u, u, u + 1}
      (primedSiteFunctor B S hS f hf)
      (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm)).2
  (moduleSubsiteInverseImage B S hS f hf).mapDerivedCategory

/-- **Stacks 07AV, the module case for the lisse-étale sites, second identity.** Let
`f : 𝒳 ⟶ 𝒴` be a smooth 1-morphism of algebraic stacks, `f'` its restriction to the lisse-étale
sites, and `Lg_!`, `L(g')_!` the derived lower shrieks of sheaves of modules along the inclusions
of the lisse-étale sites (`AlgebraicGeometry.Stack.LisseEtale.derivedModuleLowerShriekSucc`). Then

`Lg_! ⋙ f^{-1} ≅ (f')^{-1} ⋙ L(g')_!`

on the unbounded derived categories of sheaves of modules, that is,
`L(g')_! ∘ (f')^{-1} = f^{-1} ∘ Lg_!`. Here `f^{-1}`, `(f')^{-1}` are the exact inverse images
(Stacks 06WE, and restriction along `f'`), left adjoint to the canonical total right derived
direct images `Rf_*`, `Rf'_*` (`derivedAdjunctionOfExactLeftAdjoint` on
`AlgebraicGeometry.Stack.LisseEtale.modulePullbackPushforwardAdjunction` and
`AlgebraicGeometry.Stack.LisseEtale.moduleSubsiteInverseImageAdjunction`), and the isomorphism
is the conjugate, across the composed adjunctions, of the first identity
`AlgebraicGeometry.Stack.LisseEtale.moduleDerivedRestrictionBaseChangeIso`. -/
@[stacks 07AV "the module case for the lisse-étale sites, second identity: \
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
    f.hom.hom.toFunctor f.hom.hom.w (etaleTopology B) (etaleTopology_le_topology B)
  haveI := preservesFiniteColimits_modulePullback.{u, u + 1, u, u, u + 1, u} B S hS
    𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    f.hom.hom.toFunctor f.hom.hom.w (etaleTopology B) (etaleTopology_le_topology B)
  haveI : (AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
      𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      f.hom.hom.toFunctor f.hom.hom.w (etaleTopology B)
      (etaleTopology_le_topology B)).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  haveI := isContinuous_subsiteFunctor_topology.{u, w} B S hS f hf
  haveI := isCocontinuous_subsiteFunctor_topology.{u, w} B S hS f hf
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

end AlgebraicGeometry.Stack.LisseEtale
