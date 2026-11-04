module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.ComplexMapInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.MixedHomTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSmallModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentModuleULift
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentRestrictionAnyUniverse

/-!
# `Ext` out of the naive cotangent complex on the small étale site and on its model

Let `X` be an algebraic space over a scheme `S : Scheme.{u}`. Its small étale site has objects in
`Type (u + 1)`, and `AlgebraicGeometry.Space.smallEtaleModelRingedTopos` is the equivalent site
with objects in `Type u`, along `G = (smallEtaleModelEquiv X).inverse : model ⥤ X_étale`. For a
homomorphism `b : A ⟶ 𝒪` of sheaves of commutative rings on `X_étale`, the naive cotangent
complex `NL_{𝒪/A}` of Stacks 08TW is a complex of sheaves of modules with sections in
`Type (u + 1)` (the universe of the objects of the site), while on the model `NL_{G^s𝒪/G^sA}` has
its sections in `Type u`. This file identifies the `Ext` groups out of the two:

`Ext^n_{𝒪}(NL_{𝒪/A}, M) ≅ Ext^n_{G^s𝒪}(NL_{G^s𝒪/G^sA}, G^s M)`

for every sheaf of `𝒪`-modules `M` with sections in `Type u` (lifted to `Type (u + 1)` on the
left), every `n : ℤ` and any models of the two derived categories.

## The argument

Restriction along `G` of sheaves of modules with sections in `Type (u + 1)` is an equivalence
(`Stacks.SheafOfModules.reindexEquivalence`), and it carries `NL_{𝒪/A}` to the naive cotangent
complex of the model formed with sections in `Type (u + 1)`
(`Stacks.SheafOfModules.restrictionNaiveCotangentComplexIsoAnyUniverse`, Stacks 08TZ for the
equivalence of topoi), which is the universe lift of `NL_{G^s𝒪/G^sA}`
(`Stacks.SheafOfModules.naiveCotangentComplexModuleULiftIso`). Both the equivalence and the
universe lift are fully faithful exact functors preserving injective objects
(`Stacks.SheafOfModules.preservesInjectiveObjects_moduleULift`), so they do not change `Ext`
(`CategoryTheory.Functor.shiftedHomSingleAddEquivOfPreservesInjectives`).

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleModelToposHom`: the equivalence of topoi between the model
  and `X_étale`, whose inverse image is restriction along `G`.
* `AlgebraicGeometry.Space.smallEtaleModelNaiveCotangentComplexIso`: the restriction of
  `NL_{𝒪/A}` is the universe lift of `NL_{G^s𝒪/G^sA}`.
* `AlgebraicGeometry.Space.smallEtaleModelNaiveCotangentExtAddEquiv`: the identification of
  `Ext` groups.

## References

* [Stacks Project, Tag 08TZ](https://stacks.math.columbia.edu/tag/08TZ)
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t t' u

namespace AlgebraicGeometry.Space

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The comparison `G : model ⥤ X_étale` read from the model, continuous. -/
instance smallEtaleModelEquiv_symm_functor_isContinuous :
    (smallEtaleModelEquiv B S hS X).symm.functor.IsContinuous
      (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1) :=
  inferInstanceAs ((smallEtaleModelEquiv B S hS X).inverse.IsContinuous _ _)

/-- The comparison `X_étale ⥤ model`, continuous. -/
instance smallEtaleModelEquiv_symm_inverse_isContinuous :
    (smallEtaleModelEquiv B S hS X).symm.inverse.IsContinuous
      (SmallEtale.topology B S hS X.1) (smallEtaleModelTopology B S hS X.1) :=
  inferInstanceAs ((smallEtaleModelEquiv B S hS X).functor.IsContinuous _ _)

/-- **The equivalence of topoi between the model and `X_étale`**, as a morphism of topoi
`Sh(model) ⟶ Sh(X_étale)` whose inverse image is restriction along
`G = (smallEtaleModelEquiv X).inverse` and whose direct image is restriction along the other
comparison. -/
def smallEtaleModelToposHom :
    MorphismOfTopoi (Sheaf (smallEtaleModelTopology B S hS X.1) (Type u))
      (Sheaf (SmallEtale.topology B S hS X.1) (Type u)) where
  pushforward := (smallEtaleModelEquiv B S hS X).functor.sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B S hS X.1) (smallEtaleModelTopology B S hS X.1)
  inverseImage := (smallEtaleModelEquiv B S hS X).inverse.sheafPushforwardContinuous (Type u)
    (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)
  adj := (Equivalence.sheafCongr (SmallEtale.topology B S hS X.1)
    (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X) (Type u)).toAdjunction
  preservesFiniteLimits := inferInstance

variable {B S hS X} {A O : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} (b : A ⟶ O)

/-- Restriction of sheaves of `𝒪`-modules to the model, with sections in `Type t`. -/
abbrev smallEtaleModelModuleRestrictionAt (O : Sheaf (SmallEtale.topology B S hS X.1)
    CommRingCat.{u}) :=
  Stacks.Sites.Conormal.ringSheafModuleRestrictionAnyUniverse.{u, u, u, u + 1, u, t}
    (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)
    (smallEtaleModelEquiv B S hS X).inverse O

/-- Restriction of sheaves of modules to the model is an equivalence, at any universe of
sections: it is the transport along the equivalence of sites. -/
instance isEquivalence_smallEtaleModelModuleRestrictionAt :
    (smallEtaleModelModuleRestrictionAt.{t} O).IsEquivalence :=
  inferInstanceAs (Stacks.SheafOfModules.reindexEquivalence.{u, t}
    (smallEtaleModelEquiv B S hS X).symm
      (Stacks.SheafOfModules.Tensor.ringSheaf O)).functor.IsEquivalence

/-- **The restriction of `NL_{𝒪/A}` to the model is the universe lift of `NL_{G^s𝒪/G^sA}`**, as
complexes of sheaves of modules with sections in `Type (u + 1)`. -/
def smallEtaleModelNaiveCotangentComplexIso :
    ((smallEtaleModelModuleRestrictionAt.{u + 1} O).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u + 1, u, u}
          (SmallEtale.topology B S hS X.1) A O b) ≅
      ((Stacks.SheafOfModules.moduleULift.{u + 1, u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (((smallEtaleModelEquiv B S hS X).inverse.sheafPushforwardContinuous CommRingCat.{u}
            (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)).obj
              O))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
          (smallEtaleModelTopology B S hS X.1)
          (((smallEtaleModelEquiv B S hS X).inverse.sheafPushforwardContinuous CommRingCat.{u}
            (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)).obj A)
          (((smallEtaleModelEquiv B S hS X).inverse.sheafPushforwardContinuous CommRingCat.{u}
            (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)).obj O)
          (((smallEtaleModelEquiv B S hS X).inverse.sheafPushforwardContinuous CommRingCat.{u}
            (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)).map b)) :=
  Stacks.SheafOfModules.restrictionNaiveCotangentComplexIsoAnyUniverse.{u, u, u, u + 1, u, u}
      (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)
      (smallEtaleModelEquiv B S hS X).inverse (smallEtaleModelToposHom B S hS X) (Iso.refl _)
      A O b ≪≫
    (Stacks.SheafOfModules.naiveCotangentComplexModuleULiftIso.{u + 1, u, u, u, u}
      (smallEtaleModelTopology B S hS X.1) _ _ _).symm

/-- The restriction `G^s𝒪` to the model of a sheaf of commutative rings on `X_étale`. -/
abbrev smallEtaleModelRingRestriction (O : Sheaf (SmallEtale.topology B S hS X.1)
    CommRingCat.{u}) : Sheaf (smallEtaleModelTopology B S hS X.1) CommRingCat.{u} :=
  ((smallEtaleModelEquiv B S hS X).inverse.sheafPushforwardContinuous
    CommRingCat.{u} (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)).obj O

/-- Restricting the universe lift of a sheaf of `𝒪`-modules to the model is lifting its
restriction. -/
def smallEtaleModelModuleRestrictionULiftIso
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (smallEtaleModelModuleRestrictionAt.{u + 1} O).obj
        ((Stacks.SheafOfModules.moduleULift.{u + 1, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj M) ≅
      (Stacks.SheafOfModules.moduleULift.{u + 1, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingRestriction O))).obj
        ((smallEtaleModelModuleRestrictionAt.{u} O).obj M) :=
  Iso.refl _

/-- The abelian structure of the `𝒪`-modules with sections in `Type (u + 1)`, named so that
instance search does not meet the universe constraint posed by competing instances stated at a
maximum of universes. -/
local instance (priority := high) abelianLargeModules :
    Abelian (_root_.SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  SheafOfModules.instAbelian _

/-- Sheafification of abelian presheaves on the model with sections in `Type (u + 1)`, named so
that instance search does not meet the universe constraints of competing instances. -/
local instance (priority := high) hasSheafifyLargeModel :
    HasSheafify (smallEtaleModelTopology B S hS X.1) AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify

/-- Local bijectivity detects the isomorphisms of abelian sheaves on the model with sections in
`Type (u + 1)`. -/
local instance (priority := high) wEqualsLocallyBijectiveLargeModel :
    (smallEtaleModelTopology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective

/-- The abelian structure of the sheaves of modules on the model with sections in
`Type (u + 1)`, named for the same reason. -/
local instance (priority := high) abelianLargeModelModules :
    Abelian (_root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingRestriction O))) :=
  SheafOfModules.instAbelian _

/-- **`Ext` out of `NL_{𝒪/A}` on `X_étale` is `Ext` out of `NL_{G^s𝒪/G^sA}` on the model**:
for a sheaf of `𝒪`-modules `M` with sections in `Type u`,
`Ext^n_𝒪(NL_{𝒪/A}, M) ≅ Ext^n_{G^s𝒪}(NL_{G^s𝒪/G^sA}, G^s M)`, where on `X_étale` the complex
has sections in `Type (u + 1)` and `M` is lifted to that universe, for every `n` and any models
of the two derived categories. -/
def smallEtaleModelNaiveCotangentExtAddEquiv
    [HasDerivedCategory.{t} (_root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf O))]
    [HasDerivedCategory.{t'} (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingRestriction O)))]
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (n : ℤ) :
    DerivedCategory.Ext
        (DerivedCategory.Q.obj (Stacks.SheafOfModules.naiveCotangentComplex.{u, u + 1, u, u}
          (SmallEtale.topology B S hS X.1) A O b))
        ((DerivedCategory.singleFunctor _ 0).obj ((Stacks.SheafOfModules.moduleULift.{u + 1, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf O)).obj M)) n ≃+
      DerivedCategory.Ext
        (DerivedCategory.Q.obj (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
          (smallEtaleModelTopology B S hS X.1)
          (((smallEtaleModelEquiv B S hS X).inverse.sheafPushforwardContinuous CommRingCat.{u}
            (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)).obj A)
          (smallEtaleModelRingRestriction O)
          (((smallEtaleModelEquiv B S hS X).inverse.sheafPushforwardContinuous CommRingCat.{u}
            (smallEtaleModelTopology B S hS X.1) (SmallEtale.topology B S hS X.1)).map b)))
        ((DerivedCategory.singleFunctor _ 0).obj
          ((smallEtaleModelModuleRestrictionAt.{u} O).obj M)) n := by
  letI := HasDerivedCategory.standard
    (_root_.SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingRestriction O)))
  haveI := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u, 0}
    (Stacks.SheafOfModules.Tensor.ringSheaf O)
  haveI := Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u, u, u, 0}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingRestriction O))
  haveI := Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u, u, u, u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingRestriction O))
  haveI := Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u, u, u, 0}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingRestriction O))
  let L := Stacks.SheafOfModules.moduleULift.{u + 1, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingRestriction O))
  haveI : L.Full := (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u} _).full
  haveI : L.Faithful := (Stacks.SheafOfModules.moduleULiftFullyFaithful.{u + 1, u} _).faithful
  haveI : PreservesFiniteLimits L := RingedSite.Mixed.preservesFiniteLimits_moduleULift.{u + 1, u} _
  haveI : PreservesFiniteColimits L :=
    Stacks.SheafOfModules.preservesFiniteColimits_moduleULift.{u + 1, u} _
  haveI : L.PreservesInjectiveObjects :=
    Stacks.SheafOfModules.preservesInjectiveObjects_moduleULift.{u + 1, u, u, u}
  exact ((smallEtaleModelModuleRestrictionAt.{u + 1}
      O).shiftedHomSingleAddEquivOfPreservesInjectives _ _ n).trans <|
    ((Linear.homCongr ℤ (DerivedCategory.Q.mapIso (smallEtaleModelNaiveCotangentComplexIso b))
      ((shiftFunctor _ n).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
        (smallEtaleModelModuleRestrictionULiftIso M)))).toAddEquiv).trans <|
    (L.shiftedHomSingleAddEquivOfPreservesInjectives _ _ n).symm

end AlgebraicGeometry.Space

end
