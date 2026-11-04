module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraExtensionPushoutEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentHomologyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentCocontinuousRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentUniverseLift
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftDerived

/-!
# Pushout of square-zero extensions on a qcqs algebraic space: the unconditional form

Let `f : X ⟶ Y` be a morphism of algebraic spaces with `X` quasi-compact and quasi-separated.
`AlgebraicGeometry.Space.isEquivalence_of_isPushoutFunctor_of_isIso_coherator_map` proves
[Stacks Project, Tag 0D3P] from the membership of `NL_{X/Y}` in `D_QCoh(𝒪_X)`, where `NL_{X/Y}`
is formed on the `Type u` model of the small étale site and carried to `D(𝒪_X)` by the
Comparison Lemma. This file proves that membership from [Stacks Project, Tag 0D0Y], the
quasi-coherence of the cohomology sheaves of `NL_{X/Y}` formed on the small étale site itself,
and registers the tag.

## The comparison

The two complexes have their sections in different universes: `NL_{X/Y}` of
`AlgebraicGeometry.Space.naiveCotangentComplex` in `Type (u + 1)`, the one on the model in
`Type u`. They are compared at `Type (u + 1)` on the model:

* restriction to the model carries `NL_{X/Y}` to the naive cotangent complex of the restriction
  (`Stacks.SheafOfModules.naiveCotangentComplexRestrictionIso`), which is the universe lift of the
  one on the model (`Stacks.SheafOfModules.naiveCotangentComplexULiftIso`);
* restriction of `(u + 1)`-modules to the model is an equivalence
  (`AlgebraicGeometry.Space.smallEtaleModelModulesEquivULift`), the transport along the identity
  ring transport;
* raising the universe of the sections commutes with restriction, and preserves and reflects
  quasi-coherence on `X` (`AlgebraicGeometry.Space.isQuasicoherentOnSite_spaceULift_iff`, from
  the characterisation of quasi-coherence by the affine étale charts).

All four functors involved are exact, so cohomology conditions transfer along them
(`Stacks.UniverseLift.derivedCategoryB_mapDerivedCategory_obj_iff`).

## Main results

* `AlgebraicGeometry.Space.qcohDerivedProp_modelNaiveCotangentComplex`: `NL_{X/Y}` on the model,
  carried to `D(𝒪_X)`, lies in `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.isEquivalence_of_isPushoutFunctor_of_isIso_coherator_map_of_qcqs`:
  [Stacks Project, Tag 0D3P].

## References

* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
* [Stacks Project, Tag 0D0Y](https://stacks.math.columbia.edu/tag/0D0Y)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Deformation Deformation.AlgebraExtension

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The ring transport from `𝒪_X` to its restriction to the model: the identity of each ring. -/
def smallEtaleModelRingTransport (X : AlgebraicSpaces B S hS) :
    Stacks.UniverseLift.RingTransport (modelEquiv B S hS X)
      (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((ringRes (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X).inverse).obj
          (structureSheaf B S hS X.1 X.2))).obj where
  iso _ := RingEquiv.refl _
  naturality _ _ := rfl

/-- Modules with sections in `Type (u + 1)` on the small étale site of `X` and on its model are
equivalent, by restriction. -/
def smallEtaleModelModulesEquivULift (X : AlgebraicSpaces B S hS) :
    SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)) ≌
      SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((ringRes (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X).inverse).obj
          (structureSheaf B S hS X.1 X.2))) :=
  (smallEtaleModelRingTransport B S hS X).sheafEquivalence

/-- The structure sheaf of rings of the model. -/
abbrev modelRingSheaf (X : AlgebraicSpaces B S hS) :=
  Stacks.SheafOfModules.Tensor.ringSheaf
    ((ringRes (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X).inverse).obj
      (structureSheaf B S hS X.1 X.2))

/-- Raising the universe of the sections of modules on the model from `u` to `u + 1`. -/
abbrev modelULift (X : AlgebraicSpaces B S hS) :
    SheafOfModules.{u} (modelRingSheaf B S hS X) ⥤ SheafOfModules.{u + 1} (modelRingSheaf B S hS X)
        :=
  SheafOfModules.uliftForPresentationFunctor.{u, u, u, u, u + 1}

/-- Raising the universe of the sections of `𝒪_X`-modules from `u` to `u + 1`. -/
abbrev spaceULift (X : AlgebraicSpaces B S hS) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)) ⥤
      SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2)) :=
  SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, u, u + 1}

/-- Abelian sheafification at `u + 1` on the model. -/
instance (priority := high) modelHasSheafifyULift (X : AlgebraicSpaces B S hS) :
    HasSheafify (smallEtaleModelTopology B S hS X.1) AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify

/-- Abelian sheafification at `u + 1` on the model inverts exactly the locally bijective
morphisms. -/
instance (priority := high) modelWEqualsLocallyBijectiveULift (X : AlgebraicSpaces B S hS) :
    (smallEtaleModelTopology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective

/-- The functor of `smallEtaleModelModulesEquivULift` is additive. -/
instance smallEtaleModelModulesEquivULift_functor_additive (X : AlgebraicSpaces B S hS) :
    (smallEtaleModelModulesEquivULift B S hS X).functor.Additive :=
  inferInstanceAs (smallEtaleModelRingTransport B S hS X).sheafFunctor.Additive

/-- Quasi-coherence is invariant under isomorphism. -/
theorem isQuasicoherentOnSite_iff_of_iso {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u + 1} R} (e : M ≅ N) :
    M.IsQuasicoherentOnSite ↔ N.IsQuasicoherentOnSite :=
  ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso e, SheafOfModules.IsQuasicoherentOnSite.of_iso
      e.symm⟩

/-- Raising the universe of modules on the model preserves zero morphisms. -/
instance modelUliftFunctor_preservesZeroMorphisms (X : AlgebraicSpaces B S hS) :
    (SheafOfModules.uliftFunctor.{u, u, u, u, u + 1}
      (R := modelRingSheaf B S hS X)).PreservesZeroMorphisms where
  map_zero _ _ := by ext; rfl

/-- The functor `modelULift` is additive. -/
instance modelULift_additive (X : AlgebraicSpaces B S hS) : (modelULift B S hS X).Additive where
  map_add := by intros; ext; rfl

/-- The functor `modelULift` preserves finite colimits. -/
instance modelULift_preservesFiniteColimits (X : AlgebraicSpaces B S hS) :
    PreservesFiniteColimits (modelULift B S hS X) :=
  SheafOfModules.preservesFiniteColimits_uliftForPresentationFunctor.{u, u, u, u, u + 1}

/-- A `u`-module on `X` is quasi-coherent exactly when its universe lift is. -/
theorem isQuasicoherentOnSite_spaceULift_iff (X : AlgebraicSpaces B S hS)
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1
        X.2))) :
    ((spaceULift B S hS X).obj G).IsQuasicoherentOnSite ↔ G.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_anyUniverse B S hS X.1 X.2 _).trans
    ((isCartesianOnAffineCharts_uliftForPresentation_iff B S hS X.1 X.2 G).trans
      (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_anyUniverse B S hS X.1 X.2 G).symm)

/-- Lifting the universe commutes with restriction to the model. -/
def spaceULiftModelIso (X : AlgebraicSpaces B S hS) (M : RestrictedModelModules B S hS X) :
    (spaceULift B S hS X).obj ((modelModulesEquiv B S hS X).inverse.obj M) ≅
      (smallEtaleModelModulesEquivULift B S hS X).inverse.obj ((modelULift B S hS X).obj M) :=
  (smallEtaleModelModulesEquivULift B S hS X).unitIso.app _ ≪≫
    (smallEtaleModelModulesEquivULift B S hS X).inverse.mapIso
      ((modelULift B S hS X).mapIso ((modelModulesEquiv B S hS X).counitIso.app M))

/-- The property of `(u + 1)`-modules on the model corresponding to a quasi-coherent `𝒪_X`-module.
-/
abbrev modelQcohProp (X : AlgebraicSpaces B S hS) : ObjectProperty (SheafOfModules.{u + 1}
    (modelRingSheaf B S hS X)) :=
  fun N ↦ ((smallEtaleModelModulesEquivULift B S hS X).inverse.obj N).IsQuasicoherentOnSite

/-- The property `modelQcohProp` is closed under isomorphisms. -/
instance modelQcohProp_isClosedUnderIsomorphisms (X : AlgebraicSpaces B S hS) :
    (modelQcohProp B S hS X).IsClosedUnderIsomorphisms where
  of_iso e h := SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((smallEtaleModelModulesEquivULift B S hS X).inverse.mapIso e) h

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian
attribute [local instance] HasDerivedCategory.standard

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

attribute [local instance] hasWeakSheafify_commRingCat_smallEtale

/-- Membership in `D_P(𝒜)` is invariant under isomorphism. -/
theorem derivedCategoryB_of_iso {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
    (P : ObjectProperty 𝒜) [P.IsClosedUnderIsomorphisms] {K K' : DerivedCategory 𝒜} (e : K ≅ K')
    (h : DerivedCategoryB.derivedCategoryB P K) : DerivedCategoryB.derivedCategoryB P K' :=
  fun n ↦ P.prop_of_iso ((DerivedCategory.homologyFunctor 𝒜 n).mapIso e) (h n)

/-- `NL_{X/Y}` on the model with its sections in `Type (u + 1)`. -/
abbrev modelNaiveCotangentComplexULift :=
  Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u + 1} (smallEtaleModelTopology B S hS X.1)
    _ _ (modelBaseMap B S hS f)

/-- The restriction of `NL_{X/Y}` to the model is the naive cotangent complex of the
restriction. -/
def restrictedNaiveCotangentComplexIsoA :
    ((Stacks.Sites.Conormal.moduleSheafRestriction.{u + 1} (smallEtaleModelTopology B S hS X.1)
        (SmallEtale.topology B S hS X.1) (modelEquiv B S hS X).inverse
        (structureSheaf B S hS X.1 X.2)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (Stacks.SheafOfModules.naiveCotangentComplex.{u, u + 1, u, u}
    (SmallEtale.topology B S hS X.1) (inverseImageBase B S hS f) (structureSheaf B S hS X.1 X.2)
    (inverseImageBaseMap B S hS f)) ≅ modelNaiveCotangentComplexULift B S hS f :=
  Stacks.SheafOfModules.naiveCotangentComplexRestrictionIso.{u, u, u, u, u + 1, u}
      (smallEtaleModelTopology B S hS X.1)
      (SmallEtale.topology B S hS X.1) (modelEquiv B S hS X).inverse
      (inverseImageBase B S hS f) (structureSheaf B S hS X.1 X.2)
      (inverseImageBaseMap B S hS f)

/-- The naive cotangent complex on the model with sections in `Type (u + 1)` is the universe
lift of the one with sections in `Type u`. -/
def restrictedNaiveCotangentComplexIsoB :
    modelNaiveCotangentComplexULift B S hS f ≅
      ((SheafOfModules.uliftFunctor.{u, u, u, u, u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (modelNaiveCotangentComplex B S hS f) := by
  with_reducible exact (Stacks.SheafOfModules.naiveCotangentComplexULiftIso.{u, u, u, u, u + 1}
    (smallEtaleModelTopology B S hS X.1)
    ((ringRes (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X).inverse).obj
      (inverseImageBase B S hS f))
    ((ringRes (smallEtaleModelTopology B S hS X.1) (modelEquiv B S hS X).inverse).obj
      (structureSheaf B S hS X.1 X.2)) (modelBaseMap B S hS f))

/-- The two universe lifts of sheaves of modules on the model agree. -/
def restrictedNaiveCotangentComplexIsoC :
    ((SheafOfModules.uliftFunctor.{u, u, u, u, u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (modelNaiveCotangentComplex B S hS f) ≅
      ((modelULift B S hS X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (modelNaiveCotangentComplex B S hS f) :=
  (NatIso.mapHomologicalComplex (eqToIso (rfl : SheafOfModules.uliftFunctor.{u, u, u, u, u + 1} =
    modelULift B S hS X)) (ComplexShape.up ℤ)).app _

/-- **`NL_{X/Y}` restricted to the model is the naive cotangent complex on the model**, with
its sections lifted to `Type (u + 1)`. -/
def restrictedNaiveCotangentComplexIso :
    ((smallEtaleModelModulesEquivULift B S hS X).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (naiveCotangentComplex B S hS f) ≅
      ((modelULift B S hS X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (modelNaiveCotangentComplex B S hS f) :=
  restrictedNaiveCotangentComplexIsoA B S hS f ≪≫ restrictedNaiveCotangentComplexIsoB B S hS f ≪≫
    restrictedNaiveCotangentComplexIsoC B S hS f

/-- **`NL_{X/Y}` on the model, carried to `D(𝒪_X)`, lies in `D_QCoh(𝒪_X)`**: the hypothesis of
`AlgebraicGeometry.Space.isEquivalence_of_isPushoutFunctor_of_isIso_coherator_map`, from the
quasi-coherence of the cohomology sheaves of `NL_{X/Y}` ([Stacks Project, Tag 0D0Y]). -/
theorem qcohDerivedProp_modelNaiveCotangentComplex :
    qcohDerivedProp B S hS X ((modelDerivedFunctor B S hS X).obj
      (DerivedCategory.Q.obj (modelNaiveCotangentComplex B S hS f))) := by
  let E := modelModulesEquiv B S hS X
  let E' := smallEtaleModelModulesEquivULift B S hS X
  let U := modelULift B S hS X
  let Pu : ObjectProperty (RestrictedModelModules B S hS X) :=
    fun M ↦ (E.inverse.obj M).IsQuasicoherentOnSite
  let P₂ := modelQcohProp B S hS X
  let P₁ : ObjectProperty (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (structureSheaf B S hS X.1 X.2))) :=
    SheafOfModules.isQuasicoherentOnSite _
  -- step 1: along `E⁻¹`
  refine (Stacks.UniverseLift.derivedCategoryB_mapDerivedCategory_obj_iff
    E.inverse Pu
    (SheafOfModules.isQuasicoherentOnSite _) (fun _ ↦ Iff.rfl) _).mpr ?_
  -- step 2: along the universe lift on the model
  refine (Stacks.UniverseLift.derivedCategoryB_mapDerivedCategory_obj_iff
    U Pu P₂
    (fun M ↦ ?_) _).mp ?_
  · exact (isQuasicoherentOnSite_iff_of_iso
      (spaceULiftModelIso B S hS X M)).symm.trans (isQuasicoherentOnSite_spaceULift_iff B S hS X _)
  -- step 3: identify the lifted complex with the restriction of `NL_{X/Y}`
  let N := naiveCotangentComplex B S hS f
  have e : E'.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj N) ≅
      U.mapDerivedCategory.obj (DerivedCategory.Q.obj (modelNaiveCotangentComplex B S hS f)) :=
    (E'.functor.mapDerivedCategoryFactors.app N) ≪≫
      DerivedCategory.Q.mapIso (restrictedNaiveCotangentComplexIso B S hS f) ≪≫
      (U.mapDerivedCategoryFactors.app (modelNaiveCotangentComplex B S hS f)).symm
  refine derivedCategoryB_of_iso P₂ e ?_
  -- step 4: along the restriction equivalence at `u + 1`
  refine (Stacks.UniverseLift.derivedCategoryB_mapDerivedCategory_obj_iff
    E'.functor P₁ P₂ (fun G ↦ ?_) _).mpr ?_
  · exact isQuasicoherentOnSite_iff_of_iso (E'.unitIso.app G).symm
  -- step 5: the cohomology sheaves of `NL_{X/Y}` are quasi-coherent
  intro n
  exact P₁.prop_of_iso (((DerivedCategory.homologyFunctorFactors _ n).app N).symm)
    ((naiveCotangentComplex_homology B S hS f).1 n)

/-- **[Stacks Project, Tag 0D3P].** Let `f : X ⟶ Y` be a morphism of algebraic spaces with `X`
quasi-compact and quasi-separated, let `φ : ℱ ⟶ 𝒢` be a morphism of `𝒪_X`-modules such that
`DQ_X(ℱ) ⟶ DQ_X(𝒢)` is an isomorphism, where `DQ_X` is the right adjoint of
`D_QCoh(𝒪_X) ⥤ D(𝒪_X)` of [Stacks Project, Tag 0CR4], and let `F` be pushout along `φ`, from
extensions `0 ⟶ ℱ ⟶ 𝒪' ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_Y`-algebras on `X_étale` to extensions by `𝒢`
(characterised by the universal property of the pushout). Then `F` is an equivalence of
categories.

The quasi-coherence of `NL_{X/Y}` which the source's proof uses is
`AlgebraicGeometry.Space.qcohDerivedProp_modelNaiveCotangentComplex`, from
[Stacks Project, Tag 0D0Y]. -/
@[stacks 0D3P]
theorem isEquivalence_of_isPushoutFunctor_of_isIso_coherator_map_of_qcqs
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXc : IsQuasiCompactSpace B S hS X.1) (hXs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {M N : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (structureSheaf B S hS X.1 X.2))}
    (φ : M ⟶ N)
    {F : AlgebraExtension (J := SmallEtale.topology B S hS X.1) (inverseImageBaseMap B S hS f) M ⥤
      AlgebraExtension (J := SmallEtale.topology B S hS X.1) (inverseImageBaseMap B S hS f) N}
    (hF : IsPushoutFunctor.{u, u + 1, u} (a := inverseImageBaseMap B S hS f) φ F)
    (hDQ : letI := quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ X.1 X.2 hXc hXs
      IsIso ((qcohDerivedProp B S hS X).ι.rightAdjoint.map
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ))) :
    F.IsEquivalence :=
  isEquivalence_of_isPushoutFunctor_of_isIso_coherator_map B S hS f hZ hXc hXs φ hF hDQ
    (qcohDerivedProp_modelNaiveCotangentComplex B S hS f)

end AlgebraicGeometry.Space

end
