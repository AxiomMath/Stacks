module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.Homology.DerivedCategory.MapDerivedCategorySquare
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexSyntomicDescent

/-!
# `ε^*` on a represented algebraic space, and étale pullback

Let `U` be an object of the big fppf site over `S`, with scheme `T`, and let `h_U` be the algebraic
space it represents.  The small étale site of `h_U` is the small étale site of `T`, and the
associated-module functor `ε^* : Mod(𝒪_T) ⥤ Mod(𝒪_{h_U})` of Stacks 03DU (4) at `τ = étale` is
`AlgebraicGeometry.Space.representedAssociatedModule`.  This file records how `ε^*` behaves under
étale pullback, on modules and on unbounded derived categories, and how the equivalence
`ε^* : D_QCoh(𝒪_T) ⥤ D_QCoh(T_étale, 𝒪)` of Stacks 071Q is read on `D(𝒪_{h_U})`.  These are the
inputs of the dualizing complexes on algebraic spaces of Stacks 0E4X–0E4Z.

## Main definitions

* `AlgebraicGeometry.Space.representedDerivedAssociatedModule`: `ε^* : D(𝒪_T) ⥤ D(𝒪_{h_U})`.
* `AlgebraicGeometry.Space.representedDerivedPullback`: the étale pullback
  `D(𝒪_{h_U}) ⥤ D(𝒪_{h_{U'}})` along the morphism represented by `g : U' ⟶ U`.
* `AlgebraicGeometry.Space.representedChartDerivedRestriction`: the restriction
  `K ↦ K|_U` of `D(𝒪_X) ⥤ D(𝒪_{h_U})` along an étale chart `φ : h_U ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.representedAssociatedModuleEtalePullbackIso`: **`ε^*` commutes with
  étale pullback**, `(ε^*𝓕)|_{U'} ≅ ε^*(g^*𝓕)`, naturally in the `𝒪_T`-module `𝓕`.
* `AlgebraicGeometry.Space.representedDerivedAssociatedModulePullbackIso`: the same on derived
  categories, `(ε^*ω)|_{U'} ≅ ε^*(Lg^*ω)`, for `g` flat.
* `AlgebraicGeometry.Space.representedChartDerivedRestrictionCompIso`: restricting to a chart and
  then along a morphism of charts is restricting to the composite chart.
* `AlgebraicGeometry.Space.exists_representedDerivedAssociatedModule_iso` and
  `AlgebraicGeometry.Space.nonempty_iso_of_representedDerivedAssociatedModule_iso`: by the
  equivalence `ε^* : D_QCoh(𝒪_T) ⥤ D_QCoh(T_étale, 𝒪)` of Stacks 071Q
  (`AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`), every object of
  `D(𝒪_{h_U})` with quasi-coherent cohomology is `ε^*ω` for some `ω` with quasi-coherent
  cohomology, and `ε^*` reflects isomorphisms between such `ω`.
* `Stacks.Duality.isQuasicoherent_homology_of_isDualizingComplex`: the cohomology sheaves of a
  dualizing complex on a locally Noetherian scheme are quasi-coherent.

## Implementation notes

The square of modules is assembled from three known comparisons: étale pullback is the inverse
image of Stacks 03LU (`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, Stacks 03LW),
the inverse image along a represented morphism is the small étale pullback of the underlying
morphism of schemes (`AlgebraicGeometry.Space.representedModulePullbackIso`), and that pullback
commutes with `ε^*` (`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`).  All functors
involved are exact, so the square descends to derived categories by
`CategoryTheory.Functor.mapDerivedCategorySquareIso`, and along a flat morphism of schemes the
derived pullback is degreewise pullback
(`AlgebraicGeometry.Scheme.Modules.derivedPullbackIsoMapDerivedCategory`).

The derived functors carry their exactness instances as local `haveI`s: instance search does not
find the exactness of `AlgebraicGeometry.Space.etaleModulePullback` at a morphism written as
`ObjectProperty.homMk`, and the global instance
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is switched off here because it answers
`Abelian` for these categories of modules at a universe join that is never the universe of the
schemes, ending the search in an unsolvable universe constraint.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 0E4X](https://stacks.math.columbia.edu/tag/0E4X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe w u

namespace Stacks.Duality

open _root_.AlgebraicGeometry

/-- The cohomology sheaves of a dualizing complex on a locally Noetherian scheme are
quasi-coherent, being coherent. -/
theorem isQuasicoherent_homology_of_isDualizingComplex {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent :=
  have := isCoherent_homology_of_isDualizingComplex hK i
  isQuasicoherent_of_isCoherent _

end Stacks.Duality

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance]
  _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule

section Square

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- The comparison of the small étale site of `h_U` with that of its scheme carries the inverse
image of Stacks 03LU along a represented morphism to the small étale pullback of the underlying
morphism of schemes, read with the comparison functors on both sides. -/
def representedModuleEquivalencePullbackSquare :
    (representedSmallEtaleModuleEquivalence B S hS T).functor ⋙
        modulePullback B S hS (representedSpaceMap B S hS g) ≅
      SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T').functor :=
  Functor.isoWhiskerLeft _ (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (representedSmallEtaleModuleEquivalence B S hS T').counitIso.symm) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft _
      (representedModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g))) _ ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight
      (representedSmallEtaleModuleEquivalence B S hS T).unitIso.symm _) _ ≪≫
    Functor.isoWhiskerRight (Functor.leftUnitor _) _

variable (hφ : IsEtale B S hS (representedSpaceMap B S hS g).hom)

/-- **`ε^*` commutes with étale pullback.** For an étale morphism `g : U' ⟶ U` of the big fppf
site, restricting the associated module of an `𝒪_T`-module `𝓕` along the represented morphism
`h_{U'} ⟶ h_U` is the associated module of the pullback of `𝓕` along the morphism of schemes
underlying `g`, naturally in `𝓕`. -/
def representedAssociatedModuleEtalePullbackIso :
    representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T) ⋙
        etaleModulePullback.{u, u} B S hS (representedSpaceMap B S hS g) hφ ≅
      Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g) ⋙
        representedAssociatedModule B S hS T' (isAlgebraicSpace_yoneda B S hS T') :=
  Functor.isoWhiskerLeft _ (modulePullbackIsoEtaleModulePullback B S hS _ hφ).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (representedModuleEquivalencePullbackSquare B S hS g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
      (associatedBigEtaleSite B) g.left).symm _ ≪≫
    Functor.associator _ _ _

end Square

section Exact

variable (T : BigFppfOver B S hS) (hF : IsAlgebraicSpace B S hS (yoneda.obj T))

/-- `ε^*` on a represented space is left exact (Stacks 08H8). -/
instance preservesFiniteLimits_representedAssociatedModule :
    PreservesFiniteLimits (representedAssociatedModule B S hS T hF) :=
  inferInstanceAs (PreservesFiniteLimits
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
      (representedSmallEtaleModuleEquivalence B S hS T).functor))

/-- `ε^*` on a represented space is right exact, being a left adjoint. -/
instance preservesFiniteColimits_representedAssociatedModule :
    PreservesFiniteColimits (representedAssociatedModule B S hS T hF) :=
  inferInstanceAs (PreservesFiniteColimits
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
      (representedSmallEtaleModuleEquivalence B S hS T).functor))

end Exact

attribute [local instance] AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat
  AlgebraicGeometry.preservesFiniteColimits_modulesPullback AlgebraicGeometry.pullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

attribute [local instance 10000] HasDerivedCategory.standard

section Derived

/-- `ε^* : D(𝒪_T) ⥤ D(𝒪_{h_U})`, the functor induced on unbounded derived categories by the
exact associated-module functor of the scheme `T` underlying `U`. -/
def representedDerivedAssociatedModule (T : BigFppfOver B S hS) :
    DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules ⥤
      DerivedCategory (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :=
  (representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).mapDerivedCategory

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hφ : IsEtale B S hS (representedSpaceMap B S hS g).hom)

/-- The étale pullback `D(𝒪_{h_U}) ⥤ D(𝒪_{h_{U'}})` along the morphism of represented algebraic
spaces induced by `g : U' ⟶ U`; étale pullback is exact, so this is its total derived functor. -/
def representedDerivedPullback :
    DerivedCategory (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) ⥤
      DerivedCategory (Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')) :=
  haveI := etaleModulePullback_additive.{u, u} B S hS (representedSpaceMap B S hS g) hφ
  haveI := preservesFiniteLimits_etaleModulePullback B S hS (representedSpaceMap B S hS g) hφ
  haveI := preservesFiniteColimits_etaleModulePullback B S hS (representedSpaceMap B S hS g) hφ
  (etaleModulePullback.{u, u} B S hS (representedSpaceMap B S hS g) hφ).mapDerivedCategory

variable [Flat ((BigFppfOver.toScheme B S hS).map g)]

/-- **`ε^*` commutes with étale pullback, on derived categories.** For a flat `g : U' ⟶ U` whose
represented morphism is étale, `(ε^*ω)|_{U'} ≅ ε^*(Lg^*ω)` naturally in `ω ∈ D(𝒪_T)`. -/
def representedDerivedAssociatedModulePullbackIso :
    representedDerivedAssociatedModule B S hS T ⋙ representedDerivedPullback B S hS g hφ ≅
      derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom ⋙
        representedDerivedAssociatedModule B S hS T' :=
  haveI := etaleModulePullback_additive.{u, u} B S hS (representedSpaceMap B S hS g) hφ
  haveI := preservesFiniteLimits_etaleModulePullback B S hS (representedSpaceMap B S hS g) hφ
  haveI := preservesFiniteColimits_etaleModulePullback B S hS (representedSpaceMap B S hS g) hφ
  let e₁ : representedDerivedAssociatedModule B S hS T ⋙ representedDerivedPullback B S hS g hφ ≅
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).mapDerivedCategory ⋙
        representedDerivedAssociatedModule B S hS T' :=
    Functor.mapDerivedCategorySquareIso (representedAssociatedModuleEtalePullbackIso B S hS g hφ)
  let e₂ : (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).mapDerivedCategory ≅
      derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom :=
    (Scheme.Modules.derivedPullbackIsoMapDerivedCategory ((BigFppfOver.toScheme B S hS).map g)).symm
  e₁ ≪≫ Functor.isoWhiskerRight e₂ (representedDerivedAssociatedModule B S hS T')

end Derived

section Chart

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The restriction `K ↦ K|_U` of `D(𝒪_X)` to an étale chart `φ : h_U ⟶ X`: the étale pullback
along the morphism of algebraic spaces `φ`, on unbounded derived categories. -/
def representedChartDerivedRestriction (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : IsEtale B S hS φ) :
    DerivedCategory (Modules.{u, u} B S hS X hX) ⥤
      DerivedCategory (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :=
  haveI := etaleModulePullback_additive.{u, u} B S hS
    (ObjectProperty.homMk φ : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
      AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩) hφ
  haveI := preservesFiniteLimits_etaleModulePullback B S hS
    (ObjectProperty.homMk φ : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
      AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩) hφ
  haveI := preservesFiniteColimits_etaleModulePullback B S hS
    (ObjectProperty.homMk φ : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
      AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩) hφ
  (etaleModulePullback.{u, u} B S hS
    (ObjectProperty.homMk φ : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
      AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩) hφ).mapDerivedCategory

/-- Restricting to a chart `φ : h_U ⟶ X` and then along a morphism `q : W ⟶ U` is restricting to
the composite chart `h_W ⟶ h_U ⟶ X`. -/
def representedChartDerivedRestrictionCompIso {U W : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X)
    (hφ : IsEtale B S hS φ) (q : W ⟶ U)
    (hq : IsEtale B S hS (representedSpaceMap B S hS q).hom)
    (hχ : IsEtale B S hS (yoneda.map q ≫ φ)) :
    representedChartDerivedRestriction B S hS hX W (yoneda.map q ≫ φ) hχ ≅
      representedChartDerivedRestriction B S hS hX U φ hφ ⋙
        representedDerivedPullback B S hS q hq :=
  let f : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ := representedSpaceMap B S hS q
  let g : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨X, hX⟩ := ObjectProperty.homMk φ
  haveI := etaleModulePullback_additive.{u, u} B S hS f hq
  haveI := preservesFiniteLimits_etaleModulePullback B S hS f hq
  haveI := preservesFiniteColimits_etaleModulePullback B S hS f hq
  haveI := etaleModulePullback_additive.{u, u} B S hS g hφ
  haveI := preservesFiniteLimits_etaleModulePullback B S hS g hφ
  haveI := preservesFiniteColimits_etaleModulePullback B S hS g hφ
  let h : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨X, hX⟩ := ObjectProperty.homMk (yoneda.map q ≫ φ)
  haveI := etaleModulePullback_additive.{u, u} B S hS h hχ
  haveI := preservesFiniteLimits_etaleModulePullback B S hS h hχ
  haveI := preservesFiniteColimits_etaleModulePullback B S hS h hχ
  Stacks.DerivedGlueing.mapDerivedCategoryCongr
      ((etaleModulePullbackCompIso B S hS f g hq hφ hχ).symm :
        etaleModulePullback.{u, u} B S hS h hχ ≅ _) ≪≫
    (Stacks.DerivedGlueing.mapDerivedCategoryCompIso
      (etaleModulePullback.{u, u} B S hS g hφ) (etaleModulePullback.{u, u} B S hS f hq)).symm

end Chart

section Equivalence

variable (T : BigFppfOver B S hS)

/-- The comparison functor from modules on the small étale site of `T` to modules on the small
étale site of `h_U` is additive. -/
instance additive_representedSmallEtaleModuleEquivalence_functor :
    (representedSmallEtaleModuleEquivalence B S hS T).functor.Additive :=
  inferInstanceAs (representedModulePushforward B S hS T).Additive

/-- The equivalence `D(T_étale, 𝒪) ≌ D(𝒪_{h_U})` induced by the identification of the small étale
site of `h_U` with that of its scheme `T`. -/
abbrev representedDerivedModuleEquivalence :=
  Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (representedSmallEtaleModuleEquivalence B S hS T)

private instance additive_associatedModule_comp_representedEquivalence :
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor).Additive :=
  additive_representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)

private instance preservesFiniteLimits_associatedModule_comp_representedEquivalence :
    PreservesFiniteLimits (_root_.AlgebraicGeometry.SmallEtale.associatedModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor) :=
  preservesFiniteLimits_representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)

private instance preservesFiniteColimits_associatedModule_comp_representedEquivalence :
    PreservesFiniteColimits (_root_.AlgebraicGeometry.SmallEtale.associatedModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor) :=
  preservesFiniteColimits_representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)

/-- By the equivalence `ε^* : D_QCoh(𝒪_T) ⥤ D_QCoh(T_étale, 𝒪)` of Stacks 071Q, every object
of `D(𝒪_{h_U})` with quasi-coherent cohomology is `ε^*ω` for an object `ω` of `D(𝒪_T)` with
quasi-coherent cohomology. -/
theorem exists_representedDerivedAssociatedModule_iso
    (M : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)))
    (hM : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)).O))) M) :
    ∃ ω : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules,
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj ω).IsQuasicoherent) ∧
        Nonempty ((representedDerivedAssociatedModule B S hS T).obj ω ≅ M) := by
  have := _root_.AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence.{u + 1}
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  let M' := (representedDerivedModuleEquivalence B S hS T).inverse.obj M
  have hM' : DerivedCategoryB.derivedCategoryB
      (_root_.AlgebraicGeometry.SmallEtale.qcohOnSite (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property) M' := fun n => by
    have e : (representedSmallEtaleModuleEquivalence B S hS T).functor.obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T)) n).obj M') ≅
        (DerivedCategory.homologyFunctor
          (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) n).obj M :=
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
          (representedSmallEtaleModuleEquivalence B S hS T).functor n).app M').symm ≪≫
        (DerivedCategory.homologyFunctor _ n).mapIso
          ((representedDerivedModuleEquivalence B S hS T).counitIso.app M)
    exact (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T _).mp
      (SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm (hM n))
  obtain ⟨ω₀, ⟨e₀⟩⟩ : ∃ ω₀, Nonempty
      ((_root_.AlgebraicGeometry.SmallEtale.derivedAssociatedModule.{u + 1}
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj ω₀ ≅
        ⟨M', hM'⟩) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
  refine ⟨ω₀.obj, ω₀.property, ⟨?_⟩⟩
  exact (Stacks.DerivedGlueing.mapDerivedCategoryCompIso
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (representedSmallEtaleModuleEquivalence B S hS T).functor).symm.app
        (show DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules from ω₀.obj) ≪≫
    (representedDerivedModuleEquivalence B S hS T).functor.mapIso
      ((ObjectProperty.ι _).mapIso e₀) ≪≫
    (representedDerivedModuleEquivalence B S hS T).counitIso.app M

/-- By the equivalence of Stacks 071Q, `ε^* : D(𝒪_T) ⥤ D(𝒪_{h_U})` reflects isomorphisms
between objects with quasi-coherent cohomology. -/
theorem nonempty_iso_of_representedDerivedAssociatedModule_iso
    (ω ω' : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (hω : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj ω).IsQuasicoherent)
    (hω' : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj ω').IsQuasicoherent)
    (e : (representedDerivedAssociatedModule B S hS T).obj ω ≅
      (representedDerivedAssociatedModule B S hS T).obj ω') :
    Nonempty (ω ≅ ω') := by
  have := _root_.AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence.{u + 1}
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  let c := Stacks.DerivedGlueing.mapDerivedCategoryCompIso
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (representedSmallEtaleModuleEquivalence B S hS T).functor
  let e₁ := c.app ω ≪≫ e ≪≫ c.symm.app ω'
  let e₂ := (representedDerivedModuleEquivalence B S hS T).fullyFaithfulFunctor.preimageIso e₁
  let ω₀ : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)).FullSubcategory :=
    ⟨ω, hω⟩
  let ω₀' : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)).FullSubcategory :=
    ⟨ω', hω'⟩
  let F := _root_.AlgebraicGeometry.SmallEtale.derivedAssociatedModule.{u + 1}
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  let e₃ : F.obj ω₀ ≅ F.obj ω₀' := (ObjectProperty.fullyFaithfulι _).preimageIso e₂
  exact ⟨(ObjectProperty.ι _).mapIso ((Functor.FullyFaithful.ofFullyFaithful F).preimageIso e₃)⟩

end Equivalence

end AlgebraicGeometry.Space

end
