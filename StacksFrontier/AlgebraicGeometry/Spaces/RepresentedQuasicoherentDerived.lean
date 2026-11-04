module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexSyntomicDescent
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Relative
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback

/-!
# `D_QCoh` of a representable algebraic space and the complex `E|_U`

Let `T` be an object of the big fppf site over a scheme `S`, with underlying scheme `T₀`.  The
second sentence of Remark 0CSW says that an object of `D_QCoh` of the algebraic space
`yoneda.obj T` is the pullback of a unique object of `D_QCoh(𝒪_{T₀})`, by Stacks 071Q.  This file
constructs that comparison and shows that the complex `E|_U` it defines on an étale chart is
compatible with passing to a finer chart.

## Main definitions

* `AlgebraicGeometry.Space.representedQuasicoherentDerivedEquivalence`: the equivalence
  `D_QCoh(𝒪_{T₀}) ≌ D_QCoh(yoneda.obj T)`, Stacks 071Q for `T₀`
  (`AlgebraicGeometry.SmallEtale.derivedAssociatedModuleEquivalenceQcoh`) followed by the
  identification of the small étale site of `T₀` with that of `yoneda.obj T`.
* `AlgebraicGeometry.Space.representedZariskiComparison`: that equivalence, as the
  `AlgebraicGeometry.Space.ZariskiComparisonData` the complex `E|_U` of
  `AlgebraicGeometry.Space.chartComplex` is read through.

## Main results

* `AlgebraicGeometry.Space.representedDerivedAssociatedModuleChartComplexIso`: `ε^*(E|_U)` is the
  derived pullback of `E` to the chart, so `E|_U` is the object of Remark 0CSW.
* `AlgebraicGeometry.Space.nonempty_chartComplex_iso_derivedPullback`: for a morphism `g : U ⟶ V`
  of the site with étale underlying morphism of schemes, `E|_U ≅ Lg^*(E|_V)` on the charts
  `yoneda.map g ≫ a` and `a`.
* `AlgebraicGeometry.Space.isQuasicoherent_homology_derivedPullback_of_flat`: the derived pullback
  along a flat morphism of schemes preserves quasi-coherence of the cohomology sheaves.

## Implementation notes

The compatibility with a finer chart is reflected from the represented algebraic spaces: both
sides become isomorphic after `ε^*`, by the commutation of `ε^*` with étale pullback
(`AlgebraicGeometry.Space.representedDerivedAssociatedModulePullbackIso`) and of chart
restriction with composition (`AlgebraicGeometry.Space.representedChartDerivedRestrictionCompIso`),
and `ε^*` reflects isomorphisms between complexes with quasi-coherent cohomology by Stacks 071Q
(`AlgebraicGeometry.Space.nonempty_iso_of_representedDerivedAssociatedModule_iso`).

The global instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is switched off: it
answers `Abelian` for these categories of modules at a universe join that is never the module
universe `u`, and leaves the universe constraint unsolvable.

## References

* [Stacks Project, Tag 0CSW](https://stacks.math.columbia.edu/tag/0CSW)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- A complex on the small étale site of the scheme underlying `T` has quasi-coherent cohomology
exactly when the complex it becomes on the small étale site of `yoneda.obj T` has. -/
theorem derivedCategoryB_representedDerivedModuleEquivalence_functor_obj_iff
    (K : DerivedCategory (SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T))) :
    DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (representedStructureRingSheaf B S hS T))
        ((representedDerivedModuleEquivalence B S hS T).functor.obj K) ↔
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (representedSchemeStructureSheaf B S hS T)) K := by
  refine forall_congr' fun n => ?_
  let e := (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
    (representedSmallEtaleModuleEquivalence B S hS T).functor n).app K
  exact ((SheafOfModules.isQuasicoherentOnSite _).prop_iff_of_iso e).trans
    (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T _)

/-- The derived equivalence of the two small étale sites restricts to the complexes with
quasi-coherent cohomology. -/
def representedSmallEtaleDerivedQcohEquivalence :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (representedSchemeStructureSheaf B S hS T))).FullSubcategory ≌
      QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj T)
        (isAlgebraicSpace_yoneda B S hS T) :=
  @Equivalence.congrFullSubcategory _ _ _ _ _ _
    (representedDerivedModuleEquivalence B S hS T)
    ⟨fun e hX n => (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e) (hX n)⟩
    (funext fun K => propext
      (derivedCategoryB_representedDerivedModuleEquivalence_functor_obj_iff B S hS T K))

/-- **`D_QCoh` of a representable algebraic space is `D_QCoh` of the representing scheme.** -/
def representedQuasicoherentDerivedEquivalence :
    AlgebraicGeometry.QuasicoherentDerivedCategory ((BigFppfOver.toScheme B S hS).obj T) ≌
      QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj T)
        (isAlgebraicSpace_yoneda B S hS T) :=
  (_root_.AlgebraicGeometry.SmallEtale.derivedAssociatedModuleEquivalenceQcoh
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property).trans
    (representedSmallEtaleDerivedQcohEquivalence B S hS T)

/-- The functor of `representedQuasicoherentDerivedEquivalence`, read on underlying objects, is
the derived associated-module functor `ε^*` of the represented algebraic space. -/
def representedQuasicoherentDerivedEquivalenceFunctorObjIso
    (K : AlgebraicGeometry.QuasicoherentDerivedCategory ((BigFppfOver.toScheme B S hS).obj T)) :
    ((representedQuasicoherentDerivedEquivalence B S hS T).functor.obj K).obj ≅
      (representedDerivedAssociatedModule B S hS T).obj K.obj :=
  (Stacks.DerivedQCoh.mapDerivedCategoryCompIso
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (representedSmallEtaleModuleEquivalence B S hS T).functor
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor)
    (Iso.refl _)).app K.obj

/-- The comparison of Remark 0CSW at `T`. -/
def representedZariskiComparison : ZariskiComparisonData B S hS T :=
  ⟨(representedQuasicoherentDerivedEquivalence B S hS T).symm⟩

/-! ### The complex `E|_U` through the comparison -/

section Chart

variable {B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  (E : QuasicoherentDerivedCategory.{u, u} B S hS X hX)

/-- **The complex `E|_U` pulls back to `E` restricted to the chart.**  For an étale chart
`a : yoneda.obj U ⟶ X`, the associated module `ε^*(E|_U)` of the complex `E|_U` of Remark 0CSW,
read through `representedZariskiComparison`, is the derived pullback of `E` to the algebraic space
represented by `U`. -/
def representedDerivedAssociatedModuleChartComplexIso {U : BigFppfOver B S hS}
    {a : yoneda.obj U ⟶ X} (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a) :
    (representedDerivedAssociatedModule B S hS U).obj
        (chartComplex B S hS hX E ha (representedZariskiComparison B S hS U)).obj ≅
      (chartDerivedPullback B S hS hX E ha).obj :=
  (representedQuasicoherentDerivedEquivalenceFunctorObjIso B S hS U _).symm ≪≫
    (ObjectProperty.ι _).mapIso
      ((representedQuasicoherentDerivedEquivalence B S hS U).counitIso.app
        (chartDerivedPullback B S hS hX E ha))

/-- Along a flat morphism of schemes the derived pullback of a complex with quasi-coherent
cohomology has quasi-coherent cohomology. -/
theorem isQuasicoherent_homology_derivedPullback_of_flat {Y Z : Scheme.{u}} (f : Y ⟶ Z) [Flat f]
    (K : DerivedCategory Z.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Z.Modules i).obj K).IsQuasicoherent)
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPullback f.toLRSHom.toShHom).obj K)).IsQuasicoherent := by
  have := AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat f
  have := AlgebraicGeometry.preservesFiniteColimits_modulesPullback f
  refine (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor Y.Modules i).mapIso
      ((Scheme.Modules.derivedPullbackIsoMapDerivedCategory f).app K).symm) ?_
  refine (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (Scheme.Modules.pullback f) i).app K).symm ?_
  exact Stacks.Modules.isQuasicoherent_pullback f _ (hK i)

/-- **`E|_U` is compatible with passing to a finer chart.**  Let `g : U ⟶ V` be a morphism of the
site whose underlying morphism of schemes is étale, and let `a : yoneda.obj V ⟶ X` be an étale
chart such that `yoneda.map g ≫ a` is an étale chart as well.  Then the complex `E|_U` attached to
`yoneda.map g ≫ a` is the derived pullback along `g` of the complex `E|_V` attached to `a`. -/
theorem nonempty_chartComplex_iso_derivedPullback {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g))
    {a : yoneda.obj V ⟶ X} (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hga : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (yoneda.map g ≫ a)) :
    Nonempty ((chartComplex B S hS hX E hga (representedZariskiComparison B S hS U)).obj ≅
      (derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj
        (chartComplex B S hS hX E ha (representedZariskiComparison B S hS V)).obj) := by
  have : Flat ((BigFppfOver.toScheme B S hS).map g) :=
    (AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified.mp hg).1
  have hq : IsEtale B S hS (representedSpaceMap B S hS g).hom :=
    isEtale_of_presheaf_etale B S hS
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@_root_.AlgebraicGeometry.Etale) g).2 hg)
  let K := chartComplex B S hS hX E ha (representedZariskiComparison B S hS V)
  let K' := chartComplex B S hS hX E hga (representedZariskiComparison B S hS U)
  have e : (representedDerivedAssociatedModule B S hS U).obj K'.obj ≅
      (representedDerivedAssociatedModule B S hS U).obj
        ((derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj K.obj) :=
    representedDerivedAssociatedModuleChartComplexIso hX E hga ≪≫
      (representedChartDerivedRestrictionCompIso B S hS hX a
        (isEtale_of_isEtaleSchemeChart B S hS ha) g hq
        (isEtale_of_isEtaleSchemeChart B S hS hga)).app E.obj ≪≫
      (representedDerivedPullback B S hS g hq).mapIso
        (representedDerivedAssociatedModuleChartComplexIso hX E ha).symm ≪≫
      (representedDerivedAssociatedModulePullbackIso B S hS g hq).app K.obj
  exact nonempty_iso_of_representedDerivedAssociatedModule_iso B S hS U _ _ K'.property
    (isQuasicoherent_homology_derivedPullback_of_flat _ K.obj K.property) e

end Chart

end AlgebraicGeometry.Space

end
