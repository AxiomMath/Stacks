module

public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekCompactification
public import StacksFrontier.AlgebraicGeometry.Etale.ModuleSheafDirectImageAcyclicComplexes
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZeroComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.IndependenceCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LowerShriekAffineLine.QuasiFiniteLowerShriek
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusHomologyComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusNatIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.QuasiFiniteComparison

import StacksCore.Tactic.StacksAttribute

/-!
# The functors `Rf_!` of a quasi-finite separated morphism are `f_!`

Let `f : X ⟶ Y` be a quasi-finite separated morphism of schemes with `Y` quasi-compact and
quasi-separated, and let `Λ` be a ring. For a compactification `j : X ⟶ X̄` of `X` over `Y` the
functors `Rf_! = R f̄_* ∘ j_!` of [Stacks, Tag 0F7H] are
`Stacks.EtaleCohomology.derivedLowerShriek` on `D⁺_tors(X_étale, Λ)` and
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded` on `D(X_étale, Λ)` for a torsion ring `Λ`.
[Stacks, Tag 0GKM] says that they agree with the restriction of the functor
`f_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of [Stacks, Tag 0F5M].

## Main definitions

* `AlgebraicGeometry.SmallEtale.etaleModulesFShriek`: the direct image with compact support
  `f_!` of [Stacks, Tag 0F6R], with coefficients in `Λ`, read on Mathlib's small étale sites.
* `AlgebraicGeometry.SmallEtale.moduleSheafEquivMapDerivedCategoryCompIso`: its derived functor
  is the derived functor of the `f_!` of the size-bounded sites, under the equivalence of the two
  presentations of the small étale site.

## Main results

* `AlgebraicGeometry.SmallEtale.nonempty_derivedLowerShriek_iso_fShriek`:
  **[Stacks, Tag 0GKM]** for `Rf_!` on `D⁺_tors(X_étale, Λ)`.
* `AlgebraicGeometry.SmallEtale.nonempty_derivedLowerShriekUnbounded_iso_fShriek`:
  **[Stacks, Tag 0GKM]** for `Rf_!` on `D(X_étale, Λ)`, `Λ` a torsion ring.

## Implementation notes

The proof is the source's. Zariski's main theorem, [Stacks, Tag 05K0], gives a compactification
`f = j₀ ≫ f̄₀` with `f̄₀` finite
(`AlgebraicGeometry.SmallEtale.exists_isOpenImmersion_isFinite_factorization`); by
[Stacks, Tag 0F7I] (`Stacks.EtaleCohomology.derivedLowerShriekCompactificationIsoUniv` and
`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompactificationIsoUniv`) the functor `Rf_!`
of any compactification is that of `j₀`. There `Rj₀_! = j₀_!` and `R f̄₀_* = f̄₀_*`, both functors
being exact ([Stacks, Tag 03S5] and [Stacks, Tag 03QP]), and `f̄₀_* ∘ j₀_! = f_!` by
[Stacks, Tag 0F52].

The functors `Rf_!` live on Mathlib's small étale sites, `AlgebraicGeometry.Scheme.Etale`, while
`f_!` is constructed on the size-bounded small étale sites of a big étale site
(`AlgebraicGeometry.SmallEtale`, [Stacks, Tag 021B]). The two have equivalent categories of
sheaves, by `AlgebraicGeometry.SmallEtale.moduleSheafEquiv`, and `f_!` is read across that
equivalence. The identification `f̄₀_* ∘ j₀_! = f_!` is carried across it: direct images commute
with it (`AlgebraicGeometry.SmallEtale.etalePushforwardModSheafEquivIso`), and so does extension
by zero along an open immersion, both presentations of it being left adjoint to restriction,
which commutes with the equivalence on the nose
(`AlgebraicGeometry.SmallEtale.fShriekModSheafEquivIso`).

The coefficient ring `Λ` lives in the universe of the schemes, as in
`AlgebraicGeometry.SmallEtale.moduleSheafEquiv`.

## References

* [Stacks Project, Tag 0GKM](https://stacks.math.columbia.edu/tag/0GKM)
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0F5M](https://stacks.math.columbia.edu/tag/0F5M)
* [Stacks Project, Tag 0F52](https://stacks.math.columbia.edu/tag/0F52)
* [Stacks Project, Tag 05K0](https://stacks.math.columbia.edu/tag/05K0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

-- Mathlib gives the instances `LocallyOfFiniteType f` and `LocallyQuasiFinite f` for a finite
-- morphism `f` a low priority, so that through this file's imports instance search over the
-- morphisms of the big étale site exhausts the higher-priority routes before reaching them
attribute [local instance 1100] AlgebraicGeometry.IsFinite.instLocallyOfFiniteType
  AlgebraicGeometry.instLocallyQuasiFiniteOfIsFinite

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ]

section ExtensionByZero

variable {X Xbar : B.Scheme} (j : X ⟶ Xbar) [IsOpenImmersion (B.inclusion.map j)]

/-- Restriction of sheaves of `Λ`-modules along an open immersion `j : X ⟶ X̄` of a big étale
site, on the small étale sites of the site: precomposition with composition with `j`. -/
abbrev moduleRestriction : ModuleSheaf.{u, u, u} B Xbar Λ ⥤ ModuleSheaf.{u, u, u} B X Λ :=
  (smallEtalePostcompose B Xbar.obj Xbar.property
      (SmallEtale.ofEtaleHom B j)).sheafPushforwardContinuous
    (ModuleCat.{u + 1} Λ) (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B Xbar.obj Xbar.property)

/-- The `Λ`-linear direct image with compact support along an open immersion is left adjoint to
restriction. -/
def fShriekModAdjunctionRestriction :
    fShriekMod.{u, u, u} B Λ j ⊣ moduleRestriction B Λ j :=
  (Stacks.ModuleCatLift.moduleLiftAdjunction Λ _ _ _ _
      (fShriekAdjunctionRestriction B Xbar.obj Xbar.property
        (SmallEtale.ofEtaleHom B j))).ofNatIsoRight
    (Stacks.ModuleCatLift.sheafPushforwardContinuousIsoModuleLift.{u + 1} Λ
      (smallEtalePostcompose B Xbar.obj Xbar.property (SmallEtale.ofEtaleHom B j))
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Xbar.obj Xbar.property)).symm

/-- **Restriction along an open immersion corresponds under the comparison of the two small
étale sites.** Both composites are precomposition with the two isomorphic composites of
`AlgebraicGeometry.SmallEtale.toEtaleSiteCompSmallEtaleComposeIso`. -/
def moduleSheafEquivInverseRestrictionIso :
    (moduleSheafEquiv B Λ Xbar).inverse ⋙ moduleRestriction B Λ j ≅
      Stacks.EtaleCohomology.etaleModuleRestriction.{u, u} Λ (B.inclusion.map j) ⋙
        (moduleSheafEquiv B Λ X).inverse :=
  haveI : (smallEtalePostcompose B Xbar.obj Xbar.property (SmallEtale.ofEtaleHom B j) ⋙
      toEtaleSite B Xbar.obj Xbar.property).IsContinuous
      (SmallEtale.topology B X.obj X.property) Xbar.obj.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology B Xbar.obj Xbar.property) _
  haveI : (Scheme.Etale.smallEtaleCompose (B.inclusion.map j)).IsContinuous
      (B.inclusion.obj X).smallEtaleTopology Xbar.obj.smallEtaleTopology :=
    Scheme.Etale.smallEtaleCompose_isContinuous _
  haveI : (toEtaleSite B X.obj X.property).IsContinuous
      (SmallEtale.topology B X.obj X.property) (B.inclusion.obj X).smallEtaleTopology :=
    isContinuous_toEtaleSite B X.obj X.property
  haveI : (toEtaleSite B X.obj X.property ⋙
      Scheme.Etale.smallEtaleCompose (B.inclusion.map j)).IsContinuous
      (SmallEtale.topology B X.obj X.property) Xbar.obj.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ (B.inclusion.obj X).smallEtaleTopology _
  haveI : (toEtaleSite B (SmallEtale.ofEtaleHom B j).obj.left.obj
      (SmallEtale.ofEtaleHom B j).obj.left.property).IsContinuous
      (SmallEtale.topology B X.obj X.property) (B.inclusion.obj X).smallEtaleTopology :=
    isContinuous_toEtaleSite B X.obj X.property
  haveI : (Scheme.Etale.smallEtaleCompose
      (B.inclusion.map (SmallEtale.ofEtaleHom B j).obj.hom)).IsContinuous
      (B.inclusion.obj X).smallEtaleTopology Xbar.obj.smallEtaleTopology :=
    Scheme.Etale.smallEtaleCompose_isContinuous _
  haveI : (toEtaleSite B (SmallEtale.ofEtaleHom B j).obj.left.obj
      (SmallEtale.ofEtaleHom B j).obj.left.property ⋙
      Scheme.Etale.smallEtaleCompose
        (B.inclusion.map (SmallEtale.ofEtaleHom B j).obj.hom)).IsContinuous
      (SmallEtale.topology B X.obj X.property) Xbar.obj.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ (B.inclusion.obj X).smallEtaleTopology _
  Functor.sheafPushforwardContinuousComp'
      (F := smallEtalePostcompose B Xbar.obj Xbar.property (SmallEtale.ofEtaleHom B j))
      (G := toEtaleSite B Xbar.obj Xbar.property) (Iso.refl _) _ _ _ _ ≪≫
    Functor.sheafPushforwardContinuousIso
      (toEtaleSiteCompSmallEtaleComposeIso B Xbar.obj Xbar.property
        (SmallEtale.ofEtaleHom B j)).symm _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp' (F := toEtaleSite B X.obj X.property)
      (G := Scheme.Etale.smallEtaleCompose (B.inclusion.map j)) (Iso.refl _) _ _ _ _).symm

/-- **Extension by zero along an open immersion corresponds under the comparison of the two small
étale sites**: the `Λ`-linear `j_!` of the bounded sites, followed by the comparison, is the
comparison followed by Mathlib-site extension by zero. Both are left adjoint to the same functor,
by `AlgebraicGeometry.SmallEtale.moduleSheafEquivInverseRestrictionIso`. -/
def fShriekModSheafEquivIso :
    fShriekMod.{u, u, u} B Λ j ⋙ (moduleSheafEquiv B Λ Xbar).functor ≅
      (moduleSheafEquiv B Λ X).functor ⋙
        Stacks.EtaleCohomology.etaleModuleExtensionByZero.{u, u} Λ (B.inclusion.map j) :=
  Adjunction.leftAdjointUniq
    (((fShriekModAdjunctionRestriction B Λ j).comp
      (moduleSheafEquiv B Λ Xbar).toAdjunction).ofNatIsoRight
        (moduleSheafEquivInverseRestrictionIso B Λ j))
    ((moduleSheafEquiv B Λ X).toAdjunction.comp
      (Stacks.EtaleCohomology.etaleModuleExtensionByZeroAdj.{u, u} Λ (B.inclusion.map j)))

end ExtensionByZero

/-! ### `f_!` transported to Mathlib's small étale sites -/

section Transport

variable {X Y : B.Scheme} (f : X ⟶ Y) [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)]

/-- **The direct image with compact support `f_!` of Stacks 0F6R, with coefficients in `Λ`, on
Mathlib's small étale sites**: the `Λ`-linear `f_!` of the size-bounded small étale sites,
conjugated by the comparison `AlgebraicGeometry.SmallEtale.moduleSheafEquiv` of the two sites.
These are the sites on which the functors `Rf_!` of Stacks 0F7H,
`Stacks.EtaleCohomology.derivedLowerShriek` and
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded`, are defined. -/
def etaleModulesFShriek :
    Stacks.EtaleCohomology.EtaleModules.{u, u} Λ X.obj ⥤
      Stacks.EtaleCohomology.EtaleModules.{u, u} Λ Y.obj :=
  (moduleSheafEquiv B Λ X).inverse ⋙ fShriekMod.{u, u, u} B Λ f ⋙
    (moduleSheafEquiv B Λ Y).functor

/-- The transported `f_!` is additive. -/
instance etaleModulesFShriek_additive : (etaleModulesFShriek B Λ f).Additive :=
  inferInstanceAs ((moduleSheafEquiv B Λ X).inverse ⋙ fShriekMod.{u, u, u} B Λ f ⋙
    (moduleSheafEquiv B Λ Y).functor).Additive

/-- The transported `f_!` preserves finite limits, `f_!` being exact (Stacks 0F5F). -/
instance etaleModulesFShriek_preservesFiniteLimits :
    PreservesFiniteLimits (etaleModulesFShriek B Λ f) :=
  inferInstanceAs (PreservesFiniteLimits ((moduleSheafEquiv B Λ X).inverse ⋙
    fShriekMod.{u, u, u} B Λ f ⋙ (moduleSheafEquiv B Λ Y).functor))

/-- The transported `f_!` preserves finite colimits, `f_!` being exact (Stacks 0F5F). -/
instance etaleModulesFShriek_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModulesFShriek B Λ f) :=
  inferInstanceAs (PreservesFiniteColimits ((moduleSheafEquiv B Λ X).inverse ⋙
    fShriekMod.{u, u, u} B Λ f ⋙ (moduleSheafEquiv B Λ Y).functor))

/-- The transported `f_!` corresponds to the `f_!` of the size-bounded sites under the comparison
of the two sites, on sheaves. -/
def moduleSheafEquivFunctorCompEtaleModulesFShriekIso :
    (moduleSheafEquiv B Λ X).functor ⋙ etaleModulesFShriek B Λ f ≅
      fShriekMod.{u, u, u} B Λ f ⋙ (moduleSheafEquiv B Λ Y).functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafEquiv B Λ X).unitIso.symm _ ≪≫ Functor.leftUnitor _

/-- **The derived `f_!` of Stacks 0F5M is the same on the two presentations of the small étale
site**: under the equivalences of derived categories induced by the comparison of the two sites,
the functor `D(X_étale, Λ) ⥤ D(Y_étale, Λ)` induced by the transported `f_!` is the functor
induced by the `Λ`-linear `f_!` of the size-bounded sites. -/
def moduleSheafEquivMapDerivedCategoryCompIso
    [HasDerivedCategory (ModuleSheaf.{u, u, u} B X Λ)]
    [HasDerivedCategory (ModuleSheaf.{u, u, u} B Y Λ)]
    [HasDerivedCategory (Stacks.EtaleCohomology.EtaleModules.{u, u} Λ X.obj)]
    [HasDerivedCategory (Stacks.EtaleCohomology.EtaleModules.{u, u} Λ Y.obj)] :
    (moduleSheafEquiv B Λ X).functor.mapDerivedCategory ⋙
        (etaleModulesFShriek B Λ f).mapDerivedCategory ≅
      (fShriekMod.{u, u, u} B Λ f).mapDerivedCategory ⋙
        (moduleSheafEquiv B Λ Y).functor.mapDerivedCategory :=
  (Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
      (moduleSheafEquivFunctorCompEtaleModulesFShriekIso B Λ f).symm).symm ≪≫
    Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _ (Iso.refl _)

end Transport

/-! ### `Rf_! = f_!` through a compactification with finite structure morphism -/

section Factorization

open Stacks.EtaleCohomology

variable {X Xbar Y : B.Scheme} (j : X ⟶ Xbar) (fbar : Xbar ⟶ Y)
  [IsOpenImmersion (B.inclusion.map j)] [IsFinite (B.inclusion.map fbar)]

/-- **Stacks 0F52 on Mathlib's small étale sites**: for `f = j ≫ f̄` with `j` an open immersion
and `f̄` finite, the transported `f_!` is extension by zero along `j` followed by the direct image
along `f̄`. -/
def etaleModulesFShriekIsoCompactification :
    etaleModulesFShriek B Λ (j ≫ fbar) ≅
      etaleModuleExtensionByZero.{u, u} Λ (B.inclusion.map j) ⋙
        etaleModuleDirectImage.{u, u} Λ (B.inclusion.map fbar) :=
  Functor.isoWhiskerLeft (moduleSheafEquiv B Λ X).inverse
      (Functor.isoWhiskerRight (fShriekModIsoCompactificationHom B Λ j fbar)
          (moduleSheafEquiv B Λ Y).functor ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (fShriekMod.{u, u, u} B Λ j)
          (etalePushforwardModSheafEquivIso B Λ fbar) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (fShriekModSheafEquivIso B Λ j) _ ≪≫
        Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafEquiv B Λ X).counitIso _ ≪≫ Functor.leftUnitor _

/-- The compactification `j : X ⟶ X̄` of `j ≫ f̄`, for `f̄` finite. -/
abbrev compactificationOfFactorization :
    CompactificationOf (Over.mk (B.inclusion.map (j ≫ fbar))) :=
  CompactificationOf.ofFactorizationGeneral (B.inclusion.map (j ≫ fbar)) (B.inclusion.map j)
    (B.inclusion.map fbar) (B.inclusion.map_comp j fbar).symm

attribute [local instance] HasDerivedCategory.standard

/-- **`Rf_! = f_!` on `D(X_étale, Λ)` through a compactification with finite structure
morphism.** The derived lower shriek `R f̄_* ∘ Rj_!` of Stacks 0F7H is the functor induced by
the transported `f_!`: `Rj_! = j_!` and `R f̄_* = f̄_*`, both being exact, and `f̄_* ∘ j_! = f_!`
by Stacks 0F52. -/
def derivedLowerShriekUnboundedCompactificationOfFactorizationIso :
    derivedLowerShriekUnbounded.{u, u} (B.inclusion.map (j ≫ fbar))
        (compactificationOfFactorization B j fbar) Λ ≅
      (etaleModulesFShriek B Λ (j ≫ fbar)).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, u} Λ (B.inclusion.map j)) _ ≪≫
    Functor.isoWhiskerLeft _
      (etaleModuleDerivedDirectImageUnboundedIsoOfIsIntegralHom.{u, u} Λ (B.inclusion.map fbar)) ≪≫
    (Stacks.DerivedFunctor.mapDerivedCategoryCompIsoOfIso _ _ _
      (etaleModulesFShriekIsoCompactification B Λ j fbar)).symm

/-- **`Rf_! = f_!` on `D⁺(X_étale, Λ)` through a compactification with finite structure
morphism.** -/
def derivedLowerShriekCompactificationOfFactorizationIso :
    derivedLowerShriek.{u, u} (B.inclusion.map (j ≫ fbar))
        (compactificationOfFactorization B j fbar) Λ ≅
      (etaleModulesFShriek B Λ (j ≫ fbar)).mapDerivedCategoryPlus :=
  haveI := etaleModulesFShriek_additive B Λ (j ≫ fbar)
  haveI := etaleModulesFShriek_preservesFiniteLimits B Λ (j ≫ fbar)
  haveI := etaleModulesFShriek_preservesFiniteColimits B Λ (j ≫ fbar)
  Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        (etaleModuleExtensionByZero.{u, u} Λ (B.inclusion.map j))) _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        (etaleModuleDirectImage.{u, u} Λ (B.inclusion.map fbar))) ≪≫
    Stacks.DerivedFunctor.mapDerivedCategoryPlusCompIso _ _ ≪≫
    Stacks.DerivedFunctor.mapDerivedCategoryPlusNatIso
      (etaleModulesFShriekIsoCompactification B Λ j fbar).symm

end Factorization

/-! ### Stacks 0GKM -/

section Comparison

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {X Y : B.Scheme} (f : X ⟶ Y)
  [IsSeparated (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f)] [QuasiCompact (B.inclusion.map f)]
  [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj]

/-- **Stacks 0GKM on `D⁺_tors(X_étale, Λ)`.** For every compactification `j` of a quasi-finite
separated morphism `f` to a quasi-compact quasi-separated scheme, the functor
`Rf_! = R f̄_* ∘ j_! : D⁺_tors(X_étale, Λ) ⥤ D⁺_tors(Y_étale, Λ)` of Stacks 0F7H agrees with the
restriction of the functor `f_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of Stacks 0F5M. -/
theorem nonempty_derivedLowerShriek_iso_mapDerivedCategory
    (j : CompactificationOf (Over.mk (B.inclusion.map f))) :
    Nonempty ((isTorsionPlus.{u, u} Λ X.obj).ι ⋙ derivedLowerShriek.{u, u} (B.inclusion.map f) j Λ ⋙
        DerivedCategory.Plus.ι ≅
      (isTorsionPlus.{u, u} Λ X.obj).ι ⋙ DerivedCategory.Plus.ι ⋙
        (etaleModulesFShriek B Λ f).mapDerivedCategory) := by
  obtain ⟨Xbar, i, fbar, _, _, rfl⟩ := exists_isOpenImmersion_isFinite_factorization B f
  have : CompactSpace (B.inclusion.obj Y) := inferInstanceAs (CompactSpace Y.obj)
  have : QuasiSeparatedSpace (B.inclusion.obj Y) := inferInstanceAs (QuasiSeparatedSpace Y.obj)
  exact ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedLowerShriekCompactificationIsoUniv
      (B.inclusion.map (i ≫ fbar)) j (compactificationOfFactorization B i fbar) Λ) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (derivedLowerShriekCompactificationOfFactorizationIso B Λ i fbar) DerivedCategory.Plus.ι)⟩

/-- **Stacks 0GKM on `D(X_étale, Λ)`, for a torsion ring `Λ`.** For every compactification `j`
of a quasi-finite separated morphism `f` to a quasi-compact quasi-separated scheme, the functor
`Rf_! = R f̄_* ∘ j_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of Stacks 0F7H agrees with the functor
`f_!` of Stacks 0F5M. -/
theorem nonempty_derivedLowerShriekUnbounded_iso_mapDerivedCategory
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) (j : CompactificationOf (Over.mk (B.inclusion.map f))) :
    Nonempty (derivedLowerShriekUnbounded.{u, u} (B.inclusion.map f) j Λ ≅
      (etaleModulesFShriek B Λ f).mapDerivedCategory) := by
  obtain ⟨Xbar, i, fbar, _, _, rfl⟩ := exists_isOpenImmersion_isFinite_factorization B f
  have : CompactSpace (B.inclusion.obj Y) := inferInstanceAs (CompactSpace Y.obj)
  have : QuasiSeparatedSpace (B.inclusion.obj Y) := inferInstanceAs (QuasiSeparatedSpace Y.obj)
  exact ⟨derivedLowerShriekUnboundedCompactificationIsoUniv (B.inclusion.map (i ≫ fbar)) j
      (compactificationOfFactorization B i fbar) Λ hΛ ≪≫
    derivedLowerShriekUnboundedCompactificationOfFactorizationIso B Λ i fbar⟩

end Comparison

section Schemes

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- A morphism of schemes locally of finite type, read as a morphism of a big étale site
containing its source and target, is locally of finite type. -/
instance locallyOfFiniteType_inclusion_map_homMk {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (hX : B.Contains X) (hY : B.Contains Y) :
    LocallyOfFiniteType (B.inclusion.map (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY)) :=
  inferInstanceAs (LocallyOfFiniteType f)

/-- A locally quasi-finite morphism of schemes, read as a morphism of a big étale site containing
its source and target, is locally quasi-finite. -/
instance locallyQuasiFinite_inclusion_map_homMk {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] (hX : B.Contains X) (hY : B.Contains Y) :
    LocallyQuasiFinite (B.inclusion.map (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY)) :=
  inferInstanceAs (LocallyQuasiFinite f)

/-- The transported `f_!` of a morphism of schemes read in a big étale site is additive. -/
instance etaleModulesFShriek_homMk_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (hX : B.Contains X) (hY : B.Contains Y) :
    (etaleModulesFShriek B Λ (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY)).Additive :=
  etaleModulesFShriek_additive B Λ _

/-- The transported `f_!` of a morphism of schemes read in a big étale site preserves finite
limits. -/
instance etaleModulesFShriek_homMk_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (hX : B.Contains X) (hY : B.Contains Y) :
    PreservesFiniteLimits
      (etaleModulesFShriek B Λ (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY)) :=
  etaleModulesFShriek_preservesFiniteLimits B Λ _

/-- The transported `f_!` of a morphism of schemes read in a big étale site preserves finite
colimits. -/
instance etaleModulesFShriek_homMk_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (hX : B.Contains X) (hY : B.Contains Y) :
    PreservesFiniteColimits
      (etaleModulesFShriek B Λ (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY)) :=
  etaleModulesFShriek_preservesFiniteColimits B Λ _

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyQuasiFinite f]
  [LocallyOfFiniteType f] [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y]
  (hX : B.Contains X) (hY : B.Contains Y)

/-- **Stacks 0GKM** for the functors `Rf_! : D⁺_tors(X_étale, Λ) ⥤ D⁺_tors(Y_étale, Λ)` of
Stacks 0F7H. Let `f : X ⟶ Y` be a quasi-finite separated morphism of schemes with `Y`
quasi-compact and quasi-separated (so `X` is too), and `Λ` a ring. For every compactification
`j : X ⟶ X̄` of `X` over `Y`, the functor `Rf_! = R f̄_* ∘ j_!` agrees with the restriction to
`D⁺_tors(X_étale, Λ)` of the functor `f_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of Stacks 0F5M.

The direct image with compact support `f_!` of Stacks 0F6R is constructed on the small étale sites
of a big étale site `B` (Stacks 021A); it is read on Mathlib's small étale sites, where `Rf_!`
lives, through `AlgebraicGeometry.SmallEtale.etaleModulesFShriek`, and any big étale site
containing `X` and `Y` may be used (one exists: `AlgebraicGeometry.BigEtaleSite.ofSet`).
Quasi-finiteness is Stacks 02NG: locally quasi-finite, locally of finite type and quasi-compact
together. -/
@[stacks 0GKM "Rf_! on D⁺_tors(X_étale, Λ), any ring Λ, any compactification"]
theorem nonempty_derivedLowerShriek_iso_fShriek (j : CompactificationOf (Over.mk f)) :
    Nonempty ((isTorsionPlus.{u, u} Λ X).ι ⋙ derivedLowerShriek.{u, u} f j Λ ⋙
        DerivedCategory.Plus.ι ≅
      (isTorsionPlus.{u, u} Λ X).ι ⋙ DerivedCategory.Plus.ι ⋙
        (etaleModulesFShriek B Λ
          (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY)).mapDerivedCategory) := by
  have : IsSeparated (B.inclusion.map (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY)) :=
    inferInstanceAs (IsSeparated f)
  have : QuasiCompact (B.inclusion.map (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY)) :=
    inferInstanceAs (QuasiCompact f)
  have : CompactSpace (B.obj Y hY).obj := inferInstanceAs (CompactSpace Y)
  have : QuasiSeparatedSpace (B.obj Y hY).obj := inferInstanceAs (QuasiSeparatedSpace Y)
  exact nonempty_derivedLowerShriek_iso_mapDerivedCategory B Λ
    (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY) j

/-- **Stacks 0GKM** for the functors `Rf_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of Stacks 0F7H,
`Λ` a torsion ring. Let `f : X ⟶ Y` be a quasi-finite separated morphism of schemes with `Y`
quasi-compact and quasi-separated (so `X` is too). For every compactification `j : X ⟶ X̄` of
`X` over `Y`, the functor `Rf_! = R f̄_* ∘ j_!` agrees with the functor
`f_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of Stacks 0F5M.

As in `AlgebraicGeometry.SmallEtale.nonempty_derivedLowerShriek_iso_fShriek`, `f_!` is read on
Mathlib's small étale sites through `AlgebraicGeometry.SmallEtale.etaleModulesFShriek`, for any
big étale site containing `X` and `Y`. A torsion ring is one in which `m • 1 = 0` for some
`m > 0`. -/
@[stacks 0GKM "Rf_! on D(X_étale, Λ), Λ a torsion ring, any compactification"]
theorem nonempty_derivedLowerShriekUnbounded_iso_fShriek (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)
    (j : CompactificationOf (Over.mk f)) :
    Nonempty (derivedLowerShriekUnbounded.{u, u} f j Λ ≅
      (etaleModulesFShriek B Λ
        (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY)).mapDerivedCategory) := by
  have : IsSeparated (B.inclusion.map (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY)) :=
    inferInstanceAs (IsSeparated f)
  have : QuasiCompact (B.inclusion.map (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY)) :=
    inferInstanceAs (QuasiCompact f)
  have : CompactSpace (B.obj Y hY).obj := inferInstanceAs (CompactSpace Y)
  have : QuasiSeparatedSpace (B.obj Y hY).obj := inferInstanceAs (QuasiSeparatedSpace Y)
  exact nonempty_derivedLowerShriekUnbounded_iso_mapDerivedCategory B Λ
    (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY) hΛ j

end Schemes

end AlgebraicGeometry.SmallEtale

end
