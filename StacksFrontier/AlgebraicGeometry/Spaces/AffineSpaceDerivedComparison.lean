module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreComparisonTransport
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedComparisonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleIsoCongr
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence

/-!
# `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` is an equivalence on an affine algebraic space

Let `X` be an affine algebraic space over a scheme `S`, represented by an affine scheme `T`.
This file proves that the comparison functor `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is an
equivalence.  This is the input of the third assertion of Stacks 08H0 (the derived coherator
restricted to `D_QCoh(𝒪_X)` is a quasi-inverse of the comparison), and it is the source's
argument: "the result for schemes (Stacks 08D9) and Stacks 071Q".

## The proof

* **The small étale site of `T`.**  The comparison `D(QCoh(T_étale, 𝒪)) ⥤ D_QCoh(T_étale, 𝒪)`
  is an equivalence: by `AlgebraicGeometry.SmallEtale.derivedQuasicoherentComparisonSquare` it
  is intertwined with the Zariski comparison of `T`, which is an equivalence by Stacks 06Z0
  (`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isAffine_atModel`), by
  the derived functors of `ε^*` on `D(QCoh)` (Stacks 03DX (2), derived) and on `D_QCoh`
  (Stacks 071Q), both equivalences.
* **From `T_étale` to `X_étale`.**  The modules on the small étale site of `T` and the
  `𝒪_X`-modules are equivalent, matching quasi-coherence
  (`AlgebraicGeometry.Space.affineChartModuleEquivalence`): the small étale site of `T` is the
  small étale site of the represented algebraic space `h_T`
  (`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`), and that is the small
  étale site of `X` along the isomorphism `X ≅ h_T` (`AlgebraicGeometry.Space.SmallEtale.congr`,
  reindexed by `Stacks.SheafOfModules.reindexEquivalence`).  Quasi-coherence is intrinsic to the
  ringed topos (`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff`), so the comparison
  for `X` is an equivalence because the one for `T_étale` is
  (`Stacks.DerivedComparison.isEquivalence_comparison_of_equivalence`).

## Main definitions

* `AlgebraicGeometry.Space.affineChartModuleEquivalence`: `Mod(T_étale, 𝒪) ≌ Mod(𝒪_X)` for an
  isomorphism `X ≅ h_U`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_affineChartModuleEquivalence_functor_obj_iff`:
  the equivalence matches quasi-coherence.
* `AlgebraicGeometry.SmallEtale.isEquivalence_derivedQcohOnSiteComparison_of_isAffine`: the
  comparison on the small étale site of an affine scheme is an equivalence.
* `AlgebraicGeometry.Space.isEquivalence_quasicoherentDerivedComparison_of_isAffineSpace`: the
  comparison of Stacks 08F1 is an equivalence on an affine algebraic space.

## Implementation notes

All derived categories are the standard models, as for the comparison functor of Stacks 08F1,
`AlgebraicGeometry.Space.quasicoherentDerivedComparison`; the scheme-side inputs hold at every
model.

## References

* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 08D9](https://stacks.math.columbia.edu/tag/08D9)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08F1](https://stacks.math.columbia.edu/tag/08F1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u


/-! ### The modules on an affine algebraic space and on the small étale site of its chart -/

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

attribute [local instance high]
  _root_.AlgebraicGeometry.SmallEtale.abelianSheafOfModulesStructureSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (e : F ≅ yoneda.obj U)

include e

attribute [local instance] SmallEtale.congr_functor_isContinuous
  SmallEtale.congr_functor_isCocontinuous SmallEtale.congr_inverse_isCocontinuous

/-- The inverse of the equivalence `SmallEtale.congr` is continuous. -/
instance congr_inverse_isContinuous :
    (SmallEtale.congr B S hS e).inverse.IsContinuous (SmallEtale.topology B S hS (yoneda.obj U))
      (SmallEtale.topology B S hS F) :=
  Functor.isContinuous_iff_coverPreserving.2 (SmallEtale.congr_inverse_coverPreserving B S hS e)

/-- The inverse of the equivalence `SmallEtale.congr` is a dense subsite inclusion, which is the
hypothesis under which quasi-coherence is invariant under reindexing. -/
instance congr_inverse_isDenseSubsite :
    (SmallEtale.congr B S hS e).inverse.IsDenseSubsite (SmallEtale.topology B S hS (yoneda.obj U))
      (SmallEtale.topology B S hS F) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

/-- **The modules on the small étale site of the scheme underlying `U` are the `𝒪_X`-modules**,
for an isomorphism `e : X ≅ h_U` of the algebraic space `X` with the one represented by `U`.  It is
the comparison of the small étale sites of `U` and of `h_U`
(`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`) followed by reindexing along the
equivalence of small étale sites induced by `e` (`AlgebraicGeometry.Space.SmallEtale.congr`). -/
def affineChartModuleEquivalence :
    SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U) ≌ Modules.{u, u} B S hS F hF :=
  (representedSmallEtaleModuleEquivalence B S hS U).trans
    (Stacks.SheafOfModules.reindexEquivalence (J' := SmallEtale.topology B S hS F)
      (SmallEtale.congr B S hS e) (representedStructureRingSheaf B S hS U))

/-- The equivalence of module categories is additive. -/
instance additive_affineChartModuleEquivalence_functor :
    (affineChartModuleEquivalence B S hS F hF U e).functor.Additive :=
  ⟨fun {_ _ _ _} => rfl⟩

/-- The inverse of the equivalence of module categories is additive. -/
instance additive_affineChartModuleEquivalence_symm_functor :
    (affineChartModuleEquivalence B S hS F hF U e).symm.functor.Additive :=
  inferInstanceAs (affineChartModuleEquivalence B S hS F hF U e).inverse.Additive

/-- **The equivalence `Mod(U_étale, 𝒪) ≌ Mod(𝒪_X)` matches quasi-coherence.**  Both of its steps
are reindexings along equivalences of ringed sites, under which quasi-coherence is invariant
(Stacks 03DM for clause (6) of Stacks 03DL). -/
theorem isQuasicoherentOnSite_affineChartModuleEquivalence_functor_obj_iff
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :
    ((affineChartModuleEquivalence B S hS F hF U e).functor.obj M).IsQuasicoherentOnSite ↔
      M.IsQuasicoherentOnSite :=
  (Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff (J' := SmallEtale.topology B S hS F)
      (SmallEtale.congr B S hS e)
      (representedStructureRingSheaf B S hS U) _).trans
    (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U M)

/-- The inverse of the equivalence `Mod(U_étale, 𝒪) ≌ Mod(𝒪_X)` matches quasi-coherence too. -/
theorem isQuasicoherentOnSite_affineChartModuleEquivalence_inverse_obj_iff
    (G : Modules.{u, u} B S hS F hF) :
    ((affineChartModuleEquivalence B S hS F hF U e).inverse.obj G).IsQuasicoherentOnSite ↔
      G.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_affineChartModuleEquivalence_functor_obj_iff B S hS F hF U e _).symm.trans
    ((SheafOfModules.isQuasicoherentOnSite _).prop_iff_of_iso
      ((affineChartModuleEquivalence B S hS F hF U e).counitIso.app G))

attribute [local instance] isClosedUnderKernels_quasicoherentSheaves_schemeUniverse
  isClosedUnderCokernels_quasicoherentSheaves quasicoherentSheaves_abelian_of_closure

/-- **The comparison functor of Stacks 08F1 is an equivalence on an algebraic space isomorphic to
the one represented by an affine scheme.**  The comparison on the small étale site of the affine
scheme is an equivalence, and the equivalence of module categories
`AlgebraicGeometry.Space.affineChartModuleEquivalence` matches quasi-coherence, which transports
it (`Stacks.DerivedComparison.isEquivalence_comparison_of_equivalence`). -/
theorem isEquivalence_quasicoherentDerivedComparison_of_iso
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) :
    (quasicoherentDerivedComparison B S hS F hF).IsEquivalence := by
  let : HasDerivedCategory (SheafOfModules.{u}
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf) := HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedSchemeStructureSheaf B S hS U)).FullSubcategory :=
    HasDerivedCategory.standard _
  have := _root_.AlgebraicGeometry.SmallEtale.isEquivalence_derivedQcohOnSiteComparison_of_isAffine
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property
  have : (Stacks.DerivedComparison.comparison
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (representedSchemeStructureSheaf B S hS U))).IsEquivalence := this
  exact Stacks.DerivedComparison.isEquivalence_comparison_of_equivalence
    (affineChartModuleEquivalence B S hS F hF U e).symm
    (isQuasicoherentOnSite_affineChartModuleEquivalence_inverse_obj_iff B S hS F hF U e)

omit e in
/-- **The comparison functor `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is an equivalence on an
affine algebraic space.**  An affine algebraic space is isomorphic to the one represented by an
affine scheme of the site, and `isEquivalence_quasicoherentDerivedComparison_of_iso` applies. -/
theorem isEquivalence_quasicoherentDerivedComparison_of_isAffineSpace
    (hAffine : IsAffineSpace B S hS F) :
    (quasicoherentDerivedComparison B S hS F hF).IsEquivalence :=
  isEquivalence_quasicoherentDerivedComparison_of_iso B S hS F hF _
    hAffine.choose_spec.2.some hAffine.choose_spec.1

end AlgebraicGeometry.Space

end
