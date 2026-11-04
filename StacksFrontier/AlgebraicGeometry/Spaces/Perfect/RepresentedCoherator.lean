module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackEquivalenceOfIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.QuasicoherentDerivedTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.CategoryTheory.ObjectProperty.LeftAdjointInclusionTransport
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksFrontier.AlgebraicGeometry.Size.CoveringsSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackCompSupplement

/-!
# The coherator of a represented quasi-compact quasi-separated algebraic space

Let `U` be an object of the big fppf site over `S` whose underlying scheme `T` is quasi-compact
and quasi-separated.  The inclusion `D_QCoh(𝒪_{h_U}) ⥤ D(𝒪_{h_U})` for the algebraic space
`h_U = yoneda.obj U` has a right adjoint.  The proof transports Stacks 0CR0 for the scheme `T`
across two comparisons:

* the comparison `ε : T_étale ⟶ T_Zar`, whose inverse image `ε^*` is left adjoint to `Rε_*` and
  restricts to an equivalence `D_QCoh(𝒪_T) ≌ D_QCoh(T_étale, 𝒪)` (Stacks 071Q,
  `AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`);
* the identification of the small étale site of the scheme `T` with that of the algebraic space
  `h_U`, `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, which preserves
  quasi-coherence.

Both steps are `CategoryTheory.ObjectProperty.isLeftAdjoint_ι_of_isEquivalence_lift`.  This is the
affine case of the first proof of Stacks 0CR4, which the source reduces to Stacks 08H0 and
Stacks 071Q in the same way.

## Main results

* `AlgebraicGeometry.Space.isLeftAdjoint_qcohDerivedProp_ι_yoneda`

## References

* [Stacks Project, Tag 0CR4](https://stacks.math.columbia.edu/tag/0CR4)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ObjectProperty

/-- **A coherator moves along an exact equivalence of abelian categories.**  If `G : C ⥤ C'` is an
exact equivalence detecting `P'` exactly on `P`, and the inclusion of `D_P(C)` into `D(C)` has a
right adjoint, then so does the inclusion of `D_{P'}(C')` into `D(C')`.  The derived categories
may be taken at any models; in particular `G = 𝟭` moves a coherator between two models. -/
theorem isLeftAdjoint_ι_derivedCategoryB_of_isEquivalence {C : Type*} [Category* C] [Abelian C]
    {C' : Type*} [Category* C'] [Abelian C'] [HC : HasDerivedCategory C]
    [HC' : HasDerivedCategory C'] (G : C ⥤ C') [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] [G.IsEquivalence] (P : ObjectProperty C)
    (P' : ObjectProperty C') [P'.IsClosedUnderIsomorphisms] (h : ∀ M, P' (G.obj M) ↔ P M)
    (hP : (DerivedCategoryB.derivedCategoryB P).ι.IsLeftAdjoint) :
    (DerivedCategoryB.derivedCategoryB P').ι.IsLeftAdjoint := by
  have := Stacks.Injectives.mapDerivedCategory_isEquivalence G
  have : (DerivedCategoryB.derivedCategoryB P').IsClosedUnderIsomorphisms :=
    ⟨fun e hX n => P'.prop_of_iso ((DerivedCategory.homologyFunctor C' n).mapIso e) (hX n)⟩
  have hF : ∀ K, DerivedCategoryB.derivedCategoryB P' (G.mapDerivedCategory.obj K) ↔
      DerivedCategoryB.derivedCategoryB P K := fun K =>
    ⟨fun hK n => (h _).1 (P'.prop_of_iso ((G.mapDerivedCategoryHomologyIso n).app K) (hK n)),
      fun hK n => P'.prop_of_iso ((G.mapDerivedCategoryHomologyIso n).app K).symm
        ((h _).2 (hK n))⟩
  exact @isLeftAdjoint_ι_of_isEquivalence_lift _ _ _ _ _ _ G.mapDerivedCategory inferInstance
    (fun X hX => (hF X).2 hX) (isEquivalence_lift_of_isEquivalence _ _ _ hF) hP

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The locally small model of the derived category of modules on the small étale site of the
scheme underlying `U`, the model at which Stacks 071Q is applied below. -/
local instance hasDerivedCategory_representedSchemeModules :
    HasDerivedCategory.{u} (SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :=
  Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian _

/-- **The coherator of the small étale site of a quasi-compact quasi-separated scheme**: for the
scheme `T` underlying `U`, the inclusion of the complexes with quasi-coherent cohomology into the
derived category of modules on `T_étale` has a right adjoint.  Stacks 0CR0 for `T` moved along
`ε^*` by Stacks 071Q. -/
theorem isLeftAdjoint_qcohOnSite_ι_representedScheme
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U)] :
    (DerivedCategoryB.derivedCategoryB
      (SmallEtale.qcohOnSite (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
        U.left.property)).ι.IsLeftAdjoint := by
  let T := (BigFppfOver.toScheme B S hS).obj U
  exact @ObjectProperty.isLeftAdjoint_ι_of_isEquivalence_lift _ _ _ _
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent T.ringCatSheaf)) _
    (SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B) T
      U.left.property).mapDerivedCategory
    (SmallEtale.derivedAssociatedModuleAdjunction (associatedBigEtaleSite B) T
      U.left.property).isLeftAdjoint
    (fun K hK => SmallEtale.derivedAssociatedModule_mem (associatedBigEtaleSite B) T
      U.left.property ⟨K, hK⟩)
    (SmallEtale.derivedAssociatedModule_isEquivalence.{u} (associatedBigEtaleSite B) T
      U.left.property) (Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι T)

/-- **The coherator of a represented quasi-compact quasi-separated algebraic space**: for an
object `U` of the big fppf site whose underlying scheme is quasi-compact and quasi-separated, the
inclusion `D_QCoh(𝒪_{h_U}) ⥤ D(𝒪_{h_U})` has a right adjoint. -/
theorem isLeftAdjoint_qcohDerivedProp_ι_yoneda
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)]
    [QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U)] :
    (qcohDerivedProp B S hS (schemeSpace U)).ι.IsLeftAdjoint := by
  let G := (representedSmallEtaleModuleEquivalence B S hS U).functor
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  let P' := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).O)
  have hP' : P'.IsClosedUnderIsomorphisms :=
    ⟨fun e h => SheafOfModules.IsQuasicoherentOnSite.of_iso e h⟩
  exact @ObjectProperty.isLeftAdjoint_ι_derivedCategoryB_of_isEquivalence _ _ _ _ _ _ _
    (HasDerivedCategory.standard _) G _ _ _ _ _ P' hP'
    (fun M => isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U M)
    (isLeftAdjoint_qcohOnSite_ι_representedScheme B S hS U)

section Iso

variable {V W : AlgebraicSpaces B S hS} (e : V ≅ W)

include e in
attribute [local instance] HasDerivedCategory.standard in
/-- **A coherator moves along an isomorphism of algebraic spaces.** -/
theorem isLeftAdjoint_qcohDerivedProp_ι_of_iso
    (hW : (qcohDerivedProp B S hS W).ι.IsLeftAdjoint) :
    (qcohDerivedProp B S hS V).ι.IsLeftAdjoint := by
  let E := etaleModulePullbackEquivalenceOfIso.{u, u} B S hS e
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  exact @ObjectProperty.isLeftAdjoint_ι_derivedCategoryB_of_isEquivalence _ _ _ _ _ _ _ _
    E.functor _ _ _ E.isEquivalence_functor _ _
    ⟨fun e h => SheafOfModules.IsQuasicoherentOnSite.of_iso e h⟩
    (fun M => ⟨fun h => SheafOfModules.IsQuasicoherentOnSite.of_iso (E.unitIso.app M).symm
        (isQuasicoherentOnSite_etaleModulePullback B S hS e.inv _ _ h),
      fun h => isQuasicoherentOnSite_etaleModulePullback B S hS e.hom _ _ h⟩) hW

end Iso

/-- **The coherator of an affine algebraic space**: for an affine algebraic space `V`, the
inclusion `D_QCoh(𝒪_V) ⥤ D(𝒪_V)` has a right adjoint. -/
theorem isLeftAdjoint_qcohDerivedProp_ι_of_isAffineSpace (V : AlgebraicSpaces B S hS)
    (hV : IsAffineSpace B S hS V.1) : (qcohDerivedProp B S hS V).ι.IsLeftAdjoint := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hV
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) := inferInstance
  exact isLeftAdjoint_qcohDerivedProp_ι_of_iso B S hS
    (W := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
    (ObjectProperty.isoMk _ e) (isLeftAdjoint_qcohDerivedProp_ι_yoneda B S hS T)

end AlgebraicGeometry.Space

end
