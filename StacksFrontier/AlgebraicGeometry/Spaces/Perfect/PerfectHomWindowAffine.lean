module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectHomWindowInduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongCocontinuousFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectHomWindowSmallEtaleScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelPullbackExact
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentSpellings
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtalePerfectConverse
public import StacksFrontier.AlgebraicGeometry.Duality.DetectingBoundednessOfAPerfectComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSiteComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.PerfectToPseudoCoherentGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp

/-!
# A window of Hom-vanishing against a perfect object on an affine algebraic space

Let `Y` be an affine algebraic space and let `K` be a perfect object of `D(𝒪_Y)`.  This file
proves that `K` has a window of Hom-vanishing against `D_QCoh(𝒪_Y)`, in the sense of
`Stacks.HomWindow.HasHomWindow`: there are `a ≤ b` such that every `L ∈ D_QCoh(𝒪_Y)` whose
cohomology sheaves vanish in the degrees `a, …, b` admits no nonzero morphism `K ⟶ L`.  It is the
base case of the induction of
`AlgebraicGeometry.Space.hasHomWindow_of_isPerfect_of_affine`, which yields [Stacks, Tag 09MB].

## Main results

* `AlgebraicGeometry.SmallEtale.hasHomWindow_of_isPerfect`: on the small étale site of a
  quasi-compact and quasi-separated *scheme* `T`, a perfect object with quasi-coherent cohomology
  has a window.  This is the scheme statement [Stacks, Tag 09M4] read through the equivalence
  `D_QCoh(𝒪_T) ≌ D_QCoh(T_étale, 𝒪)` of Stacks 071Q, perfectness descending to the Zariski site
  by Stacks 08HG.
* `AlgebraicGeometry.Space.hasHomWindow_represented`: the same on the algebraic space represented
  by an affine scheme, across the identification of its small étale site with the small étale
  site of the scheme.
* `AlgebraicGeometry.Space.hasHomWindow_of_isAffineSpace`: the same on an affine algebraic space,
  across its isomorphism with the represented one.

## Implementation notes

Each of the three steps descends the window along an exact functor whose derived functor is
faithful (`Stacks.HomWindow.HasHomWindow.of_mapDerivedCategory`), or carries it across an
equivalence of `D_QCoh`'s; what has to be transported besides is perfectness and
quasi-coherence of `K`.  Perfectness crosses the identification of small étale sites by
`AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory_of_isCocontinuous`, the slice squares
holding on the nose by `Stacks.SheafOfModules.over_reindex_eq`; quasi-coherence crosses it by
Stacks 03DM (`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex`), and the quasi-coherence of
the cohomology of a perfect object is Stacks 08JL on the algebraic space.

The derived categories are the standard models throughout,
`CategoryTheory.HasDerivedCategory.standard` being a local instance of high priority, as in the
scheme statement of Stacks 09M4 that is applied here.

## References

* [Stacks Project, Tag 09MB](https://stacks.math.columbia.edu/tag/09MB)
* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.HomWindow

universe u

attribute [local instance 100000] HasDerivedCategory.standard


attribute [local instance 100000] AlgebraicGeometry.SmallEtale.smallEtaleModulesAbelian
  AlgebraicGeometry.SmallEtale.smallEtaleRingedSiteModulesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The cohomology sheaves of a perfect object are quasi-coherent.**  A perfect object of
`D(𝒪_Y)` on an algebraic space `Y` is pseudo-coherent, so its cohomology sheaves are
quasi-coherent by Stacks 08JL. -/
theorem qcohModules_homology_of_isPerfect (Y : AlgebraicSpaces B S hS)
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hK : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K) (i : ℤ) :
    qcohModules B S hS Y
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj K) :=
  isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom_unconditional B S hS Y.1 Y.2 K (i - 1) i
    (RingedSite.isPseudoCoherentFrom_of_isPerfect_general _ hK (i - 1)) (by omega)

section Represented

variable (T : BigFppfOver B S hS)

/-- The inverse of the comparison of small étale sites of a represented algebraic space is
continuous, at the spelling of the functor of the opposite equivalence. -/
theorem representedSmallEtaleEquivalence_symm_functor_isContinuous :
    (representedSmallEtaleEquivalence B S hS T).symm.functor.IsContinuous
      (representedSchemeSmallEtaleTopology B S hS T) (SmallEtale.topology B S hS (yoneda.obj T)) :=
  inferInstanceAs ((representedSmallEtaleEquivalence B S hS T).inverse.IsContinuous _ _)

/-- The comparison of small étale sites of a represented algebraic space is a dense subsite
inclusion, at the spelling of the inverse of the opposite equivalence. -/
theorem representedSmallEtaleEquivalence_symm_inverse_isDenseSubsite :
    (representedSmallEtaleEquivalence B S hS T).symm.inverse.IsDenseSubsite
      (SmallEtale.topology B S hS (yoneda.obj T)) (representedSchemeSmallEtaleTopology B S hS T) :=
  inferInstanceAs ((representedSmallEtaleEquivalence B S hS T).functor.IsDenseSubsite _ _)

/-- The comparison of small étale sites of a represented algebraic space is continuous, at the
spelling of the inverse of the opposite equivalence. -/
theorem representedSmallEtaleEquivalence_symm_inverse_isContinuous :
    (representedSmallEtaleEquivalence B S hS T).symm.inverse.IsContinuous
      (SmallEtale.topology B S hS (yoneda.obj T)) (representedSchemeSmallEtaleTopology B S hS T) :=
  inferInstanceAs ((representedSmallEtaleEquivalence B S hS T).functor.IsContinuous _ _)

attribute [local instance] representedSmallEtaleEquivalence_symm_functor_isContinuous
  representedSmallEtaleEquivalence_symm_inverse_isDenseSubsite
  representedSmallEtaleEquivalence_symm_inverse_isContinuous

/-- **The modules on a represented algebraic space are the modules on the small étale site of the
scheme.**  Reindexing along the inverse of the comparison of small étale sites
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`; the transported structure sheaf is the
structure sheaf of the scheme on the nose. -/
abbrev representedToSchemeModules :
    Modules.{u, u} B S hS (yoneda.obj T) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T) ≌
      SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T) :=
  Stacks.SheafOfModules.reindexEquivalence (J' := representedSchemeSmallEtaleTopology B S hS T)
    (representedSmallEtaleEquivalence B S hS T).symm (representedStructureRingSheaf B S hS T)

/-- The reindexing to the scheme is additive: it only reindexes sections. -/
theorem representedToSchemeModules_additive :
    (representedToSchemeModules B S hS T).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The modules over a restriction of the structure sheaf of a represented algebraic space form an
abelian category: `SheafOfModules.instAbelian`, pinned as
`AlgebraicGeometry.SmallEtale.smallEtaleModulesAbelian` is, for the same reason. -/
noncomputable abbrev representedOverModulesAbelian
    (V : SmallEtale B S hS (yoneda.obj T)) :
    Abelian (SheafOfModules.{u} ((representedStructureRingSheaf B S hS T).over V)) :=
  SheafOfModules.instAbelian _

/-- The modules over a restriction of the structure sheaf of the small étale site of a scheme form
an abelian category, pinned for the same reason. -/
noncomputable abbrev representedSchemeOverModulesAbelian
    (U : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property) :
    Abelian (SheafOfModules.{u} ((representedSchemeStructureSheaf B S hS T).over U)) :=
  SheafOfModules.instAbelian _

attribute [local instance 100000] representedOverModulesAbelian representedSchemeOverModulesAbelian

/-- The slice of the opposite comparison at an étale `U` over the scheme is continuous. -/
theorem representedOverSiteEquivalence_functor_isContinuous
    (U : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property) :
    (Stacks.SheafOfModules.overSiteEquivalence (representedSmallEtaleEquivalence B S hS T).symm
      U).functor.IsContinuous ((representedSchemeSmallEtaleTopology B S hS T).over U)
      ((SmallEtale.topology B S hS (yoneda.obj T)).over
        ((representedSmallEtaleEquivalence B S hS T).symm.functor.obj U)) :=
  inferInstanceAs
    ((Over.post (X := U) (representedSmallEtaleEquivalence B S hS T).symm.functor).IsContinuous
    ((representedSchemeSmallEtaleTopology B S hS T).over U)
    ((SmallEtale.topology B S hS (yoneda.obj T)).over
      ((representedSmallEtaleEquivalence B S hS T).symm.functor.obj U)))

/-- The inverse of the slice of the opposite comparison is continuous. -/
theorem representedOverSiteEquivalence_inverse_isContinuous
    (U : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property) :
    (Stacks.SheafOfModules.overSiteEquivalence (representedSmallEtaleEquivalence B S hS T).symm
      U).inverse.IsContinuous
      ((SmallEtale.topology B S hS (yoneda.obj T)).over
        ((representedSmallEtaleEquivalence B S hS T).symm.functor.obj U))
      ((representedSchemeSmallEtaleTopology B S hS T).over U) :=
  inferInstance

attribute [local instance] representedOverSiteEquivalence_functor_isContinuous
  representedOverSiteEquivalence_inverse_isContinuous

/-- Reindexing along the slice of the inverse comparison at an étale `U` over the scheme: modules
over the restricted structure sheaf of the represented space become modules over the restricted
structure sheaf of the scheme. -/
abbrev representedToSchemeOverModules
    (U : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property) :
    SheafOfModules.{u} ((representedStructureRingSheaf B S hS T).over
        ((representedSmallEtaleEquivalence B S hS T).symm.functor.obj U)) ≌
      SheafOfModules.{u} ((representedSchemeStructureSheaf B S hS T).over U) :=
  Stacks.SheafOfModules.reindexEquivalence
    (J' := (representedSchemeSmallEtaleTopology B S hS T).over U)
    (Stacks.SheafOfModules.overSiteEquivalence (representedSmallEtaleEquivalence B S hS T).symm U)
    ((representedStructureRingSheaf B S hS T).over
      ((representedSmallEtaleEquivalence B S hS T).symm.functor.obj U))

/-- The slice reindexing is additive. -/
theorem representedToSchemeOverModules_additive
    (U : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property) :
    (representedToSchemeOverModules B S hS T U).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The reindexing to the scheme is left exact, being the functor of an equivalence. -/
theorem representedToSchemeModules_preservesFiniteLimits :
    PreservesFiniteLimits (representedToSchemeModules B S hS T).functor := by
  infer_instance

/-- The reindexing to the scheme is right exact, being the functor of an equivalence. -/
theorem representedToSchemeModules_preservesFiniteColimits :
    PreservesFiniteColimits (representedToSchemeModules B S hS T).functor := by
  infer_instance

/-- The slice reindexing is left exact, being the functor of an equivalence. -/
theorem representedToSchemeOverModules_preservesFiniteLimits
    (U : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property) :
    PreservesFiniteLimits (representedToSchemeOverModules B S hS T U).functor := by
  infer_instance

/-- The slice reindexing is right exact, being the functor of an equivalence. -/
theorem representedToSchemeOverModules_preservesFiniteColimits
    (U : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property) :
    PreservesFiniteColimits (representedToSchemeOverModules B S hS T U).functor := by
  infer_instance

/-- **Perfectness crosses to the small étale site of the scheme.**  If `K` is a perfect object of
the derived category of the represented algebraic space, its reindexing is a perfect object of
the derived category of the small étale site of the scheme. -/
theorem isPerfect_representedToSchemeModules
    (K : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj T)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)))
    (hK : (smallEtaleRingedSite B S hS (yoneda.obj T)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)).IsPerfect K) :
    haveI := representedToSchemeModules_additive B S hS T
    (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).IsPerfect
      ((representedToSchemeModules B S hS T).functor.mapDerivedCategory.obj K) :=
  RingedSite.isPerfect_mapDerivedCategory_of_isCocontinuous
    (X := _root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (Y := smallEtaleRingedSite B S hS (yoneda.obj T)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T))
    (representedSmallEtaleEquivalence B S hS T).symm.functor
    (representedToSchemeModules B S hS T).functor
    (fun U => (representedToSchemeOverModules B S hS T U).functor)
    (representedToSchemeModules_additive B S hS T)
    (representedToSchemeModules_preservesFiniteLimits B S hS T)
    (representedToSchemeModules_preservesFiniteColimits B S hS T)
    (representedToSchemeOverModules_additive B S hS T)
    (representedToSchemeOverModules_preservesFiniteLimits B S hS T)
    (representedToSchemeOverModules_preservesFiniteColimits B S hS T)
    (isCocontinuous_representedSmallEtaleEquivalence_inverse B S hS T)
    (fun U => Iso.refl _)
    (fun U => NatIso.ofComponents (fun M => Iso.refl _) (by intro M M' g; rfl))
    K hK

/-- **A window on a represented affine algebraic space.**  Let `T` be an object of the big fppf
site over `S` whose underlying scheme is affine, and let `K` be a perfect object of the derived
category of the algebraic space it represents.  Then `K` has a window of Hom-vanishing against
the objects with quasi-coherent cohomology.

The reindexing to the small étale site of the scheme is an equivalence, so its derived functor is
faithful; it carries quasi-coherent modules to quasi-coherent modules (Stacks 03DM) and `K` to a
perfect object with quasi-coherent cohomology, which has a window by
`AlgebraicGeometry.SmallEtale.hasHomWindow_of_isPerfect`. -/
theorem hasHomWindow_represented (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (K : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj T)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)))
    (hK : (smallEtaleRingedSite B S hS (yoneda.obj T)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)).IsPerfect K) :
    HasHomWindow
      (qcohModules B S hS ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩)
      K := by
  have := representedToSchemeModules_additive B S hS T
  let F := (representedToSchemeModules B S hS T).functor
  have hQ : ∀ M : Modules.{u, u} B S hS (yoneda.obj T)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T),
      qcohModules B S hS ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ M →
        SmallEtale.qcohOnSite (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T)
          T.left.property (F.obj M) := fun M hM =>
    Stacks.SheafOfModules.isQuasicoherentOnSite_reindex
      (J := SmallEtale.topology B S hS (yoneda.obj T))
      (J' := representedSchemeSmallEtaleTopology B S hS T)
      (representedSmallEtaleEquivalence B S hS T).symm
      (representedStructureRingSheaf B S hS T) M (hM := hM)
  have hfaith : F.mapDerivedCategory.Faithful :=
    faithful_mapDerivedCategory_of_iso F (representedToSchemeModules B S hS T).inverse
      (representedToSchemeModules B S hS T).unitIso.symm
  refine HasHomWindow.of_mapDerivedCategory F hQ hfaith ?_
  refine SmallEtale.hasHomWindow_of_isPerfect (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property _
    (isPerfect_representedToSchemeModules B S hS T K hK) (fun i => ?_)
  exact (SmallEtale.qcohOnSite (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T)
      T.left.property).prop_of_iso ((F.mapDerivedCategoryHomologyIso i).app K).symm
    (hQ _ (qcohModules_homology_of_isPerfect B S hS
      ⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ K hK i))

end Represented

section Affine

/-- Étale pullback along a morphism of algebraic spaces equal to an identity is isomorphic to the
identity functor. -/
def etaleModulePullbackIsoOfEqId {Y : AlgebraicSpaces B S hS} (f : Y ⟶ Y)
    (hf : IsEtale B S hS f.hom) (h : f = 𝟙 Y) :
    etaleModulePullback.{u, u} B S hS f hf ≅ 𝟭 (Modules.{u, u} B S hS Y.1 Y.2) := by
  subst h
  exact etaleModulePullbackIdIso B S hS hf

/-- **A window on an affine algebraic space.**  Let `Y` be an affine algebraic space and let `K`
be a perfect object of `D(𝒪_Y)`.  Then `K` has a window of Hom-vanishing against `D_QCoh(𝒪_Y)`.

`Y` is isomorphic to the algebraic space represented by an affine scheme `T`; pullback along the
isomorphism `h_T ≅ Y` is exact with an exact inverse, hence has a faithful derived functor, and it
preserves quasi-coherence (Stacks 03M0) and perfectness, so the window of
`AlgebraicGeometry.Space.hasHomWindow_represented` for the pullback of `K` serves for `K`. -/
theorem hasHomWindow_of_isAffineSpace (Y : AlgebraicSpaces B S hS)
    (hY : IsAffineSpace B S hS Y.1) (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (hK : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect K) :
    HasHomWindow (qcohModules B S hS Y) K := by
  obtain ⟨T, hT, ⟨i⟩⟩ := hY
  let g : (⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ :
      AlgebraicSpaces B S hS) ⟶ Y := ObjectProperty.homMk i.inv
  let g' : Y ⟶ (⟨yoneda.obj T, AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T⟩ :
      AlgebraicSpaces B S hS) := ObjectProperty.homMk i.hom
  have hg : IsEtale B S hS g.hom := isEtale_of_iso B S hS i.symm
  have hg' : IsEtale B S hS g'.hom := isEtale_of_iso B S hS i
  have hgg : IsEtale B S hS (g' ≫ g).hom := isEtale_comp B S hS hg' hg
  have hcomp : g' ≫ g = 𝟙 Y := by
    ext1
    exact i.hom_inv_id
  have := etaleModulePullback_additive.{u, u} B S hS g hg
  have := preservesFiniteLimits_etaleModulePullback.{u} B S hS g hg
  have := preservesFiniteColimits_etaleModulePullback.{u} B S hS g hg
  have := etaleModulePullback_additive.{u, u} B S hS g' hg'
  have := preservesFiniteLimits_etaleModulePullback.{u} B S hS g' hg'
  have := preservesFiniteColimits_etaleModulePullback.{u} B S hS g' hg'
  have hfaith : (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.Faithful :=
    faithful_mapDerivedCategory_of_iso _ (etaleModulePullback.{u, u} B S hS g' hg')
      (etaleModulePullbackCompIso B S hS g' g hg' hg hgg ≪≫
        etaleModulePullbackIsoOfEqId B S hS _ hgg hcomp)
  exact HasHomWindow.of_mapDerivedCategory (etaleModulePullback.{u, u} B S hS g hg)
    (isQuasicoherentOnSite_etaleModulePullback B S hS g hg) hfaith
    (hasHomWindow_represented B S hS T hT _
      (isPerfect_etaleModulePullback_standard B S hS g hg K hK))

end Affine

end AlgebraicGeometry.Space

end
