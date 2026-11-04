module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleIsoEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationAffineRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# Approximation along an isomorphism of algebraic spaces, and Stacks 08HM

An isomorphism `e : X ≅ Y` of algebraic spaces over `S` induces an equivalence of their small
étale ringed sites (`AlgebraicGeometry.Space.smallEtaleIsoEquivalence`), hence an equivalence of
the categories of `𝒪`-modules, exact in both directions.  This file shows that it carries every
ingredient of the notion of approximation (Stacks 08HI) across: quasi-coherence, perfectness,
`m`-pseudo-coherence, the support of a sheaf (which is pulled back along the bijection of points),
open subspaces and their affineness and quasi-compactness.

With this, the statements of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ApproximationAffineRepresented.lean`, which are
stated for the algebraic space `h_U` represented by an object `U` with affine underlying scheme,
are transported to an arbitrary algebraic space `X` representable by an affine scheme, that is
one with `AlgebraicGeometry.Space.IsAffineSpace`: this is **Stacks 08HM** as stated.

## Main results

* `AlgebraicGeometry.Space.approximationHolds_of_iso`: approximation for a triple is carried
  along an isomorphism of algebraic spaces.
* `AlgebraicGeometry.Space.approximationByPerfectComplexes_of_iso`: so is approximation by
  perfect complexes (Stacks 08HJ).
* `AlgebraicGeometry.Space.approximationHolds_of_isAffineSpace`: **Stacks 08HM**, first
  assertion.
* `AlgebraicGeometry.Space.approximationByPerfectComplexes_of_isAffineSpace`: **Stacks 08HM**,
  second assertion.

## References

* [Stacks Project, Tag 08HM](https://stacks.math.columbia.edu/tag/08HM)
* [Stacks Project, Tag 08HI](https://stacks.math.columbia.edu/tag/08HI)
* [Stacks Project, Tag 08HJ](https://stacks.math.columbia.edu/tag/08HJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Postcomposition with an étale morphism preserves coverings -/

/-- Postcomposition of étale charts with an étale morphism of algebraic spaces is cover
preserving: it preserves fibre products and carries each generating covering family of the
small étale site to a covering family. -/
theorem coverPreserving_smallEtalePostcomp {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    CoverPreserving (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
      (smallEtalePostcomp B S hS f hf) :=
  ProEtale.coverPreserving_of_generators _ (SmallEtale.precoverage B S hS X.1) _
    fun {_ _} hR => by
      have h := precoverage_le_comap_smallEtalePostcomp B S hS f hf _ hR
      rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff,
        Sieve.generate_map_eq_functorPushforward] at h
      exact h

variable {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y)

/-- The equivalence of small étale sites is cocontinuous: its inverse is cover preserving. -/
instance isCocontinuous_smallEtaleIsoEquivalence_functor :
    (smallEtaleIsoEquivalence B S hS e).functor.IsCocontinuous
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
  (Adjunction.isCocontinuous_iff_coverPreserving _ _
      (smallEtaleIsoEquivalence B S hS e).toAdjunction).2
    (coverPreserving_smallEtalePostcomp B S hS e.inv (isEtale_hom_hom_of_iso B S hS e.symm))

/-- The inverse of the equivalence of small étale sites is cocontinuous. -/
instance isCocontinuous_smallEtaleIsoEquivalence_inverse :
    (smallEtaleIsoEquivalence B S hS e).inverse.IsCocontinuous
      (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) :=
  (Adjunction.isCocontinuous_iff_coverPreserving _ _
      (smallEtaleIsoEquivalence B S hS e).symm.toAdjunction).2
    (coverPreserving_smallEtalePostcomp B S hS e.hom (isEtale_hom_hom_of_iso B S hS e))

/-- The equivalence of small étale sites is a dense subsite inclusion. -/
instance isDenseSubsite_smallEtaleIsoEquivalence_functor :
    (smallEtaleIsoEquivalence B S hS e).functor.IsDenseSubsite
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
  Equivalence.isDenseSubsite_functor_of_isCocontinuous _ _ _

/-! ### The equivalence of module categories -/

/-- The first compatibility of the two comparisons of structure sheaves, for the inverse
equivalence of small étale sites. -/
theorem smallEtaleIsoStructureMap_symm_counit :
    Functor.whiskerRight (NatTrans.op (smallEtaleIsoEquivalence B S hS e).symm.counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj =
      (smallEtaleIsoStructureMap B S hS e).hom ≫
        (smallEtaleIsoEquivalence B S hS e).symm.inverse.op.whiskerLeft
          (smallEtaleIsoStructureMapInverse B S hS e).hom := by
  ext : 2
  exact rfl

/-- The second compatibility of the two comparisons of structure sheaves, for the inverse
equivalence of small étale sites. -/
theorem smallEtaleIsoStructureMap_symm_unit :
    (smallEtaleIsoStructureMapInverse B S hS e).hom ≫
        (smallEtaleIsoEquivalence B S hS e).symm.functor.op.whiskerLeft
          (smallEtaleIsoStructureMap B S hS e).hom ≫
        Functor.whiskerRight (NatTrans.op (smallEtaleIsoEquivalence B S hS e).symm.unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj := by
  ext : 2
  exact rfl

/-- **The modules on isomorphic algebraic spaces correspond**: transport along the equivalence of
small étale sites, the structure sheaves matching on the nose. -/
def smallEtaleIsoModuleEquivalence :
    Modules.{u, u} B S hS Y.1 Y.2 ≌ Modules.{u, u} B S hS X.1 X.2 :=
  haveI := isContinuous_smallEtaleIsoEquivalence_functor_ringedSite B S hS e
  haveI := isContinuous_smallEtaleIsoEquivalence_inverse_ringedSite B S hS e
  SheafOfModules.pushforwardPushforwardEquivalence (smallEtaleIsoEquivalence B S hS e)
    (smallEtaleIsoStructureMap B S hS e) (smallEtaleIsoStructureMapInverse B S hS e)
    (smallEtaleIsoStructureMap_counit B S hS e) (smallEtaleIsoStructureMap_unit B S hS e)

/-- Transport of modules from `Y` to `X`. -/
abbrev isoModulePushforward : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  (smallEtaleIsoModuleEquivalence B S hS e).functor

/-- Transport of modules from `X` to `Y`. -/
abbrev isoModuleRestriction : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2 :=
  (smallEtaleIsoModuleEquivalence B S hS e).inverse

/-- Transport of modules from `Y` to `X` is an additive functor. -/
instance additive_isoModulePushforward : (isoModulePushforward B S hS e).Additive where
  map_add := by intros; ext; rfl

/-- Transport of modules from `X` to `Y` is an additive functor. -/
instance additive_isoModuleRestriction : (isoModuleRestriction B S hS e).Additive where
  map_add := by intros; ext; rfl

/-- Transport of modules from `Y` to `X` preserves finite limits. -/
instance preservesFiniteLimits_isoModulePushforward :
    PreservesFiniteLimits (isoModulePushforward B S hS e) :=
  inferInstanceAs (PreservesFiniteLimits (smallEtaleIsoModuleEquivalence B S hS e).functor)

/-- Transport of modules from `Y` to `X` preserves finite colimits. -/
instance preservesFiniteColimits_isoModulePushforward :
    PreservesFiniteColimits (isoModulePushforward B S hS e) :=
  inferInstanceAs (PreservesFiniteColimits (smallEtaleIsoModuleEquivalence B S hS e).functor)

/-- Transport of modules from `X` to `Y` preserves finite limits. -/
instance preservesFiniteLimits_isoModuleRestriction :
    PreservesFiniteLimits (isoModuleRestriction B S hS e) :=
  inferInstanceAs (PreservesFiniteLimits (smallEtaleIsoModuleEquivalence B S hS e).inverse)

/-- Transport of modules from `X` to `Y` preserves finite colimits. -/
instance preservesFiniteColimits_isoModuleRestriction :
    PreservesFiniteColimits (isoModuleRestriction B S hS e) :=
  inferInstanceAs (PreservesFiniteColimits (smallEtaleIsoModuleEquivalence B S hS e).inverse)

/-! ### Support -/

/-- The support of the transport of a module from `Y` to `X` is the preimage of its support
under the bijection of points. -/
theorem supportOfSheaf_isoModulePushforward (M : Modules.{u, u} B S hS Y.1 Y.2) :
    supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj ((isoModulePushforward B S hS e).obj M)) =
      pointsMap B S hS X.1 e.hom.hom ⁻¹'
        supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj M) :=
  supportOfSheaf_sheafPushforwardContinuous_smallEtalePostcomp B S hS e.hom
    (isEtale_hom_hom_of_iso B S hS e) ((SheafOfModules.toSheaf _).obj M)

/-- The support of the transport of a module from `X` to `Y` is the preimage of its support
under the bijection of points. -/
theorem supportOfSheaf_isoModuleRestriction (M : Modules.{u, u} B S hS X.1 X.2) :
    supportOfSheaf B S hS Y.1
        ((SheafOfModules.toSheaf _).obj ((isoModuleRestriction B S hS e).obj M)) =
      pointsMap B S hS Y.1 e.inv.hom ⁻¹'
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) :=
  supportOfSheaf_sheafPushforwardContinuous_smallEtalePostcomp B S hS e.inv
    (isEtale_hom_hom_of_iso B S hS e.symm) ((SheafOfModules.toSheaf _).obj M)

/-! ### Quasi-coherence -/

/-- The transport of a quasi-coherent module from `X` to `Y` is quasi-coherent. -/
theorem isQuasicoherentOnSite_isoModuleRestriction (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) :
    ((isoModuleRestriction B S hS e).obj M).IsQuasicoherentOnSite :=
  have : (smallEtaleIsoEquivalence B S hS e).symm.inverse.IsDenseSubsite
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
    isDenseSubsite_smallEtaleIsoEquivalence_functor B S hS e
  have : (smallEtaleIsoEquivalence B S hS e).symm.functor.IsContinuous
      (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) :=
    isContinuous_smallEtaleIsoEquivalence_inverse B S hS e
  have : (smallEtaleIsoEquivalence B S hS e).symm.inverse.IsContinuous
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
    isContinuous_smallEtaleIsoEquivalence_functor B S hS e
  Stacks.SheafOfModules.isQuasicoherentOnSite_reindex (J := SmallEtale.topology B S hS X.1)
    (J' := SmallEtale.topology B S hS Y.1) (smallEtaleIsoEquivalence B S hS e).symm
    (ringStructureSheaf B S hS X.1) M (hM := hM)

/-! ### Points -/

attribute [local instance] pointTopology

/-- The two maps on points induced by an isomorphism of algebraic spaces are mutually inverse. -/
theorem pointsMap_inv_pointsMap_hom (p : points B S hS X.1) :
    pointsMap B S hS Y.1 e.inv.hom (pointsMap B S hS X.1 e.hom.hom p) = p :=
  (pointsHomeomorphOfIso B S hS ((ObjectProperty.ι _).mapIso e)).symm_apply_apply p

/-! ### The derived category -/

section Derived

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

/-- The transport of an object of `D_QCoh(𝒪_X)` to `D_QCoh(𝒪_Y)`. -/
def isoQcohTransport (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) :
    QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 :=
  ⟨(isoModuleRestriction B S hS e).mapDerivedCategory.obj E.obj, fun n =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      (((isoModuleRestriction B S hS e).mapDerivedCategoryHomologyIso n).app E.obj).symm
      (isQuasicoherentOnSite_isoModuleRestriction B S hS e _ (E.property n))⟩

/-- The support of a cohomology sheaf of the transport is the preimage of the support of the
corresponding cohomology sheaf. -/
theorem supportOfSheaf_homology_isoQcohTransport
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (i : ℤ) :
    supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
          (isoQcohTransport B S hS e E).obj)) =
      pointsMap B S hS Y.1 e.inv.hom ⁻¹' supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E.obj)) :=
  (supportOfSheaf_eq_of_mapIso B S hS Y.1 Y.2 ((SheafOfModules.toSheaf _).mapIso
      (((isoModuleRestriction B S hS e).mapDerivedCategoryHomologyIso i).app E.obj))).trans
    (supportOfSheaf_isoModuleRestriction B S hS e _)

/-- `m`-pseudo-coherence is carried along the transport. -/
theorem isPseudoCoherentFrom_isoQcohTransport
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (m : ℤ)
    (h : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom E.obj m) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherentFrom
      (isoQcohTransport B S hS e E).obj m := by
  have := RingedSite.isPseudoCoherentFrom_pushforward_of_siteEquivalence
    (Y := smallEtaleRingedSite B S hS X.1 X.2) (X := smallEtaleRingedSite B S hS Y.1 Y.2)
    (smallEtaleIsoEquivalence B S hS e)
    (hFc := isContinuous_smallEtaleIsoEquivalence_functor_ringedSite B S hS e)
    (hIc := isContinuous_smallEtaleIsoEquivalence_inverse_ringedSite B S hS e)
    (smallEtaleIsoStructureMap B S hS e) (smallEtaleIsoStructureMapInverse B S hS e)
    (smallEtaleIsoStructureMap_counit B S hS e) (smallEtaleIsoStructureMap_unit B S hS e)
    (hψ := isIso_smallEtaleIsoStructureMapInverse B S hS e) E.obj m h
  exact this

/-- Perfectness is carried back from `Y` to `X`. -/
theorem isPerfect_isoModulePushforward (P : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (h : (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect P) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect
      ((isoModulePushforward B S hS e).mapDerivedCategory.obj P) :=
  RingedSite.isPerfect_pushforward_of_siteEquivalence
    (Y := smallEtaleRingedSite B S hS Y.1 Y.2) (X := smallEtaleRingedSite B S hS X.1 X.2)
    (smallEtaleIsoEquivalence B S hS e.symm)
    (hFc := isContinuous_smallEtaleIsoEquivalence_functor_ringedSite B S hS e.symm)
    (hIc := isContinuous_smallEtaleIsoEquivalence_inverse_ringedSite B S hS e.symm)
    (smallEtaleIsoStructureMap B S hS e.symm) (smallEtaleIsoStructureMapInverse B S hS e.symm)
    (smallEtaleIsoStructureMap_counit B S hS e.symm)
    (smallEtaleIsoStructureMap_unit B S hS e.symm)
    (hψ := isIso_smallEtaleIsoStructureMapInverse B S hS e.symm) P h

/-- **Approximation is carried along an isomorphism of algebraic spaces.**  If approximation
holds on `Y` for the transported triple, it holds on `X` for the triple `(Z, E, m)`. -/
theorem approximationHolds_of_iso (Z : Set (points B S hS X.1))
    (E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2) (m : ℤ)
    (h : ApproximationHolds B S hS Y.1 Y.2 (pointsMap B S hS Y.1 e.inv.hom ⁻¹' Z)
      (isoQcohTransport B S hS e E) m) :
    ApproximationHolds B S hS X.1 X.2 Z E m := by
  obtain ⟨P, hP, hsupp, α, hiso, hepi⟩ := h
  let D := Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    (smallEtaleIsoModuleEquivalence B S hS e)
  let c : (isoModulePushforward B S hS e).mapDerivedCategory.obj
      (isoQcohTransport B S hS e E).obj ⟶ E.obj := (D.counitIso.app E.obj).hom
  have hc : IsIso c := Iso.isIso_hom _
  refine ⟨(isoModulePushforward B S hS e).mapDerivedCategory.obj P,
    isPerfect_isoModulePushforward B S hS e P hP, fun i => ?_,
    (isoModulePushforward B S hS e).mapDerivedCategory.map α ≫ c, fun i hi => ?_, ?_⟩
  · intro p hp
    have := hsupp i ((supportOfSheaf_isoModulePushforward B S hS e _).subset
      ((supportOfSheaf_eq_of_mapIso B S hS X.1 X.2 ((SheafOfModules.toSheaf _).mapIso
        (((isoModulePushforward B S hS e).mapDerivedCategoryHomologyIso i).app P))).subset hp))
    rwa [Set.mem_preimage, pointsMap_inv_pointsMap_hom] at this
  · have h₁ := (isoModulePushforward B S hS e).isIso_homologyFunctor_map_mapDerivedCategory_map
      α i (hiso i hi)
    have h₂ := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).map_isIso c
    rw [Functor.map_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂
  · have h₁ := (isoModulePushforward B S hS e).epi_homologyFunctor_map_mapDerivedCategory_map
      α m hepi
    have h₂ := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) m).map_isIso c
    rw [Functor.map_comp]
    exact @epi_comp _ _ _ _ _ _ h₁ _ (@IsIso.epi_of_iso _ _ _ _ _ h₂)

/-! ### Open subspaces -/

/-- The preimage of an open subspace along an isomorphism of algebraic spaces is isomorphic to it,
hence affine when it is. -/
theorem isAffineSpace_preimage {G : Subfunctor X.1} (hG : IsAffineSpace B S hS G.toFunctor) :
    IsAffineSpace B S hS (G.preimage e.inv.hom).toFunctor :=
  have := (Subfunctor.isPullback_preimage e.inv.hom G).isIso_fst_of_isIso
  hG.of_iso (asIso (G.fromPreimage e.inv.hom)).symm

/-- The inclusion of the preimage of an open subspace along an isomorphism is quasi-compact when
the inclusion of the open subspace is: a base change of the former is a base change of the
latter. -/
theorem isQuasiCompact_preimage_ι {G : Subfunctor X.1} (hG : IsQuasiCompact B S hS G.ι) :
    IsQuasiCompact B S hS (G.preimage e.inv.hom).ι := by
  intro W hW hWqc g
  have hsq := (IsPullback.paste_horiz (IsPullback.of_hasPullback g (G.preimage e.inv.hom).ι).flip
    (Subfunctor.isPullback_preimage e.inv.hom G)).flip
  exact IsQuasiCompactSpace.of_iso B S hS (hG W hW hWqc (g ≫ e.inv.hom)) hsq.isoPullback.symm

/-- The open subspace of `Y` cut out by the preimage of an open subset of `|X|` is the preimage of
the corresponding open subspace of `X`. -/
theorem openSubspacesOrderIso_symm_preimage (W : Set (points B S hS X.1))
    (hW : @IsOpen _ (pointTopology B S hS X.1) W)
    (hW' : @IsOpen _ (pointTopology B S hS Y.1) (pointsMap B S hS Y.1 e.inv.hom ⁻¹' W)) :
    ((openSubspacesOrderIso B S hS Y.1 Y.2).symm ⟨_, hW'⟩).1 =
      ((openSubspacesOrderIso B S hS X.1 X.2).symm ⟨W, hW⟩).1.preimage e.inv.hom := by
  set G := (openSubspacesOrderIso B S hS X.1 X.2).symm ⟨W, hW⟩ with hGdef
  have hGr : Set.range (pointsMap B S hS G.1.toFunctor G.1.ι) = W := by
    rw [← openSubspacesOrderIso_apply B S hS _ X.2, hGdef, OrderIso.apply_symm_apply]
  have hG' : IsOpenSubspace B S hS (G.1.preimage e.inv.hom) :=
    isOpenSubspace_preimage B S hS e.inv.hom G.1 X.2 Y.2 G.2
  have : (openSubspacesOrderIso B S hS Y.1 Y.2).symm ⟨_, hW'⟩ = ⟨_, hG'⟩ := by
    apply (openSubspacesOrderIso B S hS Y.1 Y.2).injective
    rw [OrderIso.apply_symm_apply]
    apply TopologicalSpace.Opens.ext
    change pointsMap B S hS Y.1 e.inv.hom ⁻¹' W =
      Set.range (pointsMap B S hS (G.1.preimage e.inv.hom).toFunctor (G.1.preimage e.inv.hom).ι)
    rw [range_pointsMap_preimage_ι, hGr]
  rw [this]

/-! ### Stacks 08HJ along an isomorphism -/

include e in
/-- **Approximation by perfect complexes is carried along an isomorphism of algebraic spaces.** -/
theorem approximationByPerfectComplexes_of_iso
    (h : ApproximationByPerfectComplexes.{u, u} B S hS Y.1 Y.2) :
    ApproximationByPerfectComplexes.{u, u} B S hS X.1 X.2 := by
  intro Z hZ hqc
  have hZ' : IsClosed (pointsMap B S hS Y.1 e.inv.hom ⁻¹' Z) :=
    hZ.preimage (continuous_pointsMap B S hS e.inv.hom)
  have hqc' : IsQuasiCompact B S hS ((openSubspacesOrderIso B S hS Y.1 Y.2).symm
      ⟨(pointsMap B S hS Y.1 e.inv.hom ⁻¹' Z)ᶜ, hZ'.isOpen_compl⟩).1.ι := by
    have heq := openSubspacesOrderIso_symm_preimage B S hS e Zᶜ hZ.isOpen_compl
      (by rw [Set.preimage_compl]; exact hZ'.isOpen_compl)
    simp only [Set.preimage_compl] at heq
    rw [heq]
    exact isQuasiCompact_preimage_ι B S hS e hqc
  obtain ⟨r, hr⟩ := h _ hZ' hqc'
  refine ⟨r, fun E m hpc hsupp => approximationHolds_of_iso B S hS e Z E m
    (hr _ m (isPseudoCoherentFrom_isoQcohTransport B S hS e E (m - r) hpc) fun i hi => ?_)⟩
  exact fun p hp => hsupp i hi ((supportOfSheaf_homology_isoQcohTransport B S hS e E i).subset hp)

end Derived

/-! ### Stacks 08HM -/

section Main

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 08HM.**  Let `S` be a scheme and let `X` be an algebraic space over `S` which is
representable by an affine scheme.  Then approximation holds (Stacks 08HI) for every triple
`(Z, E, m)` for which there is an integer `r ≥ 0` with

1. `E` `m`-pseudo-coherent,
2. `Hⁱ(E)` supported on `Z` for `i ≥ m - r + 1`,
3. `X ∖ Z` the union of `r` affine opens `V₁, …, V_r` of `X`.

The case `X = h_U` is `AlgebraicGeometry.Space.approximationHolds_of_isAffine_represented`; the
general case is transported along an isomorphism `X ≅ h_U`
(`AlgebraicGeometry.Space.approximationHolds_of_iso`). -/
@[stacks 08HM "first assertion: approximation holds for every triple (T, E, m) with E
m-pseudo-coherent, H^i(E) supported on T for i ≥ m - r + 1 and X \\ T a union of r affine opens,
for X an algebraic space representable by an affine scheme"]
theorem approximationHolds_of_isAffineSpace (hXa : IsAffineSpace B S hS F)
    (Z : Set (points B S hS F))
    (E : QuasicoherentDerivedCategory.{u, u} B S hS F hF) (m : ℤ) (r : ℕ)
    (hpc : (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E.obj m)
    (hsupp : ∀ i : ℤ, m - (r : ℤ) + 1 ≤ i →
      supportOfSheaf B S hS F
        ((SheafOfModules.toSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E.obj)) ⊆ Z)
    (V : Fin r → {G : Subfunctor F // IsOpenSubspace B S hS G})
    (hV : ∀ k, IsAffineSpace B S hS (V k).1.toFunctor)
    (hcover : ⋃ k, Set.range (pointsMap B S hS (V k).1.toFunctor (V k).1.ι) = Zᶜ) :
    ApproximationHolds B S hS F hF Z E m := by
  obtain ⟨U, hU, ⟨e₀⟩⟩ := hXa
  have := hU
  let e : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ≅
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ := ObjectProperty.isoMk _ e₀
  refine approximationHolds_of_iso B S hS e Z E m
    (approximationHolds_of_isAffine_represented B S hS U _ _ m r
      (isPseudoCoherentFrom_isoQcohTransport B S hS e E m hpc) (fun i hi => ?_)
      (fun k => ⟨(V k).1.preimage e.inv.hom,
        isOpenSubspace_preimage B S hS e.inv.hom (V k).1 hF
          (isAlgebraicSpace_yoneda B S hS U) (V k).2⟩)
      (fun k => isAffineSpace_preimage B S hS e (hV k)) ?_)
  · exact fun p hp => hsupp i hi ((supportOfSheaf_homology_isoQcohTransport B S hS e E i).subset hp)
  · simp_rw [range_pointsMap_preimage_ι]
    rw [← Set.preimage_iUnion, hcover, Set.preimage_compl]

/-- **The "in particular" of Stacks 08HM**: approximation by perfect complexes (Stacks 08HJ)
holds on an algebraic space representable by an affine scheme. -/
@[stacks 08HM "second assertion: approximation by perfect complexes holds on an algebraic space
representable by an affine scheme"]
theorem approximationByPerfectComplexes_of_isAffineSpace (hXa : IsAffineSpace B S hS F) :
    ApproximationByPerfectComplexes.{u, u} B S hS F hF := by
  obtain ⟨U, hU, ⟨e₀⟩⟩ := hXa
  have := hU
  exact approximationByPerfectComplexes_of_iso B S hS
    (ObjectProperty.isoMk _ e₀ : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ≅
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (approximationByPerfectComplexes_of_isAffine_represented B S hS U)

end Main

end AlgebraicGeometry.Space

end
