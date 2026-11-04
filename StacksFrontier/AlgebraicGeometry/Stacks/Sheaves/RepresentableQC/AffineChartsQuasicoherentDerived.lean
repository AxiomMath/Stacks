module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackEssentiallySmallUnivLE
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleQuasicoherentDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.LiftedSites
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftDerived

/-!
# `D_QCoh` of an algebraic space read on its affine étale charts

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let the
sections of the `𝒪_F`-modules lie in a universe `max u m` containing the universe `u` of the
schemes. This file identifies `D_QCoh(𝒪_F)` with the subcategory of the derived category of
sheaves of modules on the affine étale charts of `F` of the objects whose cohomology sheaves are
cartesian.

## Main results

* `AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_of_univLE` and
  `AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_of_univLE`: the
  sheafification instances, at every module universe containing `u`, on which `D_QCoh(𝒪_F)` is
  built, from the essential smallness of the small étale site.
* `AlgebraicGeometry.Space.isUniversalArrow_map_iff_bijective_sectionsBaseChange`: a restriction
  map of an `𝒪_F`-module is a base change exactly when the base change comparison
  `AlgebraicGeometry.Space.sectionsBaseChange` is bijective.
-/

@[expose] public section

-- The ambient-universe instances on sheaves of modules state their module universe as a `max`
-- of the universes of the site and of the rings, which the module universe `max u m` of the
-- `𝒪_F`-modules does not match; instance search against them leaves a stuck universe
-- constraint. The instances that apply are Mathlib's, to which they unfold.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModulesOnACategory.ChaoticComparison (IsCartesianPresheaf cartesianSheaves)

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- Presheaves of abelian groups with sections in any universe `m` containing `u` on the small
étale ringed site of an algebraic space admit sheafification: the site is essentially small at
`u`, hence at `m`. -/
instance smallEtaleRingedSite_hasSheafify_of_univLE [UnivLE.{u, m}] :
    HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m} := by
  have : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C :=
    inferInstanceAs (EssentiallySmall.{u} (SmallEtale B S hS F))
  have : EssentiallySmall.{m} (smallEtaleRingedSite B S hS F hF).C :=
    essentiallySmall_trans_univLE.{u, u, u + 1, m} this
  exact GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{m} _

/-- On the small étale ringed site of an algebraic space, the morphisms of presheaves of abelian
groups with sections in any universe `m` containing `u` inverted by sheafification are the
locally bijective ones: the site is essentially small at `u`, hence at `m`. -/
instance smallEtaleRingedSite_wEqualsLocallyBijective_of_univLE [UnivLE.{u, m}] :
    (smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m} := by
  have : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C :=
    inferInstanceAs (EssentiallySmall.{u} (SmallEtale B S hS F))
  have : EssentiallySmall.{m} (smallEtaleRingedSite B S hS F hF).C :=
    essentiallySmall_trans_univLE.{u, u, u + 1, m} this
  haveI (X : (smallEtaleRingedSite B S hS F hF).Cᵒᵖ) : HasLimitsOfShape
      (StructuredArrow X (equivSmallModel.{m} (smallEtaleRingedSite B S hS F hF).C).inverse.op)
      AddCommGrpCat.{m} :=
    hasLimitsOfShape_of_essentiallySmall.{m} _ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    (smallEtaleRingedSite B S hS F hF).J

/-- **A restriction map of an `𝒪_F`-module is a base change exactly when the base change
comparison is bijective.** Over a morphism `f : V ⟶ U` of étale charts, the restriction map
`G(U) ⟶ G(V)` is a universal arrow for restriction of scalars along `𝒪_F(U) ⟶ 𝒪_F(V)` if and
only if `AlgebraicGeometry.Space.sectionsBaseChange G f`, its adjoint transpose
`𝒪_F(V) ⊗_{𝒪_F(U)} G(U) ⟶ G(V)`, is bijective. -/
theorem isUniversalArrow_map_iff_bijective_sectionsBaseChange
    (G : Modules.{u, max u m} B S hS F hF) {U V : SmallEtale B S hS F} (f : V ⟶ U) :
    (ModuleCat.restrictScalars.{max u m}
        (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj.map
          f.op).hom).IsUniversalArrow (G.val.map f.op) ↔
      Function.Bijective (sectionsBaseChange G f) :=
  ((Functor.isUniversalArrow_iff_isIso
    (ModuleCat.extendRestrictScalarsAdj ((structurePresheaf B S hS F).map f.op).hom)
    (G.val.map f.op)).trans Iff.rfl).trans
    (bijective_sectionsBaseChange_iff_isIso_restrictionBaseChange B S hS F hF G f).symm

include hF in
/-- The inclusion of the affine étale charts is a dense subsite inclusion of the small étale
ringed site of `F` (Stacks 04JS), stated for the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
theorem affineEtaleInclusion_isDenseSubsite_ringedSite :
    (AffineEtale.inclusion B S hS F : AffineEtale B S hS F ⥤
      (smallEtaleRingedSite B S hS F hF).C).IsDenseSubsite (AffineEtale.topology B S hS F)
      (smallEtaleRingedSite B S hS F hF).J :=
  (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2

/-- **Restriction to the affine charts is an equivalence on sheaves of abelian groups with
sections in `max u m`.** This is the Comparison Lemma along the dense subsite inclusion of
Stacks 04JS; its size input holds because the comma categories of the inclusion are essentially
small at `u`. -/
theorem isEquivalence_affineEtaleRestriction_addCommGrpCat_max :
    haveI := (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
    ((AffineEtale.inclusion B S hS F).sheafPushforwardContinuous AddCommGrpCat.{max u m}
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F)).IsEquivalence := by
  have hd : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  have hl : ∀ W : (SmallEtale B S hS F)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow W (AffineEtale.inclusion B S hS F).op)
        AddCommGrpCat.{max u m} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  infer_instance

/-- **Restriction of `𝒪_F`-modules to the affine étale charts**, as an equivalence, for module
sections in `max u m`: the Comparison Lemma along the dense subsite inclusion of Stacks 04JS at
a module universe above that of the structure rings
(`Stacks.UniverseLift.moduleRestrictionEquivalenceULift`). Its target is the category of sheaves
of modules on `AlgebraicGeometry.Space.affineEtaleRingedSite`. -/
noncomputable def affineEtaleRestrictionEquivalence :
    Modules.{u, max u m} B S hS F hF ≌
      SheafOfModules.{max u m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleRingedSite B S hS F hF).O) :=
  @Stacks.UniverseLift.moduleRestrictionEquivalenceULift.{m} (smallEtaleRingedSite B S hS F hF)
    _ _ (AffineEtale.topology B S hS F) (AffineEtale.inclusion B S hS F)
    (affineEtaleInclusion_isDenseSubsite_ringedSite B S hS F hF)
    (isEquivalence_affineEtaleRestriction_addCommGrpCat_max.{u, m} B S hS F hF)

/-- The restriction of an `𝒪_F`-module to the affine étale charts is cartesian exactly when its
restriction maps along the morphisms of affine étale charts are base changes. -/
theorem isCartesianPresheaf_affineEtaleRestrictionEquivalence_iff
    (G : Modules.{u, max u m} B S hS F hF) :
    IsCartesianPresheaf ((affineEtaleRestrictionEquivalence.{u, m} B S hS F hF).functor.obj
      G).val ↔
      ∀ ⦃U V : (AffineEtale B S hS F)ᵒᵖ⦄ (a : V ⟶ U),
        (ModuleCat.restrictScalars.{max u m}
          (((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj.map
            ((AffineEtale.inclusion B S hS F).op.map a)).hom).IsUniversalArrow
          (G.val.map ((AffineEtale.inclusion B S hS F).op.map a)) :=
  @Stacks.UniverseLift.isCartesianPresheaf_moduleRestrictionEquivalenceULift_iff.{m}
    (smallEtaleRingedSite B S hS F hF) _ _ (AffineEtale.topology B S hS F)
    (AffineEtale.inclusion B S hS F)
    (affineEtaleInclusion_isDenseSubsite_ringedSite B S hS F hF)
    (isEquivalence_affineEtaleRestriction_addCommGrpCat_max.{u, m} B S hS F hF) G

/-- **`𝒪_F`-modules are sheaves of modules on the lifted affine étale site.** For module
sections in `max u m`, the category of `𝒪_F`-modules is equivalent to the category of sheaves of
modules on `AlgebraicGeometry.Space.affineEtaleLiftedSite`, the affine étale ringed site of `F`
transported to its small model at `max u m` with its rings raised to `max u m`: restriction to
the affine étale charts (`AlgebraicGeometry.Space.affineEtaleRestrictionEquivalence`) followed by
the transport along the small model (`AlgebraicGeometry.RingedSite.transportRingTransport`). -/
noncomputable def affineEtaleLiftedModulesEquivalence :
    Modules.{u, max u m} B S hS F hF ≌
      SheafOfModules.{max u m}
        (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleLiftedSite.{u, m} B S hS F hF).O) :=
  haveI := essentiallySmall_lift.{m, u} (AffineEtale B S hS F)
  (affineEtaleRestrictionEquivalence.{u, m} B S hS F hF).trans
    ((affineEtaleRingedSite B S hS F hF).transportRingTransport.{m}
      (equivSmallModel.{max u m} (AffineEtale B S hS F))).sheafEquivalence

/-- **An `𝒪_F`-module is quasi-coherent exactly when its image on the lifted affine étale site
is cartesian.** By Descent, Proposition 03DX (2), quasi-coherence is being cartesian on affine
charts; restriction to the affine charts and the transport to the small model change neither
the sections nor the restriction maps, only the rings through which they are read. -/
theorem isCartesianPresheaf_affineEtaleLiftedModulesEquivalence_iff
    (G : Modules.{u, max u m} B S hS F hF) :
    IsCartesianPresheaf ((affineEtaleLiftedModulesEquivalence.{u, m} B S hS F hF).functor.obj
      G).val ↔ G.IsQuasicoherentOnSite := by
  have := essentiallySmall_lift.{m, u} (AffineEtale B S hS F)
  refine (((affineEtaleRingedSite B S hS F hF).transportRingTransport.{m}
      (equivSmallModel.{max u m} (AffineEtale B S hS F))).isCartesianPresheaf_functor_obj_iff
        ((affineEtaleRestrictionEquivalence.{u, m} B S hS F hF).functor.obj G).val).trans ?_
  refine (isCartesianPresheaf_affineEtaleRestrictionEquivalence_iff.{u, m} B S hS F hF G).trans ?_
  refine Iff.trans ?_
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts_anyUniverse.{u, max u m}
      B S hS F hF G).symm
  constructor
  · intro h U V hU hV f
    have h' := h (Quiver.Hom.op ((AffineEtale.inclusion B S hS F).preimage
      (X := (⟨V, hV⟩ : AffineEtale B S hS F)) (Y := ⟨U, hU⟩) f))
    rw [Functor.op_map, Quiver.Hom.unop_op, Functor.map_preimage] at h'
    exact (isUniversalArrow_map_iff_bijective_sectionsBaseChange B S hS F hF G f).1 h'
  · intro h U V a
    exact (isUniversalArrow_map_iff_bijective_sectionsBaseChange B S hS F hF G
      ((AffineEtale.inclusion B S hS F).map a.unop)).2
      (h V.unop.obj U.unop.obj V.unop.property U.unop.property
        ((AffineEtale.inclusion B S hS F).map a.unop))

/-- The functor of `AlgebraicGeometry.Space.affineEtaleLiftedModulesEquivalence` is additive. -/
instance affineEtaleLiftedModulesEquivalence_functor_additive :
    (affineEtaleLiftedModulesEquivalence.{u, m} B S hS F hF).functor.Additive := by
  haveI := essentiallySmall_lift.{m, u} (AffineEtale B S hS F)
  haveI : (affineEtaleRestrictionEquivalence.{u, m} B S hS F hF).functor.Additive :=
    @Stacks.UniverseLift.moduleRestrictionEquivalenceULift_functor_additive.{m}
      (smallEtaleRingedSite B S hS F hF) _ _ (AffineEtale.topology B S hS F)
      (AffineEtale.inclusion B S hS F)
      (affineEtaleInclusion_isDenseSubsite_ringedSite B S hS F hF)
      (isEquivalence_affineEtaleRestriction_addCommGrpCat_max.{u, m} B S hS F hF)
  exact inferInstanceAs ((affineEtaleRestrictionEquivalence.{u, m} B S hS F hF).functor ⋙
    ((affineEtaleRingedSite B S hS F hF).transportRingTransport.{m}
      (equivSmallModel.{max u m} (AffineEtale B S hS F))).sheafEquivalence.functor).Additive

/-- **`D_QCoh(𝒪_F)` is the derived category of sheaves of modules on the lifted affine étale
site with cartesian cohomology sheaves.** For module sections in `max u m`, the derived functor
of `AlgebraicGeometry.Space.affineEtaleLiftedModulesEquivalence` identifies the objects of
`D(𝒪_F)` with quasi-coherent cohomology sheaves with the objects of the derived category of
sheaves of modules on `AlgebraicGeometry.Space.affineEtaleLiftedSite` whose cohomology sheaves
are cartesian
(`AlgebraicGeometry.Space.isCartesianPresheaf_affineEtaleLiftedModulesEquivalence_iff`).

On the left the derived category is the standard model, as in
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`; on the right it is the small model
`Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory` in which the
subcategory of Stacks 0GZS is stated. -/
noncomputable def quasicoherentDerivedCategoryEquivalenceCartesian :
    QuasicoherentDerivedCategory.{u, max u m} B S hS F hF ≌
      (DerivedCategoryB.derivedCategoryB (cartesianSheaves.{max u m}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (affineEtaleLiftedSite.{u, m} B S hS F hF).O))).FullSubcategory :=
  letI : HasDerivedCategory (Modules.{u, max u m} B S hS F hF) := HasDerivedCategory.standard _
  Stacks.UniverseLift.derivedCategoryBEquivalence
    (affineEtaleLiftedModulesEquivalence.{u, m} B S hS F hF)
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max u m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
    (cartesianSheaves.{max u m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleLiftedSite.{u, m} B S hS F hF).O))
    (isCartesianPresheaf_affineEtaleLiftedModulesEquivalence_iff.{u, m} B S hS F hF)

end AlgebraicGeometry.Space

end
