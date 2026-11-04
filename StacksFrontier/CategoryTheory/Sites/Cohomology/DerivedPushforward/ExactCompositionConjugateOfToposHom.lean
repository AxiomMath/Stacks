module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceStageCompatibility

/-!
# The composition isomorphism of derived pullbacks is conjugate to that of exact direct images

Let `f : X ⟶ Y`, `g : Y ⟶ Z` and `ψ : X ⟶ Z` be morphisms of ringed topoi whose direct images of
modules are exact, and let `T : (g ∘ f)_* ≅ ψ_*` be an isomorphism of direct images (for instance
the action of a 2-isomorphism `g ∘ f ≅ ψ`). The derived direct images `Rf_*`, `Rg_*`, `Rψ_*` are
then computed degreewise, by `Functor.mapDerivedCategory`, and the derived pullbacks compose by
Stacks 0D6D followed by the action of the pullback transport attached to `T`. This file shows that
the two composition isomorphisms are conjugate: along the adjunctions `Lφ^* ⊣ φ_*` (with `φ_*` the
exact direct image on derived categories), the conjugate of `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^* ≅ Lψ^*` is
the inverse of the composition isomorphism `f_* ⋙ g_* ≅ ψ_*` of exact functors read on derived
categories.

## Main results

* `conjugateEquiv_derivedPullbackCompIso_trans_hom`: the conjugation identity, for arbitrary
  identifications `βφ : Rφ_* ≅ φ_*` of the derived direct images with the exact ones that are
  compatible with the units.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0D6E](https://stacks.math.columbia.edu/tag/0D6E)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

namespace Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom

universe v u w v' u' w' v'' u'' w''

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z) (ψ : RingedToposHom X Z)

/-- The pullback transport attached to an isomorphism `T : (g ∘ f)_* ≅ ψ_*` of direct images: the
uniqueness isomorphism of the left adjoints of `ψ_*`. -/
abbrev pullbackModulesTransport (T : pushforwardModules (g.comp f) ≅ pushforwardModules ψ) :
    (g.comp f).toModulesHom.pullbackModules ≅ ψ.toModulesHom.pullbackModules :=
  (pullbackAdjPushforwardModules (g.comp f)).leftAdjointUniq
    ((pullbackAdjPushforwardModules ψ).ofNatIsoRight T.symm)

variable [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')] [HasSheafify Z.J (Type w'')]
  [IsGrothendieckAbelian.{w} X.Modules] [IsGrothendieckAbelian.{w'} Y.Modules]
  [PreservesFiniteLimits (pushforwardModules f)] [PreservesFiniteColimits (pushforwardModules f)]
  [PreservesFiniteLimits (pushforwardModules g)] [PreservesFiniteColimits (pushforwardModules g)]

/-- **The composition isomorphism of derived pullbacks is conjugate to that of exact direct
images.** For identifications `βφ : Rφ_* ≅ φ_*` of the derived direct images with the exact
direct images on derived categories, compatible with the units (`hβφ`), the conjugate of
`Lg^* ⋙ Lf^* ≅ L(g ∘ f)^* ≅ Lψ^*` (Stacks 0D6D, then the transport attached to `T`) along the
adjunctions `Lφ^* ⊣ φ_*` is the inverse of the composition isomorphism `f_* ⋙ g_* ≅ ψ_*`
(Stacks 03D6, then `T`) read on derived categories. -/
theorem conjugateEquiv_derivedPullbackCompIso_trans_hom
    [PreservesFiniteLimits (pushforwardModules ψ)] [PreservesFiniteColimits (pushforwardModules ψ)]
    (T : pushforwardModules (g.comp f) ≅ pushforwardModules ψ)
    (βf : derivedPushforward f ≅ (pushforwardModules f).mapDerivedCategory)
    (hβf : ∀ K, (derivedPushforwardUnit f).app K ≫ βf.hom.app (DerivedCategory.Qh.obj K) =
      (pushforwardModules f).mapDerivedCategoryFactorsh.inv.app K)
    (βg : derivedPushforward g ≅ (pushforwardModules g).mapDerivedCategory)
    (hβg : ∀ K, (derivedPushforwardUnit g).app K ≫ βg.hom.app (DerivedCategory.Qh.obj K) =
      (pushforwardModules g).mapDerivedCategoryFactorsh.inv.app K)
    (βψ : derivedPushforward ψ ≅ (pushforwardModules ψ).mapDerivedCategory)
    (hβψ : ∀ K, (derivedPushforwardUnit ψ).app K ≫ βψ.hom.app (DerivedCategory.Qh.obj K) =
      (pushforwardModules ψ).mapDerivedCategoryFactorsh.inv.app K) :
    conjugateEquiv ((derivedAdjunction ψ).ofNatIsoRight βψ)
        (((derivedAdjunction g).ofNatIsoRight βg).comp ((derivedAdjunction f).ofNatIsoRight βf))
        (derivedPullbackCompIso f g ≪≫
          derivedPullbackIsoOfPullbackModulesIso (pullbackModulesTransport f g ψ T)).hom =
      (RingTheory.TorIndependence.mapDerivedCategoryCompNatIso _ _ _
        ((pushforwardModulesCompIso f g).symm ≪≫ T)).inv := by
  refine AlgebraicGeometry.Space.conjugateEquiv_eq_inv_of_compUnit
    (pullbackAdjPushforwardMapHomotopy f) (pullbackAdjPushforwardMapHomotopy g)
    (pullbackAdjPushforwardMapHomotopy ψ)
    ((derivedAdjunction f).ofNatIsoRight βf) ((derivedAdjunction g).ofNatIsoRight βg)
    ((derivedAdjunction ψ).ofNatIsoRight βψ)
    (ηf := (pushforwardModules f).mapDerivedCategoryFactorsh.inv)
    (ηg := (pushforwardModules g).mapDerivedCategoryFactorsh.inv)
    (ηgf := (pushforwardModules ψ).mapDerivedCategoryFactorsh.inv)
    (εf := derivedPullbackComparison f) (εg := derivedPullbackComparison g)
    (εgf := derivedPullbackComparison ψ)
    (Functor.mapHomotopyCategoryCompIso ((pushforwardModulesCompIso f g).symm ≪≫ T)
      (ComplexShape.up ℤ))
    (pullbackMapHomotopyCompIso f g ≪≫
      Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesTransport f g ψ T)
        (ComplexShape.up ℤ))
    _ _ (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ?_ ?_ ?_ ?_ ?_ ?_
  iterate 3
    exact AlgebraicGeometry.Space.counit_ofNatIsoRight_fac _ (derivedAdjunction _) _ ‹_›
      (derivedAdjunction_counit_fac _)
  · intro W
    exact (Category.assoc _ _ _).trans
      (derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app f g
        (pullbackModulesTransport f g ψ T) W)
  · intro K
    have k := pullbackModulesCompIso_inv_app_comp_counit f g
    have ht := CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_hom_app_comp_counit
      (pullbackAdjPushforwardModules (g.comp f)) (pullbackAdjPushforwardModules ψ) T
    have H := CategoryTheory.Adjunction.mapHomotopyCategory_counit_mates_of_eq
      (c := (pushforwardModulesCompIso f g).symm ≪≫ T) rfl k ht
      (AF := pullbackAdjPushforwardMapHomotopy f) (AG := pullbackAdjPushforwardMapHomotopy g)
      (AH := pullbackAdjPushforwardMapHomotopy ψ)
      (e' := pullbackMapHomotopyCompIso f g ≪≫
        Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesTransport f g ψ T)
          (ComplexShape.up ℤ)) rfl rfl rfl rfl K
    convert H using 2
  · intro K
    exact AlgebraicGeometry.Space.compUnit_comp_mapDerivedCategoryCompNatIso_hom_app _ K

/-- `conjugateEquiv_derivedPullbackCompIso_trans_hom` for a morphism `ψ'` equal to `ψ`, with the
two composition isomorphisms given together with their identifications `hDpb`, `hE` with the
canonical ones followed by the transport along `ψ = ψ'`. -/
theorem conjugateEquiv_hom_eq_inv_of_eq {ψ' : RingedToposHom X Z} (hψ : ψ = ψ')
    [PreservesFiniteLimits (pushforwardModules ψ')]
    [PreservesFiniteColimits (pushforwardModules ψ')]
    (T : pushforwardModules (g.comp f) ≅ pushforwardModules ψ)
    (βf : derivedPushforward f ≅ (pushforwardModules f).mapDerivedCategory)
    (hβf : ∀ K, (derivedPushforwardUnit f).app K ≫ βf.hom.app (DerivedCategory.Qh.obj K) =
      (pushforwardModules f).mapDerivedCategoryFactorsh.inv.app K)
    (βg : derivedPushforward g ≅ (pushforwardModules g).mapDerivedCategory)
    (hβg : ∀ K, (derivedPushforwardUnit g).app K ≫ βg.hom.app (DerivedCategory.Qh.obj K) =
      (pushforwardModules g).mapDerivedCategoryFactorsh.inv.app K)
    (βψ : derivedPushforward ψ' ≅ (pushforwardModules ψ').mapDerivedCategory)
    (hβψ : ∀ K, (derivedPushforwardUnit ψ').app K ≫ βψ.hom.app (DerivedCategory.Qh.obj K) =
      (pushforwardModules ψ').mapDerivedCategoryFactorsh.inv.app K)
    (Dpb : derivedPullback g ⋙ derivedPullback f ≅ derivedPullback ψ')
    (hDpb : Dpb = (derivedPullbackCompIso f g ≪≫
      derivedPullbackIsoOfPullbackModulesIso (pullbackModulesTransport f g ψ T)) ≪≫
        eqToIso (congrArg (fun φ : RingedToposHom X Z ↦ derivedPullback φ) hψ))
    (E : pushforwardModules f ⋙ pushforwardModules g ≅ pushforwardModules ψ')
    (hE : E = ((pushforwardModulesCompIso f g).symm ≪≫ T) ≪≫
      eqToIso (congrArg (fun φ : RingedToposHom X Z ↦ pushforwardModules φ) hψ)) :
    conjugateEquiv ((derivedAdjunction ψ').ofNatIsoRight βψ)
        (((derivedAdjunction g).ofNatIsoRight βg).comp ((derivedAdjunction f).ofNatIsoRight βf))
        Dpb.hom =
      (RingTheory.TorIndependence.mapDerivedCategoryCompNatIso _ _ _ E).inv := by
  subst hψ hDpb hE
  simp only [eqToIso_refl, Iso.trans_refl]
  exact conjugateEquiv_derivedPullbackCompIso_trans_hom f g ψ T βf hβf βg hβg βψ hβψ

end Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom

end
