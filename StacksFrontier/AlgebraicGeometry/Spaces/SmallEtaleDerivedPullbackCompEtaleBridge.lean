module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisRestrictComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueMapComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory

/-!
# The two composition comparisons for derived pullback along étale morphisms, at a complex

Let `h : X ⟶ Y` and `g : Y ⟶ Z` be étale morphisms of algebraic spaces over a scheme `S`.  The
tree carries two unrelated comparisons of the iterated derived pullback `Lg^* ⋙ Lh^*` with the
derived pullback `L(h ≫ g)^*`:

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`, the composition law of the
  derived-pullback pseudofunctor (Stacks 0D6D), which
  `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackSquareIso` is built from;
* `AlgebraicGeometry.Space.edsDerivedRestrictCompOpen` and `…edsDerivedRestrictCompEtale`, which
  Stacks 08HB (`AlgebraicGeometry.Space.exists_hom_of_glueData`) is stated with, and which are
  the *degreewise* descent of the underived comparison of iterated étale restriction with
  restriction along the composite.

The two are compared by *uniqueness of a total left derived functor*: both are morphisms out of
functors that are left derived functors of degreewise pullback along `h ≫ g`, so they agree as
soon as they agree after precomposition with `DerivedCategory.Qh`, that is on complexes.  This
file supplies the three "value at `Qh.obj K`" identities that computation needs, and identifies
the two elementary-distinguished-square comparisons with the canonical descent
`CategoryTheory.Functor.mapDerivedCategoryCompIso` of the underived comparison, which is the
form whose value at `Qh.obj K` the tree already computes
(`CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Qh`).

## Main results

* `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom`: the isomorphism of
  degreewise descents attached to an isomorphism of exact functors is the descent of that
  isomorphism as a natural transformation.  This is what makes the two spellings of the
  elementary-distinguished-square comparisons interchangeable.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIsoEtale_hom_app_Qh`: **the universal
  property of the identification `La^* ≅ (a^*)_D` of Stacks 06YY with degreewise étale
  restriction**, at a complex: composed with the structure map of `(a^*)_D` read through
  Stacks 03LW it is the canonical comparison `La^* ⟶ a^*`.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_hom_app_Qh`: **the universal
  property of the composition law of Stacks 0D6D for algebraic spaces**, at a complex: followed
  by the canonical comparison for `h ≫ g` it is the comparison for `g`, then the one for `h`,
  then the underived compositor of the morphisms of small étale ringed topoi together with the
  2-isomorphism identifying their composite with the morphism of the composite.
* `AlgebraicGeometry.Space.edsDerivedRestrictCompOpen_eq_mapDerivedCategoryCompIso` and
  `…edsDerivedRestrictCompEtale_eq_mapDerivedCategoryCompIso`: the two comparisons Stacks 08HB is
  stated with are the canonical degreewise descents of
  `AlgebraicGeometry.Space.edsFactorIsoOpen` and `…edsFactorIsoEtale`, the underived comparisons
  written through the inverse image of modules of Stacks 03LU.

## What is **not** proved here, and what it needs

The identification of the two composition comparisons themselves is **not** proved.  Written as
the analogue for algebraic spaces of
`AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback_inv_comp`, whose proof is a
single application of `CategoryTheory.Functor.leftDerived_ext` to the chase
`AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback_inv_comp_chase`, it consumes
four inputs at a complex `K`.  Three are the results above (the two universal properties and
`CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Qh` through the two identifications).
The fourth is **the underived compatibility of Stacks 03LW with composition**, read on homotopy
categories:

`Stacks.Homology.mapHomotopyCategoryIso` of
`AlgebraicGeometry.Space.pullbackModulesIsoModulePullback ≪≫ …modulePullbackIsoEtaleModulePullback`
at `h ≫ g` is the underived compositor
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso` followed by
`AlgebraicGeometry.Space.pullbackModulesCompTransport`, then the same two identifications at `g`
and at `h`, then `AlgebraicGeometry.Space.etaleModulePullbackFactorIso`.

That is a statement about *underived* sheaves of modules.  Its content is the equality of the
composition comparison of the pullback of modules of a morphism of small étale **ringed topoi**
with the composition comparison `AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU
across `AlgebraicGeometry.Space.pullbackModulesIsoModulePullback`; every factor is an
`CategoryTheory.Adjunction.leftAdjointUniq`, so it is an identity of comparisons of left adjoints
over the corresponding identity for the direct images, of which
`AlgebraicGeometry.Space.modulePushforwardCompIso_eq_modulePushforwardCompIso'` and
`AlgebraicGeometry.Space.pushforwardModulesCompTransport_eq` are the two halves.  Nothing in the
tree states it, and nothing below assumes it: no result here carries a hypothesis.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

namespace Stacks.DerivedCategoryComparisons

universe w₁ w₂ v₁ v₂ x₁ x₂

variable {C₁ : Type x₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type x₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]

/-- **The isomorphism of degreewise descents attached to an isomorphism of exact functors is the
descent of that isomorphism as a natural transformation.**  Both are lifts through the
localization `DerivedCategory.Q` of the same degreewise transformation, and
`CategoryTheory.NatTrans.mapDerivedCategory_eq` identifies a lift by its value on a complex. -/
theorem mapDerivedCategoryIsoOfNatIso_hom (F G : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    (mapDerivedCategoryIsoOfNatIso F G e).hom = NatTrans.mapDerivedCategory e.hom :=
  NatTrans.mapDerivedCategory_eq e.hom _ fun K => by
    rw [mapDerivedCategoryIsoOfNatIso_hom_app_Q]
    rfl

end Stacks.DerivedCategoryComparisons

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive isGrothendieckAbelian_modules
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- The pullback of `𝒪`-modules along the morphism of small étale ringed topoi of a morphism of
algebraic spaces: the underived functor whose total left derived functor is
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`. -/
abbrev toposPullbackModules (a : X ⟶ Y) :
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS a).toModulesHom

/-- The pullback of modules of the morphism of small étale ringed topoi is additive.  This is
`AlgebraicGeometry.RingedToposHom.pullbackModules_additive`, restated at the spelling of
`AlgebraicGeometry.Space.toposPullbackModules`: instance resolution matches up to reducible
transparency and does not cross the two spellings of the category of `𝒪`-modules on its own. -/
instance additive_toposPullbackModules (a : X ⟶ Y) :
    (toposPullbackModules B S hS a).Additive :=
  RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B S hS a)

/-- **The comparison of Stacks 03LW in the spelling the derived pullback is derived from**: the
pullback of modules of the morphism of small étale ringed topoi of an étale morphism is étale
restriction.  This is the isomorphism along which
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIsoEtale` is constructed. -/
abbrev etalePullbackModulesIso (a : X ⟶ Y) (ha : IsEtale B S hS a.hom) :
    toposPullbackModules B S hS a ≅ etaleModulePullback.{u, u} B S hS a ha :=
  pullbackModulesIsoModulePullback B S hS a ≪≫ modulePullbackIsoEtaleModulePullback B S hS a ha

/-- **The universal property of the identification of the derived pullback along an étale
morphism with degreewise étale restriction, at a complex.**  For `a` étale, the isomorphism
`La^* ≅ (a^*)_D` of `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackIsoEtale`, followed
by the structure map of `(a^*)_D` read through the comparison of Stacks 03LW, is the canonical
comparison `La^* ⟶ a^*` of Stacks 06YY.

This is the form that uniqueness of a total left derived functor consumes: it determines the
isomorphism, since a morphism into a left derived functor is determined by its restriction along
`DerivedCategory.Qh`. -/
theorem smallEtaleDerivedModulePullbackIsoEtale_hom_app_Qh (a : X ⟶ Y)
    (ha : IsEtale B S hS a.hom)
    (K : HomotopyCategory (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) :
    (smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).hom.app
          (DerivedCategory.Qh.obj K) ≫
        (Stacks.Homology.mapDerivedCategoryComparisonOfIso
          (toposPullbackModules B S hS a)
          (etaleModulePullback.{u, u} B S hS a ha)
          (etalePullbackModulesIso B S hS a ha)).hom.app K =
      (smallEtaleDerivedModulePullbackComparison B S hS a).app K := by
  -- The instances are supplied by hand: the goal and the general lemma speak of two
  -- definitionally equal but syntactically distinct spellings of the category of `𝒪`-modules.
  exact @Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso_hom_app _ _ _ _ _ _ _ _
    (toposPullbackModules B S hS a) (etaleModulePullback.{u, u} B S hS a ha)
    (additive_toposPullbackModules B S hS a) (etaleModulePullback_additive B S hS a ha)
    (preservesFiniteLimits_etaleModulePullback B S hS a ha)
    (preservesFiniteColimits_etaleModulePullback B S hS a ha)
    (smallEtaleDerivedModulePullback B S hS a)
    (smallEtaleDerivedModulePullbackComparison B S hS a)
    (inferInstanceAs ((smallEtaleDerivedModulePullback B S hS a).IsLeftDerivedFunctor
      (smallEtaleDerivedModulePullbackComparison B S hS a)
      (smallEtaleModuleQuasiIso B S hS Y)))
    (etalePullbackModulesIso B S hS a ha) K

section Comp

variable {Z : AlgebraicSpaces B S hS}

/-- The pullback of modules along the composite of the two morphisms of small étale ringed topoi
is additive, at the spelling `AlgebraicGeometry.Space.pullbackModulesCompTransport` is stated
at. -/
instance additive_toposPullbackModulesComp (h : X ⟶ Y) (g : Y ⟶ Z) :
    ((smallEtaleRingedToposHomComp B S hS h g).toModulesHom.pullbackModules).Additive :=
  RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B S hS h g)

/-- **The universal property of the composition law of Stacks 0D6D for algebraic spaces, at a
complex.**  The comparison `Lg^* ⋙ Lh^* ≅ L(h ≫ g)^*` of
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`, followed by the canonical
comparison of Stacks 06YY for `h ≫ g`, is the comparison for `g` pushed forward by `Lh^*`, then
the comparison for `h` at the degreewise pullback along `g`, then the underived compositor of
the two morphisms of small étale ringed topoi composed with the 2-isomorphism
`AlgebraicGeometry.Space.pullbackModulesCompTransport` identifying their composite with the
morphism of the composite.

This is the form that uniqueness of a total left derived functor consumes.  It is Stacks 0D6D's
own characterization
(`derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app` in the
namespace `Stacks.Cohomology.DerivedPullbackCompositionOfToposHom`) read at the morphisms of
small étale ringed topoi of Stacks 03G8. -/
theorem smallEtaleDerivedModulePullbackCompIso_hom_app_Qh (h : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ)) :
    (smallEtaleDerivedModulePullbackCompIso B S hS h g).hom.app (DerivedCategory.Qh.obj K) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS (h ≫ g)).app K =
      (smallEtaleDerivedModulePullback B S hS h).map
          ((smallEtaleDerivedModulePullbackComparison B S hS g).app K) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS h).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
            (smallEtaleRingedToposHom B S hS g)).obj K) ≫
        DerivedCategory.Qh.map
          ((pullbackMapHomotopyCompIso (smallEtaleRingedToposHom B S hS h)
              (smallEtaleRingedToposHom B S hS g) ≪≫
            Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS h g)
              (ComplexShape.up ℤ)).hom.app K) := by
  have hfac := derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app
    (smallEtaleRingedToposHom B S hS h) (smallEtaleRingedToposHom B S hS g)
    (h := smallEtaleRingedToposHom B S hS (h ≫ g)) (pullbackModulesCompTransport B S hS h g) K
  simpa only [smallEtaleDerivedModulePullbackCompIso, Iso.trans_hom, NatTrans.comp_app,
    derivedPullbackCompIso_hom, Category.assoc] using hfac

end Comp

section Square

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **The comparison Stacks 08HB is stated with, through the open subspace, is the canonical
degreewise descent of the underived comparison of Stacks 03LU.**  So its value at a complex is
computed by `CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_Qh`, which is what the
comparison with the derived-pullback pseudofunctor needs. -/
theorem edsDerivedRestrictCompOpen_eq_mapDerivedCategoryCompIso :
    edsDerivedRestrictCompOpen B S hS hsq =
      Functor.mapDerivedCategoryCompIsoOfCompIso (edsFactorIsoOpen B S hS hsq) := by
  rw [← edsDerivedRestrictCompOpen_eq]
  refine Iso.ext ?_
  show (Functor.mapDerivedCategoryComp (edsRestrictOpen B S hS hsq)
      (edsRestrictFst B S hS hsq)).inv ≫ _ = _
  rw [Functor.mapDerivedCategoryComp_eq, Functor.mapDerivedCategoryCompIsoOfCompIso, Iso.trans_hom,
    Iso.symm_hom, Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom]
  rfl

/-- **The comparison Stacks 08HB is stated with, through the étale algebraic space, is the
canonical degreewise descent of the underived comparison of Stacks 03LU.** -/
theorem edsDerivedRestrictCompEtale_eq_mapDerivedCategoryCompIso :
    edsDerivedRestrictCompEtale B S hS hsq =
      Functor.mapDerivedCategoryCompIsoOfCompIso (edsFactorIsoEtale B S hS hsq) := by
  rw [← edsDerivedRestrictCompEtale_eq]
  refine Iso.ext ?_
  show (Functor.mapDerivedCategoryComp (edsRestrictEtale B S hS hsq)
      (edsRestrictSnd B S hS hsq)).inv ≫ _ = _
  rw [Functor.mapDerivedCategoryComp_eq, Functor.mapDerivedCategoryCompIsoOfCompIso, Iso.trans_hom,
    Iso.symm_hom, Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom]
  rfl

end Square

end AlgebraicGeometry.Space

end
