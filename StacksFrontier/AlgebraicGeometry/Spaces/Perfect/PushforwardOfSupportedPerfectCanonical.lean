module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoheratorFlatPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestrictionNoShriekData
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplementCanonical
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness of the derived direct image of a supported perfect object

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, set `T = |X| \ |U|`, and let `E` be a perfect object of `D(𝒪_V)` supported on
`j^{-1}T`.  Then `Rj_*E` is perfect in `D(𝒪_X)`: it is isomorphic to `j_!E`, which restricts to
zero on `U` and to `E` on `V`, and perfectness is local on `X_étale`.

## Main results

* `AlgebraicGeometry.Space.nonempty_edsDerivedRestrictPushEtaleObjIso`: the chosen total right
  derived functor of `j_*((-)|_V)` is the derived direct image of the restriction.
* `AlgebraicGeometry.Space.nonempty_derivedModulePushforwardIsoLowerShriek`: for `E` supported
  on `j^{-1}T` the derived direct image `Rj_*E` is isomorphic to the extension by zero `j_!E`.
* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_of_cohomologySupportedOn`:
  **Stacks 08HK**.

## References

* [Stacks Project, Tag 08HK](https://stacks.math.columbia.edu/tag/08HK)
* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open CategoryTheory.PushforwardMayerVietoris

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat
  hasRightDerivedFunctor_mapHomotopyCategory_modules

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The chosen total right derived functor of `j_{V,*}((-)|_V)` agrees with the derived direct
image of the restriction, `Rj_{V,*}(L|_V)`: both are computed on a K-injective representative
`I` of `L` by `j_*(I|_V)`, the restriction `I|_V` being K-injective again. -/
theorem nonempty_edsDerivedRestrictPushEtaleObjIso
    (L : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    Nonempty ((edsDerivedRestrictPushEtale B S hS hsq).obj L ≅
      (derivedModulePushforward B S hS (edsEtaleHom B S hS hsq)).obj
        ((edsDerivedRestrictEtale B S hS hsq).obj L)) := by
  have hres := exists_quasiIso_isKInjective_modules B S hS W.1 W.2
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_representative_of_universe hres L
  have hI' : CochainComplex.IsKInjective
      (((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    isKInjective_etaleModulePullback_of_isEtale B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq) I hI
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2) :=
    isGrothendieckAbelian_modules B S hS _ _
  have hunit := Stacks.Injectives.KInjectiveResolution.isIso_app_of_isKInjective
    DerivedCategory.Q (derivedModulePushforward B S hS (edsEtaleHom B S hS hsq))
    (derivedModulePushforwardComplexUnit B S hS (edsEtaleHom B S hS hsq))
    (Stacks.Injectives.KInjectiveResolution.invertsQuasiIso_mapHomologicalComplex_comp_Q
      (modulePushforward B S hS (edsEtaleHom B S hS hsq))) _ hI'
  exact ⟨(edsDerivedRestrictPushEtale B S hS hsq).mapIso e.symm ≪≫
    (rightDerivedObjIsoOfKInjective hres (edsRestrictPushEtale B S hS hsq) inferInstance
      (edsDerivedRestrictPushEtale B S hS hsq) (edsTotalRightDerivedUnitEtale B S hS hsq)
      inferInstance I hI).symm ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) ⋙
        modulePushforward B S hS (edsEtaleHom B S hS hsq))) (ComplexShape.up ℤ)).app I).symm ≪≫
    @asIso _ _ _ _ ((derivedModulePushforwardComplexUnit B S hS (edsEtaleHom B S hS hsq)).app _)
      hunit ≪≫
    (derivedModulePushforward B S hS (edsEtaleHom B S hS hsq)).mapIso
      (((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategoryFactors.app I).symm ≪≫
        (edsDerivedRestrictEtale B S hS hsq).mapIso e)⟩

/-- For an elementary distinguished square `(U ⊆ X, j : V ⟶ X)` with `T = |X| \ |U|` and `E` in
`D(𝒪_V)` supported on `j^{-1}T`, the derived direct image `Rj_*E` is isomorphic to `j_!E`: the
latter is supported on `T`, hence is `Rj_{V,*}((j_!E)|_V)`, and `(j_!E)|_V` is `E`. -/
theorem nonempty_derivedModulePushforwardIsoLowerShriek
    (E : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (hE : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) E) :
    Nonempty ((derivedModulePushforward B S hS (edsEtaleHom B S hS hsq)).obj E ≅
      (etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E) := by
  have := isIso_edsEtaleDerivedAdjunction_unit_app_of_cohomologySupportedOn B S hS hsq E hE
  have := isIso_derivedUnit_edsDerivedRestrictPushEtale_of_cohomologySupportedOn B S hS hsq
    ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E)
    (cohomologySupportedOn_etaleModuleLowerShriek_mapDerivedCategory B S hS
      (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
      (edsComplementPoints B S hS Uo) E hE)
  obtain ⟨eo⟩ := nonempty_edsDerivedRestrictPushEtaleObjIso B S hS hsq
    ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E)
  exact ⟨(derivedModulePushforward B S hS (edsEtaleHom B S hS hsq)).mapIso
      (asIso ((edsEtaleDerivedAdjunction B S hS hsq).unit.app E)) ≪≫ eo.symm ≪≫
    (asIso ((derivedUnitOfNatTrans (edsAdjEtale B S hS hsq).unit
      (edsDerivedRestrictPushEtale B S hS hsq)
      (edsTotalRightDerivedUnitEtale B S hS hsq)).app _)).symm⟩

/-- **Stacks 08HK.**  Let `S` be a scheme, let `(U ⊆ X, j : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`, and set `T = |X| \ |U|`.  Let `E` be a
perfect object of `D(𝒪_V)` supported on `j^{-1}T`.  Then `Rj_*E` is a perfect object of
`D(𝒪_X)`.

Perfectness is local on `X_étale` along the two morphisms of the square, and `Rj_*E` is `j_!E`,
whose restriction to `U` vanishes and whose restriction to `V` is the perfect `E`. -/
@[stacks 08HK "Rj_*E is perfect in D(O_X) for an elementary distinguished square and \
E perfect on V supported on j^{-1}T"]
theorem isPerfect_derivedModulePushforward_of_cohomologySupportedOn
    (E : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (hperf : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2).IsPerfect E)
    (hE : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) E) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect
      ((derivedModulePushforward B S hS (edsEtaleHom B S hS hsq)).obj E) := by
  have := isIso_edsEtaleDerivedAdjunction_unit_app_of_cohomologySupportedOn B S hS hsq E hE
  obtain ⟨eR⟩ := nonempty_derivedModulePushforwardIsoLowerShriek B S hS hsq E hE
  refine isPerfect_of_isPerfect_edsDerivedRestrict B S hS hsq _ ?_ ?_
  · have h0 : IsZero ((edsDerivedRestrictOpen B S hS hsq).obj
        ((derivedModulePushforward B S hS (edsEtaleHom B S hS hsq)).obj E)) :=
      (isZero_edsDerivedRestrictOpen_shriek_of_cohomologySupportedOn B S hS hsq E hE).of_iso
        ((edsDerivedRestrictOpen B S hS hsq).mapIso eR)
    exact RingedSite.isPerfect_of_isZero
      (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2) h0
  · have eV : E ≅ (edsDerivedRestrictEtale B S hS hsq).obj
        ((derivedModulePushforward B S hS (edsEtaleHom B S hS hsq)).obj E) :=
      asIso ((edsEtaleDerivedAdjunction B S hS hsq).unit.app E) ≪≫
        (edsDerivedRestrictEtale B S hS hsq).mapIso eR.symm
    exact RingedSite.IsPerfect.of_iso
      (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2) hperf eV

end Square

end AlgebraicGeometry.Space

end
