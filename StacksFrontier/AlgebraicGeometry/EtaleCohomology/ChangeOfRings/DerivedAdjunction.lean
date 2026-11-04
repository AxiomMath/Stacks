module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ChangeOfRings.RingedSiteHom
public import StacksFrontier.CategoryTheory.Localization.AbsoluteLeftDerivedAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CoefficientChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# Derived change of coefficient rings on `D(X_étale, Λ)`

Let `φ : Λ₁ ⟶ Λ₂` be a homomorphism of commutative rings and let `X` be a scheme. Restriction of
scalars is exact, so it induces the functor

`res : D(X_étale, Λ₂) ⥤ D(X_étale, Λ₁)`

degreewise. It has a left adjoint `- ⊗^L_{Λ₁} Λ₂ : D(X_étale, Λ₁) ⥤ D(X_étale, Λ₂)`,

`Hom_{Λ₂}(K ⊗^L_{Λ₁} Λ₂, M) = Hom_{Λ₁}(K, res M)`,

which is the special case of [Stacks, Tag 07A6] that [Stacks, Tag 0GLF] quotes: the derived
adjunction for the morphism of ringed topoi `(X_étale, Λ̲₂) ⟶ (X_étale, Λ̲₁)` over the identity of
the site.

## Main definitions

All in the namespace `Stacks.EtaleCohomology.ChangeOfRings`.

* `derivedRestrictScalars φ X`: `res : D(X_étale, Λ₂) ⥤ D(X_étale, Λ₁)`.
* `derivedExtendScalars φ X`: `- ⊗^L_{Λ₁} Λ₂ : D(X_étale, Λ₁) ⥤ D(X_étale, Λ₂)`.
* `derivedExtendRestrictScalarsAdj φ X`: the adjunction between them.

## Implementation notes

The derived extension of scalars is the derived pullback of Stacks 06YY along
`Stacks.EtaleCohomology.ChangeOfRings.coefficientChangeHom`, on the derived categories of sheaves
of modules over the constant ringed site `Stacks.EtaleCohomology.etaleRingedSite`; it is read on
`D(X_étale, Λᵢ)` through `Stacks.EtaleCohomology.etaleDerivedEquivalence`. On that side the
adjunction is `CategoryTheory.Adjunction.derivedMapDerivedCategoryOfResolutions` for the
K-flat complexes with flat terms, whose resolving property is Stacks 06YS and on whose
quasi-isomorphisms degreewise extension of scalars is invertible by Stacks 06YY; the identity
functor of the site is a morphism of sites, so nothing is assumed. Its right adjoint is the functor
induced by restriction of scalars of sheaves of `Λ̲ᵢ`-modules, which
`Stacks.EtaleCohomology.ChangeOfRings.pushforwardIso` identifies with `res`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

universe u r

namespace Stacks.EtaleCohomology.ChangeOfRings

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂) (X : Scheme.{u})

/-- Restriction of scalars is a right adjoint, of extension of scalars. -/
instance : (restrictScalars φ X).IsRightAdjoint := (extendRestrictScalarsAdj φ X).isRightAdjoint

/-- Restriction of scalars is a left adjoint, of coextension of scalars. -/
instance : (restrictScalars φ X).IsLeftAdjoint := (restrictCoextendScalarsAdj φ X).isLeftAdjoint

/-- Restriction of scalars of sheaves of `Λ̲₂`-modules, written through the identifications with
sheaves of `Λᵢ`-modules. -/
def pushforwardIsoConj :
    (etaleModulesEquivalence.{u, r} Λ₂ X).inverse ⋙ restrictScalars φ X ⋙
        (etaleModulesEquivalence.{u, r} Λ₁ X).functor ≅
      (coefficientChangeHom.{u, r} φ X).pushforwardTopos :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pushforwardIso.{u, r} φ X).symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleModulesEquivalence.{u, r} Λ₁ X).counitIso ≪≫
    Functor.rightUnitor _

/-- Restriction of scalars of sheaves of `Λ̲₂`-modules is left exact. -/
instance : PreservesFiniteLimits (coefficientChangeHom.{u, r} φ X).pushforwardTopos :=
  preservesFiniteLimits_of_natIso (pushforwardIsoConj.{u, r} φ X)

/-- Restriction of scalars of sheaves of `Λ̲₂`-modules is right exact. -/
instance : PreservesFiniteColimits (coefficientChangeHom.{u, r} φ X).pushforwardTopos :=
  preservesFiniteColimits_of_natIso (pushforwardIsoConj.{u, r} φ X)

/-- Restriction of scalars of sheaves of `Λ̲₂`-modules is additive. -/
instance : (coefficientChangeHom.{u, r} φ X).pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive _

/-- Extension of scalars of sheaves of `Λ̲₁`-modules is additive, being a left adjoint. -/
instance : (coefficientChangeHom.{u, r} φ X).pullbackTopos.Additive :=
  (coefficientChangeHom.{u, r} φ X).pullbackPushforwardAdjunctionTopos.left_adjoint_additive

/-- The derived change of coefficient rings `- ⊗^L_{Λ̲₁} Λ̲₂` on the constant ringed site. -/
abbrev ringedDerivedExtendScalars :
    DerivedCategory (EtaleRingedModules.{u, r} Λ₁ X) ⥤
      DerivedCategory (EtaleRingedModules.{u, r} Λ₂ X) :=
  Stacks.Cohomology.derivedCoefficientChange.{max (u + 1) r} (ringMap.{u, r} φ X)

/-- `- ⊗^L_{Λ̲₁} Λ̲₂` is left adjoint to restriction of scalars on the constant ringed site. -/
def ringedDerivedExtendScalarsAdj :
    ringedDerivedExtendScalars.{u, r} φ X ⊣
      (coefficientChangeHom.{u, r} φ X).pushforwardTopos.mapDerivedCategory :=
  (coefficientChangeHom.{u, r} φ X).pullbackPushforwardAdjunctionTopos
    |>.derivedMapDerivedCategoryOfResolutions
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := (etaleRingedSite.{u, r} Λ₁ X).ringedTopos))
    (fun K => Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
      (Y := (etaleRingedSite.{u, r} Λ₁ X).ringedTopos) K)
    (fun s hs hK hM =>
      Stacks.Cohomology.DerivedPullbackOnRingedTopoi.pullbackInvertsQuasiIso_isKFlat
        (coefficientChangeHom.{u, r} φ X) (Functor.isMorphismOfSites_id _) s hs hK hM)


/-- **Restriction of scalars `res : D(X_étale, Λ₂) ⥤ D(X_étale, Λ₁)`** along `φ : Λ₁ ⟶ Λ₂`,
induced degreewise by the exact restriction of scalars of sheaves of modules. -/
abbrev derivedRestrictScalars :
    DerivedCategory (EtaleModules.{u, r} Λ₂ X) ⥤ DerivedCategory (EtaleModules.{u, r} Λ₁ X) :=
  (restrictScalars φ X).mapDerivedCategory

/-- **The derived extension of scalars `- ⊗^L_{Λ₁} Λ₂ : D(X_étale, Λ₁) ⥤ D(X_étale, Λ₂)`**: the
derived pullback along the change of coefficient rings of the constant ringed site, read on
sheaves of `Λᵢ`-modules. -/
abbrev derivedExtendScalars :
    DerivedCategory (EtaleModules.{u, r} Λ₁ X) ⥤ DerivedCategory (EtaleModules.{u, r} Λ₂ X) :=
  (etaleDerivedEquivalence.{u, r} Λ₁ X).functor ⋙ ringedDerivedExtendScalars.{u, r} φ X ⋙
    (etaleDerivedEquivalence.{u, r} Λ₂ X).inverse

/-- Restriction of scalars on the constant ringed site, read on sheaves of `Λᵢ`-modules, is
`res`. -/
def derivedRestrictScalarsIso :
    (etaleDerivedEquivalence.{u, r} Λ₂ X).functor ⋙
        (coefficientChangeHom.{u, r} φ X).pushforwardTopos.mapDerivedCategory ⋙
          (etaleDerivedEquivalence.{u, r} Λ₁ X).inverse ≅
      derivedRestrictScalars.{u, r} φ X :=
  Functor.isoWhiskerLeft _
      (Dualizing.mapDerivedCategoryCompNatIso _ _ _ (pushforwardIso.{u, r} φ X) ≪≫
        (Dualizing.mapDerivedCategoryCompNatIso _ _ _ (Iso.refl _)).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etaleDerivedEquivalence.{u, r} Λ₂ X).unitIso.symm _ ≪≫
    Functor.leftUnitor _

/-- **[Stacks, Tag 07A6] for the change of coefficient rings on the small étale site**:
`Hom_{Λ₂}(K ⊗^L_{Λ₁} Λ₂, M) = Hom_{Λ₁}(K, res M)`. -/
def derivedExtendRestrictScalarsAdj :
    derivedExtendScalars.{u, r} φ X ⊣ derivedRestrictScalars.{u, r} φ X :=
  ((etaleDerivedEquivalence.{u, r} Λ₁ X).toAdjunction.comp
    ((ringedDerivedExtendScalarsAdj.{u, r} φ X).comp
      (etaleDerivedEquivalence.{u, r} Λ₂ X).symm.toAdjunction)).ofNatIsoRight
    (derivedRestrictScalarsIso.{u, r} φ X)

end Stacks.EtaleCohomology.ChangeOfRings

end
