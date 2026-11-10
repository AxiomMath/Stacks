module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ChangeOfRings.DerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOnRingedTopoiUnconditional
public import StacksFrontier.Homology.Injectives.KInjective.RightAdjointOfExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.ProjectionFormula

/-!
# Restriction of scalars commutes with the derived lower shriek

Let `φ : Λ₁ ⟶ Λ₂` be a homomorphism of commutative rings and let `f : X ⟶ Y` be a morphism of
schemes with a compactification `f = fbar ∘ j`. This file proves that the restriction functor
`res` of `Stacks.EtaleCohomology.ChangeOfRings.derivedRestrictScalars` commutes with
`Rf_! = R(fbar)_* ∘ j_!`, the first commutative square of [Stacks, Tag 0GL6]:

`res ∘ Rf_! = Rf_! ∘ res : D(X_étale, Λ₂) ⥤ D(Y_étale, Λ₁)`.

The source's proof is followed: it holds for `j_!` by inspection and for `R(fbar)_*` by the
change-of-rings case of Cohomology on Sites, Lemma 0D6J. It also proves that the derived
extension by zero along an open immersion commutes with `- ⊗^L_{Λ₁} Λ₂`, the open-immersion half
of the second square of [Stacks, Tag 0GL6].

## Main results

All in the namespace `Stacks.EtaleCohomology.ChangeOfRings`.

* `extensionByZeroRestrictScalarsIso`: `res ∘ j_! = j_! ∘ res` on sheaves, for `j` étale, by
  uniqueness of left adjoints.
* `derivedExtensionByZeroRestrictScalarsIso`: the same on unbounded derived categories.
* `quasiIso_directImage_map_of_isKInjective`: `f_*` carries a K-injective resolution of the
  restriction of scalars of a K-injective complex to a quasi-isomorphism.
* `derivedDirectImageRestrictScalarsIso`: `res ∘ Rf_* = Rf_* ∘ res`, for every morphism of
  schemes `f`.
* `derivedLowerShriekRestrictScalarsIso`: `res ∘ Rf_! = Rf_! ∘ res`, the first square of
  [Stacks, Tag 0GL6].
* `derivedExtensionByZeroExtendScalarsIso`: `j_!(K ⊗^L_{Λ₁} Λ₂) = j_!K ⊗^L_{Λ₁} Λ₂` for an open
  immersion `j`.

## Implementation notes

`res` is exact but does not preserve K-injective complexes, its left adjoint `- ⊗_{Λ₁} Λ₂` not
being exact. That `res ∘ Rf_*` and `Rf_* ∘ res` are both right derived functors of
`res ∘ f_* = f_* ∘ res` rests instead on `quasiIso_directImage_map_of_isKInjective`, which is the
change of coefficient rings, followed by `f`, of the composition formula of Stacks 0D6E on ringed
topoi (`quasiIso_mapHomotopyCategory_pushforward_of_isKInjective` in
`Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi`), read on sheaves of `Λᵢ`-modules through
`Stacks.EtaleCohomology.etaleModulesEquivalence`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology.ChangeOfRings

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)

/-- Coextension of scalars commutes with restriction to an étale `U`, on the nose. -/
def coextendScalarsRestrictionIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    coextendScalars φ X ⋙ etaleModuleRestriction.{u, r} Λ₂ j ≅
      etaleModuleRestriction.{u, r} Λ₁ j ⋙ coextendScalars φ U :=
  Iso.refl _

/-- **Extension by zero commutes with restriction of scalars**, `res ∘ j_! = j_! ∘ res`, for an
étale morphism `j`: the right adjoints `Hom_{Λ₁}(Λ₂, -) ∘ j^{-1}` and `j^{-1} ∘ Hom_{Λ₁}(Λ₂, -)`
agree. -/
def extensionByZeroRestrictScalarsIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    etaleModuleExtensionByZero.{u, r} Λ₂ j ⋙ restrictScalars φ X ≅
      restrictScalars φ U ⋙ etaleModuleExtensionByZero.{u, r} Λ₁ j :=
  ((conjugateIsoEquiv ((restrictCoextendScalarsAdj φ U).comp (etaleModuleExtensionByZeroAdj Λ₁ j))
    ((etaleModuleExtensionByZeroAdj Λ₂ j).comp (restrictCoextendScalarsAdj φ X))).symm
    (coextendScalarsRestrictionIso φ j).symm)

/-- **The derived extension by zero commutes with restriction of scalars**, on unbounded derived
categories: both are computed degreewise. -/
def derivedExtensionByZeroRestrictScalarsIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₂ j ⋙ derivedRestrictScalars φ X ≅
      derivedRestrictScalars φ U ⋙ etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₁ j :=
  Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ₂ j) _ ≪≫
    Dualizing.mapDerivedCategoryCompNatIso _ _ _ (extensionByZeroRestrictScalarsIso φ j) ≪≫
    (Dualizing.mapDerivedCategoryCompNatIso _ _ _ (Iso.refl _)).symm ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ₁ j).symm

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

/-- The direct image of sheaves of `Λ̲`-modules along the morphism of constant ringed topoi is
additive. -/
instance {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type r) [CommRing Λ] :
    (etaleRingedSiteHom.{u, r} Λ f).toRingedToposSiteHom.pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive _

/-- Restriction of scalars along the change of coefficient rings, after the identification of
sheaves of `Λ₂`-modules with sheaves of `Λ̲₂`-modules, is restriction of scalars followed by the
identification for `Λ₁`. -/
def equivalenceRestrictScalarsIso (X : Scheme.{u}) :
    (etaleModulesEquivalence.{u, r} Λ₂ X).functor ⋙
        (coefficientChangeHom.{u, r} φ X).pushforwardTopos ≅
      restrictScalars φ X ⋙ (etaleModulesEquivalence.{u, r} Λ₁ X).functor :=
  Functor.isoWhiskerLeft _ (pushforwardIsoConj.{u, r} φ X).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etaleModulesEquivalence.{u, r} Λ₂ X).unitIso.symm _ ≪≫
    Functor.leftUnitor _

/-- The direct image along the morphism of constant ringed topoi, after the identification of
sheaves of `Λ`-modules with sheaves of `Λ̲`-modules, is the étale direct image followed by the
identification. -/
def equivalenceDirectImageIso (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleModulesEquivalence.{u, r} Λ X).functor ⋙
        (etaleRingedSiteHom.{u, r} Λ f).toRingedToposSiteHom.pushforwardTopos ≅
      etaleModuleDirectImage.{u, r} Λ f ⋙ (etaleModulesEquivalence.{u, r} Λ Y).functor :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (etaleModulesEquivalence.{u, r} Λ Y).counitIso.symm ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (etaleModulesEquivalence.{u, r} Λ X).functor
      (etaleRingedPushforwardIso.{u, r} Λ f)) (etaleModulesEquivalence.{u, r} Λ Y).functor ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (etaleModulesEquivalence.{u, r} Λ X).unitIso.symm
        (etaleModuleDirectImage.{u, r} Λ f)) (etaleModulesEquivalence.{u, r} Λ Y).functor

/-- **The restriction of scalars of a K-injective complex computes the derived direct image.** Let
`I` be a K-injective complex of sheaves of `Λ₂`-modules on `X_étale` and let `s : res I ⟶ J` be a
quasi-isomorphism to a K-injective complex of sheaves of `Λ₁`-modules. Then `f_* s` is a
quasi-isomorphism.

This is the case of the change of coefficient rings, followed by `f`, of
`quasiIso_mapHomotopyCategory_pushforward_of_isKInjective` in
`Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi`, read on sheaves of `Λᵢ`-modules. -/
theorem quasiIso_directImage_map_of_isKInjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ) [I.IsKInjective]
    (J : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ) [J.IsKInjective]
    (s : ((restrictScalars φ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    [QuasiIso s] :
    QuasiIso (((etaleModuleDirectImage.{u, r} Λ₁ f).mapHomologicalComplex
      (ComplexShape.up ℤ)).map s) := by
  let e₂ := etaleModulesEquivalence.{u, r} Λ₂ X
  let e₁ := etaleModulesEquivalence.{u, r} Λ₁ X
  let eY := etaleModulesEquivalence.{u, r} Λ₁ Y
  have hI : CochainComplex.IsKInjective
      ((e₂.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    Stacks.Injectives.isKInjective_mapHomologicalComplex_of_isEquivalence _ I
  have hJ : CochainComplex.IsKInjective
      ((e₁.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    Stacks.Injectives.isKInjective_mapHomologicalComplex_of_isEquivalence _ J
  let b := (NatIso.mapHomologicalComplex (equivalenceRestrictScalarsIso.{u, r} φ X)
    (ComplexShape.up ℤ)).app I
  let a := (e₁.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map s
  have ha : QuasiIso a := inferInstance
  open Stacks.Cohomology.DerivedPushforwardCompositionOnTopoi in
  have hs := quasiIso_mapHomotopyCategory_pushforward_of_isKInjective
    (coefficientChangeHom.{u, r} φ X) (etaleRingedSiteHom.{u, r} Λ₁ f).toRingedToposSiteHom
    (Functor.isMorphismOfSites_id _) (etaleRingedSiteHom.{u, r} Λ₁ f).isMorphismOfSites _ hI _ hJ
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (b.hom ≫ a))
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (by
      change QuasiIso (b.hom ≫ a); infer_instance))
  replace hs : HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplex
          (etaleRingedSiteHom.{u, r} Λ₁ f).toRingedToposSiteHom.pushforwardTopos
          (ComplexShape.up ℤ)).map (b.hom ≫ a))) := hs
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hs
  change QuasiIso ((Functor.mapHomologicalComplex
      (etaleRingedSiteHom.{u, r} Λ₁ f).toRingedToposSiteHom.pushforwardTopos
      (ComplexShape.up ℤ)).map (b.hom ≫ a)) at hs
  rw [Functor.map_comp, quasiIso_iff_comp_left] at hs
  have e := Arrow.isoOfNatIso (NatIso.mapHomologicalComplex (equivalenceDirectImageIso.{u, r} Λ₁ f)
    (ComplexShape.up ℤ)) (Arrow.mk s)
  have h' : QuasiIso ((eY.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((etaleModuleDirectImage.{u, r} Λ₁ f).mapHomologicalComplex (ComplexShape.up ℤ)).map s)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _ e).1 hs
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ eY.functor).1 h'

/-- At the restriction of scalars of a K-injective complex, the unit of the derived direct image
`Rf_*` for `Λ₁` is invertible. -/
theorem isIso_directImageUnit_app_restrictScalars {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ) [I.IsKInjective] :
    IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₁ f).app
      (((restrictScalars φ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
  obtain ⟨J, s, hJ, hs⟩ := Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _
    (((restrictScalars φ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  have h₁ : IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₁ f).app J) :=
    isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ₁ f J hJ
  have h₂ : IsIso (DerivedCategory.Q.map
      (((etaleModuleDirectImage.{u, r} Λ₁ f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map s)) := by
    have := quasiIso_directImage_map_of_isKInjective.{u, r} φ f I J s
    infer_instance
  have h₃ : IsIso ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ f).map
      (DerivedCategory.Q.map s)) :=
    inferInstance
  have hnat := (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₁ f).naturality s
  have : IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₁ f).app
      (((restrictScalars φ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        (DerivedCategory.Q ⋙ etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ f).map s) := by
    rw [← hnat]
    exact IsIso.comp_isIso' h₂ h₁
  have h₄ : IsIso ((DerivedCategory.Q ⋙
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ f).map s) := h₃
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.Q ⋙ etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ f).map s)

/-- The unit exhibiting `Rf_* ⋙ res` as a right derived functor of `res ⋙ f_*`. -/
def directImageRestrictScalarsUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (restrictScalars φ X ⋙ etaleModuleDirectImage.{u, r} Λ₁ f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ f ⋙
        derivedRestrictScalars φ Y :=
  Functor.whiskerLeft
      ((etaleModuleDirectImage.{u, r} Λ₂ f).mapHomologicalComplex (ComplexShape.up ℤ))
      (restrictScalars φ Y).mapDerivedCategoryFactors.inv ≫
    Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₂ f)
      (derivedRestrictScalars φ Y)

/-- The unit exhibiting `res ⋙ Rf_*` as a right derived functor of `res ⋙ f_*`. -/
def restrictScalarsDirectImageUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (restrictScalars φ X ⋙ etaleModuleDirectImage.{u, r} Λ₁ f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedRestrictScalars φ X ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ f :=
  Functor.whiskerLeft ((restrictScalars φ X).mapHomologicalComplex (ComplexShape.up ℤ))
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₁ f) ≫
    Functor.whiskerRight (restrictScalars φ X).mapDerivedCategoryFactors.inv
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ f)

/-- `Rf_* ⋙ res` is a right derived functor of `res ⋙ f_*`, by absoluteness of right derived
functors. -/
instance directImageRestrictScalars_isRightDerivedFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ f ⋙
        derivedRestrictScalars φ Y).IsRightDerivedFunctor
      (directImageRestrictScalarsUnit.{u, r} φ f)
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ₂ X) (ComplexShape.up ℤ)) :=
  (Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective
    DerivedCategory.Q _ _
    (Stacks.Injectives.KInjectiveResolution.invertsQuasiIso_mapHomologicalComplex_comp_Q
      (restrictScalars φ X ⋙
      etaleModuleDirectImage.{u, r} Λ₁ f))).2 fun I hI => by
    have := isIso_etaleModuleDerivedDirectImageUnboundedUnit_app.{u, r} Λ₂ f I hI
    change IsIso ((restrictScalars φ Y).mapDerivedCategoryFactors.inv.app _ ≫
      (derivedRestrictScalars φ Y).map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₂ f).app I))
    infer_instance

/-- `res ⋙ Rf_*` is a right derived functor of `res ⋙ f_*`: the restriction of scalars of a
K-injective complex computes `Rf_*` (`isIso_directImageUnit_app_restrictScalars`). -/
instance restrictScalarsDirectImage_isRightDerivedFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedRestrictScalars φ X ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ f).IsRightDerivedFunctor
      (restrictScalarsDirectImageUnit.{u, r} φ f)
      (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ₂ X) (ComplexShape.up ℤ)) :=
  (Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective
    DerivedCategory.Q _ _
    (Stacks.Injectives.KInjectiveResolution.invertsQuasiIso_mapHomologicalComplex_comp_Q
      (restrictScalars φ X ⋙
      etaleModuleDirectImage.{u, r} Λ₁ f))).2 fun I hI => by
    have := isIso_directImageUnit_app_restrictScalars.{u, r} φ f I
    change IsIso ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ₁ f).app _ ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ f).map
        ((restrictScalars φ X).mapDerivedCategoryFactors.inv.app I))
    infer_instance

/-- **The derived direct image commutes with restriction of scalars**:
`res ∘ Rf_* = Rf_* ∘ res` as functors `D(X_étale, Λ₂) ⥤ D(Y_étale, Λ₁)`, for any morphism of
schemes `f` — the input of [Stacks, Tag 0GL6] which the source cites as Cohomology on Sites,
Lemma 0D6J. Both composites are right derived functors of `res ∘ f_* = f_* ∘ res`. -/
def derivedDirectImageRestrictScalarsIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ f ⋙ derivedRestrictScalars φ Y ≅
      derivedRestrictScalars φ X ⋙ etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ f :=
  Functor.rightDerivedUnique _ _ (directImageRestrictScalarsUnit.{u, r} φ f)
    (restrictScalarsDirectImageUnit.{u, r} φ f)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ₂ X) (ComplexShape.up ℤ))

/-- **The derived lower shriek commutes with restriction of scalars**, the first square of
[Stacks, Tag 0GL6]: for a compactification `f = fbar ∘ j` of `f : X ⟶ Y`,
`res ∘ Rf_! = Rf_! ∘ res` as functors `D(X_étale, Λ₂) ⥤ D(Y_étale, Λ₁)`. It holds for `j_!`
by inspection (`derivedExtensionByZeroRestrictScalarsIso`) and for `R(fbar)_*` by
`derivedDirectImageRestrictScalarsIso`; no hypothesis on `f`, `j` or the rings is used. -/
def derivedLowerShriekRestrictScalarsIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) :
    derivedLowerShriekUnbounded.{u, r} f j Λ₂ ⋙ derivedRestrictScalars φ Y ≅
      derivedRestrictScalars φ X ⋙ derivedLowerShriekUnbounded.{u, r} f j Λ₁ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedDirectImageRestrictScalarsIso.{u, r} φ j.toBase) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedExtensionByZeroRestrictScalarsIso.{u, r} φ j.immersion) _ ≪≫
    Functor.associator _ _ _

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- The étale derived inverse image along `j` commutes with restriction of scalars. -/
def derivedInverseImageRestrictScalarsIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    etaleModuleDerivedInverseImage.{u, r} Λ₂ j ⋙ derivedRestrictScalars φ U ≅
      derivedRestrictScalars φ X ⋙ etaleModuleDerivedInverseImage.{u, r} Λ₁ j :=
  Dualizing.mapDerivedCategoryCompNatIso _ _ _ (Iso.refl _) ≪≫
    Dualizing.mapDerivedCategoryNatIso _ _
      (Functor.isoWhiskerRight (etaleModuleInverseImageRestrictionIso.{u, r} Λ₂ j)
          (restrictScalars φ U) ≪≫
        (Iso.refl _ : etaleModuleRestriction.{u, r} Λ₂ j ⋙ restrictScalars φ U ≅
          restrictScalars φ X ⋙ etaleModuleRestriction.{u, r} Λ₁ j) ≪≫
        Functor.isoWhiskerLeft (restrictScalars φ X)
          (etaleModuleInverseImageRestrictionIso.{u, r} Λ₁ j).symm) ≪≫
    (Dualizing.mapDerivedCategoryCompNatIso _ _ _ (Iso.refl _)).symm

/-- **The derived extension by zero along an open immersion commutes with `- ⊗^L_{Λ₁} Λ₂`**:
`j_!(K ⊗^L_{Λ₁} Λ₂) = j_!K ⊗^L_{Λ₁} Λ₂`, by uniqueness of left adjoints, the right adjoints
`res ∘ j^{-1}` and `j^{-1} ∘ res` agreeing. -/
def derivedExtensionByZeroExtendScalarsIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₁ j ⋙ derivedExtendScalars φ X ≅
      derivedExtendScalars φ U ⋙ etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₂ j :=
  (conjugateIsoEquiv
    ((derivedExtendRestrictScalarsAdj.{u, r} φ U).comp (etaleDerivedExtensionByZeroAdj.{u, r} Λ₂ j))
    ((etaleDerivedExtensionByZeroAdj.{u, r} Λ₁ j).comp
      (derivedExtendRestrictScalarsAdj.{u, r} φ X))).symm
    (derivedInverseImageRestrictScalarsIso.{u, r} φ j)

end Stacks.EtaleCohomology.ChangeOfRings

end
