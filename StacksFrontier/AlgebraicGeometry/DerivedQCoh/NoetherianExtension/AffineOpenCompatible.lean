module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpenPushforward
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.CoheratorEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.NoetherianExtension.Basic
public import StacksFrontier.Homology.DerivedCategory.ModelComparison

/-!
# The affine-open hypothesis of Stacks 09T6 on a Noetherian scheme

[Stacks, Tag 09T6] is a criterion for the comparison functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)`
of [Stacks, Tag 06VT] to be an equivalence. Its hypothesis asks that for every affine open
`U ⊆ X`, writing `j : U ⟶ X` for the inclusion, the right derived functor
`Φ : D(QCoh(𝒪_U)) ⥤ D(QCoh(𝒪_X))` of `j_* : QCoh(𝒪_U) ⥤ QCoh(𝒪_X)` fits into a commutative square
`i_X ∘ Φ ≅ Rj_* ∘ i_U` with a total right derived functor `Rj_*` of direct image of all modules.

**This file verifies that hypothesis on every Noetherian scheme.** An affine open of a Noetherian
scheme is again Noetherian, so the square is the one supplied by [Stacks, Tag 09T3]: for a
morphism of Noetherian schemes, direct image on quasi-coherent modules has a right derived
extension compatible with derived direct image of all modules. Unlike the verification for a
scheme with affine diagonal in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpenPushforward.lean`, the inclusion `j` is not
assumed to be an affine morphism and `j_*` is not exact on quasi-coherent modules; what replaces
its exactness is the flasqueness of an injective quasi-coherent module on a Noetherian scheme,
which is what [Stacks, Tag 09T3] rests on.

## Main results

* `Stacks.DerivedQCoh.noetherianAffineOpenPushforwardCompatible` — the hypothesis
  `Stacks.DerivedQCoh.AffineOpenPushforwardCompatible` of [Stacks, Tag 09T6] holds for every
  Noetherian scheme.

## Implementation notes

**The standard model, and why it needs a raised priority.**
`CategoryTheory.HasDerivedCategory.standard` is installed as a local instance of priority `10000`
for the reason recorded at
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/NoetherianExtension/Basic.lean`: the import closure
carries locally small models of the derived categories of modules at universe `u` as global
instances, and with two models in play at equal priority instance search no longer resolves
`CategoryTheory.HasDerivedCategory.{u + 1}`. [Stacks, Tag 09T3] is stated at the standard model,
so that is the model in which the input to the proof lives.

**The quantified models of the two derived categories of `U`, and how they are reduced.**
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible` quantifies over the model of `D(𝒪_U)` and of
`D(QCoh(𝒪_U))` — it must, since the two derived categories of `X` are binders of the statement
while those of `U` occur only inside it — whereas [Stacks, Tag 09T3] is available only at the
standard model. The reduction is `StacksDraft.DerivedModel.modelEquiv`, the comparison equivalence
of two chosen models: both derived functors are produced as that comparison followed by the
functor at the standard model, and both derivation units as the unit at the standard model
rewritten along `StacksDraft.DerivedModel.modelCompQIso`, which identifies the two localizations
of the cochain complexes. That the result is again a total right derived functor is Spaltenstein's
criterion
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective`: it
tests the derivation unit only at the K-injective complexes, where the transported unit is the
original one composed with isomorphisms. The commuting square is transported in the same way, the
one piece of genuine work being the compatibility of the derived functor of the exact inclusion
`QCoh(𝒪_U) ⥤ Mod(𝒪_U)` with a change of model; both sides of that compatibility lift one functor
along the localization of the cochain complexes of quasi-coherent modules, so
`CategoryTheory.Localization.liftNatIso` identifies them.

**The two spellings of the module category.** `AlgebraicGeometry.Scheme.Modules X` and
`SheafOfModules X.ringCatSheaf` are definitionally equal but carry separately declared `Category`,
`Preadditive` and `Abelian` instances, so instance search does not cross them. The hypothesis of
[Stacks, Tag 09T6] and the derived direct image at an arbitrary model are stated in the second
spelling, while the commuting square of [Stacks, Tag 09T3] is stated in the first; the derived
direct image and its unit are therefore named a second time at the first spelling, and the one
instance that instance search cannot carry across — that the derived direct image is a right
derived functor for the quasi-isomorphisms of `K(Mod(𝒪_U))` — is transported by hand.

## References

* [Stacks Project, Tag 09T6](https://stacks.math.columbia.edu/tag/09T6)
* [Stacks Project, Tag 09T3](https://stacks.math.columbia.edu/tag/09T3)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 08D8](https://stacks.math.columbia.edu/tag/08D8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentDerived (derivedQuasicoherentComparison
  derivedQuasicoherentComparisonCompι)
open AlgebraicGeometry.AnyModel (derivedPushforward derivedPushforwardUnit)
open StacksDraft.DerivedModel (modelEquiv modelCompQIso)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DerivedQCoh

/-! ### The standard model -/

section Standard

variable (Y : Scheme.{u})

/-- The standard model of the derived category of the `𝒪_Y`-modules, named so that it remains
available in a context carrying a second, arbitrary model of the same derived category. -/
private abbrev standardModulesModel :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u} Y.ringCatSheaf) :=
  HasDerivedCategory.standard _

/-- The standard model of the derived category of the quasi-coherent `𝒪_Y`-modules, named so that
it remains available in a context carrying a second, arbitrary model of it. -/
private abbrev standardQuasicoherentModel :
    HasDerivedCategory.{u + 1} (Scheme.QuasicoherentModules Y) :=
  HasDerivedCategory.standard _

/-- The derived functor of the exact inclusion `QCoh(𝒪_Y) ⥤ Mod(𝒪_Y)`, at the standard model of
both derived categories. -/
private abbrev standardInclusionDerived :
    DerivedCategory (Scheme.QuasicoherentModules Y) ⥤
      DerivedCategory (SheafOfModules.{u} Y.ringCatSheaf) :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory

/-- The derived inclusion of the quasi-coherent modules is induced by degreewise inclusion:
composing it with the localization of the cochain complexes of quasi-coherent modules gives back
degreewise inclusion followed by the localization of the cochain complexes of all modules. -/
private abbrev standardInclusionFactors :
    DerivedCategory.Q (C := Scheme.QuasicoherentModules Y) ⋙ standardInclusionDerived Y ≅
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := SheafOfModules.{u} Y.ringCatSheaf) :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategoryFactors

variable {Y}
variable {Z : Scheme.{u}} (f : Y ⟶ Z)

/-- The derived direct image `Rf_* : D(𝒪_Y) ⥤ D(𝒪_Z)` at the standard model of both derived
categories. -/
private abbrev standardDerivedPushforward :
    DerivedCategory (SheafOfModules.{u} Y.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} Z.ringCatSheaf) :=
  derivedPushforward.{u + 1} f

/-- The derivation unit of `Stacks.DerivedQCoh.standardDerivedPushforward`, as a natural
transformation out of the cochain complexes of `𝒪_Y`-modules. -/
private abbrev standardDerivedPushforwardUnit :
    (modulesPushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := SheafOfModules.{u} Z.ringCatSheaf) ⟶
      DerivedCategory.Q (C := SheafOfModules.{u} Y.ringCatSheaf) ⋙
        standardDerivedPushforward f :=
  derivedPushforwardCochainUnit.{u + 1} f

/-- The derived direct image at the standard model, with source and target spelled
`AlgebraicGeometry.Scheme.Modules`: this is the spelling in which the commuting square of
[Stacks, Tag 09T3] is stated. -/
private abbrev standardModulesDerivedPushforward :
    DerivedCategory Y.Modules ⥤ DerivedCategory Z.Modules :=
  derivedPushforward.{u + 1} f

/-- The derivation unit of the derived direct image, in the `AlgebraicGeometry.Scheme.Modules`
spelling of the two categories of modules. -/
private abbrev standardModulesDerivedPushforwardUnit :
    (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ standardModulesDerivedPushforward f :=
  derivedPushforwardUnit.{u + 1} f

/-- Rewriting a derivation unit along an isomorphism of two localizations of the cochain complexes
gives a right derived functor, provided the unit is invertible at the K-injective complexes. -/
private theorem isRightDerivedFunctor_comp_whiskerRight_inv_of_isIso_app.{w}
    {C : Type*} [Category C] [Abelian C] [IsGrothendieckAbelian.{w} C] {H D D' : Type*}
    [Category H] [Category D] [Category D'] {F : CochainComplex C ℤ ⥤ H}
    (hF : Stacks.Injectives.KInjectiveResolution.InvertsQuasiIsoOfIsKInjective F)
    (Q : CochainComplex C ℤ ⥤ D)
    [Q.IsLocalization (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))]
    (G : D ⥤ D') {Q' : CochainComplex C ℤ ⥤ D'} (e : Q ⋙ G ≅ Q') (Φ : D' ⥤ H)
    (α : F ⟶ Q' ⋙ Φ) (hα : ∀ K : CochainComplex C ℤ, K.IsKInjective → IsIso (α.app K)) :
    (G ⋙ Φ).IsRightDerivedFunctor (α ≫ Functor.whiskerRight e.inv Φ)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
  refine (Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective
    Q _ _ hF).2 fun K hK => ?_
  have := hα K hK
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

/-- The derivation unit of the derived direct image is invertible at every K-injective complex of
`𝒪_Y`-modules: on such a complex the degreewise direct image already computes `Rf_*`. -/
private theorem isIso_standardDerivedPushforwardUnit_app
    (K : CochainComplex (SheafOfModules.{u} Y.ringCatSheaf) ℤ) (hK : K.IsKInjective) :
    IsIso ((standardDerivedPushforwardUnit f).app K) :=
  isIso_derivedPushforwardCochainUnit_app_of_isKInjective.{u + 1} f K hK

variable [IsNoetherian Y] [IsNoetherian Z]

/-- The right derived extension `Φ : D(QCoh(𝒪_Y)) ⥤ D(QCoh(𝒪_Z))` of direct image on
quasi-coherent modules of [Stacks, Tag 09T3], at the standard model of both derived categories. -/
private abbrev standardQuasicoherentExtension :
    DerivedCategory (Scheme.QuasicoherentModules Y) ⥤
      DerivedCategory (Scheme.QuasicoherentModules Z) :=
  noetherianPushforwardExtension f

/-- The derivation unit of `Stacks.DerivedQCoh.standardQuasicoherentExtension`, read on the
cochain complexes of quasi-coherent modules rather than on their homotopy category. -/
private abbrev standardQuasicoherentExtensionUnit :
    (quasicoherentPushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := Scheme.QuasicoherentModules Z) ⟶
      DerivedCategory.Q (C := Scheme.QuasicoherentModules Y) ⋙
        standardQuasicoherentExtension f :=
  cochainUnitOfHomotopyUnit (quasicoherentPushforward f) (noetherianPushforwardExtension f)
    (noetherianPushforwardExtensionUnit f)

/-- The derived extension of [Stacks, Tag 09T3] is a total right derived functor of direct image
on quasi-coherent modules for the quasi-isomorphisms of cochain complexes, and not only for those
of the homotopy category: both are detected at the K-injective complexes. -/
private theorem standardQuasicoherentExtension_isRightDerivedFunctor :
    (standardQuasicoherentExtension f).IsRightDerivedFunctor
      (standardQuasicoherentExtensionUnit f)
      (HomologicalComplex.quasiIso (Scheme.QuasicoherentModules Y) (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_cochainUnitOfHomotopyUnit (quasicoherentPushforward f)
    (noetherianPushforwardExtension f) (noetherianPushforwardExtensionUnit f)
    (AlgebraicGeometry.exists_quasiIso_isKInjective_quasicoherentModules Y)

/-- The derivation unit of the derived extension of [Stacks, Tag 09T3] is invertible at every
K-injective complex of quasi-coherent `𝒪_Y`-modules. -/
private theorem isIso_standardQuasicoherentExtensionUnit_app
    (K : CochainComplex (Scheme.QuasicoherentModules Y) ℤ) (hK : K.IsKInjective) :
    IsIso ((standardQuasicoherentExtensionUnit f).app K) :=
  let := standardQuasicoherentExtension_isRightDerivedFunctor f
  Stacks.Injectives.KInjectiveResolution.isIso_app_of_isKInjective
    (DerivedCategory.Q (C := Scheme.QuasicoherentModules Y))
    (standardQuasicoherentExtension f) (standardQuasicoherentExtensionUnit f)
    (invertsQuasiIsoOfIsKInjective_mapHomologicalComplex (quasicoherentPushforward f)) K hK

variable [QuasiCompact f] [QuasiSeparated f]

/-- **The commuting square of [Stacks, Tag 09T3] at the standard model**, with the comparison
functor of [Stacks, Tag 06VT] followed by the inclusion of the complexes with quasi-coherent
cohomology replaced by the derived inclusion of the quasi-coherent modules, which it is. -/
private def standardComparisonSquare :
    standardInclusionDerived Y ⋙ standardDerivedPushforward f ≅
      standardQuasicoherentExtension f ⋙ derivedQuasicoherentComparison.{u + 1} Z ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι :=
  letI : (standardModulesDerivedPushforward f).IsRightDerivedFunctor
      (standardModulesDerivedPushforwardUnit f)
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ)) :=
    inferInstanceAs ((derivedPushforward.{u + 1} f).IsRightDerivedFunctor
      (derivedPushforwardUnit.{u + 1} f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} Y.ringCatSheaf) (ComplexShape.up ℤ)))
  Functor.isoWhiskerRight (derivedQuasicoherentComparisonCompι.{u + 1} Y).symm
      (standardDerivedPushforward f) ≪≫
    noetherianPushforwardExtensionComparison f (standardModulesDerivedPushforward f)
      (standardModulesDerivedPushforwardUnit f)

end Standard

/-! ### Reading the two derived functors at an arbitrary model -/

section AtModel

variable {Y Z : Scheme.{u}} (f : Y ⟶ Z)
  (h₁ : HasDerivedCategory.{u + 1} (SheafOfModules.{u} Y.ringCatSheaf))
  (h₂ : HasDerivedCategory.{u + 1} (Scheme.QuasicoherentModules Y))

/-- **The derived inclusion of the quasi-coherent modules is compatible with a change of model.**
Comparing a chosen model of `D(QCoh(𝒪_Y))` and of `D(𝒪_Y)` with the standard one carries the
derived inclusion read at the chosen models to the derived inclusion read at the standard ones.

Both sides lift, along the localization of the cochain complexes of quasi-coherent modules, the
single functor given by degreewise inclusion followed by the localization of the cochain complexes
of all modules at the standard model, so the universal property of that localization identifies
them. -/
private def inclusionDerivedModelIso :
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory ⋙
        (modelEquiv h₁ (standardModulesModel Y)).functor ≅
      (modelEquiv h₂ (standardQuasicoherentModel Y)).functor ⋙ standardInclusionDerived Y := by
  letI : Localization.Lifting (DerivedCategory.Q (C := Scheme.QuasicoherentModules Y))
      (HomologicalComplex.quasiIso (Scheme.QuasicoherentModules Y) (ComplexShape.up ℤ))
      ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        @DerivedCategory.Q (SheafOfModules.{u} Y.ringCatSheaf) _ _ (standardModulesModel Y))
      ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory ⋙
        (modelEquiv h₁ (standardModulesModel Y)).functor) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategoryFactors
        (modelEquiv h₁ (standardModulesModel Y)).functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (modelCompQIso h₁ (standardModulesModel Y))⟩
  letI : Localization.Lifting (DerivedCategory.Q (C := Scheme.QuasicoherentModules Y))
      (HomologicalComplex.quasiIso (Scheme.QuasicoherentModules Y) (ComplexShape.up ℤ))
      ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        @DerivedCategory.Q (SheafOfModules.{u} Y.ringCatSheaf) _ _ (standardModulesModel Y))
      ((modelEquiv h₂ (standardQuasicoherentModel Y)).functor ⋙
        standardInclusionDerived Y) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (modelCompQIso h₂ (standardQuasicoherentModel Y))
        (standardInclusionDerived Y) ≪≫
      standardInclusionFactors Y⟩
  exact Localization.liftNatIso (DerivedCategory.Q (C := Scheme.QuasicoherentModules Y))
    (HomologicalComplex.quasiIso (Scheme.QuasicoherentModules Y) (ComplexShape.up ℤ))
    ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
      @DerivedCategory.Q (SheafOfModules.{u} Y.ringCatSheaf) _ _ (standardModulesModel Y))
    ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
      @DerivedCategory.Q (SheafOfModules.{u} Y.ringCatSheaf) _ _ (standardModulesModel Y))
    ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapDerivedCategory ⋙
      (modelEquiv h₁ (standardModulesModel Y)).functor)
    ((modelEquiv h₂ (standardQuasicoherentModel Y)).functor ⋙ standardInclusionDerived Y)
    (Iso.refl _)

/-- **The derived direct image `Rf_*` with its source read at a chosen model of `D(𝒪_Y)`.** The
comparison of that model with the standard one is followed by the derived direct image at the
standard model. -/
private abbrev derivedPushforwardAt :
    DerivedCategory (SheafOfModules.{u} Y.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} Z.ringCatSheaf) :=
  (modelEquiv h₁ (standardModulesModel Y)).functor ⋙ standardDerivedPushforward f

/-- The derivation unit of `Stacks.DerivedQCoh.derivedPushforwardAt`: the unit at the standard
model, rewritten along the identification of the two localizations of the cochain complexes of
`𝒪_Y`-modules. -/
private def derivedPushforwardUnitAt :
    (modulesPushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := SheafOfModules.{u} Z.ringCatSheaf) ⟶
      DerivedCategory.Q (C := SheafOfModules.{u} Y.ringCatSheaf) ⋙ derivedPushforwardAt f h₁ :=
  standardDerivedPushforwardUnit f ≫
    Functor.whiskerRight (modelCompQIso h₁ (standardModulesModel Y)).inv
      (standardDerivedPushforward f)

/-- **`Stacks.DerivedQCoh.derivedPushforwardAt` is a total right derived functor of `f_*` at the
chosen model.** Spaltenstein's criterion tests the derivation unit only at the K-injective
complexes, and there this unit is the unit at the standard model composed with isomorphisms. -/
private theorem derivedPushforwardAt_isRightDerivedFunctor :
    (derivedPushforwardAt f h₁).IsRightDerivedFunctor (derivedPushforwardUnitAt f h₁)
      (HomologicalComplex.quasiIso (SheafOfModules.{u} Y.ringCatSheaf) (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_comp_whiskerRight_inv_of_isIso_app
    (invertsQuasiIsoOfIsKInjective_pushforward.{u + 1} f)
    (DerivedCategory.Q (C := SheafOfModules.{u} Y.ringCatSheaf))
    (modelEquiv h₁ (standardModulesModel Y)).functor (modelCompQIso h₁ (standardModulesModel Y))
    (standardDerivedPushforward f) _ (isIso_standardDerivedPushforwardUnit_app f)

variable [IsNoetherian Y] [IsNoetherian Z] [QuasiCompact f] [QuasiSeparated f]

/-- **The derived extension of [Stacks, Tag 09T3] with its source read at a chosen model of
`D(QCoh(𝒪_Y))`.** The comparison of that model with the standard one is followed by the derived
extension at the standard model. -/
private abbrev quasicoherentExtensionAt :
    DerivedCategory (Scheme.QuasicoherentModules Y) ⥤
      DerivedCategory (Scheme.QuasicoherentModules Z) :=
  (modelEquiv h₂ (standardQuasicoherentModel Y)).functor ⋙ standardQuasicoherentExtension f

/-- The derivation unit of `Stacks.DerivedQCoh.quasicoherentExtensionAt`: the unit at the standard
model, rewritten along the identification of the two localizations of the cochain complexes of
quasi-coherent `𝒪_Y`-modules. -/
private def quasicoherentExtensionUnitAt :
    (quasicoherentPushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := Scheme.QuasicoherentModules Z) ⟶
      DerivedCategory.Q (C := Scheme.QuasicoherentModules Y) ⋙
        quasicoherentExtensionAt f h₂ :=
  standardQuasicoherentExtensionUnit f ≫
    Functor.whiskerRight (modelCompQIso h₂ (standardQuasicoherentModel Y)).inv
      (standardQuasicoherentExtension f)

/-- **`Stacks.DerivedQCoh.quasicoherentExtensionAt` is a total right derived functor of direct
image on quasi-coherent modules at the chosen model.** As for all modules, Spaltenstein's
criterion reduces this to the invertibility of the unit at the K-injective complexes. -/
private theorem quasicoherentExtensionAt_isRightDerivedFunctor :
    (quasicoherentExtensionAt f h₂).IsRightDerivedFunctor (quasicoherentExtensionUnitAt f h₂)
      (HomologicalComplex.quasiIso (Scheme.QuasicoherentModules Y) (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_comp_whiskerRight_inv_of_isIso_app
    (invertsQuasiIsoOfIsKInjective_mapHomologicalComplex (quasicoherentPushforward f))
    (DerivedCategory.Q (C := Scheme.QuasicoherentModules Y))
    (modelEquiv h₂ (standardQuasicoherentModel Y)).functor
    (modelCompQIso h₂ (standardQuasicoherentModel Y)) (standardQuasicoherentExtension f) _
    (isIso_standardQuasicoherentExtensionUnit_app f)

/-- **The commuting square of [Stacks, Tag 09T3] at an arbitrary model of the two derived
categories of the source.** The derived extension of direct image on quasi-coherent modules,
followed by the comparison functor of [Stacks, Tag 06VT] over the target and the inclusion of the
complexes with quasi-coherent cohomology, agrees with the comparison functor over the source, that
inclusion, and the derived direct image of all modules.

The square at the standard model is transported by the comparison of the two models, using that
the comparison functor followed by the inclusion of `D_QCoh` is the derived inclusion of the
quasi-coherent modules and that the derived inclusion commutes with a change of model. -/
private def comparisonSquareAt :
    quasicoherentExtensionAt f h₂ ⋙ derivedQuasicoherentComparison.{u + 1} Z ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι ≅
      derivedQuasicoherentComparison.{u + 1} Y ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι ⋙ derivedPushforwardAt f h₁ :=
  Functor.isoWhiskerLeft (modelEquiv h₂ (standardQuasicoherentModel Y)).functor
      (standardComparisonSquare f).symm ≪≫
    Functor.isoWhiskerRight (inclusionDerivedModelIso h₁ h₂).symm
      (standardDerivedPushforward f) ≪≫
    Functor.isoWhiskerRight (derivedQuasicoherentComparisonCompι.{u + 1} Y).symm
      (derivedPushforwardAt f h₁)

end AtModel

/-! ### The hypothesis of Stacks 09T6 on a Noetherian scheme -/

/-- **The affine-open hypothesis of [Stacks, Tag 09T6] holds on a Noetherian scheme.** Let `X` be
a Noetherian scheme. Then for every affine open `U ⊆ X`, with `j : U ⟶ X` the inclusion and at
every model of the two derived categories of `U`, there are a total right derived functor
`Rj_* : D(𝒪_U) ⥤ D(𝒪_X)` of direct image of all modules and a total right derived functor
`Φ : D(QCoh(𝒪_U)) ⥤ D(QCoh(𝒪_X))` of `j_* : QCoh(𝒪_U) ⥤ QCoh(𝒪_X)`, each with its derivation unit
relative to the localization of the cochain complexes, fitting into the commutative square
`i_X ∘ Φ ≅ Rj_* ∘ i_U` of [Stacks, Tag 09T6]; that is,
`Stacks.DerivedQCoh.AffineOpenPushforwardCompatible X` holds.

An affine open of a Noetherian scheme is Noetherian: its ring of sections is Noetherian and its
space is a Noetherian, hence compact, space. So the square is the one [Stacks, Tag 09T3] supplies
for a morphism of Noetherian schemes, `AlgebraicGeometry.noetherianPushforwardExtensionComparison`,
read with `AlgebraicGeometry.AnyModel.derivedPushforward` for the derived direct image. Nothing
here asks `j` to be an affine morphism; the exactness of `j_*` on quasi-coherent modules, which
discharges the hypothesis for a scheme with affine diagonal, is replaced by the flasqueness of the
injective quasi-coherent modules on a Noetherian scheme. -/
theorem noetherianAffineOpenPushforwardCompatible (X : Scheme.{u}) [IsNoetherian X] :
    AffineOpenPushforwardCompatible.{u + 1} X := by
  intro U hU _ _ h₁ h₂
  have : IsAffine U.toScheme := hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : TopologicalSpace.NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
  have : CompactSpace U := TopologicalSpace.NoetherianSpace.compactSpace U
  have : IsNoetherian U.toScheme := {}
  exact ⟨derivedPushforwardAt U.ι h₁, derivedPushforwardUnitAt U.ι h₁,
    quasicoherentExtensionAt U.ι h₂, quasicoherentExtensionUnitAt U.ι h₂,
    derivedPushforwardAt_isRightDerivedFunctor U.ι h₁,
    quasicoherentExtensionAt_isRightDerivedFunctor U.ι h₂,
    ⟨comparisonSquareAt U.ι h₁ h₂⟩⟩

end Stacks.DerivedQCoh

end
