module
public import StacksCore.CategoryTheory.Filtration.Preadditive
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.Homology.KFlat.BifunctorLocalization

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.Flat
public import StacksFrontier.Homology.KFlat.LadderResolution

/-!
# K-flat resolutions and the derived tensor product of étale sheaves of `Λ`-modules

Let `Λ` be a commutative ring and `X` a scheme. Every complex of sheaves of `Λ`-modules on the
small étale site of `X` receives a quasi-isomorphism, an epimorphism in each degree, from a
complex of flat sheaves which is K-flat in both variables of the tensor product
`Stacks.EtaleCohomology.etaleModuleTensor Λ X` (Stacks 06YS for the tensor product over `Λ`).
Hence `D(X_étale, Λ)` is the localization of the (left) K-flat complexes, and the tensor product
descends to the derived tensor product `⊗^L_Λ : D(X_étale, Λ) ⥤ D(X_étale, Λ) ⥤ D(X_étale, Λ)`.

## Main results

* `Stacks.EtaleCohomology.kFlat_etaleModule_of_isStrictlyLE`,
  `Stacks.EtaleCohomology.kFlatLeft_etaleModule_of_isStrictlyLE`: a bounded above complex of flat
  sheaves of `Λ`-modules is K-flat in each variable (Stacks 06YQ).
* `Stacks.EtaleCohomology.exists_etaleModule_kFlatResolution`: the K-flat resolution with flat
  terms (Stacks 06YS).
* `Stacks.EtaleCohomology.etaleModule_kFlatLocalizer_hasLeftResolutions`,
  `Stacks.EtaleCohomology.etaleModule_kFlatLocalizerLeft_hasLeftResolutions`: the K-flat and left
  K-flat resolutions as instances, from which
  `CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions` and
  `kFlatQLeft_isLocalization_of_hasLeftResolutions` give the two localizations.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedTensor`: the derived tensor product `⊗^L_Λ`.

## Implementation notes

The construction is the generic ladder argument
`CochainComplex.KFlatBifunctor.exists_kFlatResolution_of_flat`, with the class of flat sheaves
`Stacks.EtaleCohomology.IsFlatEtaleModule`, exactly as for abelian étale sheaves
(`Stacks.EtaleCohomology.exists_kFlatResolution`). The derived tensor product is an `abbrev` of
`CochainComplex.KFlatBifunctor.derivedBifunctor`, so that all the generic results about
`derivedBifunctor` apply to it as they stand. The derived category is the standard one,
`HasDerivedCategory.standard`, activated locally as everywhere in the étale development.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u r

namespace Stacks.EtaleCohomology

open AlgebraicGeometry CochainComplex.KFlatBifunctor ZeroObject

attribute [local instance] etaleModuleMonoidalCategory etaleModuleBraidedCategory

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- Flatness of étale sheaves of `Λ`-modules, as a property of objects. -/
abbrev isFlatEtaleModuleProperty : ObjectProperty (EtaleModules.{u, r} Λ X) :=
  fun F ↦ IsFlatEtaleModule F

/-- Flatness of étale sheaves of `Λ`-modules is invariant under isomorphism. -/
instance : (isFlatEtaleModuleProperty.{u, r} Λ X).IsClosedUnderIsomorphisms where
  of_iso e h := IsFlatEtaleModule.of_iso e h

/-- Some zero object of the category of étale sheaves of `Λ`-modules is flat. -/
instance : (isFlatEtaleModuleProperty.{u, r} Λ X).ContainsZero :=
  ⟨⟨_, isZero_zero _, isFlatEtaleModule_of_isZero (isZero_zero _)⟩⟩

/-- **A bounded above complex of flat étale sheaves of `Λ`-modules is K-flat** (Stacks 06YQ). -/
theorem kFlat_etaleModule_of_isStrictlyLE (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (b : ℤ) [K.IsStrictlyLE b] (hK : ∀ i, IsFlatEtaleModule (K.X i)) :
    KFlat (etaleModuleTensor.{u, r} Λ X) K :=
  kFlat_of_isStrictlyLE_of_flat (isFlatEtaleModuleProperty.{u, r} Λ X) _
    (fun _ hM _ hG ↦ IsFlatEtaleModule.acyclic_map_tensorRight hM hG) K b hK

/-- **A bounded above complex of flat étale sheaves of `Λ`-modules is K-flat in the left
variable** (Stacks 06YQ). -/
theorem kFlatLeft_etaleModule_of_isStrictlyLE (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ)
    (b : ℤ) [K.IsStrictlyLE b] (hK : ∀ i, IsFlatEtaleModule (K.X i)) :
    KFlatLeft (etaleModuleTensor.{u, r} Λ X) K :=
  kFlatLeft_of_isStrictlyLE_of_flat (isFlatEtaleModuleProperty.{u, r} Λ X) _
    (fun _ hM _ hG ↦ IsFlatEtaleModule.acyclic_map_tensorLeft hM hG) K b hK

/-- **K-flat resolutions with flat terms of complexes of étale sheaves of `Λ`-modules** (Stacks
06YS for the tensor product over `Λ`). Every complex receives a quasi-isomorphism, an epimorphism
in each degree, from a complex of flat sheaves which is K-flat in both variables of the tensor
product. -/
theorem exists_etaleModule_kFlatResolution (G : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    ∃ (P : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (p : P ⟶ G),
      KFlat (etaleModuleTensor.{u, r} Λ X) P ∧ KFlatLeft (etaleModuleTensor.{u, r} Λ X) P ∧
        (∀ i, IsFlatEtaleModule (P.X i)) ∧ QuasiIso p ∧ (∀ i, Epi (p.f i)) :=
  exists_kFlatResolution_of_flat (isFlatEtaleModuleProperty.{u, r} Λ X)
    (fun _ _ hA hB ↦ isFlatEtaleModule_biprod hA hB)
    (fun A ↦ by
      obtain ⟨B, p, hB, hp⟩ := exists_epi_isFlatEtaleModule A
      exact ⟨B, hB, p, hp⟩)
    (fun D hD ↦ isFlatEtaleModule_colimit_nat D hD) _
    (fun _ hM _ hG ↦ IsFlatEtaleModule.acyclic_map_tensorRight hM hG)
    (fun _ hM _ hG ↦ IsFlatEtaleModule.acyclic_map_tensorLeft hM hG) G

/-- Every complex of étale sheaves of `Λ`-modules receives a quasi-isomorphism from a complex
which is K-flat for the tensor product. -/
theorem exists_etaleModule_kFlat_quasiIso (G : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    ∃ (P : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (p : P ⟶ G),
      KFlat (etaleModuleTensor.{u, r} Λ X) P ∧ QuasiIso p := by
  obtain ⟨P, p, hP, -, -, hp, -⟩ := exists_etaleModule_kFlatResolution Λ X G
  exact ⟨P, p, hP, hp⟩

/-- Every complex of étale sheaves of `Λ`-modules receives a quasi-isomorphism from a complex
which is K-flat in the left variable of the tensor product. -/
theorem exists_etaleModule_kFlatLeft_quasiIso (G : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    ∃ (P : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) (p : P ⟶ G),
      KFlatLeft (etaleModuleTensor.{u, r} Λ X) P ∧ QuasiIso p := by
  obtain ⟨P, p, -, hP, -, hp, -⟩ := exists_etaleModule_kFlatResolution Λ X G
  exact ⟨P, p, hP, hp⟩

/-- **The K-flat resolutions of étale sheaves of `Λ`-modules, as an instance**:
`exists_etaleModule_kFlat_quasiIso` in the form the localization instance
`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions` takes, so that
`D(X_étale, Λ)` is the localization of the K-flat complexes (for the tensor product over `Λ`) at
the quasi-isomorphisms. -/
instance etaleModule_kFlatLocalizer_hasLeftResolutions :
    (kFlatLocalizer (etaleModuleTensor.{u, r} Λ X)).HasLeftResolutions :=
  CochainComplex.KFlatBifunctor.kFlatLocalizer_hasLeftResolutions _
    (exists_etaleModule_kFlat_quasiIso Λ X)

/-- **The left K-flat resolutions of étale sheaves of `Λ`-modules, as an instance**:
`exists_etaleModule_kFlatLeft_quasiIso` in the form the localization instance
`CochainComplex.KFlatBifunctor.kFlatQLeft_isLocalization_of_hasLeftResolutions` takes, so that
`D(X_étale, Λ)` is the localization of the complexes K-flat in the left variable of the tensor
product over `Λ` at the quasi-isomorphisms. -/
instance etaleModule_kFlatLocalizerLeft_hasLeftResolutions :
    (kFlatLocalizerLeft (etaleModuleTensor.{u, r} Λ X)).HasLeftResolutions :=
  CochainComplex.KFlatBifunctor.kFlatLocalizerLeft_hasLeftResolutions _
    (exists_etaleModule_kFlatLeft_quasiIso Λ X)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The derived tensor product of étale sheaves of `Λ`-modules**,
`⊗^L_Λ : D(X_étale, Λ) ⥤ D(X_étale, Λ) ⥤ D(X_étale, Λ)`: the descent of the total tensor product
of complexes along the two K-flat localizations. -/
noncomputable abbrev etaleModuleDerivedTensor :
    DerivedCategory (EtaleModules.{u, r} Λ X) ⥤ DerivedCategory (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory (EtaleModules.{u, r} Λ X) :=
  CochainComplex.KFlatBifunctor.derivedBifunctor (etaleModuleTensor.{u, r} Λ X)

end Derived

end Stacks.EtaleCohomology

end
