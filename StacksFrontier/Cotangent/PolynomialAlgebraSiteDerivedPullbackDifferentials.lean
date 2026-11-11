module

public import StacksFrontier.Cotangent.PolynomialAlgebraSitePointValues
import StacksCore.Tactic.StacksAttribute

/-!
# `Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}` on the small model of `C_{B/A}`

Let `A → B` be a ring map and let `π`, `i`, `𝒪` and `B̲` be as in [Stacks, Tag 08PR], on the
small model `CommAlgCat.smallBoundedPolynomialSite A B κ` of the footnote-restricted site
`C_{B/A}`. The morphism of ringed topoi `i : (Sh(C_{B/A}), B̲) ⟶ (Sh(C_{B/A}), 𝒪)` is the identity
on underlying topoi, with structure map the augmentation `𝒪 ⟶ B̲`; the topology being chaotic,
sheaves of modules are presheaves of modules, and the module pullback `i^*` is extension of
scalars along the augmentation, `Stacks.ChaoticSite.extendScalars`. Its total left derived functor
`Li^* : D(𝒪) ⥤ D(B̲)` is `Stacks.ChaoticSite.derivedExtendScalars`, which exists because
presheaves of modules have enough projectives.

[Stacks, Tag 08PU] is the chain

`L_{B/A} = Lπ_!(Li^*Ω_{𝒪/A}) = Lπ_!(i^*Ω_{𝒪/A}) = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)`.

This file proves the middle equality before `Lπ_!` is applied, as an isomorphism in `D(B̲)`, by
the source's argument: each `Ω_{P/A}` is a free `P`-module, so a projective resolution of
`Ω_{𝒪/A}` stays a resolution after extension of scalars
(`Stacks.PullbackModel.quasiIso_extendScalars_of_projective_sections`), which is to say that the
comparison `Li^* ⟶ i^*` is invertible at `Ω_{𝒪/A}[0]`. It then assembles the whole chain, with
`Lπ_!` the derived colimit read on abelian groups, at the cardinal bounding the standard
resolution.

## Main definitions

* `CommAlgCat.smallPolynomialModulePullback`: `i^*`, extension of scalars along `𝒪 ⟶ B̲`.
* `CommAlgCat.smallPolynomialDerivedModulePullback`: `Li^* : D(𝒪) ⥤ D(B̲)`.

## Main results

* `CommAlgCat.isIso_derivedExtendScalarsCounit_singleDifferentials`: the comparison
  `Li^* ⟶ i^*` is invertible at `Ω_{𝒪/A}[0]`.
* `CommAlgCat.smallPolynomialDerivedPullbackDifferentialsIso`: **`Li^*Ω_{𝒪/A} ≅ i^*Ω_{𝒪/A}`** in
  `D(B̲)`.
* `CommAlgCat.cotangentComplexIsoDerivedLowerShriekDerivedPullback`:
  **`L_{B/A} ≅ Lπ_!(Li^*Ω_{𝒪/A})`** in `D(Ab)`, through `Lπ_!(i^*Ω_{𝒪/A})` and
  `Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)`.

## References

* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

/- The derived category of presheaves of modules used throughout is the standard localisation, the
one `Stacks.ChaoticSite.derivedExtendScalars` is formed in; the instance with a free module
universe, `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory`, would
otherwise be found first. -/
attribute [-instance] Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-- **`i^*` on the small model of `C_{B/A}`**: the module pullback along the morphism of ringed
topoi `i : (Sh(C_{B/A}), B̲) ⟶ (Sh(C_{B/A}), 𝒪)` of [Stacks, Tag 08PR], which is extension of
scalars along the augmentation `𝒪 ⟶ B̲`. -/
abbrev smallPolynomialModulePullback :
    PresheafOfModules.{u} (smallPolynomialStructurePresheaf A B κ) ⥤
      PresheafOfModules.{u} (smallPolynomialConstantPresheaf A B κ) :=
  Stacks.ChaoticSite.extendScalars (smallPolynomialAugmentation A B κ)

/-- **`Li^* : D(𝒪) ⥤ D(B̲)` on the small model of `C_{B/A}`**, the total left derived functor of
`CommAlgCat.smallPolynomialModulePullback`. -/
abbrev smallPolynomialDerivedModulePullback :
    DerivedCategory (PresheafOfModules.{u} (smallPolynomialStructurePresheaf A B κ)) ⥤
      DerivedCategory (PresheafOfModules.{u} (smallPolynomialConstantPresheaf A B κ)) :=
  Stacks.ChaoticSite.derivedExtendScalars (smallPolynomialAugmentation A B κ)

/-- **The comparison `Li^* ⟶ i^*` is invertible at `Ω_{𝒪/A}[0]`.** Choose a projective resolution
`P^• ⟶ Ω_{𝒪/A}[0]` ([Stacks, Tag 0646]). The comparison is invertible at the K-projective complex
`P^•`; `Li^*` inverts the quasi-isomorphism `P^• ⟶ Ω_{𝒪/A}[0]`; and `i^*` carries it to a
quasi-isomorphism because every section `Ω_{P/A}` of `Ω_{𝒪/A}` is a free `P`-module. -/
theorem isIso_derivedExtendScalarsCounit_singleDifferentials :
    IsIso ((Stacks.ChaoticSite.derivedExtendScalarsCounit
        (smallPolynomialAugmentation A B κ)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (smallPolynomialDifferentials A B κ)))) := by
  have := Stacks.CategoryHomology.hasPointwiseLeftDerivedFunctor_of_enoughProjectives
    (Stacks.ChaoticSite.extendScalars (smallPolynomialAugmentation A B κ))
  have := Stacks.ChaoticSite.derivedExtendScalars_isLeftDerivedFunctor
    (smallPolynomialAugmentation A B κ)
  let R := (ProjectiveResolutionLemma.statement3 (0 : ℤ)
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (smallPolynomialDifferentials A B κ)) inferInstance).choose
  have : R.complex.IsStrictlyLE 0 := R.boundedAbove
  have := R.projective
  have := R.quasiIso
  have : R.complex.IsKProjective := CochainComplex.isKProjective_of_projective _ 0
  have hK := Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective _
    (Stacks.ChaoticSite.derivedExtendScalarsCounit (smallPolynomialAugmentation A B κ))
    R.complex
  have e := NatIso.mapHomologicalComplex (Stacks.PullbackModel.extendScalarsIsoLeftAdjoint
    (smallPolynomialAugmentationComm A B κ)) (ComplexShape.up ℤ)
  have harr : Arrow.mk (((Stacks.PullbackModel.extendScalars
        (smallPolynomialAugmentationComm A B κ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map R.α) ≅
      Arrow.mk (((Stacks.ChaoticSite.extendScalars (smallPolynomialAugmentation A B κ)
        ).mapHomologicalComplex (ComplexShape.up ℤ)).map R.α) :=
    Arrow.isoMk (e.app _) (e.app _) (e.hom.naturality _).symm
  have hq : QuasiIso (((Stacks.ChaoticSite.extendScalars (smallPolynomialAugmentation A B κ)
      ).mapHomologicalComplex (ComplexShape.up ℤ)).map R.α) :=
    (quasiIso_iff_of_arrow_mk_iso _ _ harr).1
      (Stacks.PullbackModel.quasiIso_extendScalars_of_projective_sections _ R.boundedAbove
        R.projective (projective_smallPolynomialDifferentials_obj A B κ) R.α R.quasiIso)
  have h₁ : IsIso ((DerivedCategory.Qh ⋙ smallPolynomialDerivedModulePullback A B κ).map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map R.α)) := by
    have : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map R.α)) :=
      (DerivedCategory.isIso_Qh_map_iff _).2
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff R.α).2 R.quasiIso)
    exact inferInstanceAs (IsIso ((smallPolynomialDerivedModulePullback A B κ).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map R.α))))
  have h₂ : IsIso (DerivedCategory.Qh.map
      (((Stacks.ChaoticSite.extendScalars (smallPolynomialAugmentation A B κ)).mapHomotopyCategory
        (ComplexShape.up ℤ)).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map R.α))) :=
    (DerivedCategory.isIso_Qh_map_iff _).2
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hq)
  have hnat := (Stacks.ChaoticSite.derivedExtendScalarsCounit
    (smallPolynomialAugmentation A B κ)).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map R.α)
  have : IsIso ((DerivedCategory.Qh ⋙ smallPolynomialDerivedModulePullback A B κ).map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map R.α) ≫
        (Stacks.ChaoticSite.derivedExtendScalarsCounit (smallPolynomialAugmentation A B κ)).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
              (smallPolynomialDifferentials A B κ)))) := by
    rw [hnat]
    exact IsIso.comp_isIso' hK h₂
  exact IsIso.of_isIso_comp_left
    ((DerivedCategory.Qh ⋙ smallPolynomialDerivedModulePullback A B κ).map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map R.α)) _

/-- **`Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}`** in `D(B̲)`, on the small model of the footnote-restricted site
`C_{B/A}`: the total left derived functor of the module pullback along `i`, evaluated at
`Ω_{𝒪/A}` in degree zero, is the underived pullback in degree zero. This is the comparison
`Li^* ⟶ i^*` at `Ω_{𝒪/A}[0]`, invertible by
`CommAlgCat.isIso_derivedExtendScalarsCounit_singleDifferentials`, read between the two
single-degree embeddings. -/
@[stacks 08PU "the step Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A} in D(B̲), on the small model of the \
  footnote-restricted site C_{B/A}, where i^* is extension of scalars along the augmentation \
  𝒪 ⟶ B̲ and Li^* its total left derived functor"]
def smallPolynomialDerivedPullbackDifferentialsIso :
    (smallPolynomialDerivedModulePullback A B κ).obj
        ((DerivedCategory.singleFunctor _ 0).obj (smallPolynomialDifferentials A B κ)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((smallPolynomialModulePullback A B κ).obj (smallPolynomialDifferentials A B κ)) :=
  (smallPolynomialDerivedModulePullback A B κ).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
        ((DerivedCategory.quotientCompQhIso _).app _).symm) ≪≫
    @asIso _ _ _ _ _ (isIso_derivedExtendScalarsCounit_singleDifferentials A B κ) ≪≫
    DerivedCategory.Qh.mapIso
      (((smallPolynomialModulePullback A B κ).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app _) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (smallPolynomialModulePullback A B κ) (ComplexShape.up ℤ) 0).app _) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm

/-- **[Stacks, Tag 08PU] as the full chain, in `D(Ab)`**: on the small model of the
footnote-restricted site `C_{B/A}`, at the cardinal bounding the standard resolution,

`L_{B/A} ≅ Lπ_!(Li^*Ω_{𝒪/A})`,

with `Lπ_!` the derived colimit of the underlying abelian presheaves
(`Stacks.ChaoticSite.abelianDerivedColimitOfModules`). The isomorphism is the composite of the
source's three steps: `Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}`
(`CommAlgCat.smallPolynomialDerivedPullbackDifferentialsIso`); `i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲`, the
sheaf `(P, α) ↦ B ⊗_{P,α} Ω_{P/A}` (`CommAlgCat.extendScalarsDifferentialsIso`); and
`Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲) = L_{B/A}`, computed on the standard resolution
(`CommAlgCat.derivedLowerShriekCotangentIso`). -/
@[stacks 08PU "the chain L_{B/A} = Lπ_!(Li^*Ω_{𝒪/A}) = Lπ_!(i^*Ω_{𝒪/A}) = \
  Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲), read in D(Ab), on the small model of the footnote-restricted site \
  C_{B/A}"]
def cotangentComplexIsoDerivedLowerShriekDerivedPullback :
    DerivedCategory.Q.obj
        (((forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B)) ≅
      (Stacks.ChaoticSite.abelianDerivedColimitOfModules
          (smallPolynomialConstantPresheaf A B (standardResolutionVarCardinal A B))).obj
        ((smallPolynomialDerivedModulePullback A B (standardResolutionVarCardinal A B)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (smallPolynomialDifferentials A B (standardResolutionVarCardinal A B)))) :=
  ((Stacks.ChaoticSite.abelianDerivedColimitOfModules
          (smallPolynomialConstantPresheaf A B (standardResolutionVarCardinal A B))).mapIso
        (smallPolynomialDerivedPullbackDifferentialsIso A B (standardResolutionVarCardinal A B)) ≪≫
      (abelianDerivedLowerShriek A B).mapIso
        (((PresheafOfModules.toPresheaf (smallPolynomialConstantPresheaf A B
            (standardResolutionVarCardinal A B))).mapDerivedCategorySingleFunctor 0).app _ ≪≫
          (DerivedCategory.singleFunctorIsoCompQ _ 0).app _) ≪≫
      derivedLowerShriekSingleMapIso A B
        ((PresheafOfModules.toPresheaf (smallPolynomialConstantPresheaf A B
            (standardResolutionVarCardinal A B))).mapIso
          ((Stacks.PullbackModel.extendScalarsIsoLeftAdjoint
            (smallPolynomialAugmentationComm A B
              (standardResolutionVarCardinal A B))).app
                (smallPolynomialDifferentials A B (standardResolutionVarCardinal A B))).symm) ≪≫
      derivedLowerShriekSingleMapIso A B
        (extendScalarsDifferentialsIso A B (standardResolutionVarCardinal A B)) ≪≫
      derivedLowerShriekCotangentIso A B).symm

end CommAlgCat

end
