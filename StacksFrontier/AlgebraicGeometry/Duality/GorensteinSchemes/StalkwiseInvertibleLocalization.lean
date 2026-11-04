module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StalkwiseInvertible
public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayLocus
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.RingTheory.Dualizing.InvertibleHomologySingle
import all StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StalkwiseInvertible
import all StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayLocus
import all StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible
import all StacksFrontier.RingTheory.Dualizing.LocallyShiftedSingle

/-!
# Invertibility of derived stalks via affine models

The stalk of a quasi-coherent module at a point of an affine open is the localization of its
sections, and the invertibility of the derived stalk of a complex with quasi-coherent cohomology
can be read off from a complex of modules over the sections of an affine open.

## Main results

* `nonempty_localizedModule_linearEquiv_stalk`: the stalk of a quasi-coherent module at a point
  of an affine open `U` is the localization of its sections over `U` at the corresponding prime.
* `isInvertible_derivedStalk_iff_of_specModule_iso`: the derived stalk `K_x` is invertible
  exactly when the derived localization `ω ⊗^L 𝒪_{X,x}` of an affine model `ω` of `K` is.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Duality

section RingLevel

attribute [local instance] HasDerivedCategory.standard

end RingLevel

section Stalkwise

open Stacks.AlgebraicGeometry.CoherentTFAE Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **The stalk of a quasi-coherent module at a point of an affine open is the localization of
its sections**, in any presentation `N` of the sections: at a point `y` of the affine open `U`,
the stalk `F_y` is `Γ(X, U)`-linearly the localization of `N` at the prime of `y`. -/
public lemma nonempty_localizedModule_linearEquiv_stalk {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {N : ModuleCat.{u} Γ(X, U)}
    (e : specModule F hU ≅ N) {y : X} (hy : y ∈ U) :
    letI := Stacks.ModuleStalkSpecialization.sectionsStalkModule F hy
    Nonempty (LocalizedModule (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl N ≃ₗ[Γ(X, U)]
      F.presheaf.stalk y) := by
  let := Stacks.ModuleStalkSpecialization.sectionsStalkModule F hy
  have : IsLocalizedModule (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
      (Stacks.ModuleStalkSpecialization.germₗ F hy) :=
    Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ _ hU hy
  exact ⟨(localizedModuleCongr _ e.toLinearEquiv).symm ≪≫ₗ
    IsLocalizedModule.iso (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
      ((Stacks.ModuleStalkSpecialization.germₗ F hy).comp
        (Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections F
          ⟨U, hU⟩).toLinearEquiv.toLinearMap)⟩

/-- **Invertibility of a derived stalk, read on an affine model.** Let `K` be an object of
`D(𝒪_X)` with quasi-coherent cohomology sheaves, `U` an affine open containing `x`, and `ω` a
complex over `Γ(X, U)` whose cohomology modules compute the sections over `U` of the cohomology
sheaves of `K`. Then the derived stalk `K_x` is invertible in `D(𝒪_{X,x})` exactly when the
derived localization `ω ⊗^L 𝒪_{X,x}` is. -/
public theorem isInvertible_derivedStalk_iff_of_specModule_iso {X : Scheme.{u}}
    [HasDerivedCategory.{u + 1} X.Modules] (K : DerivedCategory X.Modules)
    (hQ : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U)
    (ω : @DerivedCategory (ModuleCat.{u} Γ(X, U)) _ _ (HasDerivedCategory.standard _))
    (hω : letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
      ∀ i : ℤ, Nonempty (specModule ((DerivedCategory.homologyFunctor X.Modules i).obj K) hU ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω)) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk x))
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
      (X.presheaf.stalk x)).choose
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    MonoidalCategory.IsInvertible ((AlgebraicGeometry.derivedStalkFunctor x).obj K) ↔
      MonoidalCategory.IsInvertible ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap Γ(X, U) (X.presheaf.stalk x))).obj ω) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk x))
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (X.presheaf.stalk x)).choose
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  let : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.IsPrime := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have hdeg : ∀ i : ℤ,
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) i).obj
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars
            (algebraMap Γ(X, U) (X.presheaf.stalk x))).obj ω) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) i).obj
          ((AlgebraicGeometry.derivedStalkFunctor x).obj K) := by
    intro i
    refine isoOfRestrictScalarsIso (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl ?_
    refine (localizedHomologyIsoOfIsLocalization _ ω i).symm ≪≫
      (nonempty_localizedModule_linearEquiv_stalk _ hU (hω i).some hxU).some.toModuleIso ≪≫
      (ModuleCat.restrictScalars (algebraMap Γ(X, U) (X.presheaf.stalk x))).mapIso
        ((Dualizing.mapDerivedCategoryHomologyIso
          (Stacks.ModuleSkyscraper.modulesStalkFunctor X x) i).app K).symm
  refine Iff.trans (Dualizing.isInvertible_iff_homology_concentrated_free _) ?_
  refine Iff.trans ?_ (Dualizing.isInvertible_iff_homology_concentrated_free _).symm
  exact exists_congr fun n => and_congr
    (forall_congr' fun i => imp_congr_right fun _ => (hdeg i).isZero_iff.symm)
    ⟨fun ⟨e⟩ => ⟨hdeg n ≪≫ e⟩, fun ⟨e⟩ => ⟨(hdeg n).symm ≪≫ e⟩⟩

end Stalkwise

end Stacks.Duality

end
