module

public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayLocus
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.RingTheory.Dualizing.InvertibleHomologySingle
import all StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayLocus
import all StacksFrontier.RingTheory.Dualizing.LocalCriterionInvertible
import all StacksFrontier.RingTheory.Dualizing.LocallyShiftedSingle

/-!
# The stalkwise criterion for Gorenstein local rings on a scheme with a dualizing complex

Let `X` be a locally Noetherian scheme carrying a dualizing complex `ω_X^•`
(`Stacks.Duality.IsDualizingComplex`, [Stacks, Tag 0A87]). This file proves
[Stacks, Tag 0BFQ], clause (1)(b): the local ring at `x` is Gorenstein exactly when the derived
stalk `ω_{X,x}^•` is an invertible object of `D(𝒪_{X,x})`.

## Main results

* `Stacks.Duality.isGorensteinLocalRing_stalk_iff_isInvertible_derivedStalk`: the local ring at
  `x` is Gorenstein exactly when the derived stalk of the dualizing complex is invertible.

## Implementation notes

*The route is through an affine model, not through the derived stalk being dualizing.* The
statement one would like is that the derived stalk of a dualizing complex is a dualizing complex
over `𝒪_{X,x}`; with it, clause (1)(b) would be the ring-level criterion
[Stacks, Tag 0DW9 (1)(b)] read at `𝒪_{X,x}`. That statement is not available here: it would need
an identification, in the derived category, of the stalk of `K` at `x` with the derived
localization of an affine model, and the comparison of the stalk of a restriction to an open
subscheme with the stalk itself exists in this development only for abelian groups
(`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`), not for modules.

What is used instead is that **invertibility over a local ring is a condition on the cohomology
modules** — `Dualizing.isInvertible_iff_homology_concentrated_free`, the cohomology vanishes
outside one degree and is the ring itself there — and that the cohomology modules *are* identified:
the derived localization taken is the one at `𝒪_{X,x}` itself, which is a localization of `Γ(X, U)`
at the prime of `x` (`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), so no second local
ring and no ring isomorphism enter. In every degree the cohomology of that derived localization and
the stalk of the cohomology sheaf are both the localization of the same `Γ(X, U)`-module, hence
`Γ(X, U)`-linearly isomorphic, and a `Γ(X, U)`-linear isomorphism of `𝒪_{X,x}`-modules is
`𝒪_{X,x}`-linear because `𝒪_{X,x}` is a localization of `Γ(X, U)`
(`LinearEquiv.extendScalarsOfIsLocalization`). The resulting isomorphism of objects of `D(𝒪_{X,x})`
degree by degree is enough, invertibility being cohomological.

The affine translation table is the module-level form of
`Stacks.Duality.exists_model_stalk_translation`: the dualizing model `ω` over `Γ(X, U)` is held
fixed across all degrees,
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections` identifies the sections
of the cohomology sheaf, and `Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ` exhibits
the stalk as their localization. Only the `Subsingleton` shadow of this was needed for
[Stacks, Tag 0AWT]; here the linear equivalence itself is kept.

*The model of the derived categories.* The monoidal structure
`DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory`, for which invertibility is
asserted, exists only at `HasDerivedCategory.standard`, so the model of `D(𝒪_{X,x})` is pinned
there by a `letI` in the statement. `AlgebraicGeometry.derivedStalkFunctor` carries *one* morphism
universe for both of its derived categories, so this pins the model of `D(𝒪_X)` as well: the
instance argument is `HasDerivedCategory.{u + 1} X.Modules` rather than the free
`HasDerivedCategory.{w} X.Modules` of `Stacks.Duality.IsDualizingComplex`. That is an
instantiation of the hypothesis, not a restriction of the mathematics — `u + 1` is the morphism
universe of the standard model — but a caller working at the locally small model must transport.

## References

* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Duality

section RingLevel

attribute [local instance] HasDerivedCategory.standard

/-- Localization at a submonoid carries a linear equivalence to a linear equivalence. -/
private noncomputable def localizedModuleCongr {R : Type u} [CommRing R] (S : Submonoid R)
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    LocalizedModule S M ≃ₗ[R] LocalizedModule S N :=
  IsLocalizedModule.iso S ((LocalizedModule.mkLinearMap S N).comp (e : M →ₗ[R] N))

/-- **Cohomology commutes with derived localization**, at an arbitrary localization rather than
at `Localization.AtPrime`. This is the natural isomorphism
`CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso` read at one
object. -/
private noncomputable def localizedHomologyIsoOfIsLocalization
    {A : Type u} [CommRing A] (S : Submonoid A) {B : Type u} [CommRing B] [Algebra A B]
    [IsLocalization S B] (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    ModuleCat.of A (LocalizedModule S
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ω)) ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A B)).obj ω)) := by
  let U := ModuleCat.uliftFunctor.{u, u} A
  let Kbig := U.mapDerivedCategory.obj ω
  let eHom := (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso U i).app ω
  let eLoc := (CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso
    (R := A) (A := B) S i).app Kbig
  let eLift := (CochainComplex.DerivedTensor.localizedModuleFunctor.{u, u} S).mapIso eHom
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj ω
  let eULift := Dualizing.localizedModuleUliftIso (R := A) S (M := H)
  refine Iso.symm ?_
  change (ModuleCat.restrictScalars (algebraMap A B)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
          (algebraMap A B)).functor.obj Kbig)) ≅ _
  exact eLoc ≪≫ eLift ≪≫ eULift

/-- **Restriction of scalars along a localization reflects isomorphisms of modules**: an
`A`-linear isomorphism of two `B`-modules is `B`-linear when `B` is a localization of `A`. -/
private noncomputable def isoOfRestrictScalarsIso {A : Type u} [CommRing A] (S : Submonoid A)
    {B : Type u} [CommRing B] [Algebra A B] [IsLocalization S B] {M N : ModuleCat.{u} B}
    (e : (ModuleCat.restrictScalars (algebraMap A B)).obj M ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj N) :
    M ≅ N := by
  letI : Module A (M : Type u) := Module.compHom _ (algebraMap A B)
  letI : Module A (N : Type u) := Module.compHom _ (algebraMap A B)
  letI : IsScalarTower A B (M : Type u) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower A B (N : Type u) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have e' : (M : Type u) ≃ₗ[A] (N : Type u) := e.toLinearEquiv
  exact (LinearEquiv.extendScalarsOfIsLocalization S B e').toModuleIso

end RingLevel

section Stalkwise

open Stacks.AlgebraicGeometry.CoherentTFAE Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **The affine translation table, at the level of modules.** At an affine open `U` of a locally
Noetherian scheme carrying a dualizing complex there is a dualizing complex `ω` over `Γ(X, U)`
such that, at every point `y` of `U` and in every degree `i`, the stalk at `y` of the `i`-th
cohomology sheaf of `K` is the localization at the prime of `y` of `H^i(ω)`.

This is `Stacks.Duality.exists_model_stalk_translation` with the linear equivalence kept instead
of only its `Subsingleton` shadow. -/
private lemma exists_model_stalk_module_translation [HasDerivedCategory.{w} X.Modules]
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)), Dualizing.IsDualizingComplex ω ∧
      ∀ (i : ℤ) (y : X) (hy : y ∈ U),
        letI := Stacks.ModuleStalkSpecialization.sectionsStalkModule
          ((DerivedCategory.homologyFunctor X.Modules i).obj K) hy
        Nonempty (LocalizedModule (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U)) i).obj ω) ≃ₗ[Γ(X, U)]
          ((DerivedCategory.homologyFunctor X.Modules i).obj K).presheaf.stalk y) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  obtain ⟨ω, hω, hiso⟩ := exists_specModule_homology_iso hU (hK U hU)
  refine ⟨ω, hω, fun i y hy => ?_⟩
  let := Stacks.ModuleStalkSpecialization.sectionsStalkModule
    ((DerivedCategory.homologyFunctor X.Modules i).obj K) hy
  have : _root_.SheafOfModules.IsCoherent ((DerivedCategory.homologyFunctor X.Modules i).obj K) :=
    isCoherent_homology_of_isDualizingComplex hK i
  have : ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent :=
    (isQuasicoherent_isFiniteType_of_isCoherent _).1
  have : IsLocalizedModule (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
      (Stacks.ModuleStalkSpecialization.germₗ
        ((DerivedCategory.homologyFunctor X.Modules i).obj K) hy) :=
    Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ _ hU hy
  exact ⟨(localizedModuleCongr _ (hiso i).some.toLinearEquiv).symm ≪≫ₗ
    IsLocalizedModule.iso (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
      ((Stacks.ModuleStalkSpecialization.germₗ
          ((DerivedCategory.homologyFunctor X.Modules i).obj K) hy).comp
        (Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections
          ((DerivedCategory.homologyFunctor X.Modules i).obj K)
          ⟨U, hU⟩).toLinearEquiv.toLinearMap)⟩

/-- On a locally Noetherian scheme carrying a dualizing complex `K`, the local ring at `x` is
Gorenstein exactly when the derived stalk `K_x` is an invertible object of `D(𝒪_{X,x})`. -/
@[stacks 0BFQ "(1)(b): the local ring at a point is Gorenstein iff the derived stalk of the
dualizing complex is invertible"]
public theorem isGorensteinLocalRing_stalk_iff_isInvertible_derivedStalk
    [HasDerivedCategory.{u + 1} X.Modules] (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) (x : X) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk x))
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
      (X.presheaf.stalk x)).choose
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) ↔
      MonoidalCategory.IsInvertible ((AlgebraicGeometry.derivedStalkFunctor x).obj K) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk x))
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (X.presheaf.stalk x)).choose
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  let : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.IsPrime := (hU.primeIdealOf ⟨x, hxU⟩).isPrime
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  obtain ⟨ω, hω, htr⟩ := exists_model_stalk_module_translation hK hU
  have hωB : Dualizing.IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap Γ(X, U) (X.presheaf.stalk x))).obj ω) :=
    Dualizing.isDualizingComplex_localization
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl ω hω
  have hdeg : ∀ i : ℤ,
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) i).obj
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars
            (algebraMap Γ(X, U) (X.presheaf.stalk x))).obj ω) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) i).obj
          ((AlgebraicGeometry.derivedStalkFunctor x).obj K) := by
    intro i
    refine isoOfRestrictScalarsIso (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl ?_
    refine (localizedHomologyIsoOfIsLocalization _ ω i).symm ≪≫
      (htr i x hxU).some.toModuleIso ≪≫
      (ModuleCat.restrictScalars (algebraMap Γ(X, U) (X.presheaf.stalk x))).mapIso
        ((Dualizing.mapDerivedCategoryHomologyIso
          (Stacks.ModuleSkyscraper.modulesStalkFunctor X x) i).app K).symm
  refine (Dualizing.local_criterion_native (X.presheaf.stalk x) _ hωB).trans ?_
  refine Iff.trans (Dualizing.isInvertible_iff_homology_concentrated_free _) ?_
  refine Iff.trans ?_ (Dualizing.isInvertible_iff_homology_concentrated_free _).symm
  exact exists_congr fun n => and_congr
    (forall_congr' fun i => imp_congr_right fun _ => (hdeg i).isZero_iff)
    ⟨fun ⟨e⟩ => ⟨(hdeg n).symm ≪≫ e⟩, fun ⟨e⟩ => ⟨hdeg n ≪≫ e⟩⟩

end Stalkwise

end Stacks.Duality

end
