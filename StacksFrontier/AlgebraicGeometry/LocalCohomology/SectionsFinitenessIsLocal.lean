module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FiniteLocallyFreeComplementAffine
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.LocalFinitenessDescent
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.Localization
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessIsLocal
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence

/-!
# Finiteness of the sections over an open of a Noetherian affine scheme is local

Let `A` be a Noetherian ring and `V` an open of `Spec A`. This file proves that the `A`-module
`Γ(Spec A, V)` is finite as soon as `Γ(Spec A_𝔭, V_𝔭)` is a finite `A_𝔭`-module for every prime
`𝔭`, where `V_𝔭` is the preimage of `V` under `Spec A_𝔭 ⟶ Spec A`. Both finiteness statements are
written as coherence of the direct image of the structure sheaf of the open, which over a
Noetherian affine base is the same thing and is the spelling that survives instance search at a
concrete localization.

This is the shape in which [Stacks, Tag 0BK1] consumes [Stacks, Tag 0AW9]: that tag says that
finiteness of local cohomology may be checked after localizing at every prime, and
[Stacks, Tag 0BK0] turns the question about `Γ(Spec A, V)` into one about `H¹_{V(I)}(A)`.

## Main results

* `Stacks.LocalCohomology.exists_eq_zeroLocusCompl`: an open of `Spec A` is the complement of
  the zero locus of an ideal.
* `Stacks.LocalCohomology.preimage_zeroLocusCompl`: the preimage of such an open along a map of
  spectra is the complement of the zero locus of the extended ideal.
* `Stacks.LocalCohomology.module_finite_sections_zeroLocusCompl_iff`: over a Noetherian ring,
  `Γ(Spec A, Spec A ∖ V(I))` is a finite `A`-module exactly when `H¹_{V(I)}(A)` is. This is
  clause (3) of [Stacks, Tag 0BK0] in degree zero, read on the sections.
* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_forall_localization`:
  **finiteness of the sections over an open of a Noetherian affine scheme is local on the
  base**, which is [Stacks, Tag 0AW9] in the form the induction of [Stacks, Tag 0BK1] uses.

## Implementation notes

The two models of local cohomology in this library — the derived `V(I)`-supported sections
`Stacks.LocalCohomology.localCohomologyWithSupportIn` of [Stacks, Tag 0EF4], in which clause (3)
of [Stacks, Tag 0BK0] is stated, and the coreflection model
`Stacks.LocalCohomology.localCohomologyModule` of [Stacks, Tag 0A6Q], in which
[Stacks, Tag 0AW9] is stated — are identified over a Noetherian ring by
`Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule`, which is
[Stacks, Tag 0955]. Everything below is stated in the coreflection model, which is the one
[Stacks, Tag 0AW9] and the localization comparison [Stacks, Tag 0ALZ] use.

Degree zero of the four-term sequence of [Stacks, Tag 0DWR] is what makes the degree shift
harmless: `H⁰_{V(I)}(A)` is a submodule of `A` and hence finite, so [Stacks, Tag 0AW9] at `n = 1`
only has content in degree one.

The localization step needs the `A_𝔭`-module structure, not merely the `A`-module structure, on
`H¹_{V(I A_𝔭)}(A_𝔭)`; `Stacks.LocalCohomology.localCohomologyModuleLocalizationIso` is an
isomorphism of `A`-modules, so `LinearMap.extendScalarsOfIsLocalization` is used to upgrade it.

## References

* [Stacks Project, Tag 0AW9](https://stacks.math.columbia.edu/tag/0AW9)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0BK1](https://stacks.math.columbia.edu/tag/0BK1)
* [Stacks Project, Tag 0ALZ](https://stacks.math.columbia.edu/tag/0ALZ)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.LocalCohomologySequence

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomology

/-! ### Presenting an open of an affine scheme as the complement of a zero locus -/

/-- **Every open of `Spec A` is the complement of the zero locus of an ideal.** The complement of
the open is closed, hence the zero locus of its vanishing ideal. -/
theorem exists_eq_zeroLocusCompl (R : CommRingCat.{u}) (V : (Spec R).Opens) :
    ∃ I : Ideal (ToType R), V = zeroLocusCompl I := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
      ((V : Set (Spec R))ᶜ)).mp (isClosed_compl_iff.mpr V.isOpen)
  exact ⟨I, TopologicalSpace.Opens.ext ((compl_compl _).symm.trans (congrArg compl hI))⟩

/-- **The preimage of the complement of a zero locus is the complement of the zero locus of the
extended ideal.** -/
theorem preimage_zeroLocusCompl {R S : CommRingCat.{u}} (f : R ⟶ S) (I : Ideal (ToType R)) :
    Spec.map f ⁻¹ᵁ zeroLocusCompl I = zeroLocusCompl (I.map f.hom) := by
  have h1 : PrimeSpectrum.comap f.hom ⁻¹' (PrimeSpectrum.zeroLocus (I : Set (ToType R))) =
      PrimeSpectrum.zeroLocus ((I.map f.hom : Ideal (ToType S)) : Set (ToType S)) :=
    (PrimeSpectrum.preimage_comap_zeroLocus f.hom _).trans
      (PrimeSpectrum.zeroLocus_span (f.hom '' (I : Set (ToType R)))).symm
  exact TopologicalSpace.Opens.ext (Set.preimage_compl.trans (congrArg compl h1))

/-! ### Sections over the complement of a zero locus, and local cohomology in degree one -/

/-- The zeroth higher direct image of `Ã|_U` is the direct image of the structure sheaf of `U`:
`Ã` is `𝒪_{Spec A}` and the zeroth right derived functor of the left exact direct image is the
direct image itself. -/
private def rightDerivedZeroTildeSelfIso (R : CommRingCat.{u}) (I : Ideal (ToType R)) :
    (((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived 0).obj
        ((tilde (ModuleCat.of (ToType R) (ToType R))).restrict (zeroLocusCompl I).ι)) ≅
      (Scheme.Modules.pushforward (zeroLocusCompl I).ι).obj
        (SheafOfModules.unit (zeroLocusCompl I).toScheme.ringCatSheaf) :=
  ((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived 0).mapIso
      (tildeSelfRestrictUnitIso I) ≪≫
    (Functor.rightDerivedZeroIsoSelf
      (Scheme.Modules.pushforward (zeroLocusCompl I).ι)).app _

/-- Coherence of `R⁰j_*(Ã|_U)` is coherence of `j_*𝒪_U`. -/
private theorem isCoherent_rightDerivedZero_tildeSelf_iff (R : CommRingCat.{u})
    (I : Ideal (ToType R)) :
    (((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived 0).obj
        ((tilde (ModuleCat.of (ToType R) (ToType R))).restrict
          (zeroLocusCompl I).ι)).IsCoherent ↔
      ((Scheme.Modules.pushforward (zeroLocusCompl I).ι).obj
        (SheafOfModules.unit (zeroLocusCompl I).toScheme.ringCatSheaf)).IsCoherent :=
  ⟨fun h => by
    have := h
    exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      (rightDerivedZeroTildeSelfIso R I).symm,
   fun h => by
    have := h
    exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      (rightDerivedZeroTildeSelfIso R I)⟩

/-- Finiteness of the sections over `U = Spec A ∖ V(I)` is coherence of `j_*𝒪_U`. -/
private theorem module_finite_sections_zeroLocusCompl_iff_isCoherent (R : CommRingCat.{u})
    [IsNoetherianRing R] (I : Ideal (ToType R)) :
    Module.Finite (ToType R) Γ(Spec R, zeroLocusCompl I) ↔
      ((Scheme.Modules.pushforward (zeroLocusCompl I).ι).obj
        (SheafOfModules.unit (zeroLocusCompl I).toScheme.ringCatSheaf)).IsCoherent :=
  ⟨isCoherent_pushforward_structureSheaf_of_module_finite_sections R _,
    module_finite_sections_of_isCoherent R _⟩

/-- The two models of local cohomology agree in degree one, over a Noetherian ring. -/
private theorem finite_localCohomologyWithSupportIn_iff_localCohomologyModule
    (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal (ToType R)) :
    Module.Finite (ToType R) (localCohomologyWithSupportIn.{u, u} (ToType R)
        (PrimeSpectrum.zeroLocus (I : Set (ToType R)))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of (ToType R) (ToType R))) ((0 + 1 : ℕ) : ℤ)) ↔
      Module.Finite (ToType R) (localCohomologyModule (ToType R) I
        (Ideal.fg_of_isNoetherianRing I) (ModuleCat.of (ToType R) (ToType R)) 1) :=
  Module.Finite.equiv_iff (localCohomologyWithSupportInIsoLocalCohomologyModule (ToType R) I
    (Ideal.fg_of_isNoetherianRing I) (ModuleCat.of (ToType R) (ToType R)) 1).toLinearEquiv

/-- **Clause (3) of [Stacks, Tag 0BK0] in degree zero, read on the sections.** Let `A` be a
Noetherian ring, `I ⊆ A` an ideal and `U = Spec A ∖ V(I)`. Then `Γ(Spec A, U)` is a finite
`A`-module exactly when the local cohomology `H¹_{V(I)}(A)` is.

Finiteness of the sections is coherence of `j_*𝒪_U`
(`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_module_finite_sections` and
`Stacks.LocalCohomology.module_finite_sections_of_isCoherent`); that direct image is `R⁰j_*(Ã|_U)`
because `Ã` is the structure sheaf (`tildeSelfRestrictUnitIso`) and the zeroth right derived
functor of a left exact functor is the functor itself; its coherence is finiteness of
`H⁰(U, Ã)` by clause (3) (a) ⟺ (b) of [Stacks, Tag 0BK0] and then finiteness of `H¹_{V(I)}(A)`
by its (b) ⟺ (c); and the two models of local cohomology agree over a Noetherian ring by
[Stacks, Tag 0955]. -/
theorem module_finite_sections_zeroLocusCompl_iff (R : CommRingCat.{u}) [IsNoetherianRing R]
    (I : Ideal (ToType R)) :
    Module.Finite (ToType R) Γ(Spec R, zeroLocusCompl I) ↔
      Module.Finite (ToType R) (localCohomologyModule (ToType R) I
        (Ideal.fg_of_isNoetherianRing I) (ModuleCat.of (ToType R) (ToType R)) 1) := by
  have hfinA : Module.Finite R (ModuleCat.of (ToType R) (ToType R)) :=
    inferInstanceAs (Module.Finite (ToType R) (ToType R))
  exact (module_finite_sections_zeroLocusCompl_iff_isCoherent R I).trans
    ((isCoherent_rightDerivedZero_tildeSelf_iff R I).symm.trans
      ((moduleFinite_complementCohomologyBase_iff_isCoherent I
          (ModuleCat.of (ToType R) (ToType R)) 0).symm.trans
        ((finite_complementCohomologyBase_iff_finite_localCohomology I
            (ModuleCat.of (ToType R) (ToType R)) 0).trans
          (finite_localCohomologyWithSupportIn_iff_localCohomologyModule R I))))

/-! ### Finiteness of the sections is local on the base -/

/-- An `A`-linear isomorphism between a module over a localization `L` of `A` and an `L`-module
transports finiteness over `L`: an `A`-linear map between two `L`-modules is `L`-linear
(`LinearEquiv.extendScalarsOfIsLocalization`). -/
private theorem module_finite_of_restrictScalars_iso {A : Type u} [CommRing A]
    (S : Submonoid A) (L : Type u) [CommRing L] [Algebra A L] [IsLocalization S L]
    (Y : ModuleCat.{u} L) (N : Type u) [AddCommGroup N] [Module A N] [Module L N]
    [IsScalarTower A L N] (h : Module.Finite L Y)
    (e : (ModuleCat.restrictScalars (algebraMap A L)).obj Y ≅ ModuleCat.of A N) :
    Module.Finite L N := by
  have : IsScalarTower A L ((ModuleCat.restrictScalars (algebraMap A L)).obj Y) :=
    ⟨fun x y z => by
      rw [ModuleCat.restrictScalars.smul_def, Algebra.smul_def, mul_smul]
      rfl⟩
  have : Module.Finite L ((ModuleCat.restrictScalars (algebraMap A L)).obj Y) := h
  exact Module.Finite.equiv (e.toLinearEquiv.extendScalarsOfIsLocalization S L)

/-- `H⁰_{V(I)}(A)` is a finite `A`-module: the counit of the local cohomology adjunction embeds
it into `A`, which is Noetherian. -/
private theorem finite_localCohomologyModule_zero (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) :
    Module.Finite A (localCohomologyModule A I hI (ModuleCat.of A A) 0) :=
  Module.Finite.of_injective
    (localCohomologyZeroToModule.{u, u} A I hI (ModuleCat.of A A)).hom
    (localCohomologyZeroToModule_injective.{u, u} A I hI (ModuleCat.of A A))

/-- The localization at `𝔭` of `H^i_{V(I)}(A)` is finite over `A_𝔭` as soon as
`H^i_{V(I A_𝔭)}(A_𝔭)` is: the two are identified by [Stacks, Tag 0ALZ] in the form
`Stacks.LocalCohomology.localCohomologyModuleLocalizationIso`. -/
private theorem finite_localizedModule_localCohomologyModule (A : Type u) [CommRing A]
    (I : Ideal A) (hI : I.FG) (p : PrimeSpectrum A) (i : ℤ)
    (h : Module.Finite (Localization.AtPrime p.asIdeal)
      (localCohomologyModule (Localization.AtPrime p.asIdeal)
        (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
        (hI.map (algebraMap A (Localization.AtPrime p.asIdeal)))
        (ModuleCat.of (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) i)) :
    Module.Finite (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl
        (localCohomologyModule A I hI (ModuleCat.of A A) i)) :=
  module_finite_of_restrictScalars_iso p.asIdeal.primeCompl _ _ _ h
    (localCohomologyModuleLocalizationIso A I hI p i)

/-- **Finiteness of the sections over an open of a Noetherian affine scheme is local on the
base.** Let `A` be a Noetherian ring and `V` an open of `Spec A`. If the direct image of the
structure sheaf of the preimage `V_𝔭` of `V` in `Spec A_𝔭` is coherent for every prime `𝔭` of
`A`, then the direct image of the structure sheaf of `V` is coherent on `Spec A`.

This is [Stacks, Tag 0AW9] in the shape the reduction of [Stacks, Tag 0BK1] consumes it. The
open is the complement of the zero locus of an ideal `I` (`exists_eq_zeroLocusCompl`), and its
preimage is the complement of the zero locus of `I A_𝔭` (`preimage_zeroLocusCompl`); coherence of
either direct image is finiteness of local cohomology in degree one
(`module_finite_sections_zeroLocusCompl_iff`); the local cohomology of `A_𝔭` is the localization
of that of `A` by [Stacks, Tag 0ALZ]; and in degree zero finiteness is automatic because
`H⁰_{V(I)}(A)` is a submodule of `A`. [Stacks, Tag 0AW9] then concludes.

The hypothesis is stated as coherence of the direct image rather than as finiteness of the
sections because `Algebra ↑(CommRingCat.of C) Γ(Spec (CommRingCat.of C), U)` is not found by
instance search at a concrete `CommRingCat.of`, as the module docstring of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.LocalFinitenessDescent` records; the two are
equivalent by `Stacks.LocalCohomology.module_finite_sections_of_isCoherent` and
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_module_finite_sections`, which
may be *applied* at a concrete localization even though they cannot be *stated* there. -/
theorem isCoherent_pushforward_structureSheaf_of_forall_localization (R : CommRingCat.{u})
    [IsNoetherianRing R] (V : (Spec R).Opens)
    (h : ∀ p : PrimeSpectrum (ToType R),
      ((Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom
              (algebraMap (ToType R) (Localization.AtPrime p.asIdeal))) ⁻¹ᵁ V).ι).obj
        (SheafOfModules.unit.{u} (Spec.map (CommRingCat.ofHom
            (algebraMap (ToType R) (Localization.AtPrime p.asIdeal))) ⁻¹ᵁ
          V).toScheme.ringCatSheaf)).IsCoherent) :
    ((Scheme.Modules.pushforward V.ι).obj
      (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)).IsCoherent := by
  obtain ⟨I, rfl⟩ := exists_eq_zeroLocusCompl R V
  refine (module_finite_sections_zeroLocusCompl_iff_isCoherent R I).mp ?_
  rw [module_finite_sections_zeroLocusCompl_iff R I]
  refine (localCohomology_finite_iff_localizations_finite.{u, u} (ToType R) I (ToType R) 1).mpr
    ?_ 1 le_rfl
  intro p i hi
  have hLnoeth : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  have : IsNoetherianRing (CommRingCat.of (Localization.AtPrime p.asIdeal)) := hLnoeth
  refine finite_localizedModule_localCohomologyModule (ToType R) I
    (Ideal.fg_of_isNoetherianRing I) p (i : ℤ) ?_
  match i with
  | 0 => exact finite_localCohomologyModule_zero (Localization.AtPrime p.asIdeal) _ _
  | 1 =>
    have hp := h p
    rw [preimage_zeroLocusCompl] at hp
    exact (module_finite_sections_zeroLocusCompl_iff
        (CommRingCat.of (Localization.AtPrime p.asIdeal)) _).mp
      ((module_finite_sections_zeroLocusCompl_iff_isCoherent
        (CommRingCat.of (Localization.AtPrime p.asIdeal)) _).mpr hp)
  | (n + 2) => exact absurd hi (by omega)

end Stacks.LocalCohomology

end
