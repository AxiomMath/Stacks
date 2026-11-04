module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.ZeroLocusComplBridge
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.OpenExtension
public import StacksCore.Tactic.StacksAttribute

/-!
# Extending a quasi-coherent module from an open of an affine scheme

For a finitely generated ideal `I` of a ring `R`, every quasi-coherent module on the open
complement `Spec R \ V(I)` is the restriction of the module sheaf associated to an `R`-module.
This is the first step in computing the cohomology of such a module in terms of the local
cohomology of an `R`-module along `V(I)`.

## Main definitions

* `Stacks.LocalCohomology.complementZeroLocus` (imported) is the open complement of the zero locus
  of an ideal in an affine spectrum.

## Main results

* `Stacks.LocalCohomology.exists_module_iso_restrict_tilde` gives an `R`-module whose associated
  sheaf restricts to a given quasi-coherent module on that complement.
* `Stacks.LocalCohomology.exists_finiteModule_iso_restrict_tilde` gives a *finite* such module
  when `R` is Noetherian and the given module is coherent.

## Implementation notes

The open subscheme `Spec R \ V(I)` is represented by the scheme attached to the open
`complementZeroLocus R I`. Restriction is Mathlib's restriction of modules along the canonical
open immersion, and the associated module sheaf is `AlgebraicGeometry.tilde.functor`. Finite
generation of `I` enters only through quasi-compactness of that open immersion, which is what
makes the extension available.

The finite version is the same statement as
`AlgebraicGeometry.exists_finiteModule_tilde_restrict_zeroLocusCompl`, by
`AlgebraicGeometry.zeroLocusCompl_eq_complementZeroLocus`; coherence of the module is passed
explicitly because instance synthesis does not see that equality.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology

-- `Stacks.LocalCohomology.complementZeroLocus`, the open complement of the zero locus of an
-- ideal in an affine spectrum, is defined in
-- `StacksFrontier.RingTheory.LocalCohomology.LowDegree` and imported above; the definition is not
-- repeated here.

/-- **Stacks Project, Tag 0DWR.** Every quasi-coherent module on the complement of the zero
locus of a finitely generated ideal in an affine spectrum is the restriction of the sheaf
associated to a module. -/
@[stacks 0DWR "extension"]
theorem exists_module_iso_restrict_tilde
    (R : Type u) [CommRing R] (I : Ideal R) (_hI : I.FG)
    (F : (complementZeroLocus R I : Scheme).Modules) [F.IsQuasicoherent] :
    ∃ M : ModuleCat.{u} R,
      Nonempty
        (F ≅ ((tilde.functor (CommRingCat.of R)).obj M).restrict
          (complementZeroLocus R I).ι) := by
  let U := complementZeroLocus R I
  have : QuasiCompact U.ι :=
    quasiCompact_iff_isSpectralMap.mpr
      (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp
        (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg _hI))
  obtain ⟨G, hG, ⟨eGF⟩⟩ :=
    AlgebraicGeometry.exists_quasicoherent_restrict_iso U.ι F
  let q : (SheafOfModules.isQuasicoherent
      (Spec (CommRingCat.of R)).ringCatSheaf).FullSubcategory := ⟨G, hG⟩
  let M : ModuleCat.{u} R := (tildeEquiv (R := CommRingCat.of R)).inverse.obj q
  exact ⟨M, ⟨eGF.symm.trans ((Scheme.Modules.restrictFunctor U.ι).mapIso
    ((ObjectProperty.ι _).mapIso
      (((tildeEquiv (R := CommRingCat.of R)).counitIso.app q).symm)))⟩⟩

/-- Over a Noetherian ring, a coherent module on the complement of the zero locus of an ideal in
an affine spectrum is the restriction of the sheaf associated to a *finite* module. This is
Stacks 0BK0 (1), in the `complementZeroLocus` spelling of that open. -/
@[ega "I 1.5.1" "a) ⇒ c)", ega "I 1.5.3", ega "I 9.4.8" "special case"]
theorem exists_finiteModule_iso_restrict_tilde
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (F : (complementZeroLocus R I : Scheme).Modules) [hF : F.IsCoherent] :
    ∃ M : ModuleCat.{u} R, Module.Finite R M ∧
      Nonempty
        (F ≅ ((tilde.functor (CommRingCat.of R)).obj M).restrict
          (complementZeroLocus R I).ι) := by
  obtain ⟨M, hMfin, ⟨e⟩⟩ :=
    @AlgebraicGeometry.exists_finiteModule_tilde_restrict_zeroLocusCompl
      (CommRingCat.of R) ‹IsNoetherianRing R› I F hF
  exact ⟨M, hMfin, ⟨e.symm⟩⟩

end Stacks.LocalCohomology
