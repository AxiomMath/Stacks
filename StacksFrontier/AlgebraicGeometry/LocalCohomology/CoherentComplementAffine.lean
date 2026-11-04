module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FiniteLocallyFreeComplementAffine
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.Generalities.ComplementCohomologyModule
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.GlobalSectionsFinite
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.LocalizationData
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology of a coherent module on the complement of a vanishing locus

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, let `X = Spec A`, let `Z = V(I)`, let
`U = X ∖ Z` and let `j : U → X` be the inclusion.  This file states [Stacks, Tag 0BK0] — its
clause (2), and then the whole four-clause lemma — as declarations of its own, assembled from
the pieces that prove the clauses and that are scattered over the local cohomology trees.

Clause (2) says that for an `A`-module `M` and a sheaf `F` on `U` identified with `M̃|_U` there is
an exact sequence
`0 ⟶ H⁰_Z(M) ⟶ M ⟶ Γ(U, F) ⟶ H¹_Z(M) ⟶ 0`
and `A`-linear isomorphisms `H^p(U, F) ≅ H^{p+1}_Z(M)` in every degree `p ≥ 1`.

## Main results

* `Stacks.LocalCohomology.exact_lowDegreeSequence_and_nonempty_complementCohomology_iso` —
  **[Stacks, Tag 0BK0] (2).**
* `Stacks.LocalCohomology.coherent_complement_affine` — **[Stacks, Tag 0BK0]**, all four clauses
  in one statement.

## Implementation notes

The two halves of clause (2) are proved elsewhere and are only put into one statement here:
`Stacks.LocalCohomology.lowDegreeExactSequence` is the four-term sequence, and
`Stacks.LocalCohomology.nonempty_complementSheafCohomology_iso_localCohomologyModule` is the
comparison above degree zero, both for the given `F` and `M`.  Neither uses the Noetherian
hypothesis of the tag beyond the finite generation of `I`.

`H^p(U, F)` is `Stacks.LocalCohomology.complementSheafCohomology`: the right derived functor of
global sections on the open subscheme `U`, read over `R` along `R ≅ Γ(X, 𝒪_X) → Γ(U, 𝒪_U)`.
Clause (3) is stated with that same `H^p(U, F)` and with `R^pj_*F` for `F` itself.  The
equivalence (a) ⟺ (b) is [Stacks, Tag 01XK] over the affine base `X`,
`Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_cohomology_iff_isCoherent`, applied
to `F`; the equivalence (b) ⟺ (c) moves `H^p(U, F)` to `H^p(U, M̃|_U)` along the given
identification and then to the cohomology over `U` of `M̃` on `X` by
`Stacks.LocalCohomology.complementSheafCohomologyTildeIso`, where
`Stacks.LocalCohomologySequence.finite_complementCohomologyBase_iff_finite_localCohomology`
applies.

The hypothesis `hI : I.FG` is implied by `[IsNoetherianRing R]` through
`Ideal.fg_of_isNoetherianRing`; it is carried explicitly only because the finite generation is
what the four-term sequence's localization data is built from, and it appears in the types of the
local cohomology modules below.

The four-clause statement takes the four clauses from, in order,
`AlgebraicGeometry.exists_finiteModule_tilde_restrict` (clause (1), at the quasi-compact open
`U`), the clause (2) statement above, the pair
`Stacks.LocalCohomologySequence.moduleFinite_complementCohomologyBase_iff_isCoherent` and
`Stacks.LocalCohomologySequence.finite_complementCohomologyBase_iff_finite_localCohomology`
(clause (3)), and
`Stacks.LocalCohomology.finite_iso_restrict_and_isZero_localCohomology_globalSectionsModule`
(clause (4)).  Everything is stated on `Stacks.LocalCohomology.complementZeroLocus R I`, the open
on which `F` is given, so no comparison with the definitionally equal open
`AlgebraicGeometry.zeroLocusCompl I` is needed: the criterion of [Stacks, Tag 01XK] is applied
directly to the inclusion of `complementZeroLocus R I`.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.LocalCohomologySequence Stacks.AlgebraicGeometry.ProperCohomologyFinite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomology

/-- **[Stacks, Tag 0BK0] (2).** Let `R` be a Noetherian ring, let `I ⊆ R` be an ideal, let
`X = Spec R`, let `Z = V(I)` and let `U = X ∖ Z`.  Let `M` be an `R`-module and let `F` be a
sheaf of modules on `U` identified with `M̃|_U`.  Then the four-term sequence
`0 ⟶ H⁰_Z(M) ⟶ M ⟶ Γ(U, F) ⟶ H¹_Z(M) ⟶ 0`
built from the canonical map out of local cohomology, the restriction map and the connecting map
of the localization triangle is exact, and `H^p(U, F) ≅ H^{p+1}_Z(M)` as `R`-modules for every
`p ≥ 1`, with `H^p(U, F)` the cohomology of `F` on `U` read over `R`
(`Stacks.LocalCohomology.complementSheafCohomology`).

Neither half needs `M` finite or `F` coherent, which the source assumes. -/
@[stacks 0BK0 "(2)",
  ega "III 1.4.3" "special case",
  sga "2 II Corollary4" "special case",
  sga "4 V 6.5" "special case"]
theorem exact_lowDegreeSequence_and_nonempty_complementCohomology_iso
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I.FG)
    (M : ModuleCat.{u} R) (F : (complementZeroLocus R I : Scheme).Modules)
    (e : F ≅ complementTilde R I M) :
    (∃ D : LocalizationTriangleData.{u, u} R I hI,
        Function.Injective (localCohomologyZeroToModule R I hI M) ∧
        Function.Exact (localCohomologyZeroToModule R I hI M)
          (restrictionToComplement D M F e) ∧
        Function.Exact (restrictionToComplement D M F e) (localizationBoundary D M F e) ∧
        Function.Surjective (localizationBoundary D M F e)) ∧
      ∀ p : ℕ, 1 ≤ p →
        Nonempty ((complementSheafCohomology R I p).obj F ≅
          localCohomologyModule R I hI M ((p + 1 : ℕ) : ℤ)) := by
  refine ⟨?_, fun p hp ↦ ?_⟩
  · obtain ⟨D, hD⟩ := lowDegreeExactSequence.{u, u} R I hI
    exact ⟨D, hD M F e⟩
  · exact nonempty_complementSheafCohomology_iso_localCohomologyModule R I hI M F e p hp

/-- **[Stacks, Tag 0BK0].** Let `R` be a Noetherian ring, let `I ⊆ R` be an ideal, let
`X = Spec R`, let `Z = V(I)`, let `U = X ∖ Z` and let `j : U → X` be the inclusion.  Let `F` be a
coherent `𝒪_U`-module.  Then

1. there is a finite `R`-module `M` such that `F` is the restriction of `M̃` to `U`;
2. given `M` there is an exact sequence
   `0 ⟶ H⁰_Z(M) ⟶ M ⟶ Γ(U, F) ⟶ H¹_Z(M) ⟶ 0`
   and isomorphisms `H^p(U, F) ≅ H^{p+1}_Z(M)` for `p ≥ 1`;
3. given `M` and `p ≥ 0` the following are equivalent: `R^pj_*F` is coherent, `H^p(U, F)` is a
   finite `R`-module, and `H^{p+1}_Z(M)` is a finite `R`-module;
4. if the equivalent conditions of (3) hold for `p = 0` then `M` may be taken to be `Γ(U, F)`,
   which is then a finite `R`-module whose associated sheaf restricts to `F` on `U` and which
   satisfies `H⁰_Z(Γ(U, F)) = H¹_Z(Γ(U, F)) = 0`.

Clauses (2), (3) and (4) are stated for every finite `M` identifying `F` with `M̃|_U`, which is
what "given `M`" means: the identification is part of the data and clause (1) produces one.
`H^p(U, F)` is the cohomology of `F` on `U` read over `R`
(`Stacks.LocalCohomology.complementSheafCohomology`) and `j` is the inclusion of `U`; clause
(4)'s hypothesis is condition (c) of clause (3) in degree zero.  The
hypothesis `hI : I.FG` is implied by `[IsNoetherianRing R]` through
`Ideal.fg_of_isNoetherianRing`.

Each clause is also registered on the declaration that proves it; nothing new is proved here. -/
@[stacks 0BK0]
theorem coherent_complement_affine
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I.FG)
    (F : (complementZeroLocus R I : Scheme).Modules) [F.IsCoherent] :
    (∃ M : ModuleCat.{u} R, Module.Finite R M ∧ Nonempty (F ≅ complementTilde R I M)) ∧
      ∀ M : ModuleCat.{u} R, Module.Finite R M → ∀ e : F ≅ complementTilde R I M,
        ((∃ D : LocalizationTriangleData.{u, u} R I hI,
              Function.Injective (localCohomologyZeroToModule R I hI M) ∧
              Function.Exact (localCohomologyZeroToModule R I hI M)
                (restrictionToComplement D M F e) ∧
              Function.Exact (restrictionToComplement D M F e)
                (localizationBoundary D M F e) ∧
              Function.Surjective (localizationBoundary D M F e)) ∧
            ∀ p : ℕ, 1 ≤ p →
              Nonempty ((complementSheafCohomology R I p).obj F ≅
                localCohomologyModule R I hI M ((p + 1 : ℕ) : ℤ))) ∧
          (∀ p : ℕ,
            [(((Scheme.Modules.pushforward (complementZeroLocus R I).ι).rightDerived p).obj
                F).IsCoherent,
              Module.Finite R ((complementSheafCohomology R I p).obj F),
              Module.Finite R (localCohomologyModule R I hI M ((p + 1 : ℕ) : ℤ))].TFAE) ∧
          (Module.Finite R (localCohomologyModule R I hI M 1) →
            Module.Finite R (complementGlobalSections R I F) ∧
              Nonempty (F ≅ complementTilde R I (complementGlobalSections R I F)) ∧
              IsZero (localCohomologyModule R I hI (complementGlobalSections R I F) 0) ∧
              IsZero (localCohomologyModule R I hI (complementGlobalSections R I F) 1)) := by
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have := hqc
  have := hft
  refine ⟨?_, fun M hM e ↦ ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨N, hN, ⟨g⟩⟩ := exists_finiteModule_tilde_restrict (A := CommRingCat.of R)
      (complementZeroLocus R I) (isCompact_zeroLocusCompl (A := CommRingCat.of R) I) F
    exact ⟨N, hN, ⟨g.symm⟩⟩
  · exact exact_lowDegreeSequence_and_nonempty_complementCohomology_iso R I hI M F e
  · have := hM
    intro p
    have hmodel : Module.Finite R (localCohomologyWithSupportIn.{u, u} R
          (PrimeSpectrum.zeroLocus (I : Set R))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ((p + 1 : ℕ) : ℤ)) ↔
        Module.Finite R (localCohomologyModule R I hI M ((p + 1 : ℕ) : ℤ)) :=
      ⟨fun _ ↦ Module.Finite.equiv
          (localCohomologyWithSupportInIsoLocalCohomologyModule R I hI M _).toLinearEquiv,
        fun _ ↦ Module.Finite.equiv
          (localCohomologyWithSupportInIsoLocalCohomologyModule R I hI M _).symm.toLinearEquiv⟩
    tfae_have 1 ↔ 2 :=
      (Iff.trans (Module.finite_restrictScalars_ringEquiv_iff
          (Stacks.LocalCohomologyTilde.baseRingEquiv (CommRingCat.of R))
          ((ModuleCat.restrictScalars (complementZeroLocus R I).ι.appTop.hom).obj
            (((Stacks.Cohomology.AffineBase.moduleGlobalSections
              (complementZeroLocus R I : Scheme)).rightDerived p).obj F)))
        (moduleFinite_cohomology_iff_isCoherent (complementZeroLocus R I).ι F p)).symm
    tfae_have 2 ↔ 3 :=
      (Module.finite_iff_of_moduleCat_iso ((complementSheafCohomology R I p).mapIso e ≪≫
          complementSheafCohomologyTildeIso R I M p)).trans
        ((finite_complementCohomologyBase_iff_finite_localCohomology
          (A := CommRingCat.of R) I M p).trans hmodel)
    tfae_finish
  · have := hM
    exact finite_iso_restrict_and_isZero_localCohomology_globalSectionsModule R I hI F M e

end Stacks.LocalCohomology

end
