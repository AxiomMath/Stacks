module

import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.StalkFinitePresentationAffine

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.FlatLocusFiniteModule

/-!
# Openness of the relative flat locus of a finite module, and finite presentation on it

Let `R → S` be a ring map of finite presentation and let `M` be a *finite* `S`-module. The
relative flat locus `U = {q ⊂ S prime | M_q flat over R}` is open in `Spec S` as soon as `R` has
only finitely many weakly associated primes, and `M` becomes finitely presented on every basic
open contained in `U`. Those are two of the three assertions of Stacks 05IL.

Both are formal consequences of the affine content of Stacks 05IK,
`Stacks.Flatness.ExistsAwayFlatFinitePresentationOfFlatAtPrime`: openness because flatness on a
basic open gives flatness at each of its primes
(`Module.Flat.localizedModule_atPrime_of_away`), and finite presentation because finite
presentation is Zariski-local (`Module.FinitePresentation.of_localizationSpan`), which turns the
local statement into finite presentation of a module flat at every prime; the assertion on a
basic open `D(g)` is that statement applied to `R → S_g` and `M_g`, for which the primes of `S_g`
are the primes of `S` in `D(g)` and `(M_g)_P` is `M_{P ∩ S}` by composing two localizations.

## Main results

* `Stacks.Flatness.isOpen_setOf_flat_localizedModule_atPrime_of_finite_weaklyAssociatedPrimes`
  is the openness assertion of Stacks 05IL.
* `Stacks.Flatness.finitePresentation_of_forall_flat_localizedModule_atPrime`: a finite module
  which is flat over the base at every prime is finitely presented.
* `Stacks.Flatness.finitePresentation_localizedModule_away_of_basicOpen_subset_flatLocus` is the
  finite-presentation assertion of Stacks 05IL.

Flatness over `R` on a basic open contained in `U` is the remaining assertion of Stacks 05IL and
needs none of this: it is
`Stacks.Flatness.OpenFlatLocus.flat_localizedModule_away_of_forall_flat_atPrime`.

## Implementation notes

These three statements live here rather than beside
`Stacks.Flatness.ExistsAwayFlatFinitePresentationOfFlatAtPrime` in
`StacksFrontier/RingTheory/Flat/FlatLocusFiniteModule.lean`, where that definition is made, because
the theorem that discharges it —
`Stacks.Flatness.existsAwayFlatFinitePresentationOfFlatAtPrime` — is proved through the geometry
of Stacks 05I5 and 05I7, and therefore *below* the module making the definition. A file stating
the definition cannot import its own proof.

That proof is reached by a non-`public` import, so the instances of the geometric development do
not propagate to the ring-theoretic consumers of this file; in particular the module structure on
the stalk of a sheaf of modules does not become visible to them.

## References

* [Stacks Project, Tag 05IL](https://stacks.math.columbia.edu/tag/05IL)
* [Stacks Project, Tag 05IK](https://stacks.math.columbia.edu/tag/05IK)
-/

public section

universe u v w

namespace Stacks.Flatness

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
  [Algebra.FinitePresentation R S] {M : Type w} [AddCommGroup M] [Module S M] [Module R M]
  [IsScalarTower R S M] [Module.Finite S M]

/-- **Stacks Project, Tag 05IL (openness).** For a ring map `R → S` of finite presentation and a
finite `S`-module `M`, the locus of primes `q` of `S` at which `M_q` is flat over `R` is open in
`Spec S`, provided `R` has only finitely many weakly associated primes. -/
@[stacks 05IL "openness of the relative flat locus",
  ega "IV 11.1.6" "case C = B",
  ega "IV 11.3.3" "WeakAss finite"]
theorem isOpen_setOf_flat_localizedModule_atPrime_of_finite_weaklyAssociatedPrimes
    (hR : (weaklyAssociatedPrimes R R).Finite) :
    IsOpen {q : PrimeSpectrum S | Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)} := by
  rw [isOpen_iff_forall_mem_open]
  intro q hq
  obtain ⟨g, hgq, -, hflat⟩ := existsAwayFlatFinitePresentationOfFlatAtPrime R S M hR q hq
  refine ⟨PrimeSpectrum.basicOpen g, fun q' hq' => ?_, (PrimeSpectrum.basicOpen g).2, hgq⟩
  have : Module.Flat R (LocalizedModule.Away g M) := hflat
  exact Module.Flat.localizedModule_atPrime_of_away q'.asIdeal g
    ((PrimeSpectrum.mem_basicOpen g q').mp hq')

/-- **A finite module flat over the base at every prime is finitely presented.** For a ring map
`R → S` of finite presentation whose source has finitely many weakly associated primes, a finite
`S`-module all of whose localizations at primes are flat over `R` is a finitely presented
`S`-module.

Finite presentation is Zariski-local, and the local statement produces, around each prime, a
basic open on which the module is finitely presented. -/
theorem finitePresentation_of_forall_flat_localizedModule_atPrime
    (hR : (weaklyAssociatedPrimes R R).Finite)
    (hflat : ∀ q : PrimeSpectrum S, Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)) :
    Module.FinitePresentation S M := by
  classical
  set s : Set S := {g | Module.FinitePresentation (Localization.Away g)
    (LocalizedModule.Away g M)} with hs
  refine Module.FinitePresentation.of_localizationSpan s ?_ fun g => g.2
  by_contra hne
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_le_maximal (Ideal.span s) hne
  obtain ⟨g, hgP, hfp, -⟩ :=
    existsAwayFlatFinitePresentationOfFlatAtPrime R S M hR ⟨P, hP.isPrime⟩ (hflat _)
  exact hgP (hPle (Ideal.subset_span hfp))

/-- **Stacks Project, Tag 05IL (finite presentation on a basic open).** For a ring map `R → S` of
finite presentation and a finite `S`-module `M`, if the basic open `D(g)` is contained in the
locus where `M` is flat over `R`, then `M_g` is a finitely presented `S_g`-module, provided `R`
has only finitely many weakly associated primes. -/
@[stacks 05IL "finite presentation on a basic open inside the flat locus"]
theorem finitePresentation_localizedModule_away_of_basicOpen_subset_flatLocus
    (hR : (weaklyAssociatedPrimes R R).Finite) (g : S)
    (hg : (↑(PrimeSpectrum.basicOpen g) : Set (PrimeSpectrum S)) ⊆
      {q : PrimeSpectrum S | Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)}) :
    Module.FinitePresentation (Localization.Away g) (LocalizedModule.Away g M) := by
  have : Algebra.FinitePresentation S (Localization.Away g) :=
    IsLocalization.Away.finitePresentation g
  have : Algebra.FinitePresentation R (Localization.Away g) :=
    Algebra.FinitePresentation.trans R S (Localization.Away g)
  refine finitePresentation_of_forall_flat_localizedModule_atPrime (R := R)
    (S := Localization.Away g) (M := LocalizedModule.Away g M) hR fun P => ?_
  set A := Localization.Away g with hA
  set N := LocalizedModule.Away g M with hN
  -- a prime `P` of `S_g` lies over a prime of `S` in `D(g)`, and `(M_g)_P` is `M` localized there
  have hPprime : P.asIdeal.IsPrime := P.isPrime
  let q : Ideal S := P.asIdeal.comap (algebraMap S A)
  have hqprime : q.IsPrime := Ideal.comap_isPrime _ _
  have hgq : g ∉ q := fun hmem =>
    hPprime.ne_top (P.asIdeal.eq_top_of_isUnit_mem hmem
      (IsLocalization.Away.algebraMap_isUnit g))
  have hbc1 : IsBaseChange A (LocalizedModule.mkLinearMap (Submonoid.powers g) M) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) A _).mp inferInstance
  have hbc2 : IsBaseChange (Localization.AtPrime P.asIdeal)
      (LocalizedModule.mkLinearMap P.asIdeal.primeCompl N) :=
    (isLocalizedModule_iff_isBaseChange P.asIdeal.primeCompl _ _).mp inferInstance
  have hloc : IsLocalizedModule q.primeCompl
      ((LocalizedModule.mkLinearMap P.asIdeal.primeCompl N).restrictScalars S ∘ₗ
        LocalizedModule.mkLinearMap (Submonoid.powers g) M) :=
    (isLocalizedModule_iff_isBaseChange _ (Localization.AtPrime P.asIdeal) _).mpr
      (hbc1.comp hbc2)
  have hq : Module.Flat R (LocalizedModule.AtPrime q M) :=
    hg ((PrimeSpectrum.mem_basicOpen g ⟨q, hqprime⟩).mpr hgq)
  exact Module.Flat.of_linearEquiv
    ((IsLocalizedModule.iso q.primeCompl
      ((LocalizedModule.mkLinearMap P.asIdeal.primeCompl N).restrictScalars S ∘ₗ
        LocalizedModule.mkLinearMap (Submonoid.powers g) M)).restrictScalars R).symm

end Stacks.Flatness

end
