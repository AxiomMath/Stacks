module

public import StacksFrontier.RingTheory.Flat.FinitePresentationOfFlatFinite
public import StacksFrontier.RingTheory.Flat.FlatLocusFiniteModuleOpenness
public import StacksFrontier.RingTheory.Flat.OpenFlatLocusFiniteModule
public import StacksFrontier.RingTheory.FinitePresentation.Relative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative flat locus over an algebra of finite type, and flat algebras over a domain

Let `R → S` be a ring map of finite type and let `M` be a finite `S`-module. The relative flat
locus `{q ⊂ S prime | M_q flat over R}` is open in `Spec S` as soon as `R` has only finitely many
weakly associated primes, and under the same hypothesis a finite `S`-module which is flat over
`R` is finitely presented. Over a domain the hypothesis is automatic, and the two conclusions are
the two parts of Stacks 053G.

The passage from finite type to finite presentation is a choice of surjection
`R[x_1, …, x_n] → S`, which makes `M` a finite module over the polynomial ring; the polynomial
ring is of finite presentation over `R`, so the results of
`StacksFrontier/RingTheory/Flat/FlatLocusFiniteModule.lean` apply to it.

## Main results

* `Stacks.Flatness.isOpen_setOf_flat_localizedModule_atPrime_of_finiteType` is the openness
  assertion of Stacks 05IR.
* `Stacks.Flatness.finitePresentationRel_localizedModule_away_of_basicOpen_subset_flatLocus` is
  the relative-finite-presentation assertion of Stacks 05IR.
* `Stacks.Flatness.finitePresentation_of_finite_of_flat_of_finiteType` and
  `Stacks.Flatness.finitePresentation_of_flat_of_finiteType`: a finite flat module, and a flat
  algebra, of finite type over a ring with finitely many weakly associated primes are finitely
  presented.
* `Stacks.Flatness.finitePresentation_of_flat_of_finiteType_of_isDomain` and
  `Stacks.Flatness.finitePresentation_of_finite_of_flat_of_isDomain` are the two parts of
  Stacks 053G, the case of a domain.

## Implementation notes

Everything here rests on `Stacks.Flatness.ExistsAwayFlatFinitePresentationOfFlatAtPrime`, the
affine content of Stacks 05IK, which is the theorem
`Stacks.Flatness.existsAwayFlatFinitePresentationOfFlatAtPrime`; it reaches the statements below
through Stacks 05IL in
`StacksFrontier/RingTheory/Flat/FlatLocusFiniteModuleOpenness.lean`.

Openness is reduced to the polynomial case by
`Module.isOpen_setOf_flat_localizedModule_atPrime_of_mvPolynomial`. The finite-presentation
statements do *not* use the two reductions of
`StacksFrontier/RingTheory/Flat/FinitePresentationOfFlatFinite.lean`, whose hypothesis — that every
finite module over a polynomial ring which is flat over the base is finitely presented over it —
is refuted by `Module.not_forall_finitePresentation_mvPolynomial_of_finite_of_flat`; the
finiteness of the weakly associated primes of the base is exactly what is missing there, so the
reduction is carried out here instead, where that hypothesis is available. Its two ingredients
are `Module.FinitePresentation.of_restrictScalars_of_finiteType`, which descends finite
presentation along the surjection, and
`Algebra.FinitePresentation.of_surjective_of_finitePresentation_module` for the algebra
conclusion.

The flatness hypothesis of these statements is global, so every localization of the module is
flat over `R` (`Module.Flat.of_isLocalizedModule_of_tower`), which is what
`Stacks.Flatness.finitePresentation_of_forall_flat_localizedModule_atPrime` consumes. Over a
domain the only weakly associated prime is the zero ideal
(`weaklyAssociatedPrimes_finite_of_isDomain`).

The remaining assertion of Stacks 05IR, that `M_g` is flat over `R`, holds with no hypothesis
on the base and is
`Stacks.Flatness.OpenFlatLocus.flat_localizedModule_away_of_forall_flat_atPrime`. The relative
finite presentation of `M_g` does not follow from its finite presentation as an `S_g`-module,
because `S_g` need not be of finite presentation over `R`; what is needed is a *polynomial*
presentation of `S_g`, and `S_g` is of finite type over `R` because the away localization is of
finite presentation over `S` (`IsLocalization.Away.finitePresentation`). Any surjection
`R[x_1, …, x_m] → S_g` then works, since `M_g` is finite over the polynomial ring and flat over
`R`, so Stacks 053G's ungraded form applies to it.

## References

* [Stacks Project, Tag 05IR](https://stacks.math.columbia.edu/tag/05IR)
* [Stacks Project, Tag 053G](https://stacks.math.columbia.edu/tag/053G)
-/

@[expose] public section

universe u v w

namespace Stacks.Flatness

/-- **Stacks Project, Tag 05IR (openness).** For a ring map `R → S` of finite type and a finite
`S`-module `M`, the locus of primes `q` of `S` at which `M_q` is flat over `R` is open in
`Spec S`, provided `R` has only finitely many weakly associated primes. -/
@[stacks 05IR "openness of the relative flat locus",
  ega "IV 11.1.6" "case C = B",
  ega "IV 11.3.3" "WeakAss finite"]
theorem isOpen_setOf_flat_localizedModule_atPrime_of_finiteType
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    {M : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite S M] (hR : (weaklyAssociatedPrimes R R).Finite) :
    IsOpen {q : PrimeSpectrum S | Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)} :=
  Module.isOpen_setOf_flat_localizedModule_atPrime_of_mvPolynomial
    fun _ _ _ _ _ _ =>
      isOpen_setOf_flat_localizedModule_atPrime_of_finite_weaklyAssociatedPrimes hR

/-- **A finite flat module over an algebra of finite type is finitely presented.** Let `R → S` be
of finite type with `R` having only finitely many weakly associated primes, and let `M` be a
finite `S`-module which is flat over `R`. Then `M` is a finitely presented `S`-module. -/
theorem finitePresentation_of_finite_of_flat_of_finiteType
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    {M : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite S M] [Module.Flat R M] (hR : (weaklyAssociatedPrimes R R).Finite) :
    Module.FinitePresentation S M := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  let P := MvPolynomial (Fin n) R
  let : Algebra P S := f.toRingHom.toAlgebra
  let : Module P M := Module.compHom M f.toRingHom
  let : IsScalarTower P S M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R P M := IsScalarTower.of_algebraMap_smul fun r m => by
    change f (algebraMap R P r) • m = r • m
    rw [f.commutes, algebraMap_smul]
  let : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have hsurj : Function.Surjective (algebraMap P S) := hf
  have : Module.Finite P S := Module.Finite.of_surjective (Algebra.linearMap P S) hsurj
  have : Module.Finite P M := Module.Finite.trans (R := P) S M
  have : Module.FinitePresentation P M :=
    finitePresentation_of_forall_flat_localizedModule_atPrime hR fun q =>
      Module.Flat.of_isLocalizedModule_of_tower q.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
  exact Module.FinitePresentation.of_restrictScalars_of_finiteType P S M

/-- **A flat algebra of finite type is of finite presentation.** Let `R → S` be of finite type and
flat, with `R` having only finitely many weakly associated primes. Then `S` is of finite
presentation over `R`. -/
theorem finitePresentation_of_flat_of_finiteType
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [Module.Flat R S] (hR : (weaklyAssociatedPrimes R R).Finite) :
    Algebra.FinitePresentation R S := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  let P := MvPolynomial (Fin n) R
  let : Algebra P S := f.toRingHom.toAlgebra
  let : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have hsurj : Function.Surjective (algebraMap P S) := hf
  have : Module.Finite P S := Module.Finite.of_surjective (Algebra.linearMap P S) hsurj
  have : Module.FinitePresentation P S :=
    finitePresentation_of_forall_flat_localizedModule_atPrime hR fun q =>
      Module.Flat.of_isLocalizedModule_of_tower q.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl S)
  exact Algebra.FinitePresentation.of_surjective_of_finitePresentation_module hsurj

/-- **Stacks Project, Tag 053G, part (1).** A flat algebra of finite type over a domain is of
finite presentation. -/
@[stacks 053G "(1): a flat algebra of finite type over a domain is of finite presentation"]
theorem finitePresentation_of_flat_of_finiteType_of_isDomain
    {R : Type u} [CommRing R] [IsDomain R] {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Module.Flat R S] :
    Algebra.FinitePresentation R S :=
  finitePresentation_of_flat_of_finiteType (weaklyAssociatedPrimes_finite_of_isDomain R)

/-- **Stacks Project, Tag 053G, part (2).** A finite module over an algebra of finite type over a
domain is finitely presented as soon as it is flat over the domain. -/
@[stacks 053G "(2): a finite module flat over a domain is finitely presented"]
theorem finitePresentation_of_finite_of_flat_of_isDomain
    {R : Type u} [CommRing R] [IsDomain R] {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] {M : Type w} [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] [Module.Finite S M] [Module.Flat R M] :
    Module.FinitePresentation S M :=
  finitePresentation_of_finite_of_flat_of_finiteType
    (weaklyAssociatedPrimes_finite_of_isDomain R)

/-- **Stacks Project, Tag 05IR (relative finite presentation on a basic open).** For a ring map
`R → S` of finite type and a finite `S`-module `M`, if the basic open `D(g)` is contained in the
locus where `M` is flat over `R`, then `M_g` is an `S_g`-module finitely presented relative to
`R`, provided `R` has only finitely many weakly associated primes. -/
@[stacks 05IR "relative finite presentation on a basic open inside the flat locus"]
theorem finitePresentationRel_localizedModule_away_of_basicOpen_subset_flatLocus
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    {M : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    [Module.Finite S M] (hR : (weaklyAssociatedPrimes R R).Finite) (g : S)
    (hg : (↑(PrimeSpectrum.basicOpen g) : Set (PrimeSpectrum S)) ⊆
      {q : PrimeSpectrum S | Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)}) :
    Module.FinitePresentationRel R (Localization.Away g) (LocalizedModule.Away g M) := by
  have hflat : Module.Flat R (LocalizedModule.Away g M) :=
    OpenFlatLocus.flat_localizedModule_away_of_forall_flat_atPrime g fun q hq => hg hq
  have hft : Algebra.FiniteType R (Localization.Away g) :=
    Algebra.FiniteType.trans (R := R) (S := S) (A := Localization.Away g) inferInstance
      inferInstance
  obtain ⟨m, α, hα⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  set A := Localization.Away g
  set N := LocalizedModule.Away g M
  let P := MvPolynomial (Fin m) R
  -- transport the module along the chosen polynomial presentation of `S_g`
  let : Algebra P A := α.toRingHom.toAlgebra
  let : Module P N := Module.compHom N α.toRingHom
  let : IsScalarTower P A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R P N := IsScalarTower.of_algebraMap_smul fun r x => by
    change α (algebraMap R P r) • x = r • x
    rw [α.commutes, algebraMap_smul]
  let : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq' α.comp_algebraMap.symm
  have hsurj : Function.Surjective (algebraMap P A) := hα
  have : Module.Finite P A := Module.Finite.of_surjective (Algebra.linearMap P A) hsurj
  have : Module.Finite P N := Module.Finite.trans (R := P) A N
  exact ⟨m, α, hα, finitePresentation_of_finite_of_flat_of_finiteType hR⟩

end Stacks.Flatness
