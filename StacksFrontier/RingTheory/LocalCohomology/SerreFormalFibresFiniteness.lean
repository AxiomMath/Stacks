module

public import StacksFrontier.RingTheory.LocalCohomology.Cutoff.Attainment
public import StacksFrontier.RingTheory.LocalCohomology.CutoffCompletionSerre
public import StacksFrontier.RingTheory.LocalCohomology.FaltingsFiniteness

/-!
# Finiteness of local cohomology under a Serre condition on the formal fibres

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, let `Z = V(I) ⊆ Spec(A)` and let `M` be a
finite `A`-module. Write `s = s_{A,I}(M)` for the local cohomology finiteness cutoff of Tag
0BJR, which is `Stacks.LocalCohomology.localCohomologyCutoff A I M`. Assume throughout that `A`
is universally catenary, and make *no* assumption on the formal fibres of the local rings of
`A` beyond a Serre condition imposed one degree at a time. Tag 0BJW is the observation that the
two conclusions of Tag 0BJV survive this weakening:

* if `n < s` and the formal fibres of the local rings of `A` satisfy `(S_n)`, then `H^i_Z(M)` is
  a finite `A`-module for every `i ≤ n`;
* if `s` is the natural number `s` and the formal fibres of the local rings of `A` satisfy
  `(S_{s-1})`, then `H^s_Z(M)` is *not* a finite `A`-module.

Cohen–Macaulay formal fibres satisfy `(S_k)` for every `k`, so Tag 0BJV is the special case in
which both hypotheses are available at once; see
`Stacks.LocalCohomology.finite_lt_and_not_finite_localCohomologyCutoff_of_formalFibers`.

The proof is the source's, and is the proof of Tag 0BJV verbatim: finiteness through a fixed
degree is tested prime by prime after localizing (Tag 0AW9), local cohomology commutes with the
flat base change `A → (A_𝔭)^` (Tag 0ALZ) and finiteness descends along the faithfully flat map
`A_𝔭 → (A_𝔭)^` (Tag 03C4), so the question is one about the completed local rings of `A`. Those
are Noetherian complete local rings, hence have dualizing complexes
(`Dualizing.exists_isDualizingComplex_of_isAdicComplete`), and over a ring with a dualizing
complex Faltings' criterion (Tag 0EFD, here in the form
`finite_localCohomologyWithSupportIn_iff_lt_localCohomologyCutoff_of_dualizing`) turns finiteness
in the degrees `i ≤ n` into the inequality `n < s`. The hypotheses on `A` enter only through the
two bounds of Tag 0BJT, in the form of the cutoff steps
`Stacks.LocalCohomology.lt_localCohomologyCutoff_adicCompletion_localization` (used with
`k = n`) and `Stacks.LocalCohomology.exists_localCohomologyCutoff_adicCompletion_localization_eq`
(used with `k = s - 1`), and those are exactly the two places where `(S_k)` suffices in place of
Cohen–Macaulayness.

## Main results

All live in the namespace `Stacks.LocalCohomology`.

* `finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_serreFormalFibers` —
  **Tag 0BJW**, finiteness through a degree `n` below the cutoff under `(S_n)` formal fibres.
* `not_finite_localCohomologyWithSupportIn_localCohomologyCutoff_of_serreFormalFibers` —
  **Tag 0BJW**, non-finiteness in the cutoff degree under `(S_{s-1})` formal fibres.
* `finite_lt_and_not_finite_localCohomologyCutoff_of_serreFormalFibers` — **Tag 0BJW**, the
  two clauses as one statement, mirroring the combined carrier of Tag 0BJV.

## Implementation notes

The two statements mirror the two carriers of Tag 0BJV in
`StacksFrontier.RingTheory.LocalCohomology.FaltingsFiniteness` exactly — same conclusion, same
handling of the degree as an integer `i ≤ (n : ℤ)`, same `localCohomologyWithSupportIn`
spelling — with the hypothesis `FormalFibersAreCohenMacaulay` replaced by
`Stacks.LocalCohomology.FormalFibersHavePropertySk` at the single relevant index. Because the
Serre index depends on the degree, the degree is bound before the formal-fibre hypothesis,
which is the only difference in the shape of the binders.

The reduction to the complete local case is the hypothesis-free part of the Tag 0BJV argument.
It is carried out by the lemmas
`Stacks.LocalCohomology.finite_localCohomologyModule_iff_forall_completedLocalization` and
`Stacks.LocalCohomology.finite_localCohomologyModule_completedLocalRingAt_iff` of
`StacksFrontier.RingTheory.LocalCohomology.FaltingsFiniteness`.

Local cohomology with support in a closed set appears in two models, which agree over a
Noetherian ring: `Stacks.LocalCohomology.localCohomologyWithSupportIn` for the support
`V(I) = PrimeSpectrum.zeroLocus I`, in which Tags 0EFD and 0BJU are stated, and
`Stacks.LocalCohomology.localCohomologyModule` for the ideal `I`, in which Tags 0AW9 and 0ALZ
are stated; the comparison is
`Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule`. The statements
below use the first.

The cutoff is an infimum in `ℕ∞`, so it is `⊤` exactly when no admissible pair of primes
exists. The two clauses are therefore stated so as to stay correct there: the first is indexed
by a natural number `n` strictly below the cutoff, which for `s = ⊤` gives finiteness in every
degree, and the second is hypothesized on the cutoff being a natural number, which is vacuous
for `s = ⊤`. There is no degree `⊤`, so this is exactly the content of the source statement.

## References

* [Stacks Project, Tag 0BJW](https://stacks.math.columbia.edu/tag/0BJW)
* [Stacks Project, Tag 0BJV](https://stacks.math.columbia.edu/tag/0BJV)
* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
* [Stacks Project, Tag 0BJT](https://stacks.math.columbia.edu/tag/0BJT)
* [Stacks Project, Tag 0EFD](https://stacks.math.columbia.edu/tag/0EFD)
* [Stacks Project, Tag 0AW9](https://stacks.math.columbia.edu/tag/0AW9)
* [Stacks Project, Tag 0ALZ](https://stacks.math.columbia.edu/tag/0ALZ)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-! ### The two clauses of Tag 0BJW -/

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- The finiteness clause of Tag 0BJW, in the coreflection model. -/
private theorem finite_localCohomologyModule_of_lt_localCohomologyCutoff_of_serreFormalFibers
    (hA : Ring.IsUniversallyCatenary A) (n : ℕ)
    (hformal : ∀ p : PrimeSpectrum A,
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) n)
    (hn : (n : ℕ∞) < localCohomologyCutoff A I M) :
    ∀ i : ℕ, i ≤ n → Module.Finite A
      (localCohomologyModule A I (Ideal.fg_of_isNoetherianRing I) (ModuleCat.of A M) (i : ℤ)) := by
  rw [finite_localCohomologyModule_iff_forall_completedLocalization]
  intro p i hi
  have hcut := lt_localCohomologyCutoff_adicCompletion_localization A I M n hA hformal hn p
  rw [Ideal.map_map] at hcut
  exact (finite_localCohomologyModule_completedLocalRingAt_iff A I
    (Ideal.fg_of_isNoetherianRing I) M p n).mpr hcut i hi

/-- **Stacks Project, Tag 0BJW, finiteness through a degree below the cutoff.** Let `A` be a
universally catenary Noetherian ring, let `I ⊆ A` be an ideal, let `Z = V(I)` and let `M` be a
finite `A`-module. Fix a natural number `n` strictly below the cutoff `s = s_{A,I}(M)` of Tag
0BJR and assume only that the formal fibres of the local rings of `A` satisfy Serre's condition
`(S_n)`. Then `H^i_Z(M)` is a finite `A`-module in every degree `i ≤ n`.

This is Tag 0BJV's finiteness clause with the Cohen–Macaulay hypothesis on the formal fibres
weakened to `(S_n)`, which is all the proof uses: the hypothesis enters only through the Tag
0BJT bound `lt_localCohomologyCutoff_adicCompletion_localization` at `k = n`. For `s = ⊤` the
statement gives finiteness in every degree, provided the formal fibres are `(S_n)` for the `n`
in question. -/
@[stacks 0BJW "finiteness through degree n when the formal fibres are (S_n)"]
public theorem
    finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_serreFormalFibers
    (hA : Ring.IsUniversallyCatenary A) (n : ℕ)
    (hformal : ∀ p : PrimeSpectrum A,
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) n)
    (hn : (n : ℕ∞) < localCohomologyCutoff A I M) (i : ℤ) (hi : i ≤ (n : ℤ)) :
    Module.Finite A
      (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) :=
  (finite_forall_int_iff_forall_nat A I (Ideal.fg_of_isNoetherianRing I)
      (ModuleCat.of A M) n).mpr
    (finite_localCohomologyModule_of_lt_localCohomologyCutoff_of_serreFormalFibers A I M hA n
      hformal hn) i hi

/-- **Stacks Project, Tag 0BJW, non-finiteness at the cutoff.** In the situation of
`finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_serreFormalFibers`, if the
cutoff `s = s_{A,I}(M)` is the natural number `s` and the formal fibres of the local rings of
`A` satisfy Serre's condition `(S_{s-1})`, then `H^s_Z(M)` is *not* a finite `A`-module.

Were it finite it would join the finite modules in the degrees below `s` — available from the
finiteness clause at `n = s - 1`, whose `(S_{s-1})` hypothesis is the one assumed here — to make
`H^i_Z(M)` finite for all `i ≤ s`; testing that on the completion of the local ring at the prime
at which the cutoff is attained, Tag 0EFD would then force `s < s`. The prime is produced by the
Tag 0BJT bound `exists_localCohomologyCutoff_adicCompletion_localization_eq` at `k = s - 1`,
which is the only place the formal-fibre hypothesis is used besides the finiteness clause. The
hypothesis that the cutoff is a natural number is needed as stated: the cutoff is an infimum in
`ℕ∞` and there is no degree `⊤`. -/
@[stacks 0BJW "non-finiteness in the cutoff degree when the formal fibres are (S_{s-1})"]
public theorem
    not_finite_localCohomologyWithSupportIn_localCohomologyCutoff_of_serreFormalFibers
    (hA : Ring.IsUniversallyCatenary A) (s : ℕ)
    (hformal : ∀ p : PrimeSpectrum A,
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) (s - 1))
    (hs : localCohomologyCutoff A I M = (s : ℕ∞)) :
    ¬ Module.Finite A
      (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) (s : ℤ)) := by
  intro hfin
  have hI : I.FG := Ideal.fg_of_isNoetherianRing I
  have hfin' : Module.Finite A (localCohomologyModule A I hI (ModuleCat.of A M) (s : ℤ)) :=
    Module.Finite.equiv
      (localCohomologyWithSupportInIsoLocalCohomologyModule A I hI
        (ModuleCat.of A M) (s : ℤ)).toLinearEquiv
  have hall : ∀ i : ℕ, i ≤ s →
      Module.Finite A (localCohomologyModule A I hI (ModuleCat.of A M) (i : ℤ)) := by
    intro i hi
    rcases eq_or_lt_of_le hi with rfl | hlt
    · exact hfin'
    · refine finite_localCohomologyModule_of_lt_localCohomologyCutoff_of_serreFormalFibers A I M
        hA (s - 1) hformal ?_ i (by omega)
      rw [hs]
      exact_mod_cast Nat.sub_lt (by omega) Nat.one_pos
  have hfa := (finite_localCohomologyModule_iff_forall_completedLocalization A I hI M s).mp hall
  have hformal' : ∀ p : PrimeSpectrum A,
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal)
        ((localCohomologyCutoff A I M).toNat - 1) := by
    intro p
    rw [hs, ENat.toNat_natCast]
    exact hformal p
  obtain ⟨q, _, hcut⟩ := exists_localCohomologyCutoff_adicCompletion_localization_eq A I M hA
    (by rw [hs]; exact ENat.natCast_lt_top s) hformal'
  rw [Ideal.map_map, hs] at hcut
  have hlt := (finite_localCohomologyModule_completedLocalRingAt_iff A I hI M q s).mp (hfa q)
  rw [hcut] at hlt
  exact lt_irrefl _ hlt

/-- **Stacks Project, Tag 0BJW.** In the situation of Tag 0BJV — `A` a Noetherian ring,
`I ⊆ A` an ideal, `Z = V(I) ⊆ Spec(A)`, `M` a finite `A`-module and `s = s_{A,I}(M)` the cutoff
of Tag 0BJR — assume `A` is universally catenary and make no assumption at all on the formal
fibres. Then both conclusions of Tag 0BJV survive under a Serre condition imposed one degree at
a time:

* given `n` with `s > n`, if the formal fibres of the local rings of `A` satisfy `(S_n)` then
  `H^i_Z(M)` is finite for `i ≤ n`;
* if `s` is a natural number and the formal fibres satisfy `(S_{s-1})` then `H^s_Z(M)` is not
  finite.

This is the whole remark in one statement; the two conjuncts are
`finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_serreFormalFibers` and
`not_finite_localCohomologyWithSupportIn_localCohomologyCutoff_of_serreFormalFibers`, and the
shape matches the combined carrier
`finite_lt_and_not_finite_localCohomologyCutoff_of_formalFibers` of Tag 0BJV, except that the
formal-fibre hypothesis is bound inside each conjunct because its Serre index depends on the
degree under discussion. -/
@[stacks 0BJW]
public theorem finite_lt_and_not_finite_localCohomologyCutoff_of_serreFormalFibers
    (hA : Ring.IsUniversallyCatenary A) :
    (∀ n : ℕ, (∀ p : PrimeSpectrum A,
          FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) n) →
        (n : ℕ∞) < localCohomologyCutoff A I M → ∀ i : ℤ, i ≤ (n : ℤ) →
        Module.Finite A
          (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i)) ∧
      (∀ s : ℕ, (∀ p : PrimeSpectrum A,
          FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) (s - 1)) →
        localCohomologyCutoff A I M = (s : ℕ∞) →
        ¬ Module.Finite A
          (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A M)) (s : ℤ))) :=
  ⟨fun n hformal hn i hi =>
      finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_serreFormalFibers A I M
        hA n hformal hn i hi,
    fun s hformal hs =>
      not_finite_localCohomologyWithSupportIn_localCohomologyCutoff_of_serreFormalFibers A I M
        hA s hformal hs⟩

end Stacks.LocalCohomology

end
