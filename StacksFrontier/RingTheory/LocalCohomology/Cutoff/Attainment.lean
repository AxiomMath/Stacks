module

public import StacksFrontier.RingTheory.Catenary.Localization
public import StacksFrontier.RingTheory.LocalCohomology.Cutoff.Completion
public import StacksFrontier.RingTheory.LocalCohomology.CutoffCompletionSerre
public import StacksFrontier.RingTheory.LocalCohomology.CutoffLocalization

/-!
# The local cohomology cutoff is attained, and attained after completing a localization

Let `A` be a commutative ring, `I ⊆ A` an ideal and `M` an `A`-module. The local cohomology
finiteness cutoff `s_{A,I}(M)` of Stacks 0BJR is an infimum over the admissible pairs of primes
`𝔭 ⊆ 𝔮` with `𝔭 ∉ V(I)` and `𝔮 ∈ V(I)`. Three facts about that infimum are proved here.

* When it is finite it is **attained**: `ℕ∞` is well-ordered, so a nonempty set of admissible
  values has a least element, and the cutoff being finite says exactly that the set is nonempty.
* Localizing at the larger prime `𝔮` of an admissible pair does not raise the cutoff above that
  pair's value. Together with the reverse inequality
  `Stacks.LocalCohomology.localCohomologyCutoff_le_localization` this makes the cutoff
  **attained at a localization**: a finite cutoff is the cutoff of `M_𝔮` over `A_𝔮` for some
  `𝔮 ∈ V(I)`.
* Over a universally catenary Noetherian local ring whose formal fibres satisfy `(S_k)`, the
  two bounds of Stacks 0BJT pin the cutoff of the completion: it is unchanged when the cutoff is
  at most `k + 1`, and it still exceeds `k` when the original cutoff does.

Combining the second and third gives the cutoff step of both halves of Stacks 0BJW, from one
shared pair of bounds at two values of `k`: for `k = n` one gets `n < s` after completing every
localization, and for `k = s - 1` one gets a prime `𝔮 ∈ V(I)` at which the completed
localization has cutoff exactly `s`.

## Main results

* `Stacks.LocalCohomology.exists_pair_eq_localCohomologyCutoff` — a finite cutoff is attained by
  an admissible pair of primes.
* `Stacks.LocalCohomology.localCohomologyCutoff_localization_le` — the cutoff over `A_𝔮` is at
  most the value of any admissible pair `𝔭 ⊆ 𝔮`.
* `Stacks.LocalCohomology.exists_localCohomologyCutoff_localization_eq` — a finite cutoff is the
  cutoff of a localization at a prime of `V(I)`.
* `Stacks.LocalCohomology.lt_localCohomologyCutoff_adicCompletion` and
  `Stacks.LocalCohomology.localCohomologyCutoff_adicCompletion_eq` — the two consequences of the
  Stacks 0BJT bounds under an `(S_k)` hypothesis on the formal fibres.
* `Stacks.LocalCohomology.lt_localCohomologyCutoff_adicCompletion_localization` and
  `Stacks.LocalCohomology.exists_localCohomologyCutoff_adicCompletion_localization_eq` — the
  cutoff step of the two halves of Stacks 0BJW.

## Implementation notes

**None of these declarations carries a `@[stacks 0BJW]` attribute, because what is proved here
is only the cutoff half of 0BJW's two clauses.** Stacks 0BJW is the remark that the two
conclusions of Theorem 51.11.6 (Tag 0BJV) survive under an `(S_n)` hypothesis on the formal
fibres in place of the Cohen–Macaulay one, "by the same argument". That argument reduces,
through Tag 0AW9 and the two bounds of Tag 0BJT proved here, to the **complete local case**: for
`C` a Noetherian complete local ring, `H^i_{V(J)}(N)` is finite for `i < s_{C,J}(N)` and
`H^s_{V(J)}(N)` is not finite. That case comes, as in the source, from Cohen's structure theorem
and Proposition 51.11.1 (Tag 0EFD) for a ring with a dualizing complex; it is available in
`StacksFrontier.RingTheory.LocalCohomology.FaltingsFiniteness`, as
`finite_localCohomologyWithSupportIn_iff_lt_localCohomologyCutoff_of_dualizing` together with
`Dualizing.exists_isDualizingComplex_of_isAdicComplete`. The finiteness statements of 0BJW that
these two cutoff steps feed are therefore proved, and carry the `@[stacks 0BJW]` attribute, in
`StacksFrontier.RingTheory.LocalCohomology.SerreFormalFibresFiniteness`:
`finite_localCohomologyWithSupportIn_of_lt_localCohomologyCutoff_of_serreFormalFibers` uses
`lt_localCohomologyCutoff_adicCompletion_localization`, and
`not_finite_localCohomologyWithSupportIn_localCohomologyCutoff_of_serreFormalFibers` uses
`exists_localCohomologyCutoff_adicCompletion_localization_eq`.

The completion of `A` is `AdicCompletion (IsLocalRing.maximalIdeal A) A` and the completion of
`M` is `AdicCompletion (IsLocalRing.maximalIdeal A) M`, matching Tag 0BJT as stated in
`Stacks.LocalCohomology.localCohomologyCutoff_adicCompletion_le` and
`Stacks.LocalCohomology.min_succ_le_localCohomologyCutoff_adicCompletion`. The Serre index of
the second clause is `s.toNat - 1`, truncated subtraction in `ℕ`; the only property of it used
is `s ≤ (s.toNat - 1) + 1`, which holds for every finite `s` including `s = 0`.

## References

* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
* [Stacks Project, Tag 0BJT](https://stacks.math.columbia.edu/tag/0BJT)
* [Stacks Project, Tag 0BJW](https://stacks.math.columbia.edu/tag/0BJW)
-/

@[expose] public section

universe u v

namespace Stacks.LocalCohomology

/-- **A finite local cohomology cutoff is attained.** The cutoff is the infimum of the values
attached to the admissible pairs of primes; `ℕ∞` is well-ordered, so that infimum belongs to the
set of values as soon as the set is nonempty, and a cutoff below `⊤` forces it to be. -/
public theorem exists_pair_eq_localCohomologyCutoff
    (A : Type u) [CommRing A] (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]
    (hs : localCohomologyCutoff A I M < ⊤) :
    ∃ p q : PrimeSpectrum A, ¬ I ≤ p.asIdeal ∧ I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal ∧
      localCohomologyCutoff A I M =
        Module.depth (Localization.AtPrime p.asIdeal)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M) +
          (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
  have hne : {n : ℕ∞ | ∃ p q : PrimeSpectrum A,
      ¬ I ≤ p.asIdeal ∧ I ≤ q.asIdeal ∧ p.asIdeal ≤ q.asIdeal ∧
        n = Module.depth (Localization.AtPrime p.asIdeal)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M) +
          (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height}.Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun hempty =>
      ne_top_of_lt hs (by rw [localCohomologyCutoff, hempty, sInf_empty])
  exact csInf_mem hne

/-- **Localizing at the larger prime of an admissible pair does not raise the cutoff above that
pair's value.** The pair `𝔭 ⊆ 𝔮` extends to an admissible pair `𝔭 A_𝔮 ⊆ 𝔮 A_𝔮` of `A_𝔮`
contributing the same depth and the same relative height, so the infimum over `A_𝔮` is at most
the value of the original pair. -/
public theorem localCohomologyCutoff_localization_le
    (A : Type u) [CommRing A] (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]
    (p q : PrimeSpectrum A) (hp : ¬ I ≤ p.asIdeal) (hq : I ≤ q.asIdeal)
    (hpq : p.asIdeal ≤ q.asIdeal) :
    localCohomologyCutoff (Localization.AtPrime q.asIdeal)
        (I.map (algebraMap A (Localization.AtPrime q.asIdeal)))
        (LocalizedModule q.asIdeal.primeCompl M) ≤
      Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M) +
        (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
  classical
  let B := Localization.AtPrime q.asIdeal
  let f : A →+* B := algebraMap A B
  let P : Ideal B := p.asIdeal.map f
  let Q : Ideal B := q.asIdeal.map f
  have hPp : P.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime q.asIdeal hpq
  have hQp : Q.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime q.asIdeal le_rfl
  let p' : PrimeSpectrum B := ⟨P, hPp⟩
  let q' : PrimeSpectrum B := ⟨Q, hQp⟩
  have hP : P.comap f = p.asIdeal :=
    Ideal.under_map_of_isLocalizationAtPrime q.asIdeal hpq
  have hp' : ¬ I.map f ≤ P := fun h => hp (hP ▸ Ideal.map_le_iff_le_comap.mp h)
  have hqdisj : Disjoint (q.asIdeal.primeCompl : Set A) (q.asIdeal : Set A) :=
    Set.disjoint_left.2 fun _ hx hxq => hx hxq
  -- The depth at `P` over `B` is the depth at `𝔭` over `A`, because `B_P = A_𝔭`.
  have hdepth :
      Module.depth (Localization.AtPrime p'.asIdeal)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p'.asIdeal))
            (LocalizedModule p'.asIdeal.primeCompl (LocalizedModule q.asIdeal.primeCompl M)) =
        Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M) := by
    have hcomap : PrimeSpectrum.comap f p' = p := PrimeSpectrum.ext hP
    have h :
        Module.depth (Localization.AtPrime (PrimeSpectrum.comap f p').asIdeal)
            (IsLocalRing.maximalIdeal
              (Localization.AtPrime (PrimeSpectrum.comap f p').asIdeal))
            (LocalizedModule (PrimeSpectrum.comap f p').asIdeal.primeCompl M) =
          Module.depth (Localization.AtPrime p'.asIdeal)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p'.asIdeal))
            (LocalizedModule p'.asIdeal.primeCompl (LocalizedModule q.asIdeal.primeCompl M)) :=
      depth_localizedModule_localizationLocalization (A := A) (M := M)
        q.asIdeal.primeCompl p'.asIdeal
    let D : PrimeSpectrum A → ℕ∞ := fun r =>
      Module.depth (Localization.AtPrime r.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime r.asIdeal))
        (LocalizedModule r.asIdeal.primeCompl M)
    exact h.symm.trans (congrArg D hcomap)
  have hheight : (q'.asIdeal.map (Ideal.Quotient.mk p'.asIdeal)).height =
      (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height :=
    (height_map_quotientMk_localization (A := A) (B := B) q.asIdeal.primeCompl
      p.asIdeal q.asIdeal hpq hqdisj).symm
  exact (localCohomologyCutoff_le B (I.map f) (LocalizedModule q.asIdeal.primeCompl M)
    p' q' hp' (Ideal.map_mono hq) (Ideal.map_mono hpq)).trans_eq (by rw [hdepth, hheight])

/-- **A finite cutoff is the cutoff of a localization.** Choosing an admissible pair `𝔭 ⊆ 𝔮`
attaining the infimum and localizing at `𝔮`, the two inequalities
`localCohomologyCutoff_le_localization` and `localCohomologyCutoff_localization_le` squeeze the
cutoff of `M_𝔮` over `A_𝔮` onto `s_{A,I}(M)`. -/
public theorem exists_localCohomologyCutoff_localization_eq
    (A : Type u) [CommRing A] (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]
    (hs : localCohomologyCutoff A I M < ⊤) :
    ∃ q : PrimeSpectrum A, I ≤ q.asIdeal ∧
      localCohomologyCutoff (Localization.AtPrime q.asIdeal)
          (I.map (algebraMap A (Localization.AtPrime q.asIdeal)))
          (LocalizedModule q.asIdeal.primeCompl M) =
        localCohomologyCutoff A I M := by
  obtain ⟨p, q, hp, hq, hpq, hmin⟩ := exists_pair_eq_localCohomologyCutoff A I M hs
  exact ⟨q, hq, le_antisymm
    ((localCohomologyCutoff_localization_le A I M p q hp hq hpq).trans_eq hmin.symm)
    (localCohomologyCutoff_le_localization I M q.asIdeal)⟩

section Completion

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **Completion keeps the cutoff above `k` when the formal fibres satisfy `(S_k)`.** The lower
bound of Stacks 0BJT says the completed cutoff is at least `min (k + 1) s`, and `k < s` makes
that minimum `k + 1`. -/
public theorem lt_localCohomologyCutoff_adicCompletion (k : ℕ)
    (hA : Ring.IsUniversallyCatenary A) (hformal : FormalFibersHavePropertySk A k)
    (hk : (k : ℕ∞) < localCohomologyCutoff A I M) :
    (k : ℕ∞) < localCohomologyCutoff (AdicCompletion (IsLocalRing.maximalIdeal A) A)
      (I.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
      (AdicCompletion (IsLocalRing.maximalIdeal A) M) := by
  have hsucc : ((k + 1 : ℕ) : ℕ∞) ≤ localCohomologyCutoff A I M := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (ENat.add_one_le_iff (ENat.natCast_ne_top k)).2 hk
  refine lt_of_lt_of_le ?_ ((min_eq_left hsucc) ▸
    min_succ_le_localCohomologyCutoff_adicCompletion A I M k hA hformal)
  exact_mod_cast Nat.lt_succ_self k

/-- **Completion does not change a cutoff that is at most `k + 1`, when the formal fibres satisfy
`(S_k)`.** The two bounds of Stacks 0BJT give `min (k + 1) s ≤ ŝ ≤ s`, and `s ≤ k + 1` turns the
minimum into `s`. -/
public theorem localCohomologyCutoff_adicCompletion_eq (k : ℕ)
    (hA : Ring.IsUniversallyCatenary A) (hformal : FormalFibersHavePropertySk A k)
    (hk : localCohomologyCutoff A I M ≤ ((k + 1 : ℕ) : ℕ∞)) :
    localCohomologyCutoff (AdicCompletion (IsLocalRing.maximalIdeal A) A)
        (I.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
        (AdicCompletion (IsLocalRing.maximalIdeal A) M) =
      localCohomologyCutoff A I M :=
  le_antisymm (localCohomologyCutoff_adicCompletion_le A I M hA)
    ((min_eq_right hk) ▸ min_succ_le_localCohomologyCutoff_adicCompletion A I M k hA hformal)

end Completion

/-- **The cutoff step of Stacks 0BJW's first clause.** If the cutoff of `M` exceeds `n` and the
formal fibres of every local ring of `A` satisfy `(S_n)`, then the cutoff still exceeds `n`
after localizing at any prime and completing. The localization step is
`localCohomologyCutoff_le_localization` and the completion step is
`lt_localCohomologyCutoff_adicCompletion`. -/
public theorem lt_localCohomologyCutoff_adicCompletion_localization
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] (n : ℕ)
    (hA : Ring.IsUniversallyCatenary A)
    (hformal : ∀ p : PrimeSpectrum A,
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal) n)
    (hn : (n : ℕ∞) < localCohomologyCutoff A I M) (p : PrimeSpectrum A) :
    (n : ℕ∞) < localCohomologyCutoff
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (Localization.AtPrime p.asIdeal))
      ((I.map (algebraMap A (Localization.AtPrime p.asIdeal))).map
        (algebraMap (Localization.AtPrime p.asIdeal)
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
            (Localization.AtPrime p.asIdeal))))
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M)) := by
  exact lt_localCohomologyCutoff_adicCompletion (Localization.AtPrime p.asIdeal)
    (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
    (LocalizedModule p.asIdeal.primeCompl M) n
    (Ring.IsUniversallyCatenary.localization p.asIdeal.primeCompl _ hA) (hformal p)
    (hn.trans_le (localCohomologyCutoff_le_localization I M p.asIdeal))

/-- **The cutoff step of Stacks 0BJW's second clause.** If the cutoff `s` of `M` is finite and
the formal fibres of every local ring of `A` satisfy `(S_{s-1})`, then `s` is realised exactly:
there is a prime `𝔮 ∈ V(I)` for which the completion of `A_𝔮` at its maximal ideal, with the
extended ideal and the completed module, again has cutoff `s`. The prime comes from
`exists_localCohomologyCutoff_localization_eq` and the completion step from
`localCohomologyCutoff_adicCompletion_eq`, whose hypothesis `s ≤ (s.toNat - 1) + 1` holds for
every finite `s`. -/
public theorem exists_localCohomologyCutoff_adicCompletion_localization_eq
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hA : Ring.IsUniversallyCatenary A) (hs : localCohomologyCutoff A I M < ⊤)
    (hformal : ∀ p : PrimeSpectrum A,
      FormalFibersHavePropertySk (Localization.AtPrime p.asIdeal)
        ((localCohomologyCutoff A I M).toNat - 1)) :
    ∃ q : PrimeSpectrum A, I ≤ q.asIdeal ∧
      localCohomologyCutoff
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
            (Localization.AtPrime q.asIdeal))
          ((I.map (algebraMap A (Localization.AtPrime q.asIdeal))).map
            (algebraMap (Localization.AtPrime q.asIdeal)
              (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
                (Localization.AtPrime q.asIdeal))))
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
            (LocalizedModule q.asIdeal.primeCompl M)) =
        localCohomologyCutoff A I M := by
  set s := localCohomologyCutoff A I M
  obtain ⟨q, hq, hloc⟩ := exists_localCohomologyCutoff_localization_eq A I M hs
  have hks : s ≤ ((s.toNat - 1 + 1 : ℕ) : ℕ∞) :=
    calc s = (s.toNat : ℕ∞) := (ENat.natCast_toNat (ne_top_of_lt hs)).symm
      _ ≤ ((s.toNat - 1 + 1 : ℕ) : ℕ∞) := by exact_mod_cast (by omega : s.toNat ≤ s.toNat - 1 + 1)
  exact ⟨q, hq, (localCohomologyCutoff_adicCompletion_eq (Localization.AtPrime q.asIdeal)
    (I.map (algebraMap A (Localization.AtPrime q.asIdeal)))
    (LocalizedModule q.asIdeal.primeCompl M) (s.toNat - 1)
    (Ring.IsUniversallyCatenary.localization q.asIdeal.primeCompl _ hA) (hformal q)
    (hloc.trans_le hks)).trans hloc⟩

end Stacks.LocalCohomology

end
