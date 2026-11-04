module

public import StacksFrontier.RingTheory.Dualizing.Ubiquity
public import StacksFrontier.RingTheory.Dualizing.UbiquityCompleteLocal
public import StacksFrontier.RingTheory.Dualizing.UbiquityStability

/-!
# The ubiquity lemma, all five classes conjoined

[Stacks, Tag 0BFR] asserts that five types of rings have a dualizing complex: the fields, the
Noetherian complete local rings, `ℤ`, the Dedekind domains, and anything obtained from one of
those by passing to an algebra essentially of finite type, to an ideal-adic completion, to a
henselization, or to a strict henselization. Each clause is proved in its own place; this file
records the single statement that conjoins all five, so that the tag is carried whole by one
declaration and not only clause by clause.

## Main results

* `Dualizing.exists_isDualizingComplex_ubiquity` — **[Stacks, Tag 0BFR]**, the five clauses
  conjoined.

## Implementation notes

The conjuncts are the statements of the per-clause declarations verbatim, so this file contains
no mathematics: the proof is the tuple of those declarations. They are, in the order of the
source,

1. `Dualizing.exists_isDualizingComplex` (fields),
2. `Dualizing.exists_isDualizingComplex_of_isPrecomplete_maximalIdeal` (Noetherian complete
   local rings),
3. `Dualizing.exists_isDualizingComplex_int` (`ℤ`),
4. `Dualizing.exists_isDualizingComplex_of_isDedekindDomain` (Dedekind domains),
5. `Dualizing.exists_isDualizingComplex_of_essentiallyOfFiniteType`,
   `Dualizing.exists_isDualizingComplex_adicCompletion`,
   `Dualizing.exists_isDualizingComplex_henselizationPair`,
   `Dualizing.exists_isDualizingComplex_henselization` and
   `Dualizing.exists_isDualizingComplex_strictHenselization` (the four operations),

and each of them keeps its own `@[stacks 0BFR]` registration naming its clause.

Two points where the conjunction says more than a literal reading of the source, never less.
Completeness in clause (2) is precompleteness for the maximal ideal, as in [Stacks, Tag 07PJ].
That is the weaker of the two hypotheses on offer — `IsAdicComplete` is precompleteness together
with a Hausdorff condition — so clause (2) as stated here covers every `IsAdicComplete`
Noetherian local ring and more; for a Noetherian local ring the two in fact agree, the Hausdorff
half being automatic. And clause (5) is stated for the whole class of Noetherian rings carrying
a dualizing complex, not merely for the four classes listed above it: that is what the source's
proof establishes and what clause (5) is used for.

So stated, clause (5) composes: each of its four conclusions delivers both Noetherianness of the
new ring and the existence of a dualizing complex over it, which is exactly the hypothesis the
next operation asks for. Iterating is the content of the source's "obtained from one of the
rings above".

## References

* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
* [Stacks Project, Tag 0A7K](https://stacks.math.columbia.edu/tag/0A7K)
* [Stacks Project, Tag 0DWD](https://stacks.math.columbia.edu/tag/0DWD)
* [Stacks Project, Tag 07PJ](https://stacks.math.columbia.edu/tag/07PJ)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v w uL

namespace Dualizing

/-- **Stacks Project, Tag 0BFR.** The following types of rings have a dualizing complex:

1. fields,
2. Noetherian complete local rings,
3. `ℤ`,
4. Dedekind domains,
5. any ring obtained from a Noetherian ring with a dualizing complex by taking an algebra
   essentially of finite type, or by taking an ideal-adic completion, or by taking a
   henselization, or by taking a strict henselization.

The five conjuncts are `Dualizing.exists_isDualizingComplex`,
`Dualizing.exists_isDualizingComplex_of_isPrecomplete_maximalIdeal`,
`Dualizing.exists_isDualizingComplex_int`,
`Dualizing.exists_isDualizingComplex_of_isDedekindDomain` and, for clause (5), the five
statements `Dualizing.exists_isDualizingComplex_of_essentiallyOfFiniteType`,
`Dualizing.exists_isDualizingComplex_adicCompletion`,
`Dualizing.exists_isDualizingComplex_henselizationPair`,
`Dualizing.exists_isDualizingComplex_henselization` and
`Dualizing.exists_isDualizingComplex_strictHenselization`; each carries the tag for its own
clause. See the implementation notes of this file for the two places where the conjunction says
more than the source. -/
@[stacks 0BFR "all five clauses conjoined"]
theorem exists_isDualizingComplex_ubiquity :
    (∀ (k : Type u) [Field k],
        ∃ K : DerivedCategory (ModuleCat.{u} k), IsDualizingComplex K) ∧
    (∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
        [IsPrecomplete (IsLocalRing.maximalIdeal A) A],
        ∃ K : DerivedCategory (ModuleCat.{u} A), IsDualizingComplex K) ∧
    (∃ K : DerivedCategory (ModuleCat.{0} ℤ), IsDualizingComplex K) ∧
    (∀ (A : Type u) [CommRing A] [IsDedekindDomain A],
        ∃ K : DerivedCategory (ModuleCat.{u} A), IsDualizingComplex K) ∧
    (∀ (A B : Type u) [CommRing A] [CommRing B] [IsNoetherianRing A] [Algebra A B],
        IsEssentiallyOfFiniteType A B (algebraMap A B) →
        (∃ K : DerivedCategory (ModuleCat.{u} A), IsDualizingComplex K) →
        ∃ (hB' : IsNoetherianRing B) (L : DerivedCategory (ModuleCat.{u} B)),
          @IsDualizingComplex B _ hB' _ L) ∧
    (∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A),
        (∃ K : DerivedCategory (ModuleCat.{u} A), IsDualizingComplex K) →
        letI : IsNoetherianRing (AdicCompletion I A) := AdicCompletion.isNoetherianRing I
        ∃ L : DerivedCategory (ModuleCat.{u} (AdicCompletion I A)), IsDualizingComplex L) ∧
    (∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
        (Ah : Type w) [CommRing Ah] [Algebra A Ah]
        (hh : HenselianPair Ah (I.map (algebraMap A Ah)))
        (hι : ∀ (B : Type (max u w)) (_ : CommRing B) (J : Ideal B),
          HenselianPair B J →
            ∀ f : A →+* B, I ≤ J.comap f →
              ∃! g : Ah →+* B,
                g.comp (algebraMap A Ah) = f ∧ I.map (algebraMap A Ah) ≤ J.comap g),
        (∃ K : DerivedCategory (ModuleCat.{v} A), IsDualizingComplex K) →
        letI : IsNoetherianRing Ah :=
          (henselization_isNoetherian_and_completion_equiv A I Ah hh hι).2.1
        ∃ L : DerivedCategory (ModuleCat.{max v w} Ah), IsDualizingComplex L) ∧
    (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
        (Ah : Type w) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
        [IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) Ah],
        (∃ K : DerivedCategory (ModuleCat.{v} A), IsDualizingComplex K) →
        letI : IsNoetherianRing Ah :=
          IsLocalRing.isNoetherianRing_of_isHenselization (A := A) (B := Ah)
            (IsLocalRing.ResidueField A)
        ∃ L : DerivedCategory (ModuleCat.{max v w} Ah), IsDualizingComplex L) ∧
    (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
        (L : Type uL) [Field L] [Algebra (IsLocalRing.ResidueField A) L]
        (Ash : Type w) [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
        [IsLocalRing.IsHenselization A L Ash],
        (∃ K : DerivedCategory (ModuleCat.{max u v w} A), IsDualizingComplex K) →
        letI : IsNoetherianRing Ash :=
          IsLocalRing.isNoetherianRing_of_isHenselization (A := A) (B := Ash) L
        ∃ M : DerivedCategory (ModuleCat.{max u v w} Ash), IsDualizingComplex M) :=
  ⟨fun k _ ↦ exists_isDualizingComplex.{u} k,
    fun A _ _ _ _ ↦ exists_isDualizingComplex_of_isPrecomplete_maximalIdeal.{u} A,
    exists_isDualizingComplex_int,
    fun A _ _ ↦ exists_isDualizingComplex_of_isDedekindDomain.{u} A,
    fun _ _ _ _ _ _ hB hA ↦
      exists_isDualizingComplex_of_essentiallyOfFiniteType.{u} hB hA,
    fun _ _ _ I hA ↦ exists_isDualizingComplex_adicCompletion.{u} I hA,
    fun A _ _ I Ah _ _ hh hι hA ↦
      exists_isDualizingComplex_henselizationPair.{u, v, w} A I Ah hh hι hA,
    fun A _ _ _ Ah _ _ _ _ hA ↦
      exists_isDualizingComplex_henselization.{u, v, w} A Ah hA,
    fun A _ _ _ L _ _ Ash _ _ _ _ hA ↦
      exists_isDualizingComplex_strictHenselization.{u, v, w, uL} A L Ash hA⟩

end Dualizing

end
