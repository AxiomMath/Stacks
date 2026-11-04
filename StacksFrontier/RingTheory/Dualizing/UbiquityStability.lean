module

public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.EssentiallyFiniteType
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.AdicCompletion
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.Henselization

/-!
# Clause (5) of the ubiquity lemma: having a dualizing complex is stable

[Stacks, Tag 0BFR] closes its list of rings with a dualizing complex under four operations:
passing to an algebra essentially of finite type, to an ideal-adic completion, to a
henselization, and to a strict henselization. This file records all four as statements about the
class of rings having a dualizing complex, which is the form in which clause (5) is used: if `A`
has one, so does the ring obtained from it.

Each is immediate from the stronger result of the source, which produces a dualizing complex on
the nose rather than asserting existence: the essentially-finite-type case is
[Stacks, Tag 0A7K], and the other three are the three parts of [Stacks, Tag 0DWD], the base
change of a dualizing complex along `A → A^∧`, along the henselization of a pair `(A, I)`, and
along the henselization or a strict henselization of a Noetherian local ring.

## Main results

* `Dualizing.exists_isDualizingComplex_of_essentiallyOfFiniteType` — **[Stacks, Tag 0BFR]**,
  clause (5) for algebras essentially of finite type.
* `Dualizing.exists_isDualizingComplex_adicCompletion` — **[Stacks, Tag 0BFR]**, clause (5) for
  ideal-adic completions.
* `Dualizing.exists_isDualizingComplex_henselizationPair` — **[Stacks, Tag 0BFR]**, clause (5)
  for the henselization of a pair.
* `Dualizing.exists_isDualizingComplex_henselization`,
  `Dualizing.exists_isDualizingComplex_strictHenselization` — **[Stacks, Tag 0BFR]**, clause (5)
  for the henselization and a strict henselization of a Noetherian local ring.

## Implementation notes

Noetherianness of the new ring is part of the conclusion rather than a hypothesis, since
`Dualizing.IsDualizingComplex` cannot be stated without it: for an algebra essentially of finite
type it is existentially quantified, as in [Stacks, Tag 0A7K], and in the other three cases it
is a theorem — `AdicCompletion.isNoetherianRing`,
`Dualizing.henselization_isNoetherian_and_completion_equiv` and
`IsLocalRing.isNoetherianRing_of_isHenselization` — and so is supplied by a `letI` in the
statement.

The hypotheses presenting the henselizations are those of [Stacks, Tag 0DWD] verbatim: a
henselian pair together with its universal property for the pair case, and the class
`IsLocalRing.IsHenselization` with a prescribed residue field extension for the local cases,
which is a strict henselization exactly when that extension is a separable algebraic closure.
The module universe of the base change is `max v w` for a complex of `ModuleCat.{v}`-modules
over a ring in universe `w`, which is why the conclusions are stated at that index.

The statement conjoining all five clauses of [Stacks, Tag 0BFR] is
`Dualizing.exists_isDualizingComplex_ubiquity` in
`StacksFrontier/RingTheory/Dualizing/UbiquityFiveClasses.lean`; the one conjoining all three parts
of [Stacks, Tag 0DWD] is `Dualizing.isDualizingComplex_completion_henselization` in
`StacksFrontier/RingTheory/Dualizing/UbiquityDualizingComplexes/CompletionHenselization.lean`.

## References

* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
* [Stacks Project, Tag 0A7K](https://stacks.math.columbia.edu/tag/0A7K)
* [Stacks Project, Tag 0DWD](https://stacks.math.columbia.edu/tag/0DWD)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v w uL

namespace Dualizing

/-- **Stacks Project, Tag 0BFR, clause (5) for algebras essentially of finite type.** If a
Noetherian ring `A` has a dualizing complex, then so does every `A`-algebra essentially of finite
type over `A`. This is the existence form of [Stacks, Tag 0A7K]. -/
@[stacks 0BFR "clause (5), algebras essentially of finite type"]
public theorem exists_isDualizingComplex_of_essentiallyOfFiniteType {A B : Type u} [CommRing A]
    [CommRing B] [IsNoetherianRing A] [Algebra A B]
    (hB : IsEssentiallyOfFiniteType A B (algebraMap A B))
    (hA : ∃ K : DerivedCategory (ModuleCat.{u} A), IsDualizingComplex K) :
    ∃ (hB' : IsNoetherianRing B) (L : DerivedCategory (ModuleCat.{u} B)),
      @IsDualizingComplex B _ hB' _ L := by
  obtain ⟨K, hK⟩ := hA
  exact exists_isDualizingComplex_of_isEssentiallyOfFiniteType hB K hK

/-- **Stacks Project, Tag 0BFR, clause (5) for ideal-adic completions.** If a Noetherian ring `A`
has a dualizing complex, then so does its `I`-adic completion for every ideal `I`: the base
change of the dualizing complex along `A → A^∧` is one by [Stacks, Tag 0DWD] part (2). -/
@[stacks 0BFR "clause (5), ideal-adic completions"]
public theorem exists_isDualizingComplex_adicCompletion {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A)
    (hA : ∃ K : DerivedCategory (ModuleCat.{u} A), IsDualizingComplex K) :
    letI : IsNoetherianRing (AdicCompletion I A) := AdicCompletion.isNoetherianRing I
    ∃ L : DerivedCategory (ModuleCat.{u} (AdicCompletion I A)), IsDualizingComplex L := by
  obtain ⟨K, hK⟩ := hA
  exact ⟨_, isDualizingComplex_adicCompletion I K hK⟩

/-- **Stacks Project, Tag 0BFR, clause (5) for the henselization of a pair.** If a Noetherian
ring `A` has a dualizing complex, then so does the henselization `A^h` of a pair `(A, I)`: the
base change of the dualizing complex along `A → A^h` is one by [Stacks, Tag 0DWD] part (1). -/
@[stacks 0BFR "clause (5), henselization of a pair"]
public theorem exists_isDualizingComplex_henselizationPair
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (Ah : Type w) [CommRing Ah] [Algebra A Ah]
    (hh : HenselianPair Ah (I.map (algebraMap A Ah)))
    (hι : ∀ (B : Type (max u w)) (_ : CommRing B) (J : Ideal B),
      HenselianPair B J →
        ∀ f : A →+* B, I ≤ J.comap f →
          ∃! g : Ah →+* B,
            g.comp (algebraMap A Ah) = f ∧ I.map (algebraMap A Ah) ≤ J.comap g)
    (hA : ∃ K : DerivedCategory (ModuleCat.{v} A), IsDualizingComplex K) :
    letI : IsNoetherianRing Ah :=
      (henselization_isNoetherian_and_completion_equiv A I Ah hh hι).2.1
    ∃ L : DerivedCategory (ModuleCat.{max v w} Ah), IsDualizingComplex L := by
  obtain ⟨K, hK⟩ := hA
  exact ⟨_, isDualizingComplex_henselizationPair A I Ah hh hι K hK⟩

/-- **Stacks Project, Tag 0BFR, clause (5) for the henselization of a local ring.** If a
Noetherian local ring `A` has a dualizing complex, then so does its henselization: the base
change of the dualizing complex along `A → A^h` is one by [Stacks, Tag 0DWD] part (3). -/
@[stacks 0BFR "clause (5), henselization of a local ring"]
public theorem exists_isDualizingComplex_henselization
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (Ah : Type w) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) Ah]
    (hA : ∃ K : DerivedCategory (ModuleCat.{v} A), IsDualizingComplex K) :
    letI : IsNoetherianRing Ah :=
      IsLocalRing.isNoetherianRing_of_isHenselization (A := A) (B := Ah)
        (IsLocalRing.ResidueField A)
    ∃ L : DerivedCategory (ModuleCat.{max v w} Ah), IsDualizingComplex L := by
  obtain ⟨K, hK⟩ := hA
  exact ⟨_, isDualizingComplex_henselization (Ah := Ah) K hK⟩

/-- **Stacks Project, Tag 0BFR, clause (5) for a strict henselization of a local ring.** If a
Noetherian local ring `A` has a dualizing complex, then so does any henselization of `A` with a
prescribed residue field extension `L/κ(A)` — in particular a strict henselization: the base
change of the dualizing complex is one by [Stacks, Tag 0DWD] part (3). -/
@[stacks 0BFR "clause (5), strict henselization of a local ring"]
public theorem exists_isDualizingComplex_strictHenselization
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (L : Type uL) [Field L] [Algebra (IsLocalRing.ResidueField A) L]
    (Ash : Type w) [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    [IsLocalRing.IsHenselization A L Ash]
    (hA : ∃ K : DerivedCategory (ModuleCat.{max u v w} A), IsDualizingComplex K) :
    letI : IsNoetherianRing Ash :=
      IsLocalRing.isNoetherianRing_of_isHenselization (A := A) (B := Ash) L
    ∃ M : DerivedCategory (ModuleCat.{max u v w} Ash), IsDualizingComplex M := by
  obtain ⟨K, hK⟩ := hA
  exact ⟨_, isDualizingComplex_strictHenselization.{u, v, w, uL} L K hK⟩

end Dualizing

end
