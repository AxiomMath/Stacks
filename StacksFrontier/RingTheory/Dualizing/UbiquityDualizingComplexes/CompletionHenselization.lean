module

public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.AdicCompletion
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.Henselization

/-!
# Completion and henselization preserve dualizing complexes, all three parts conjoined

[Stacks, Tag 0DWD] fixes a Noetherian ring `A`, an ideal `I ⊆ A` and a dualizing complex
`ω_A^•`, and asserts three things: that `ω_A^• ⊗_A A^h` is dualizing on the henselization
`(A^h, I^h)` of the pair `(A, I)`, that `ω_A^• ⊗_A A^∧` is dualizing on the `I`-adic completion,
and that if `A` is local then `ω_A^• ⊗_A A^h`, resp. `ω_A^• ⊗_A A^{sh}`, is dualizing on the
henselization, resp. a strict henselization, of `A`. Each part is proved in its own place; this
file records the single statement that conjoins all three, so that the tag is carried whole by
one declaration and not only part by part.

## Main results

* `Dualizing.isDualizingComplex_completion_henselization` — **[Stacks, Tag 0DWD]**, the three
  parts conjoined.

## Implementation notes

The conjuncts are the statements of the per-part declarations verbatim, so this file contains no
mathematics: the proof is the tuple of those declarations. They are, in the order of the source,
`Dualizing.isDualizingComplex_henselizationPair` (part 1),
`Dualizing.isDualizingComplex_adicCompletion` (part 2) and
`Dualizing.isDualizingComplex_henselization` together with
`Dualizing.isDualizingComplex_strictHenselization` (part 3); each keeps its own
`@[stacks 0DWD]` registration naming its part.

The source's `ω_A^• ⊗_A A'` is `ModuleCat.extendScalars` along `A → A'` applied degreewise and
passed to derived categories; since every one of the four ring maps is flat, that functor is
exact and the ordinary extension of scalars computes the derived tensor product, so the four
displayed functors are the source's four base changes. Flatness and Noetherianness of the new
ring are conclusions of the cited lemmas rather than hypotheses, but the statement already needs
them — `Dualizing.IsDualizingComplex` over `A'` needs `IsNoetherianRing A'`, and
`ModuleCat.extendScalars` acts on derived categories only because it is exact — so they are
introduced by `haveI` inside the statement exactly as in the per-part declarations. All of them
are propositions, so this pins no data.

The module universe is `max u v w`, for `A : Type u` and the henselizations in `Type w`: that is
the index at which all four parts are available, part (3) for a strict henselization being the
one that constrains it, as explained in the implementation notes of
`StacksFrontier/RingTheory/Dualizing/UbiquityDualizingComplexes/Henselization.lean`. The three
dedicated statements are each free of some of that constraint and are the ones to use; this
conjunction exists to carry the tag.

The existence form of all four parts, which is how clause (5) of [Stacks, Tag 0BFR] uses them,
is in `StacksFrontier/RingTheory/Dualizing/UbiquityStability.lean`.

## References

* [Stacks Project, Tag 0DWD](https://stacks.math.columbia.edu/tag/0DWD)
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
-/

@[expose] public section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.extendScalars_additive
  Dualizing.extendScalars_preservesFiniteLimits_of_flat
  Dualizing.extendScalars_preservesFiniteColimits_of_flat

universe u v w t

namespace Dualizing

/-- **Stacks Project, Tag 0DWD.** Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal and let
`ω_A^•` be a dualizing complex. Then

1. `ω_A^• ⊗_A A^h` is a dualizing complex on the henselization `(A^h, I^h)` of the pair
   `(A, I)`,
2. `ω_A^• ⊗_A A^∧` is a dualizing complex on the `I`-adic completion `A^∧`, and
3. if `A` is local, then `ω_A^• ⊗_A A^h`, resp. `ω_A^• ⊗_A A^{sh}`, is a dualizing complex on
   the henselization, resp. a strict henselization, of `A`.

The conjuncts are `Dualizing.isDualizingComplex_henselizationPair`,
`Dualizing.isDualizingComplex_adicCompletion`, `Dualizing.isDualizingComplex_henselization` and
`Dualizing.isDualizingComplex_strictHenselization`, each of which carries the tag for its own
part. As there, part (3) for a strict henselization is stated for a henselization of `A` along
an arbitrary prescribed extension `κ(A) ⊆ L` of its residue field, which is a strict
henselization exactly when `L` is a separable algebraic closure of `κ(A)`. -/
@[stacks 0DWD "all three parts conjoined"]
theorem isDualizingComplex_completion_henselization
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{max u v w} A)) (hK : IsDualizingComplex K) :
    (∀ (Ah : Type w) [CommRing Ah] [Algebra A Ah]
        (hh : HenselianPair Ah (I.map (algebraMap A Ah)))
        (hι : ∀ (B : Type (max u w)) (_ : CommRing B) (J : Ideal B),
          HenselianPair B J →
            ∀ f : A →+* B, I ≤ J.comap f →
              ∃! g : Ah →+* B,
                g.comp (algebraMap A Ah) = f ∧ I.map (algebraMap A Ah) ≤ J.comap g),
        haveI : Module.Flat A Ah :=
          (flat_henselization_and_bijective_quotientMap A I Ah hh hι).1
        haveI : IsNoetherianRing Ah :=
          (henselization_isNoetherian_and_completion_equiv A I Ah hh hι).2.1
        IsDualizingComplex
          ((ModuleCat.extendScalars.{u, w, max u v w}
            (algebraMap A Ah)).mapDerivedCategory.obj K)) ∧
    IsDualizingComplex
      ((ModuleCat.extendScalars.{u, u, max u v w}
        (algebraMap A (AdicCompletion I A))).mapDerivedCategory.obj K) ∧
    ∀ [IsLocalRing A],
      (∀ (Ah : Type w) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
          [IsHenselization A (ResidueField A) Ah],
          haveI : Module.Flat A Ah := IsHenselization.flat (L := ResidueField A)
          haveI : IsNoetherianRing Ah :=
            isNoetherianRing_of_isHenselization (A := A) (B := Ah) (ResidueField A)
          IsDualizingComplex
            ((ModuleCat.extendScalars.{u, w, max u v w}
              (algebraMap A Ah)).mapDerivedCategory.obj K)) ∧
      (∀ (L : Type t) [Field L] [Algebra (ResidueField A) L]
          (Ash : Type w) [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
          [IsHenselization A L Ash],
          haveI : Module.Flat A Ash := IsHenselization.flat (L := L)
          haveI : IsNoetherianRing Ash :=
            isNoetherianRing_of_isHenselization (A := A) (B := Ash) L
          IsDualizingComplex
            ((ModuleCat.extendScalars.{u, w, max u v w}
              (algebraMap A Ash)).mapDerivedCategory.obj K)) :=
  ⟨fun Ah _ _ hh hι ↦ isDualizingComplex_henselizationPair A I Ah hh hι K hK,
    isDualizingComplex_adicCompletion I K hK,
    ⟨fun Ah _ _ _ _ ↦ isDualizingComplex_henselization (Ah := Ah) K hK,
      fun L _ _ Ash _ _ _ _ ↦
        isDualizingComplex_strictHenselization.{u, v, w, t} (Ash := Ash) L K hK⟩⟩

end Dualizing

end
