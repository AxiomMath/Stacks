module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass

/-!
# The first Chern class of an invertible module as a bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `ℒ` be an invertible `O_X`-module. **Stacks 0B77** says
that the rule assigning to every `f : X' ⟶ X` locally of finite type the operation

  `c₁(f^*ℒ) ∩ - : CH_k(X') ⟶ CH_{k-1}(X')`

is a bivariant class of degree `1`, that is, an element of `A^1(X ⟶ X)`. The source deduces it
from four earlier results: the projection formula of Stacks 02SU, the flat-pullback identity of
Stacks 02SS, the descent of the cap product to Chow groups of Stacks 02TI, and the commutation
with Gysin maps of Stacks 0B72.

The cap operation is forced by the characterization
`Stacks.Chow.IsFirstChernClassBivariant` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FirstChernClass`, so the content of the lemma is
the three naturality axioms of Stacks 0B76 for that operation. Each of Stacks 02SU, 02SS and 0B72
is an identity on the test scheme `X'`, while the axioms of a bivariant class are identities on
the chosen categorical pullback `X ×_X X'`; the transport of all three across the isomorphism
`X ×_X X' ≅ X'` is proved in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass`, and this file applies it to
the first Chern class operation and assembles the class.

## Main definitions

* `Stacks.Chow.firstChernClassBivariant` — **Stacks 0B77**, the bivariant class of degree `1`
  for `𝟙 X` given by capping with the first Chern class of `ℒ`.

## Main results

* `Stacks.Chow.firstChernClassBivariant_cap` — its cap operation is the forced one,
  `Stacks.Chow.firstChernClassBivariantCap`.
* `Stacks.Chow.isFirstChernClassBivariant_firstChernClassBivariant` — **Stacks 0B77**: the class
  does satisfy the characterization, that is, it caps by `c₁(f^*ℒ) ∩ -` on every test scheme.
* `Stacks.Chow.eq_firstChernClassBivariant` — it is the only bivariant class with that property.

## Implementation notes

### What is assumed, and which proof step each hypothesis stands for

Four hypotheses are carried, one for each result the source proof cites, and each is that result
read for the cap operation on the *test schemes*:

* `hproper` is `Stacks.Chow.IdentityCapRule.ProperNaturality`, the projection formula of
  **Stacks 02SU**. The library proves it for the cap product of an invertible module as
  `Stacks.Chow.properChowPushforward_firstChernClassCap` of
  `StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward`, under the integral-component
  hypothesis `Stacks.Chow.FirstChernCapCompatibleWithPushforward`.
* `hflat` is `Stacks.Chow.IdentityCapRule.FlatNaturality`, the identity
  `f^*(c₁(ℒ) ∩ α) = c₁(f^*ℒ) ∩ f^*α` of **Stacks 02SS**. The library proves it as
  `Stacks.Chow.flatPullbackChow_firstChernClassCapOnChow` of
  `StacksFrontier.AlgebraicGeometry.Chow.ChernClasses.FlatPullback`, under the integral-component
  hypothesis `Stacks.Chow.FirstChernCapCompatibleWithFlatPullback`.
* `hgysin` is `Stacks.Chow.IdentityCapRule.GysinNaturality`, the identity
  `c₁(ℒ|_D) ∩ i^*α = i^*(c₁(ℒ) ∩ α)` of **Stacks 0B72**. The library proves it as
  `Stacks.Chow.gysinHomomorphismOnChow_firstChernClassCapOnChow` of
  `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCap`, under the integral-component hypothesis
  `Stacks.Chow.GysinCommutesWithChernCapOnComponents`.
* `hiso` is `Stacks.Chow.GysinSystem.IsNaturalUnderInverseIso`, the isomorphism case of
  **Stacks 02TA** for the Gysin system the axioms of Stacks 0B76 are stated against. It is not a
  step of the source proof but of the transport: the Gysin axiom compares the Gysin map on a test
  scheme with the Gysin map on its identity base change, and nothing in
  `Stacks.Chow.GysinSystem` relates those two, as the counterexample in
  `StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward` shows.

Two of the four are derivable; the obstruction described above is real but is not an obstruction to `hproper` or `hiso`.

* `hproper` **is** derivable at the canonical cap product, as
  `Stacks.Chow.properNaturality_firstChernIdentityCapRule` of
  `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FirstChernClassCanonical`, with no hypothesis. The
  library's integral-component form of Stacks 02SU is stated for one fixed pair of component rules
  of Stacks 02SO, but at the rules of an invertible module and its pullback the identity is
  unconditional — `Stacks.Chow.properChowPushforward_firstChernClassCapOfInvertible_of_isProper'` —
  so all that is needed to quantify over test schemes is the coherence isomorphism
  `(h ∘ g)^*ℒ ≅ h^*(g^*ℒ)` (the pullback of modules being functorial only up to isomorphism)
  together with the invariance of the cap product under isomorphism of invertible modules.
* `hiso` **is** dischargeable for the canonical Gysin system, by
  `Stacks.Chow.GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso` of
  `StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InverseIsoGysin` through
  `Stacks.Chow.gysinSystemOfInvertible_eq_canonicalGysinSystem`. It is a property of the system,
  not of the cap product, so no integral-component input enters it at all.
* `hflat` is not discharged yet, but is not blocked on a missing tag either: the cycle-level
  Stacks 02SS at the rules of an invertible module and its pullback is unconditional, as
  `Stacks.Chow.flatPullback_firstChernCapOfInvertible_rationallyEquivalent`. What remains is the
  same coherence bridge as for `hproper`, plus the degree transports the `HEq` in the predicate
  carries.
* `hgysin` is the one genuinely blocked case; see the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FirstChernClass`, which record that it reduces to
  Stacks 02TM read on the integral closed subschemes of a test scheme, and that Stacks 02TM itself
  is proved with no hypothesis for an *integral ambient* scheme but the restriction bridge to the
  integral components of a general one has no producer.

### The cap product is a parameter

`Stacks.Chow.FirstChernCapRule`, the datum standing for Stacks 02SO together with the vanishing
of Stacks 02TI, is a parameter rather than quantified over, for the reason recorded in the
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic`: for a `Prop`
hypothesis quantifying is free by proof irrelevance, while for **data** `∀ G, P G` is strictly
stronger than `P G₀`, and over-strengthening is as unfaithful to the source as weakening.
Substituting the genuine cap product turns the class below into the one of Stacks 0B77 verbatim,
and `Stacks.Chow.eq_firstChernClassBivariant` shows it does not depend on which proofs of the
four hypotheses are supplied.

## References

* [Stacks Project, Tag 0B77](https://stacks.math.columbia.edu/tag/0B77)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 0B72](https://stacks.math.columbia.edu/tag/0B72)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (fcap : FirstChernCapRule C) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (G : GysinSystem C)
  (hproper : IdentityCapRule.ProperNaturality C sX 1 (firstChernIdentityCapRule C sX fcap L))
  (hflat : IdentityCapRule.FlatNaturality C sX 1 (firstChernIdentityCapRule C sX fcap L))
  (hgysin : IdentityCapRule.GysinNaturality C sX 1 (firstChernIdentityCapRule C sX fcap L) G)
  (hiso : G.IsNaturalUnderInverseIso)

/-- **Stacks 0B77.** The first Chern class of an invertible module `ℒ` on `X` as a bivariant
class of degree `1` for the identity of `X`: the rule that assigns to every `f : X' ⟶ X` locally
of finite type the operation `c₁(f^*ℒ) ∩ - : CH_k(X') ⟶ CH_{k-1}(X')` is an element of
`A^1(X ⟶ X)`.

Its cap operation is the one forced by `Stacks.Chow.IsFirstChernClassBivariant`, and the three
naturality axioms of Stacks 0B76 for it are the projection formula of Stacks 02SU, the
flat-pullback identity of Stacks 02SS and the Gysin identity of Stacks 0B72, each read on the
test schemes and transported here to the chosen pullbacks `X ×_X X'`. -/
def firstChernClassBivariant : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) 1 :=
  firstChernClass C sX fcap L G hproper
    (IdentityCapRule.transportFlatNaturality C sX 1 (firstChernIdentityCapRule C sX fcap L) hflat)
    (IdentityCapRule.transportGysinNaturality C sX 1 (firstChernIdentityCapRule C sX fcap L) G
      hgysin hiso)

/-- The cap operation of the bivariant first Chern class is the transport of
`α ↦ c₁(g^*ℒ) ∩ α` to the chosen pullback `X ×_X T`. -/
theorem firstChernClassBivariant_cap {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (k : ℤ) :
    (firstChernClassBivariant C sX fcap L G hproper hflat hgysin hiso).cap g k =
      firstChernClassBivariantCap C sX fcap L g k :=
  rfl

/-- **Stacks 0B77.** The class constructed above is the bivariant first Chern class of `ℒ`: on
every test scheme `g : T ⟶ X` and in every degree, pushing `c₁(ℒ) ∩ α` forward along the
projection `X ×_X T ⟶ T` gives `c₁(g^*ℒ) ∩ α`. So the rule of the statement really is the cap
operation of a bivariant class of degree `1`. -/
theorem isFirstChernClassBivariant_firstChernClassBivariant :
    IsFirstChernClassBivariant C sX fcap L G
      (firstChernClassBivariant C sX fcap L G hproper hflat hgysin hiso) :=
  isFirstChernClassBivariant_firstChernClass C sX fcap L G hproper
    (IdentityCapRule.transportFlatNaturality C sX 1 (firstChernIdentityCapRule C sX fcap L) hflat)
    (IdentityCapRule.transportGysinNaturality C sX 1 (firstChernIdentityCapRule C sX fcap L) G
      hgysin hiso)

/-- **Stacks 0B77, uniqueness.** The bivariant first Chern class is the only bivariant class of
degree `1` for the identity of `X` that caps by `c₁(g^*ℒ) ∩ -` on every test scheme. In
particular it does not depend on which proofs of the four hypotheses are supplied. -/
theorem eq_firstChernClassBivariant
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) 1)
    (hc : IsFirstChernClassBivariant C sX fcap L G c) :
    c = firstChernClassBivariant C sX fcap L G hproper hflat hgysin hiso :=
  eq_of_isFirstChernClassBivariant C sX fcap L G hc
    (isFirstChernClassBivariant_firstChernClassBivariant C sX fcap L G hproper hflat hgysin hiso)

end Stacks.Chow

end
