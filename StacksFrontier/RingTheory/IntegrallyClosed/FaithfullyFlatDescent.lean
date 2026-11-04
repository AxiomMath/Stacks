module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Normality descends along a faithfully flat ring map

Proof of Stacks 033G. Let `R → S` be a faithfully flat ring map with `S` a normal ring, i.e. with
`S_𝔮` a normal domain for every prime `𝔮` of `S`. Then `R` is a normal ring.

Let `𝔭` be a prime of `R`. Faithful flatness makes `Spec S → Spec R` surjective, so there is a
prime `𝔮` of `S` lying over `𝔭`, and `R_𝔭 → S_𝔮` is again flat; being a local homomorphism of
local rings it is faithfully flat. So it suffices to descend normality of a *domain*: if `A → B`
is faithfully flat with `B` an integrally closed domain, then `A` is an integrally closed domain.
That descent splits into two halves that share no hypotheses.

Upstairs, where `B` is normal: a fraction `a / b ∈ Frac(A)` integral over `A` is integral over `B`
in `Frac(B)`, hence of the form `c ∈ B`, and comparing in `Frac(B)` gives `a = b · c` in `B`. So
`b ∣ a` holds after the map to `B`.

Downstairs, where `A → B` is faithfully flat: divisibility descends, because such a map contracts
the extension of the ideal `bA` back to `bA` — this is the source's "`a : A → A/bA` becomes zero
after base change to `B`". Hence `b ∣ a` in `A`, that is, `a / b ∈ A`.

## Main results

* `Stacks.IntegrallyClosed.FlatDescent.solution`: the statement of Stacks Tag 033G.

## Implementation notes

The statement `IsIntegrallyClosed.of_faithfullyFlat` that Mathlib lacks — the faithfully flat
analogue of `IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn`, which does not
apply here because `A` need not be integrally closed *in* `B`, as `ℤ → ℤ[i]` shows — is the second
conjunct of `isDomain_and_isIntegrallyClosed_of_faithfullyFlat` below. The source reduces to the
local case only to have a normal *domain* upstairs; the descent itself needs no locality, and is
proved in that generality.

Faithful flatness is used in exactly two ways, and the two are separated: injectivity of
`algebraMap A B`, which gives the `IsDomain` conjunct outright, and
`algebraMap_dvd_algebraMap_iff`, the descent of divisibility, which is
`Ideal.comap_map_eq_self_of_faithfullyFlat` on a principal ideal.

The reduction to the local case is carried out by Mathlib's API for localizations at lying-over
primes rather than by hand: `Ideal.exists_isPrime_liesOver_of_faithfullyFlat` produces `𝔮`,
`Localization.AtPrime.algebraOfLiesOver` is the `R_𝔭`-algebra structure on `S_𝔮` (a `def`, not an
instance, so it is introduced by `let`), and flatness of `R_𝔭 → S_𝔮` is then an instance.
Faithful flatness follows from `Module.FaithfullyFlat.of_flat_of_isLocalHom`, since
`Localization.localRingHom` is a local homomorphism.

## References

* [Stacks 033G](https://stacks.math.columbia.edu/tag/033G)
  (`algebra-lemma-descend-normal`); the passage to `S_𝔮` is Lemma 00HR.
-/

namespace Stacks.IntegrallyClosed.FlatDescent

/-- Divisibility descends along a faithfully flat algebra map: if `b ∣ a` holds after the map to a
faithfully flat `A`-algebra `B`, it holds in `A`. -/
public theorem algebraMap_dvd_algebraMap_iff (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {a b : A} :
    algebraMap A B b ∣ algebraMap A B a ↔ b ∣ a := by
  rw [← Ideal.mem_span_singleton, ← Ideal.mem_span_singleton,
    ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (Ideal.span {b}), Ideal.mem_comap,
    Ideal.map_span, Set.image_singleton]

/-- If `B` is an integrally closed domain and `A → B` is injective, then a fraction `a / b` of
`Frac(A)` which is integral over `A` becomes divisible in `B`: there `b ∣ a`. -/
private theorem algebraMap_dvd_algebraMap_of_isIntegral_mk' (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [IsDomain B] [IsIntegrallyClosed B] (hinj : Function.Injective (algebraMap A B))
    {a : A} {b : nonZeroDivisors A}
    (hx : IsIntegral A (IsLocalization.mk' (FractionRing A) a b)) :
    algebraMap A B (b : A) ∣ algebraMap A B a := by
  have : IsDomain A := hinj.isDomain _
  have hinjL : Function.Injective (algebraMap A (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hinj
  -- The induced map on fraction fields.
  let φ : FractionRing A →ₐ[A] FractionRing B :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId A (FractionRing B)) hinjL
  obtain ⟨c, hc⟩ :=
    IsIntegrallyClosed.isIntegral_iff.mp ((hx.map φ).tower_top : IsIntegral B _)
  refine ⟨c, IsFractionRing.injective B (FractionRing B) ?_⟩
  have h := congrArg φ (IsLocalization.mk'_spec (FractionRing A) a b)
  rw [map_mul, φ.commutes, φ.commutes, ← hc] at h
  rw [map_mul, ← IsScalarTower.algebraMap_apply A B (FractionRing B),
    ← IsScalarTower.algebraMap_apply A B (FractionRing B), mul_comm]
  exact h.symm

/-- If `B` is a faithfully flat `A`-algebra which is an integrally closed domain, then `A` is one
too. -/
@[ega "IV 2.1.13" "more general"]
private theorem isDomain_and_isIntegrallyClosed_of_faithfullyFlat (A B : Type*) [CommRing A]
    [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B] [IsDomain B] [IsIntegrallyClosed B] :
    IsDomain A ∧ IsIntegrallyClosed A := by
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  refine ⟨hinj.isDomain _, (isIntegrallyClosed_iff (FractionRing A)).mpr ?_⟩
  intro x hx
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) x
  obtain ⟨r, hr⟩ := (algebraMap_dvd_algebraMap_iff A B).mp
    (algebraMap_dvd_algebraMap_of_isIntegral_mk' A B hinj hx)
  exact ⟨r, by rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, mul_comm, ← hr]⟩

/-- **Stacks 033G.** Let `R → S` be a faithfully flat ring map. If `S` is a normal ring, i.e. all
its localizations at primes are normal domains, then so is `R`. -/
@[ega "IV 2.1.13" "special case"]
public theorem solution {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (hS : ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  intro p _
  -- A prime of `S` lying over `p`, which exists since `Spec S → Spec R` is surjective.
  obtain ⟨q, hq, hlo⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := S) p
  obtain ⟨_, _⟩ := hS q
  -- `R_p → S_q` is a flat local homomorphism of local rings, hence faithfully flat.
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact isDomain_and_isIntegrallyClosed_of_faithfullyFlat _ (Localization.AtPrime q)

end Stacks.IntegrallyClosed.FlatDescent

/-!
# Normality descends along a faithfully flat ring map

A commutative ring `R` is a *normal ring* (Definition 00GV) when the localization `R_𝔭` is a
normal domain — a domain integrally closed in its fraction field — for every prime `𝔭` of `R`.
This descends along a faithfully flat ring map: if `R → S` is faithfully flat and `S` is a normal
ring, then `R` is a normal ring.

The source's argument reduces to the local case twice. Localizing at a prime `𝔭` of `R` and then
at a prime `𝔮` of `S` lying over `𝔭` keeps the map faithfully flat, so one may assume `R` and `S`
local and `S` a normal domain; then `R` is a domain because `R → S` is injective, and for
`a, b ∈ R` with `a/b` integral over `R` one has `a/b ∈ S`, so multiplication by `a` on `R/bR`
vanishes after base change to `S`, whence `a ∈ bR` by faithful flatness.

## Main results

* `isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat`: if a faithfully flat algebra over
  `R` is a normal ring, then so is `R`.

## Implementation notes

Mathlib has no predicate for a normal ring — its `IsIntegrallyClosed` file describes one in prose
and cites tag 00GV, but stops there — so "`R` is a normal ring" is inlined as
"`Localization.AtPrime 𝔭` is a domain and is integrally closed, for every prime `𝔭`", both in the
hypothesis on `S` and in the conclusion about `R`. That is the spelling used for item (1) of tag
030C and for tag 031S, and the shape `isRegularRing_iff` uses for the same kind of local condition,
so a later promotion of that predicate turns this statement into `IsNormalRing S → IsNormalRing R`
by `Iff.rfl`. The `IsDomain` conjunct is genuine content in both places: `IsIntegrallyClosed` is
Mathlib's `IsIntegrallyClosedIn R (FractionRing R)`, which carries no domain hypothesis, and
neither `R` nor `S` is assumed to be a domain here — a finite product of normal domains is a normal
ring (tag 0CYA), so the statement has non-domain content.

The source's ring map `R → S` is an `Algebra R S` instance, and faithful flatness is the class
`Module.FaithfullyFlat R S` on the module `S` over `R`; that is the same condition on
`algebraMap R S` as `RingHom.FaithfullyFlat`, by `RingHom.faithfullyFlat_algebraMap_iff`, and it
is the form Mathlib's descent API consumes.

Faithfulness to [StacksProject 033G]:

1. No dead hypothesis. Flatness alone does not suffice: for the cuspidal domain
   `R = ℤ[x, y]/(y² - x³)`, the map to `S = FractionRing R` is flat, being a localization, and
   `S` is a field, hence a normal ring, while `R` is not normal (`y/x` is integral over `R` and
   not in `R`); what fails is surjectivity of `Spec(S) → Spec(R)`, i.e. faithfulness. The
   hypothesis on `S` is load-bearing too: `S = R` is faithfully flat over any `R`.
2. The scalars and base are the source's. Integrality is read in each ring's own fraction field —
   over `S_𝔮` inside `Frac(S_𝔮)` in the hypothesis, over `R_𝔭` inside `Frac(R_𝔭)` in the
   conclusion — and there is no base change; faithful flatness is of `S` as an `R`-module.
3. The canonical map is pinned. The source's `R → S` is `algebraMap R S`, and the hypothesis is
   faithful flatness of that map, not the existence of some faithfully flat `R`-algebra structure.
4. The instantiation is not degenerate. `R = ℤ × ℤ` and `S = ℤ[i] × ℤ[i]`, free of rank `2` over
   `R` hence faithfully flat, satisfy the hypothesis without either ring being a domain, and the
   conclusion for them is the normality of `ℤ × ℤ`.

## References

* [StacksProject 033G](https://stacks.math.columbia.edu/tag/033G)

## Tags

normal ring, normal domain, faithfully flat, descent
-/

@[expose] public section

/-- **Stacks 033G.** Let `R → S` be a faithfully flat ring map. If `S` is a normal ring, i.e. all
its localizations at primes are normal domains, then so is `R`. -/
@[stacks 033G "Normality is inlined as `IsDomain` plus `IsIntegrallyClosed` on \
  `Localization.AtPrime 𝔭` for every prime `𝔭`, as in item (1) of tag 030C and in tag 031S, \
  Mathlib having no predicate for a normal ring; the ring map `R → S` is an `Algebra R S` \
  instance and its faithful flatness is `Module.FaithfullyFlat R S`. See the module docstring.",
  ega "IV 6.5.4" "(i), affine case", ega "IV 2.1.13" "special case", ega "IV 7.5.3" "(vi)"]
public theorem isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    (hS : ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) :=
    Stacks.IntegrallyClosed.FlatDescent.solution hS

end
