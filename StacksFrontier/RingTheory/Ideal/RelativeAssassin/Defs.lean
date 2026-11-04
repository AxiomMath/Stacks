module

public import StacksFrontier.RingTheory.Ideal.RelativeAssassin

@[expose] public section

universe u v w



/-!
# The relative assassin of a module over a ring map

Let `R → S` be a ring map and let `N` be an `S`-module. A prime `𝔮` of `S` contracts to the prime
`𝔭 = R ∩ 𝔮` of `R`, and the fibre module of `N` at `𝔭` is the `S`-module `N ⊗_R κ(𝔭)`. The
*relative assassin of `N` over `S/R`* is the set of primes of `S` that are associated, over `S`,
to the fibre module of the prime they lie over:
`Ass_{S/R}(N) = {𝔮 ⊂ S | 𝔮 ∈ Ass_S(N ⊗_R κ(𝔭)) with 𝔭 = R ∩ 𝔮}`.

As motivation, it depends only on the fibre modules `N ⊗_R κ(𝔭)` over the fibre rings
`S ⊗_R κ(𝔭)`; and, as for the assassin of a module, the notion makes most sense when those fibre
rings are Noetherian, for instance when `R → S` is of finite type.

This is the set called `A` in `Module.relativeAssassin_comparison`, which compares it with the
five variants one is tempted to use instead. In particular it is also the set `A'` there: the
image of `Ass_{S ⊗_R κ(𝔭)}(N ⊗_R κ(𝔭))` under the canonical map `Spec(S ⊗_R κ(𝔭)) → Spec(S)`.

## Main definitions

* `Module.relativeAssassin R S N`: the relative assassin `Ass_{S/R}(N)`, a subset of `Spec(S)`.

## Implementation notes

The relative assassin is a subset of `PrimeSpectrum S`, the source's `Spec(S)`, rather than of
`Ideal S`: its elements carry their primality, which is what allows the contraction
`𝔭 = R ∩ 𝔮` to be formed as a point of `Spec(R)` and the residue field `κ(𝔭)` to be formed at
all.

`Ass_S` is the source's associated primes: `𝔮 ∈ Ass_S(P)` means that some `m : P` has annihilator
exactly `𝔮`, spelled `∃ m, (⊥ : Submodule S P).colon {m} = 𝔮` (membership in that ideal is
`Submodule.mem_colon_singleton`, so it is the ideal `{s | s • m = 0}`). Primality of `𝔮` is
already carried by `q : PrimeSpectrum S`, so this equation is the whole of the definition.

This is *not* Mathlib's `associatedPrimes S P`, whose members are the primes equal to the
*radical* of such an annihilator: writing `Ann(m)` for the annihilator of `m`, the three notions
in play are `∃ m, Ann(m) = 𝔮` (the associated primes), `∃ m, √Ann(m) = 𝔮` (Mathlib) and
`∃ m, 𝔮` minimal over `Ann(m)` (the weakly associated primes), and each inclusion is strict. The
first and second agree over a Noetherian ring (`isAssociatedPrime_iff`), but no Noetherian
hypothesis is available here, and the radical reading would enlarge the set: for `R = k` a field,
`S = k[x₁, x₂, …]` and `N = S/(x₁², x₂², …)`, the prime `𝔮 = (x₁, x₂, …)` is the radical of the
annihilator of `1` but is the annihilator of no element of `N ⊗_k κ((0)) ≅ N`. The correct
weakening for non-Noetherian fibre rings is the *relative weak assassin* of the following
section, not the radical of an annihilator.

`Module.relativeAssassin_comparison` describes its set `A` with Mathlib's `associatedPrimes`.
That description and this definition agree once a Noetherian hypothesis is in force, as it is in
items (3) and (5) there; the source's identification of `Ass_{S/R}(N)` with `A` is for `Ass` read
as above.

Membership is `Module.mem_relativeAssassin_iff`, which is how a reader uses the definition
without unfolding it.

Faithfulness. (1) No hypothesis is dead: the data are `R`, `S`, the ring map `algebraMap R S`
and the `S`-module `N`, and all of them occur in the defining condition; no Noetherian, finiteness
or flatness hypothesis is imposed, since the source imposes none (they enter only in the
comparisons of tag 05GB). (2) The scalars are the source's: `Ass` is taken over `S`, the tensor
product and the residue field are over `R`, and the `R`-module structure on `N` is the
restriction of scalars along `R → S` (`IsScalarTower R S N`). (3) The canonical map is pinned,
not merely required to exist: `𝔭` is `PrimeSpectrum.comap (algebraMap R S) 𝔮`, the source's
`R ∩ 𝔮`, and not some prime lying under `𝔮`. (4) The instantiation is not degenerate: for `R = k`
a field, `S = k[X]` and `N = k[X]/(X)` the only prime of `k` is `(0)` with `κ((0)) = k`, so
`Ass_{S/R}(N) = Ass_{k[X]}(k[X]/(X)) = {(X)}`; and for the identity map `R → R` with `N = R` one
gets `Ass_{R/R}(R) = Spec(R)`, because `Ass_R(κ(𝔭)) = {𝔭}`.

## References

* [StacksProject 05GC](https://stacks.math.columbia.edu/tag/05GC)

## Tags

associated prime, relative assassin, fibre module, fibre ring
-/

@[expose] public section

open TensorProduct



namespace Module

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- The **relative assassin** `Ass_{S/R}(N)` of an `S`-module `N` over a ring map `R → S`: the
set of primes `𝔮` of `S` which, with `𝔭 = R ∩ 𝔮` the contraction of `𝔮` to `R`, are associated
primes over `S` of the fibre module `N ⊗_R κ(𝔭)`, that is, are the annihilator of some element
of it. This is the set `A` of `Module.relativeAssassin_comparison`. -/
@[stacks 05GC]
public def relativeAssassin : Set (PrimeSpectrum S) :=
  {q | ∃ m : N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField,
    (⊥ : Submodule S (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)).colon
      {m} = q.asIdeal}

variable {R S N}

/-- A prime `𝔮` of `S` lies in the relative assassin of `N` over `S/R` if and only if it is the
annihilator of some element of the fibre module `N ⊗_R κ(R ∩ 𝔮)`, that is, is an associated prime
over `S` of that module. -/
public theorem mem_relativeAssassin_iff {q : PrimeSpectrum S} :
    q ∈ relativeAssassin R S N ↔
      ∃ m : N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField,
        (⊥ : Submodule S
          (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)).colon {m} =
          q.asIdeal := Iff.rfl

end Module
