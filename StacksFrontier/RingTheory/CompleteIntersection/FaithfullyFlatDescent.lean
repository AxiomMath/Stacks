module

public import StacksFrontier.RingTheory.LocalCompleteIntersection.Basic
public import StacksFrontier.RingTheory.LocalCompleteIntersection.FlatDescent
public import StacksFrontier.RingTheory.LocalCompleteIntersection.FlatLocalHomomorphism

/-!
# The complete intersection property descends along a faithfully flat ring map

Let `k` be a field and let `S → T` be a faithfully flat map of finite type `k`-algebras. This
file proves that if `T` is a local complete intersection over `k` (Definition 00S9 (2)) then so
is `S`.

The argument is the one that proves the same statement for regularity, Lemma 07NG. Let `𝔭` be a
prime of `S`. Faithful flatness makes `Spec T → Spec S` surjective, so there is a prime `𝔮` of
`T` lying over `𝔭`, and the induced map `S_𝔭 → T_𝔮` is a flat local homomorphism of Noetherian
local rings. The complete intersection property of a Noetherian local ring descends along such a
map: by Lemma 09Q2 the completion of `T_𝔮` is a complete intersection exactly when the completion
of `S_𝔭` and the completion of the closed fibre both are, and only the first conjunct is wanted.
Over a field of finite type the intrinsic property at every prime is the relative one, Lemma
09Q6, which turns this into the statement about `IsLocalCompleteIntersection`.

Nothing is needed about the closed fibre of `S_𝔭 → T_𝔮`, which is what makes the descent
direction so much cheaper than the ascent: the forward implication of Lemma 09Q2 hands over the
base conjunct unconditionally.

## Main results

* `LocalCompleteIntersection.isCompleteIntersectionRing_iff_adicCompletion`: a Noetherian local
  ring is a complete intersection exactly when its completion is one in the presentation-free
  sense for complete local rings.
* `LocalCompleteIntersection.isCompleteIntersectionRing_of_flat`: the complete intersection
  property of a Noetherian local ring descends along a flat local homomorphism. This is the
  base conjunct of [Stacks Project, Tag 09Q2].
* `IsLocalCompleteIntersection.of_faithfullyFlat`: being a local complete intersection over a
  field descends along a faithfully flat map of finite type algebras.

## Implementation notes

`LocalCompleteIntersection.IsCompleteIntersectionRing` and
`LocalCompleteIntersection.IsCompleteIntersectionCompleteLocalRing` differ only by the
completeness clause, the first asking of a Noetherian local ring what the second asks of its
completion; `isCompleteIntersectionRing_iff_adicCompletion` is that comparison, and it is what
lets Lemma 09Q2 — stated for completions — be read as a statement about the rings themselves.

The flat local homomorphism `S_𝔭 → T_𝔮` is `Localization.localRingHom`, whose flatness is
`RingHom.Flat.localRingHom` and whose locality is `Localization.isLocalHom_localRingHom`, the
same three ingredients `IsRegularRing.of_faithfullyFlat` uses. The prime `𝔮` comes from
`Ideal.exists_isPrime_liesOver_of_faithfullyFlat`.

## References

* [Stacks Project, Tag 07NG](https://stacks.math.columbia.edu/tag/07NG)
* [Stacks Project, Tag 09Q2](https://stacks.math.columbia.edu/tag/09Q2)
* [Stacks Project, Tag 09Q6](https://stacks.math.columbia.edu/tag/09Q6)
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace LocalCompleteIntersection

/- `isCompleteIntersectionRing_iff_adicCompletion` and `isCompleteIntersectionRing_of_flat`
stood here. Each was declared a second time, under this same fully-qualified name in this same
`LocalCompleteIntersection` namespace, in
`StacksFrontier/RingTheory/LocalCompleteIntersection/FlatDescent.lean` -- at :67 and :99 there --
with an identical statement and a different proof. Two public declarations sharing a
fully-qualified name is a collision, not a mere duplication: a module importing both cannot name
either unambiguously. Both are deleted here in favour of that module's, which this one now
imports: it is the canonical home, holding the tagged `@[stacks 09Q7]`
`isCompleteIntersectionRing_iff_of_flat` of which `isCompleteIntersectionRing_of_flat` is one
half, together with the closed-fibre half, and having two importers to this file's one.

`IsLocalCompleteIntersection.of_faithfullyFlat` below is NOT merged onto that module's
`isLocalCompleteIntersection_of_faithfullyFlat`
(`StacksFrontier/RingTheory/LocalCompleteIntersection/FlatDescent.lean`), although the two prove
the same thing: this one takes `S : Type v` and `T : Type w` in two universes where that one
takes `A B : Type v` in one, so it is strictly more general and merging it onto the other would
weaken it. -/

end LocalCompleteIntersection

/-- **Being a local complete intersection over a field descends along a faithfully flat map.**
Let `k` be a field and let `S → T` be a map of finite type `k`-algebras which is faithfully
flat. If `T` is a local complete intersection over `k` (Definition 00S9 (2)) then so is `S`.

Lemma 09Q6 reads both sides as conditions on the local rings, intrinsically; a prime `𝔮` of `T`
over a given prime `𝔭` of `S` makes `S_𝔭 → T_𝔮` a flat local homomorphism of Noetherian local
rings, and `LocalCompleteIntersection.isCompleteIntersectionRing_of_flat` transfers the property
from `T_𝔮` to `S_𝔭`. -/
theorem IsLocalCompleteIntersection.of_faithfullyFlat (k : Type u) [Field k] (S : Type v)
    (T : Type w) [CommRing S] [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T]
    [IsScalarTower k S T] [Algebra.FiniteType k S] [Algebra.FiniteType k T]
    [Module.FaithfullyFlat S T] (hT : IsLocalCompleteIntersection k T) :
    IsLocalCompleteIntersection k S := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing k T
  have hT' :=
    (LocalCompleteIntersection.isLocalCompleteIntersection_iff_isLocalCompleteIntersectionRing
      k T).mp hT
  refine
    (LocalCompleteIntersection.isLocalCompleteIntersection_iff_isLocalCompleteIntersectionRing
      k S).mpr fun p hp => ?_
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (A := S) (B := T) p
  have hcomap : p = q.comap (algebraMap S T) := hqp.over
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q (algebraMap S T) hcomap).toAlgebra
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) q p hcomap
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom p q (algebraMap S T) hcomap
  exact LocalCompleteIntersection.isCompleteIntersectionRing_of_flat _
    (Localization.AtPrime q) (hT' q)

end
