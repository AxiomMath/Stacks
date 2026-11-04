module

public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# Regularity descends along a faithfully flat ring map

Proof of Stacks 07NG. Let `R → S` be a faithfully flat ring map with `S` a regular ring. Then `R`
is a regular ring.

The proof is the source's. First `R` is Noetherian: Noetherianness descends along a faithfully flat
ring map (Lemma 033E). Now let `𝔭` be a prime of `R`. Faithful flatness makes `Spec S → Spec R`
surjective, so there is a prime `𝔮` of `S` lying over `𝔭`, and the induced map `R_𝔭 → S_𝔮` is a
flat local homomorphism of Noetherian local rings whose target is regular, `S` being a regular
ring. Hence `R_𝔭` is regular by Lemma 00OF. As `𝔭` was arbitrary, `R` is regular.

## Main results

* `Stacks.RegularRing.FlatDescent.solution`: the statement of Stacks Tag 07NG.

## Implementation notes

Lemma 033E, the Noetherian descent, is `IsNoetherianRing.of_faithfullyFlat` below. It is not a
tagged statement here and Mathlib has no ring-level form of it, but it
is one step from Mathlib's module-level form: `IsNoetherian R M` descends from
`IsNoetherian S (S ⊗[R] M)` by
`Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat`, and `IsNoetherianRing R`
is `IsNoetherian R R`, whose base change `S ⊗[R] R` is `S` by `Algebra.TensorProduct.rid`. So no
ascending chain argument is needed.

The map `R_𝔭 → S_𝔮` is `Localization.localRingHom`, which needs `𝔭 = 𝔮.comap (algebraMap R S)`;
that is exactly the field of the `Ideal.LiesOver` produced by
`Ideal.exists_isPrime_liesOver_of_faithfullyFlat`. Its flatness is
`RingHom.Flat.localRingHom` and its locality is `Localization.isLocalHom_localRingHom`, and
`R_𝔭` is Noetherian by `IsLocalization.isNoetherianRing`; these are the four hypotheses of
`IsRegularLocalRing.of_flat_of_isLocalHom`. The regularity of `S_𝔮` is `IsRegularRing`'s own field
`IsRegularRing.isRegularLocalRing_localization`.

## References

* [StacksProject 07NG](https://stacks.math.columbia.edu/tag/07NG)

## Tags

regular ring, faithfully flat, descent, regular local ring, Noetherian ring
-/

@[expose] public section

namespace Stacks.RegularRing.FlatDescent



open TensorProduct in
/-- **Noetherianness descends along a faithfully flat ring map** (Stacks 033E). This is the
ring-level shadow of Mathlib's module-level
`Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat`, applied to `M = R`
after identifying `S ⊗[R] R` with `S`. -/
@[ega "0 6.5.2" "special case"]
private theorem IsNoetherianRing.of_faithfullyFlat {R : Type u} (S : Type v) [CommRing R]
    [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] [IsNoetherianRing S] :
    IsNoetherianRing R :=
  Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat (A := S)
    (isNoetherian_of_linearEquiv (Algebra.TensorProduct.rid R S S).symm.toLinearEquiv)

/-- **Regularity descends along a faithfully flat ring map** (Stacks 07NG): if `S` is a
faithfully flat `R`-algebra and a regular ring, then `R` is a regular ring. -/
public theorem solution {R : Type u} (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] [IsRegularRing S] : IsRegularRing R := by
  have hR : IsNoetherianRing R := IsNoetherianRing.of_faithfullyFlat S
  rw [isRegularRing_iff]
  intro p hp
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (A := R) (B := S) p
  have hcomap : p = q.comap (algebraMap R S) := hqp.over
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q (algebraMap R S) hcomap).toAlgebra
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) q p hcomap
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom p q (algebraMap R S) hcomap
  have : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ hR
  exact IsRegularLocalRing.of_flat_of_isLocalHom (Localization.AtPrime q)

end Stacks.RegularRing.FlatDescent

end

/-!
# Regularity descends along a faithfully flat ring map

A commutative ring `R` is *regular* when it is Noetherian and `R_𝔭` is a regular local ring for
every prime `𝔭` of `R`. This property descends along a faithfully flat ring map: if `R → S` is
faithfully flat and `S` is regular, then `R` is regular.

The source's proof. `R` is Noetherian by Lemma 033E, Noetherianness descending along a faithfully
flat ring map. Let `𝔭 ⊂ R` be a prime and choose a prime `𝔮 ⊂ S` lying over it, which exists
because faithful flatness makes `Spec S → Spec R` surjective. Then `R_𝔭 → S_𝔮` is a flat local
homomorphism of Noetherian local rings with `S_𝔮` regular, so `R_𝔭` is regular by Lemma 00OF.
As `𝔭` was arbitrary, `R` is regular.

## Main results

* `IsRegularRing.of_faithfullyFlat`: a ring admitting a faithfully flat algebra which is a regular
  ring is itself a regular ring.

## Implementation notes

"Regular ring" is Mathlib's `IsRegularRing` (Definition 00OD), a class which already packages
Noetherianness together with regularity of every localization at a prime — `isRegularRing_iff`
spells out the second half — so the source's conclusion "`R` is a regular ring" is the single
instance `IsRegularRing R` and the Noetherian half of it, which the source's proof obtains from
Lemma 033E, is part of the statement rather than a hypothesis.

The source's ring map `R → S` is an `Algebra R S` instance, Mathlib's way of naming a ring map, and
its faithful flatness is the class `Module.FaithfullyFlat R S`; that is the same condition on
`algebraMap R S` as `RingHom.FaithfullyFlat`, by `RingHom.faithfullyFlat_algebraMap_iff`, and it
is the form both Mathlib's descent API and the companion statement 033G consume. `S` is an explicit
argument, occurring neither in the conclusion nor in any other explicit argument; for the same
reason this is not an instance, `R` having no way to know a faithfully flat extension of itself.
The two rings live in independent universes.

This is the global companion of the local statement 00OF,
`IsRegularLocalRing.of_flat_of_isLocalHom`, whose name it mutates: there the map is flat and local
between local Noetherian rings, here it is faithfully flat between arbitrary ones. No locality or
Noetherian hypothesis is imposed on `R` or `S` beyond what `IsRegularRing S` carries, so nothing
here restricts to the local case.

Faithfulness to [StacksProject 07NG]:

1. No dead hypothesis. Faithful flatness cannot be weakened to flatness: for `R = k[x, y]/(xy)`,
   the localization `S = R[x⁻¹] ≅ k[x, x⁻¹]` is flat over `R` and is a regular ring, being a
   localization of `k[x]`, while `R` is not regular at the origin — what fails is surjectivity of
   `Spec S → Spec R`, i.e. faithfulness. The hypothesis on `S` is load-bearing too: `S = R` is
   faithfully flat over every `R`, so without it the conclusion would assert that every ring is
   regular.
2. The scalars and base are the source's. Faithful flatness is that of `S` as an `R`-module along
   `algebraMap R S`, with no localization of it interposed, and both regularity assertions are
   about the rings `R` and `S` themselves, each localized at its own primes.
3. The canonical map is pinned. The hypothesis is faithful flatness of the given `algebraMap R S`,
   not the existence of some faithfully flat `R`-algebra structure on `S`.
4. The instantiation is not degenerate. `R = ℚ[x]` and `S = ℚ[x][y]` satisfy every hypothesis — `S`
   is free over `R`, hence faithfully flat, and is a regular ring by
   `Polynomial.isRegularRing_of_isRegularRing` — and the conclusion for them is the regularity of
   `ℚ[x]`, with both rings nontrivial and of positive dimension.

## References

* [StacksProject 07NG](https://stacks.math.columbia.edu/tag/07NG)

## Tags

regular ring, faithfully flat, descent, regular local ring, Noetherian ring
-/

@[expose] public section



/-- **Regularity descends along a faithfully flat ring map** (Stacks 07NG). Let `R → S` be a ring
map. If it is faithfully flat and `S` is a regular ring, then `R` is a regular ring. -/
@[stacks 07NG "The source's \"regular ring\" is Mathlib's class `IsRegularRing` \
  (Definition 00OD), which already includes Noetherianness, so the Noetherianness of `R` that the \
  source derives from Lemma 033E is part of the conclusion; the ring map `R → S` is an \
  `Algebra R S` instance and its faithful flatness is `Module.FaithfullyFlat R S`, equal to \
  `(algebraMap R S).FaithfullyFlat` by `RingHom.faithfullyFlat_algebraMap_iff`. See the module \
  docstring."]
public theorem IsRegularRing.of_faithfullyFlat {R : Type u} (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] [IsRegularRing S] : IsRegularRing R :=
    by exact Stacks.RegularRing.FlatDescent.solution S

end
