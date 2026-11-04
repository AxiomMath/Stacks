module

public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension

@[expose] public section

universe u v w

/-!
# Codimension of one finite type affine scheme in another is the difference of heights

Let `k` be a field, let `f : S' → S` be a surjection of `k`-algebras of finite type, let
`X = Spec S` and `X' = Spec S'`, and let `x ∈ X` be the point given by a prime `𝔭 ⊆ S`, with
`x' = comap f x ∈ X'` the corresponding point, given by the prime `𝔭' = f⁻¹(𝔭)`. This file
proves Stacks 00P2:
$$
  \dim_{x'} X' - \dim_x X = \operatorname{height}(𝔭') - \operatorname{height}(𝔭),
$$
in the equivalent additive form `dim_{x'} X' + height 𝔭 = dim_x X + height 𝔭'`.

Lemma 00P1 computes each local dimension as a height plus a transcendence degree,
`dim_x X = height 𝔭 + trdeg_k κ(𝔭)` and `dim_{x'} X' = height 𝔭' + trdeg_k κ(𝔭')`, so the
statement is the assertion that the two transcendence degrees agree. They do because the
surjection identifies the residue fields: `S' → S` is surjective on stalks, so the induced map
`κ(𝔭') → κ(𝔭)` is bijective, hence an isomorphism of `k`-algebras, and `Algebra.trdeg` is
invariant under such an isomorphism.

## Main results

* `Stacks.Spectrum.RelativeCodimension.solution`: the identity of Stacks 00P2.

## Implementation notes

The residue field comparison is
`Stacks.Spectrum.RelativeCodimension.toENat_trdeg_residueField_eq_of_surjectiveOnStalks`, which
carries the whole content of the proof. It is stated for an arbitrary algebra map over a
commutative ring whose hypothesis is `RingHom.SurjectiveOnStalks` rather than surjectivity — that
is what makes `Ideal.ResidueField.mapₐ` bijective
(`RingHom.SurjectiveOnStalks.residueFieldMap_bijective`), a surjection being one case
(`RingHom.surjectiveOnStalks_of_surjective`) — and, as Mathlib's `Ideal.ResidueField.mapₐ` is, with
the hypothesis `q = p.comap f` on a given pair of primes rather than by taking `q` to be the comap.
No isomorphism of residue fields is named: `AlgEquiv.ofBijective` applied to the canonical map is
one term.

Since `S'` and `S` may live in different universes, so may their residue fields, and the
transcendence degrees are `Cardinal`s in those universes. They are compared after
`Cardinal.lift` (`AlgEquiv.lift_trdeg_eq`), which `Cardinal.toENat` then forgets
(`Cardinal.toENat_lift`), so no universe hypothesis is needed.

## References

* [StacksProject 00P2](https://stacks.math.columbia.edu/tag/00P2)
-/

@[expose] public section



namespace Stacks.Spectrum.RelativeCodimension

open PrimeSpectrum

/-- If `f : A →ₐ[R] B` is surjective on stalks and `q = p.comap f` for a prime `p ⊆ B`, then the
residue fields at `q` and at `p` have the same transcendence degree over `R`, as elements of
`ℕ∞`: the canonical map `κ(q) → κ(p)` is then bijective, hence an `R`-algebra isomorphism. -/
private lemma toENat_trdeg_residueField_eq_of_surjectiveOnStalks {R : Type*} [CommRing R]
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (hf : f.toRingHom.SurjectiveOnStalks) (q : Ideal A) [q.IsPrime]
    (p : Ideal B) [p.IsPrime] (hq : q = p.comap f.toRingHom) :
    Cardinal.toENat (Algebra.trdeg R q.ResidueField) =
      Cardinal.toENat (Algebra.trdeg R p.ResidueField) := by
  have e : q.ResidueField ≃ₐ[R] p.ResidueField :=
    AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ q p f hq) (hf.residueFieldMap_bijective q p hq)
  simpa using congrArg Cardinal.toENat e.lift_trdeg_eq

end Stacks.Spectrum.RelativeCodimension

end

/-!
# Codimension of one finite type affine scheme in another is the difference of heights

Let `k` be a field, let `S' → S` be a surjection of `k`-algebras of finite type, let
`X = Spec S` and `X' = Spec S'`, and let `x ∈ X` be the point given by a prime `𝔭 ⊆ S`, with
`x' ∈ X'` the corresponding point, given by the prime `𝔭' = f⁻¹(𝔭)`. Then
$$
  \dim_{x'} X' - \dim_x X = \operatorname{height}(𝔭') - \operatorname{height}(𝔭),
$$
the codimension of `X'` in `X` at `x` being the difference of the heights (Stacks 00P2).

The source's proof is one line: Lemma 00P1 computes each local dimension as
`dim_x X = height 𝔭 + trdeg_k κ(𝔭)` and `dim_{x'} X' = height 𝔭' + trdeg_k κ(𝔭')`, and the
surjection identifies the residue fields, `S' ⧸ 𝔭' ≅ S ⧸ 𝔭` and hence `κ(𝔭') ≅ κ(𝔭)` as
`k`-algebras, so the two transcendence degrees agree and cancel.

## Main results

* `PrimeSpectrum.localKrullDim_comap_add_height_eq_localKrullDim_add_height_comap`: the identity,
  in the additive form described below.

## Implementation notes

*The difference of the source is stated as an equality of sums.* All four quantities live in
`WithBot ℕ∞` (resp. `ℕ∞`), where subtraction is truncated and would make the statement strictly
weaker — and, read literally, would also assert nothing at the pairs where a truncation occurs.
The equivalent additive rearrangement
`dim_{x'} X' + height 𝔭 = dim_x X + height 𝔭'` carries the full content, is symmetric in the two
sides, and needs no finiteness side conditions; under the surjection all four quantities are in
fact finite and `height 𝔭 ≤ height 𝔭'`, `dim_x X ≤ dim_{x'} X'`, so it says exactly the source's
formula.

*`dim_x X` is `TopologicalSpace.localKrullDim`, and `dim(S_𝔭)` is `𝔭.height`.* These are the
choices of Stacks 00P1, whose statement this one is a formal consequence of:
`localKrullDim` is Definition 0055 (4), the infimum of
`topologicalKrullDim U` over the open neighbourhoods `U` of `x`, and `Ideal.height` is the Krull
dimension of any model of the local ring at the prime, by
`IsLocalization.AtPrime.ringKrullDim_eq_height`. A point and its prime ideal are one datum,
`x : PrimeSpectrum S` with `𝔭 = x.asIdeal`.

*The surjection is an `AlgHom` with `Function.Surjective`, not a presentation `S = S' ⧸ I`.* Any
surjection is then covered without transporting along `S ≃ₐ[k] S' ⧸ ker f`, and the corresponding
point `x'` is pinned as `PrimeSpectrum.comap f x`, whose ideal is `x.asIdeal.comap f` — the
source's "corresponding prime ideal of `S'`".

*Only `S'` is assumed of finite type.* `Algebra.FiniteType k S` then follows from `hf` by
`Algebra.FiniteType.of_surjective`, so hypothesizing it as well would be redundant.

Faithfulness. (1) Every hypothesis is used: `hf` is not for bookkeeping — for the non-surjective
inclusion `k[X] → k[X, Y]` at the generic point `x = ⊥` the two sides read `1 + 0` and `2 + 0`;
`x` occurs on both sides; and `Field k` together with `Algebra.FiniteType k S'` are the source's
finiteness hypotheses on the pair `S' → S`, consumed by applying Lemma 00P1 to `S'` and to `S`
(the conclusion mentions no transcendence degree, so `k` enters the statement only through them —
they say "S' is of finite type over a field", which is what makes each local dimension the sum of
a height and the dimension of `V(𝔭)`; for a Noetherian ring that is not catenary at `x` the two
sides differ). (2) The scalars and base are the source's: `f` is a `k`-algebra map for the given
`Algebra k S'`, `Algebra k S`, and both heights and both topologies are those of `S'` and `S`
themselves — no base change and no localization appears. (3) The canonical objects are pinned,
not merely asserted to exist: `x'` is `comap f x` rather than some prime lying under `𝔭`, and the
conclusion determines `dim_{x'} X'` from the other three quantities rather than bounding it.
(4) The instantiation is not degenerate: for `S' = k[X, Y]`, `S = k[X, Y] ⧸ (Y) ≅ k[X]` and
`x = ⊥` the identity reads `2 + 0 = 1 + 1`, a genuine codimension `1`; for `S' = k[X, Y]` and
`S = k` at the origin it reads `2 + 0 = 0 + 2`; and for `f` the identity it is a tautology, so
the content is in the drop of the local dimension against the drop of the height.

## References

* [StacksProject 00P2](https://stacks.math.columbia.edu/tag/00P2)
-/

@[expose] public section



namespace PrimeSpectrum

/-- **Stacks 00P2.** Let `k` be a field, let `f : S' → S` be a surjection of finite type
`k`-algebras, let `x ∈ Spec S` be a point and let `x' = comap f x` be the corresponding point of
`Spec S'`. Then the dimension of `Spec S'` at `x'` exceeds the dimension of `Spec S` at `x` by
exactly the amount by which the height of `x'` exceeds the height of `x`. -/
@[stacks 00P2 "`dim_x X` is `TopologicalSpace.localKrullDim`, Definition 0055 (4), and
`height 𝔭` is `Ideal.height`, as in the sibling 00P1; the source's difference of differences is
stated as the equivalent equality of sums, subtraction in `WithBot ℕ∞` being truncated. See the
module docstring."]
public theorem localKrullDim_comap_add_height_eq_localKrullDim_add_height_comap
    (k : Type u) [Field k] {S' : Type v} {S : Type w} [CommRing S'] [CommRing S]
    [Algebra k S'] [Algebra k S] [Algebra.FiniteType k S'] (f : S' →ₐ[k] S)
    (hf : Function.Surjective f) (x : PrimeSpectrum S) :
    TopologicalSpace.localKrullDim (PrimeSpectrum S') (comap f.toRingHom x) +
        (x.asIdeal.height : WithBot ℕ∞) =
      TopologicalSpace.localKrullDim (PrimeSpectrum S) x +
        ((comap f.toRingHom x).asIdeal.height : WithBot ℕ∞) := by
  have : Algebra.FiniteType k S := .of_surjective f hf
  have key : Cardinal.toENat (Algebra.trdeg k (comap f.toRingHom x).asIdeal.ResidueField) =
      Cardinal.toENat (Algebra.trdeg k x.asIdeal.ResidueField) :=
    Stacks.Spectrum.RelativeCodimension.toENat_trdeg_residueField_eq_of_surjectiveOnStalks f
      (RingHom.surjectiveOnStalks_of_surjective hf) _ _ (PrimeSpectrum.comap_asIdeal f.toRingHom x)
  rw [localKrullDim_eq_height_add_trdeg_residueField k (comap f.toRingHom x),
    localKrullDim_eq_height_add_trdeg_residueField k x, key]
  push_cast
  abel

end PrimeSpectrum

namespace Stacks.Spectrum.RelativeCodimension

/-- The identity of Stacks 00P2 in additive form: for a surjection `f : S' → S` of `k`-algebras
with `S'` of finite type and a point `x ∈ Spec S`,
`dim_{comap f x} Spec S' + height x = dim_x Spec S + height (comap f x)`. Both local dimensions
are expanded by Lemma 00P1 as a height plus a transcendence degree, and the two transcendence
degrees agree because `f` identifies the residue fields. -/
public alias solution :=
    PrimeSpectrum.localKrullDim_comap_add_height_eq_localKrullDim_add_height_comap

end Stacks.Spectrum.RelativeCodimension

end
