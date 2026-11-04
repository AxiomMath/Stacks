module

import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent

public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.RingTheory.KrullDimension.QuotientHeight

@[expose] public section

universe u v

/-!
# The Serre condition `(S_k)` descends along a faithfully flat ring map

Proof of Stacks 0352. Let `R → S` be a faithfully flat ring map with `S` Noetherian and having
property `(S_k)`: `min{k, dim(S_𝔮)} ≤ depth(S_𝔮)` for every prime `𝔮` of `S`. Then `R` is
Noetherian and has property `(S_k)`.

The proof is the source's. First `R` is Noetherian, Noetherianness descending along a faithfully
flat ring map (Lemma 033E). Now let `𝔭` be a prime of `R` and choose a prime `𝔮` of `S` lying over
`𝔭` which corresponds to a minimal prime of the fibre ring `S ⊗_R κ(𝔭)`. Then
`A = R_𝔭 → S_𝔮 = B` is a flat local homomorphism of Noetherian local rings and `𝔪_A B` is an
ideal of definition of `B`, so `dim(A) = dim(B)` (Lemma 00ON) and `depth(A) = depth(B)`
(Lemma 0337, whose fibre term `depth(B/𝔪_A B)` vanishes because `B/𝔪_A B` is
zero-dimensional). Hence the inequality `(S_k)` asks of `A` is the one it asks of `B`.

## Main results

* `Stacks.Serre.DepthConditionDescent.solution`: the statement of Stacks Tag 0352.

## Implementation notes

The source's two citations are used along a single flat local homomorphism `A → B` of Noetherian
local rings *of the same dimension*, and neither the depth nor the dimension of the fibre is
computed independently. Equality of dimensions is a hypothesis rather than a conclusion because it
is the form the geometric input takes — the choice of `𝔮` produces a prime of the same height as
`𝔭` — and because it is what makes the fibre zero-dimensional. That the fibre is zero-dimensional
is the source's "`𝔪_A B` is an ideal of definition of `B`", and it is a lemma of its own,
`ringKrullDim_quotient_map_maximalIdeal_eq_zero_of_ringKrullDim_eq`: in the dimension formula
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (Lemma 00ON) the fibre term
`dim(B/𝔪_A B)` is cancelled off `dim(B) = dim(A) + dim(B/𝔪_A B)`, the height of `𝔪_A` being
finite. A zero-dimensional fibre has depth zero (`Module.depth_eq_zero_of_supportDim_eq_zero`,
Lemma 00LK at a module with zero-dimensional support), so the last term of Lemma 0337 vanishes and
`depth(B) = depth(A)`. That conclusion is `Module.depth_self_eq_of_flat_of_ringKrullDim_eq`, the
lemma this statement rests on.

The geometric input is the existence, over a faithfully flat map of Noetherian rings, of a prime
of `S` lying over `𝔭` *of the same height*
(`Ideal.exists_isPrime_liesOver_height_eq_of_faithfullyFlat`) — the source's `𝔮` corresponding to
a minimal prime of the fibre ring `S ⊗_R κ(𝔭)`. Mathlib has neither this nor its ingredients, and
they are proved here as they are in the companion statement 0353, each under the hypothesis its proof
uses (`Algebra.HasGoingDown R S` rather than flatness, and an arbitrary ideal rather than `𝔭S`):
a prime minimal over `I` has height zero in `R ⧸ I`; a prime minimal over `𝔭S` lies over `𝔭`; and
such a prime has the height of `𝔭`, by Lemma 00ON with a vanishing fibre term. Being needed by
0352, 0353 and 07NG alike, the existence statement is a missing lemma of the theory rather than a
convenience of this file.

The heights of `𝔭` and `𝔮` are converted to the statement's `dim(R_𝔭)` and `dim(S_𝔮)` by
`IsLocalization.AtPrime.ringKrullDim_eq_height`, and
`IsLocalRing.maximalIdeal_height_eq_ringKrullDim` converts back inside the abstract lemma, where
the dimension formula is stated for heights.
Lemma 033E is this repository's `descent_noetherian`; it is stated for a bundled `RingHom`, so the
instances `Module.FaithfullyFlat R S` and `IsNoetherianRing S` reach it through
`RingHom.faithfullyFlat_algebraMap_iff`. The algebra structure `A = R_𝔭 → S_𝔮 = B` is
`Localization.AtPrime.algebraOfLiesOver 𝔭 𝔮`, deliberately not a global instance; once it is in
scope its flatness, its locality and the Noetherianness of both local rings are found by instance
search.

## References

* [StacksProject 0352](https://stacks.math.columbia.edu/tag/0352)
* [StacksProject 0337](https://stacks.math.columbia.edu/tag/0337)
* [StacksProject 00ON](https://stacks.math.columbia.edu/tag/00ON)
* [StacksProject 00LK](https://stacks.math.columbia.edu/tag/00LK)
* [StacksProject 033E](https://stacks.math.columbia.edu/tag/033E)

## Tags

Serre condition, depth, Krull dimension, faithfully flat, descent, going down, minimal prime,
height, Noetherian ring
-/

@[expose] public section

/-- A prime `q` minimal over an ideal `I` has height zero in `R ⧸ I`: by
`Ideal.minimalPrimes_eq_comap` it is the contraction of a minimal prime of `R ⧸ I`, and the
minimal primes are exactly the primes of height zero. -/
private theorem Ideal.height_map_quotient_mk_eq_zero_of_mem_minimalPrimes {R : Type u} [CommRing R]
    (I : Ideal R) {q : Ideal R} (hq : q ∈ I.minimalPrimes) :
    (q.map (Ideal.Quotient.mk I)).height = 0 := by
  rw [Ideal.minimalPrimes_eq_comap] at hq
  obtain ⟨Q, hQ, rfl⟩ := hq
  have : Q.IsPrime := hQ.1.1
  rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  exact Ideal.height_eq_zero_iff.mpr hQ

/-- If going-down holds for `R → S`, a prime `q` of `S` minimal over `pS` lies over `p`. Going
down produces a prime below `q` lying over `p`; it contains `pS`, so minimality identifies it
with `q`. -/
private theorem Ideal.liesOver_of_mem_minimalPrimes_map {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.HasGoingDown R S] (p : Ideal R) [p.IsPrime] (q : Ideal S)
    (hq : q ∈ (p.map (algebraMap R S)).minimalPrimes) : q.LiesOver p := by
  have : q.IsPrime := hq.1.1
  have : q.LiesOver (q.under R) := ⟨rfl⟩
  obtain ⟨P, hPq, hPp, hPo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := q.under R) q
    (Ideal.map_le_iff_le_comap.mp hq.1.2)
  exact le_antisymm hPq (hq.2 ⟨hPp, Ideal.map_le_iff_le_comap.mpr hPo.over.le⟩ hPq) ▸ hPo

/-- If going-down holds for a map of Noetherian rings `R → S`, a prime `q` of `S` minimal over
`pS` has the same height as `p`: in the dimension formula
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (Stacks 00ON) the fibre term is the
height of the image of `q` in `S ⧸ pS`, and that vanishes because `q` is minimal over `pS`. -/
private theorem Ideal.height_eq_of_mem_minimalPrimes_map {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Algebra.HasGoingDown R S] (p : Ideal R) [p.IsPrime] (q : Ideal S)
    (hq : q ∈ (p.map (algebraMap R S)).minimalPrimes) : q.height = p.height := by
  have : q.IsPrime := hq.1.1
  have : q.LiesOver p := Ideal.liesOver_of_mem_minimalPrimes_map p q hq
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q,
    Ideal.height_map_quotient_mk_eq_zero_of_mem_minimalPrimes _ hq, add_zero]

/-- Lemma 033E: if `R → S` is faithfully flat and `S` is Noetherian, then `R` is Noetherian. -/
private theorem isNoetherianRing_of_faithfullyFlat (R : Type u) (S : Type v) [CommRing R]
    [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] [IsNoetherianRing S] :
    IsNoetherianRing R :=
  descent_noetherian (algebraMap R S) (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
    inferInstance

/-- **Over a faithfully flat map of Noetherian rings, every prime is the contraction of a prime of
the same height.** This is the source's choice of `q`: faithful flatness makes
`Spec S → Spec R` surjective, so some prime of `S` contains `pS`, and a prime `q` minimal over
`pS` inside it lies over `p` and has `p`'s height — the source's `q` corresponding to a minimal
prime of the fibre ring `S ⊗[R] κ(p)`, for which `𝔪_p S_q` is an ideal of definition. -/
private theorem Ideal.exists_isPrime_liesOver_height_eq_of_faithfullyFlat {R : Type u} (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] [IsNoetherianRing R]
    [IsNoetherianRing S] (p : Ideal R) [p.IsPrime] :
    ∃ q : Ideal S, q.IsPrime ∧ q.LiesOver p ∧ q.height = p.height := by
  obtain ⟨q₀, hq₀, hq₀o⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (A := R) (B := S) p
  obtain ⟨q, hq, -⟩ :=
    Ideal.exists_minimalPrimes_le (J := q₀) (Ideal.map_le_iff_le_comap.mpr hq₀o.over.le)
  exact ⟨q, hq.1.1, Ideal.liesOver_of_mem_minimalPrimes_map p q hq,
    Ideal.height_eq_of_mem_minimalPrimes_map p q hq⟩

namespace Stacks.Serre.DepthConditionDescent



open IsLocalRing

/-- A nonzero finite module with zero-dimensional support over a local ring has depth zero: by
Lemma 00LK its depth is at most `dim(Supp(M)) = 0`, the hypothesis `𝔪 • M ≠ M` of that lemma
being Nakayama's lemma. -/
@[ega "IV 5.7.3" "special case"]
private lemma Module.depth_eq_zero_of_supportDim_eq_zero {B : Type u} [CommRing B] [IsLocalRing B]
    (M : Type v) [AddCommGroup M] [Module B M] [Module.Finite B M] [Nontrivial M]
    (h : Module.supportDim B M = 0) : Module.depth B (maximalIdeal B) M = 0 := by
  have hle := Module.depth_le_supportDim B (maximalIdeal B) M
    (Ne.symm (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (by
      rw [IsLocalRing.jacobson_eq_maximalIdeal _
        (Module.annihilator_eq_top_iff.not.mpr (not_subsingleton M))])))
  rw [h] at hle
  exact le_antisymm (by exact_mod_cast hle) zero_le

/-- **The fibre of a flat local homomorphism of Noetherian local rings of the same dimension is
zero-dimensional**: `dim(B/𝔪_A B) = 0`. This is the source's "`𝔪_A B` is an ideal of definition of
`B`", read off the dimension formula `dim(B) = dim(A) + dim(B/𝔪_A B)` (Stacks 00ON, stated for
heights) by cancelling `dim(A)`, which is legitimate because `𝔪_A` has finite height. -/
@[ega "IV 21.10.1" "partial"]
private lemma ringKrullDim_quotient_map_maximalIdeal_eq_zero_of_ringKrullDim_eq (A : Type u)
    (B : Type v) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A]
    [IsNoetherianRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hdim : ringKrullDim B = ringKrullDim A) :
    ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) = 0 := by
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have h00ON := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A)
    (maximalIdeal B)
  rw [show (maximalIdeal B).height = (maximalIdeal A).height by
    exact_mod_cast (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B)).trans
      (hdim.trans (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)).symm)] at h00ON
  have hfib := WithTop.add_left_cancel (x := (maximalIdeal A).height)
    Ideal.height_ne_top_of_isPrime (h00ON.symm.trans (add_zero _).symm)
  rw [ringKrullDim_quotient_eq_height_map_maximalIdeal
    (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)).ne, hfib]
  rfl

/-- **Depth is unchanged by a flat local homomorphism of the same dimension.** If `A → B` is a
flat local homomorphism of Noetherian local rings with `dim(B) = dim(A)`, then
`depth(B) = depth(A)`: the fibre `B/𝔪_A B` is zero-dimensional, hence of depth zero by Lemma 00LK,
so the fibre term of the additivity of depth (Stacks 0337) vanishes. -/
private lemma Module.depth_self_eq_of_flat_of_ringKrullDim_eq (A : Type u) (B : Type v) [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (hdim : ringKrullDim B = ringKrullDim A) :
    Module.depth B (maximalIdeal B) B = Module.depth A (maximalIdeal A) A := by
  have : Nontrivial (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)).ne
  rw [Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal A B,
    Module.depth_eq_zero_of_supportDim_eq_zero (B ⧸ (maximalIdeal A).map (algebraMap A B))
      (by rw [Module.supportDim_quotient_eq_ringKrullDim,
        ringKrullDim_quotient_map_maximalIdeal_eq_zero_of_ringKrullDim_eq A B hdim]), add_zero]

/-- If `R → S` is faithfully flat, `S` is Noetherian and every localization `S_𝔮` at a prime
satisfies `min{k, dim(S_𝔮)} ≤ depth(S_𝔮)`, then `R` is Noetherian and every localization `R_𝔭`
satisfies `min{k, dim(R_𝔭)} ≤ depth(R_𝔭)`: property `(S_k)` descends. -/
public theorem solution
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [IsNoetherianRing S] {k : ℕ}
    (hS : ∀ (q : Ideal S) [q.IsPrime],
      min (k : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime q)) ≤
        (Module.depth (Localization.AtPrime q)
          (IsLocalRing.maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) :
            WithBot ℕ∞)) :
    IsNoetherianRing R ∧
      ∀ (p : Ideal R) [p.IsPrime],
        min (k : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime p)) ≤
          (Module.depth (Localization.AtPrime p)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) :
              WithBot ℕ∞) := by
  have hR := isNoetherianRing_of_faithfullyFlat R S
  refine ⟨hR, fun p _ => ?_⟩
  obtain ⟨q, _, _, hq⟩ := Ideal.exists_isPrime_liesOver_height_eq_of_faithfullyFlat S p
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  have hdim : ringKrullDim (Localization.AtPrime q) = ringKrullDim (Localization.AtPrime p) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
      IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hq]
  rw [← hdim, ← Module.depth_self_eq_of_flat_of_ringKrullDim_eq (Localization.AtPrime p)
    (Localization.AtPrime q) hdim]
  exact hS q

end Stacks.Serre.DepthConditionDescent

end

/-!
# The Serre condition `(S_k)` descends along a faithfully flat ring map

Fix an integer `k ≥ 0`. A Noetherian ring `R` has property `(S_k)` (Definition 031P) when
`depth(R_𝔭) ≥ min{k, dim(R_𝔭)}` for every prime `𝔭` of `R`, the depth being that of the local
ring `R_𝔭` along its maximal ideal. Both halves of "Noetherian and `(S_k)`" descend along a
faithfully flat ring map: if `R → S` is faithfully flat and `S` is Noetherian with `(S_k)`, then
`R` is Noetherian and has `(S_k)`.

The source's proof. `R` is Noetherian by Lemma 033E, Noetherianness descending along a faithfully
flat ring map. Let `𝔭 ⊂ R` be a prime and choose a prime `𝔮 ⊂ S` lying over `𝔭` which corresponds
to a minimal prime of the fibre ring `S ⊗_R κ(𝔭)`; such a `𝔮` exists because faithful flatness
makes `Spec S → Spec R` surjective. Then `A = R_𝔭 → S_𝔮 = B` is a flat local homomorphism of
Noetherian local rings and `𝔪_A B` is an ideal of definition of `B`, by minimality of `𝔮` in the
fibre. Hence `dim(A) = dim(B)` (Lemma 00ON), and `depth(A) = depth(B)` (Lemma 0337, whose formula
`depth(B) = depth(A) + depth(B/𝔪_A B)` has vanishing last term because `B/𝔪_A B` is Artinian).
So the inequality `(S_k)` asks of `A` is the one it asks of `B`, which holds.

## Main results

* `isNoetherianRing_and_min_le_depth_atPrime_of_faithfullyFlat`: a ring admitting a faithfully
  flat algebra which is Noetherian and has `(S_k)` is itself Noetherian and has `(S_k)`.

## Implementation notes

Mathlib has no predicate for `(S_k)`, so the condition is spelled out from Definition 031P as the
inequality `min{k, dim(R_𝔭)} ≤ depth(R_𝔭)` at every prime `𝔭`, in the shape used for the cases
`k = 1` and `k = 2` in tags 031Q and 031S: `Module.depth` of tag 00LI along the maximal ideal of
`Localization.AtPrime 𝔭` for the depth, and `ringKrullDim (Localization.AtPrime 𝔭)` — the
source's literal `dim(R_𝔭)`, equal to `Ideal.height 𝔭` by
`IsLocalization.AtPrime.ringKrullDim_eq_height` — for the dimension. Depth takes values in `ℕ∞`
with `depth(0) = ⊤` while `ringKrullDim` takes values in `WithBot ℕ∞`, the value `⊥` recording
`dim(∅) = -∞`, so the inequality is read in `WithBot ℕ∞`; no localization at a prime is the zero
ring, so the left-hand side is in fact never `⊥` here. The general-`k` predicate `PropertySkRing`
this repository carries cannot state the conclusion: it presupposes `IsNoetherianRing R` as an
instance, which is one half of what is being concluded, and it measures depth with a different
constant from the `Module.depth` of tag 00LI that Lemma 0337 and tags 031Q, 031S are phrased
with. The integer `k` is arbitrary, as in the source.

Unlike the parallel descent statement 07NG, whose conclusion `IsRegularRing R` bundles
Noetherianness, nothing here bundles it, so "`R` is Noetherian and has `(S_k)`" is a conjunction
and the Noetherian half that the source gets from Lemma 033E is part of the conclusion rather
than a hypothesis. The source's ring map `R → S` is an `Algebra R S` instance and its faithful
flatness the class `Module.FaithfullyFlat R S`, the same condition on `algebraMap R S` as
`RingHom.FaithfullyFlat` by `RingHom.faithfullyFlat_algebraMap_iff`; this is the form the companion
statements 033G and 07NG consume. The two rings live in independent universes.

Faithfulness to [StacksProject 0352]:

1. No dead hypothesis. Faithful flatness cannot be weakened to flatness: for the union of two
   planes `R = k[x, y, z, w]/((x, y) ∩ (z, w))`, inverting `x` kills the component `(x, y)`, so
   `S = R_x ≅ k[x, y]_x` is a flat `R`-algebra which is regular, hence Noetherian with `(S_k)`
   for every `k`, while `R` fails `(S_2)` at the origin, where the depth is `1` and the dimension
   `2`; what fails is surjectivity of `Spec S → Spec R`. Both hypotheses on `S` are load-bearing
   as well, since `S = R` is faithfully flat over every `R`: without them the statement would
   assert that every ring is Noetherian with `(S_k)`. Finally `k` is used on both sides, and both
   conjuncts of the conclusion are asserted, not just the depth inequality.
2. The scalars and base are the source's. Faithful flatness is that of `S` as an `R`-module along
   `algebraMap R S`, with no localization interposed; and the two `(S_k)` conditions are formed
   at each prime over the local ring there — the depth of `R_𝔭` as a module over itself along
   `𝔪_𝔭`, not `Module.depth R 𝔭 R`, and the dimension of `R_𝔭`, not of `R`.
3. The canonical maps are pinned. The hypothesis is faithful flatness of the given
   `algebraMap R S`, not the existence of some faithfully flat `R`-algebra structure on `S`, and
   the local rings are the canonical models `Localization.AtPrime 𝔭` and `Localization.AtPrime 𝔮`
   with their canonical algebra structures, so the conditions are about the localizations of `R`
   and of `S` themselves and not about local rings with the same invariants.
4. The instantiation is not degenerate. `R = ℚ[x]`, `S = ℚ[x, y]` and any `k` satisfy every
   hypothesis — `S` is free over `R`, hence faithfully flat, and is a regular ring, so it is
   Noetherian and has `(S_k)` — and both rings are nontrivial of positive dimension. The
   conclusion is not vacuous for any `k`: at a prime of height `≥ k` in a ring failing `(S_k)`
   the inequality genuinely fails, as the union of two planes above shows for `k = 2`.

## References

* [StacksProject 0352](https://stacks.math.columbia.edu/tag/0352)

## Tags

Serre condition, depth, Krull dimension, faithfully flat, descent, Noetherian ring
-/

@[expose] public section



/-- **Stacks Tag 0352.** Let `R → S` be a ring map. If it is faithfully flat and `S` is Noetherian
with property `(S_k)` — the depth of `S_𝔮` is at least `min{k, dim(S_𝔮)}` for every prime `𝔮` —
then `R` is Noetherian and has property `(S_k)`. The depth inequalities are read in
`WithBot ℕ∞`. -/
@[stacks 0352 "Property `(S_k)` is spelled out from Definition 031P as the inequality \
  `min{k, dim(R_𝔭)} ≤ depth(R_𝔭)` at every prime, with `Module.depth` (tag 00LI) along the \
  maximal ideal of `Localization.AtPrime 𝔭` and `ringKrullDim` for the dimension, as in tags \
  031Q and 031S, the inequality being read in `WithBot ℕ∞`; the ring map `R → S` is an \
  `Algebra R S` instance and its faithful flatness is `Module.FaithfullyFlat R S`. See the \
  module docstring.", ega "IV 6.4.1" "(i), affine E=O,F=O"]
public theorem isNoetherianRing_and_min_le_depth_atPrime_of_faithfullyFlat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [IsNoetherianRing S] {k : ℕ}
    (hS : ∀ (q : Ideal S) [q.IsPrime],
      min (k : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime q)) ≤
        (Module.depth (Localization.AtPrime q)
          (IsLocalRing.maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) :
            WithBot ℕ∞)) :
    IsNoetherianRing R ∧
      ∀ (p : Ideal R) [p.IsPrime],
        min (k : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime p)) ≤
          (Module.depth (Localization.AtPrime p)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) :
              WithBot ℕ∞) :=
  Stacks.Serre.DepthConditionDescent.solution (S := S) hS

end

/-!
# The Serre condition `(R_k)` descends along a faithfully flat ring map

Proof of Stacks 0353. Let `R → S` be a faithfully flat ring map with `S` Noetherian and having
property `(R_k)`: the local ring `S_𝔮` is regular for every prime `𝔮` of `S` of height at most `k`.
Then `R` is Noetherian and has property `(R_k)`.

The proof is the source's. First `R` is Noetherian, Noetherianness descending along a faithfully
flat ring map (Lemma 033E). Now let `𝔭` be a prime of `R` with `dim(R_𝔭) ≤ k`. Faithful flatness
makes `Spec S → Spec R` surjective, so `𝔭S` is a proper ideal of `S`; choose a prime `𝔮` of `S`
minimal over `𝔭S`, that is, one corresponding to a minimal prime of the fibre ring
`S ⊗_R κ(𝔭)`. Going-down, which holds for the flat map `R → S`, forces `𝔮` to lie over `𝔭` and
makes `𝔪_𝔭 S_𝔮` an ideal of definition of `S_𝔮`, so `dim(S_𝔮) = dim(R_𝔭) ≤ k` (Lemma 00ON). Hence
`S_𝔮` is regular, `S` having `(R_k)`, and `A = R_𝔭 → S_𝔮 = B` is a flat local homomorphism of
Noetherian local rings with regular target, so `R_𝔭` is regular by Lemma 00OF.

## Main results

* `Stacks.Serre.RegularityDescent.solution`: the statement of Stacks Tag 0353.

## Implementation notes

All of the source's argument except its two citations lives in the choice of `𝔮`, and that choice
is stated here as a single lemma: over a faithfully flat map of Noetherian rings, every prime of
`R` is the contraction of a prime of `S` *of the same height*
(`Ideal.exists_isPrime_liesOver_height_eq_of_faithfullyFlat`). Mathlib has neither this nor its
ingredients, so they are proved here, each stated under the hypothesis its proof actually uses —
`Algebra.HasGoingDown R S` rather than flatness, and an arbitrary ideal rather than `𝔭S`:

* `Ideal.height_map_quotient_mk_eq_zero_of_mem_minimalPrimes`: a prime minimal over an ideal `I`
  has height zero in `R ⧸ I`. This is `Ideal.height_eq_zero_iff` read through
  `Ideal.minimalPrimes_eq_comap`, which says that the minimal primes over `I` are exactly the
  contractions of the minimal primes of `R ⧸ I`.
* `Ideal.liesOver_of_mem_minimalPrimes_map`: a prime `𝔮` minimal over `𝔭S` lies over `𝔭`. Going
  down applied to `𝔭 ≤ 𝔮 ∩ R` produces a prime below `𝔮` lying over `𝔭`; it contains `𝔭S`, so
  minimality of `𝔮` collapses it onto `𝔮`.
* `Ideal.height_eq_of_mem_minimalPrimes_map`: such a `𝔮` has the same height as `𝔭`. This is the
  source's "`𝔪_𝔭 S_𝔮` is an ideal of definition of `S_𝔮`, hence `dim(S_𝔮) = dim(R_𝔭)`": in the
  dimension formula `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (Lemma 00ON) the fibre
  term is the height of the image of `𝔮` in `S ⧸ 𝔭S`, which vanishes by the previous lemma. Only
  the inequality `≤` of Lemma 00ON is used, but the equality costs nothing and is the honest
  statement.

Lemma 033E, the Noetherian descent, is this repository's `descent_noetherian`; it is stated for a
bundled `RingHom`, so the instances `Module.FaithfullyFlat R S` and `IsNoetherianRing S` are passed
to it through `RingHom.faithfullyFlat_algebraMap_iff`.

The source's `dim(R_𝔭) ≤ k` is the statement's `Ideal.height 𝔭 ≤ k`, the two agreeing by
`IsLocalization.AtPrime.ringKrullDim_eq_height`; the heights, being `ℕ∞`-valued, compare with the
`ℕ∞`-valued bound `k` directly.

Lemma 00OF is `IsRegularLocalRing.of_flat_of_isLocalHom`, whose hypotheses are about
`algebraMap R_𝔭 S_𝔮`. That map is `Localization.AtPrime.algebraOfLiesOver 𝔭 𝔮`, the canonical
algebra structure attached to `𝔮.LiesOver 𝔭`, deliberately not an instance; once it is in scope its
flatness, its locality and the Noetherianness of `R_𝔭` are all found by instance search, so no
`Localization.localRingHom` plumbing is needed.

## References

* [StacksProject 0353](https://stacks.math.columbia.edu/tag/0353)

## Tags

Serre condition, regular in codimension, regular local ring, faithfully flat, descent, going down,
minimal prime, height, Noetherian ring
-/

@[expose] public section

namespace Stacks.Serre.RegularityDescent



/-- If `R → S` is faithfully flat, `S` is Noetherian and `S_𝔮` is regular for every prime `𝔮`
of height at most `k`, then `R` is Noetherian and `R_𝔭` is regular for every prime `𝔭` of height at
most `k`: property `(R_k)` descends. -/
public theorem solution
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [IsNoetherianRing S] {k : ℕ∞}
    (hS : ∀ (q : Ideal S) [q.IsPrime], q.height ≤ k →
      IsRegularLocalRing (Localization.AtPrime q)) :
    IsNoetherianRing R ∧
      ∀ (p : Ideal R) [p.IsPrime], p.height ≤ k →
        IsRegularLocalRing (Localization.AtPrime p) := by
  have := isNoetherianRing_of_faithfullyFlat R S
  refine ⟨this, fun p _ hpk => ?_⟩
  obtain ⟨q, _, _, hq⟩ := Ideal.exists_isPrime_liesOver_height_eq_of_faithfullyFlat S p
  have := hS q (hq.trans_le hpk)
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  exact IsRegularLocalRing.of_flat_of_isLocalHom (Localization.AtPrime q)

end Stacks.Serre.RegularityDescent

end

/-!
# The Serre condition `(R_k)` descends along a faithfully flat ring map

A Noetherian ring `R` has property `(R_k)` (Definition 031P) when the local ring `R_𝔭` is regular
for every prime `𝔭` of `R` of height at most `k`; one also says `R` is regular in codimension
`≤ k`. Both halves of "Noetherian and `(R_k)`" descend along a faithfully flat ring map: if
`R → S` is faithfully flat and `S` is Noetherian with `(R_k)`, then `R` is Noetherian and has
`(R_k)`.

The source's proof. `R` is Noetherian by Lemma 033E, Noetherianness descending along a faithfully
flat ring map. Let `𝔭 ⊂ R` be a prime with `dim(R_𝔭) ≤ k` and choose a prime `𝔮 ⊂ S` lying over
`𝔭` which corresponds to a minimal prime of the fibre ring `S ⊗_R κ(𝔭)`; such a `𝔮` exists because
faithful flatness makes `Spec S → Spec R` surjective. Then `A = R_𝔭 → S_𝔮 = B` is a flat local
homomorphism of Noetherian local rings and `𝔪_A B` is an ideal of definition of `B`, by minimality
of `𝔮` in the fibre. Hence `dim(A) = dim(B)` (Lemma 00ON), so `dim(B) ≤ k` and `B` is a regular
local ring because `S` has `(R_k)`. By Lemma 00OF, `A` is regular too.

## Main results

* `isNoetherianRing_and_isRegularLocalRing_atPrime_of_faithfullyFlat`: a ring admitting a
  faithfully flat algebra which is Noetherian and has `(R_k)` is itself Noetherian and has `(R_k)`.

## Implementation notes

Mathlib has no predicate for `(R_k)`, so the condition is spelled out from Definition 031P as the
implication `height 𝔭 ≤ k → IsRegularLocalRing (Localization.AtPrime 𝔭)`, in exactly the shape
used for the case `k = 1` in tag 031S: `Ideal.height` for the source's height of a prime,
`Localization.AtPrime` for the canonical local ring there, and Mathlib's `IsRegularLocalRing`,
which bundles local and Noetherian along with regularity of the maximal ideal. The source's proof
tests `dim(R_𝔭) ≤ k` rather than `height 𝔭 ≤ k`; these agree, by
`IsLocalization.AtPrime.ringKrullDim_eq_height`. The general-`k` predicate `PropertyRk` this
repository carries cannot state the conclusion: it presupposes `IsNoetherianRing R` as an
instance, which is one half of what is being concluded.

The bound `k` is taken in `ℕ∞` rather than in the source's non-negative integers. This is a
costless generalization — `Ideal.height` is already `ℕ∞`-valued, so no coercion is spent, and the
source's proof nowhere uses that `k` is finite, testing only `dim(R_𝔭) ≤ k` — and it is
meaningful: the value `k = ⊤` imposes no condition on the height, so the statement at `k = ⊤`
is the descent of regularity itself, tag 07NG, which the finite cases do not give.

Unlike that companion 07NG, whose conclusion `IsRegularRing R` bundles Noetherianness, nothing
here bundles it, so "`R` is Noetherian and has `(R_k)`" is a conjunction and the Noetherian half
that the source gets from Lemma 033E is part of the conclusion rather than a hypothesis; the
parallel statement 0352 for `(S_k)` is arranged the same way. The source's ring map `R → S` is an
`Algebra R S` instance and its faithful flatness the class `Module.FaithfullyFlat R S`, the same
condition on `algebraMap R S` as `RingHom.FaithfullyFlat` by
`RingHom.faithfullyFlat_algebraMap_iff`; this is the form the companion statements 033G, 0352 and
07NG consume. The two rings live in independent universes.

Faithfulness to [StacksProject 0353]:

1. No dead hypothesis. Faithful flatness cannot be weakened to flatness: for `R = k[x, y]/(xy)`
   the localization `S = R[x⁻¹] ≅ k[x, x⁻¹]` is flat over `R`, is Noetherian, and is a regular
   ring, hence has `(R_k)` for every `k`, while `R` fails `(R_1)` at the prime `(x, y)`, which has
   height `1` and whose local ring is not a domain; what fails is surjectivity of
   `Spec S → Spec R`. Both hypotheses on `S` are load-bearing as well, since `S = R` is
   faithfully flat over every `R`: without them the statement would assert that every ring is
   Noetherian with `(R_k)`. Finally `k` is used on both sides, and both conjuncts of the
   conclusion are asserted, not just the regularity of the localizations.
2. The scalars and base are the source's. Faithful flatness is that of `S` as an `R`-module along
   `algebraMap R S`, with no localization interposed; the two `(R_k)` conditions are formed at the
   primes of `R` and of `S` respectively, each measuring the height of a prime in its own ring and
   the regularity of the local ring of that ring there.
3. The canonical maps are pinned. The hypothesis is faithful flatness of the given
   `algebraMap R S`, not the existence of some faithfully flat `R`-algebra structure on `S`, and
   the local rings are the canonical models `Localization.AtPrime 𝔭` and `Localization.AtPrime 𝔮`,
   so the conditions are about the localizations of `R` and of `S` themselves and not about local
   rings with the same invariants.
4. The instantiation is not degenerate. `R = ℚ[x]`, `S = ℚ[x][y]` and any `k` satisfy every
   hypothesis — `S` is free over `R`, hence faithfully flat, and is a regular ring by
   `Polynomial.isRegularRing_of_isRegularRing`, so it is Noetherian and has `(R_k)` — and both
   rings are nontrivial of positive dimension. The conclusion is not vacuous for any `k ≥ 1`: at
   the height-one prime `(x, y)` of `k[x, y]/(xy)` above, `(R_k)` genuinely fails.

## References

* [StacksProject 0353](https://stacks.math.columbia.edu/tag/0353)

## Tags

Serre condition, regular in codimension, regular local ring, faithfully flat, descent,
Noetherian ring
-/

@[expose] public section



/-- **Stacks Tag 0353.** Let `R → S` be a ring map. If it is faithfully flat and `S` is Noetherian
with property `(R_k)` — the local ring `S_𝔮` is regular for every prime `𝔮` of height at most `k`
— then `R` is Noetherian and has property `(R_k)`. The bound `k` ranges over `ℕ∞`, the value `⊤`
giving the descent of regularity itself (tag 07NG). -/
@[stacks 0353 "Property `(R_k)` is spelled out from Definition 031P as the implication \
  `height 𝔭 ≤ k → IsRegularLocalRing (Localization.AtPrime 𝔭)`, with `Ideal.height` and \
  `IsRegularLocalRing`, as in tag 031S; the source's `dim(R_𝔭) ≤ k` is `Ideal.height 𝔭 ≤ k` by \
  `IsLocalization.AtPrime.ringKrullDim_eq_height`. The bound `k` is generalized from a \
  non-negative integer to an element of `ℕ∞`, whose top value recovers tag 07NG. The ring map \
  `R → S` is an `Algebra R S` instance and its faithful flatness is `Module.FaithfullyFlat R S`. \
  See the module docstring.", ega "IV 6.5.3" "(i), affine case"]
public theorem isNoetherianRing_and_isRegularLocalRing_atPrime_of_faithfullyFlat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [IsNoetherianRing S] {k : ℕ∞}
    (hS : ∀ (q : Ideal S) [q.IsPrime], q.height ≤ k →
      IsRegularLocalRing (Localization.AtPrime q)) :
    IsNoetherianRing R ∧
      ∀ (p : Ideal R) [p.IsPrime], p.height ≤ k →
        IsRegularLocalRing (Localization.AtPrime p) :=
  Stacks.Serre.RegularityDescent.solution (S := S) hS

end
