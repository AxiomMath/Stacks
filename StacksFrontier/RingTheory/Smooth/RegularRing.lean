module

public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
public import StacksFrontier.RingTheory.Serre.FlatAscent
public import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Regularity ascends along smooth maps of rings

Proof of `Algebra.isRegularRing_of_smooth` (Stacks 07NF): if `φ : R → S` is a smooth ring map and
`R` is a regular ring, then `S` is a regular ring.

A regular ring (Definition 00OD) is a Noetherian ring all of whose localizations at primes are
regular local rings, so it is exactly a Noetherian ring with Serre's property `(R_k)` for every
`k`, the property that `A_𝔭` is regular for every prime `𝔭` of height at most `k`; the two halves
of that equivalence are `hasPropertyRk_of_isRegularRing`, where the height bound is simply
discarded, and `isRegularRing_of_forall_hasPropertyRk`, where a prime is covered by the `k` equal
to its own height, finite because the ring is Noetherian. A smooth ring map is flat and of finite
presentation, and its fibre rings `S ⊗_R κ(𝔭)` are smooth over the fields `κ(𝔭)`, hence regular
by Lemma 00TT; so `(R_k)` ascends from `R` to `S` for every `k` by Lemma 033A, and `S` is regular.

## Main results

* `Stacks.Smooth.RegularRingAscent.solution`: the statement of `Algebra.isRegularRing_of_smooth`.

## Implementation notes

The mathematics is carried by `isRegularRing_of_formallySmooth`: a finite type, formally smooth
algebra over a field is a regular ring. This is Lemma 00TT read at every prime at once — only the
last conjunct of 00TT is used, regularity of the local ring at a point of smoothness — and it is
the regular analogue of `isReduced_of_smooth_of_field` in the sibling proof of 033B. Finite
presentation plays no part in it: Noetherianness needs only finite type, and smoothness at a
prime is by definition formal smoothness of the localization there, so those are the hypotheses
it is stated with, weaker than `Algebra.Smooth`.

Lemma 033A is `property_Rk_of_flat_of_fibre_of_base`, phrased with `HasPropertyRk` and
with the fibre ring `fibreRing R S p = S ⊗[R] κ(𝔭)`. Mathlib's `Ideal.Fiber` is the transposed
`κ(𝔭) ⊗[R] S`, which is the side carrying the `κ(𝔭)`-algebra structure and the base-changed
smoothness; the two are identified by `Algebra.TensorProduct.comm`, along which regularity travels
by `IsRegularRing.of_ringEquiv`.

## References

* [StacksProject 07NF](https://stacks.math.columbia.edu/tag/07NF)
* [StacksProject 033A](https://stacks.math.columbia.edu/tag/033A)
* [StacksProject 00TT](https://stacks.math.columbia.edu/tag/00TT)
* [StacksProject 00OD](https://stacks.math.columbia.edu/tag/00OD)
-/

@[expose] public section

namespace Stacks.Smooth.RegularRingAscent

/-- A regular ring has Serre's property `(R_k)` for every `k`: the height bound is not needed,
every localization at a prime being regular. -/
public theorem hasPropertyRk_of_isRegularRing (A : Type*) [CommRing A] [IsRegularRing A] (k : ℕ) :
    HasPropertyRk A k :=
  fun p _ _ => IsRegularRing.isRegularLocalRing_localization p

/-- Conversely, a Noetherian ring with Serre's property `(R_k)` for every `k` is a regular ring:
a prime of a Noetherian ring has finite height, so `(R_k)` for `k = ht 𝔭` already covers `𝔭`. -/
public theorem isRegularRing_of_forall_hasPropertyRk (A : Type*) [CommRing A]
    [IsNoetherianRing A] (h : ∀ k : ℕ, HasPropertyRk A k) : IsRegularRing A :=
  ⟨fun p _ => h p.height.toNat p (ENat.natCast_toNat Ideal.height_ne_top_of_isPrime).ge⟩

/-- A finite type, formally smooth algebra over a field is a regular ring: it is Noetherian, being
of finite type over a field, and formal smoothness localizes to smoothness at each of its primes,
so each of its localizations is a regular local ring by Lemma 00TT. -/
public theorem isRegularRing_of_formallySmooth (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] [Algebra.FormallySmooth K A] : IsRegularRing A :=
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  ⟨fun q _ => (Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing (k := K) (S := A)
    ⟨q, ‹q.IsPrime›⟩ (Localization.AtPrime q)).2 inferInstance⟩

/-- The fibre ring `S ⊗_R κ(𝔭)` of a formally smooth algebra of finite type is a regular ring: it
is the transpose of Mathlib's fibre `κ(𝔭) ⊗_R S`, which inherits both hypotheses over the field
`κ(𝔭)` by base change. -/
public theorem isRegularRing_fibreRing (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Algebra.FormallySmooth R S] (p : Ideal R) [p.IsPrime] :
    IsRegularRing (fibreRing R S p) :=
  have : IsRegularRing (p.Fiber S) := isRegularRing_of_formallySmooth p.ResidueField (p.Fiber S)
  IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm R p.ResidueField S).toRingEquiv

/-- If `S` is a smooth `R`-algebra and `R` is a regular ring, then `S` is a regular ring. -/
public theorem solution (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Smooth R S] [IsRegularRing R] : IsRegularRing S :=
  -- `S` is of finite presentation, hence of finite type, over the Noetherian ring `R`.
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  isRegularRing_of_forall_hasPropertyRk S fun k =>
    -- Lemma 033A: `(R_k)` ascends along the flat map `R → S` from `R` and its fibre rings.
    property_Rk_of_flat_of_fibre_of_base R S k
      (fun p _ => have := isRegularRing_fibreRing R S p; hasPropertyRk_of_isRegularRing _ k)
      (hasPropertyRk_of_isRegularRing R k)

end Stacks.Smooth.RegularRingAscent

end

/-!
# A smooth algebra over a regular ring is regular

Regularity ascends along smooth maps of rings: if `φ : R → S` is a smooth ring map and `R` is a
regular ring, then `S` is a regular ring. A regular ring (Definition 00OD) is a Noetherian ring all
of whose localizations at primes are regular local rings.

The source's proof. A regular ring is exactly a Noetherian ring satisfying Serre's condition
`(R_k)` for every `k` (regularity of `R_𝔭` for all primes `𝔭` of height `≤ k`), and a smooth ring
map is flat with regular fibres, so `(R_k)` ascends along `φ` for every `k` by Lemma 033A, whose
fibre hypothesis is supplied by Lemma 00TT: the fibre rings of a smooth map are smooth, hence
regular, over the residue fields.

## Main results

* `Algebra.isRegularRing_of_smooth`: a smooth algebra over a regular commutative ring is regular.

## Implementation notes

The ring map is an `Algebra R S` instance, so `φ` is `algebraMap R S` and smoothness of `φ` is
`Algebra.Smooth R S` — `Algebra.FormallySmooth R S` together with `Algebra.FinitePresentation R S`
— which `RingHom.smooth_algebraMap` identifies with `(algebraMap R S).Smooth`, the predicate on the
bare ring map. This is the shape of the companion statements 033B and 033C, the reduced and the
normal
analogues of this lemma, and the name mutates theirs (`Algebra.isReduced_of_smooth`,
`Algebra.isNormalRing_of_smooth`) by swapping in the property that ascends.

Regularity is Mathlib's `IsRegularRing`, which is Definition 00OD verbatim: Noetherian, with
`Localization.AtPrime 𝔭` a regular local ring for every prime `𝔭`. Noetherianness is therefore part
of both the hypothesis and the conclusion rather than a separate assumption; on the conclusion side
this is genuine content of the lemma beyond the local statement, and it is what the finite
presentation half of smoothness pays for, `S` being of finite type over the Noetherian ring `R`.
Being a class, `IsRegularRing R` is an instance argument, as `IsReduced R` is in 033B; `R` and `S`
are explicit, again as in 033B and 033C, since no instance argument determines `R` from the
conclusion, and they live in independent universes.

Mathlib has the polynomial case `Polynomial.isRegularRing_of_isRegularRing` and its multivariate
form, transport along a ring equivalence (`IsRegularRing.of_ringEquiv`), and localization
(`IsRegularRing.isRegularLocalRing_localization`), but no ascent of regularity along a flat or a
smooth ring map, so this is not an instance of anything upstream.

Faithfulness to [StacksProject 07NF]:

1. No dead hypothesis. Regularity of `R` is used: `Algebra.Smooth R R` holds for every `R`, so the
   identity map of a non-regular ring such as `ZMod 4` is smooth with non-regular target.
   Smoothness is used, and both halves of it: `k[x, y]/(xy)` over a field `k` is of finite
   presentation with regular base and non-regular target, hence not formally smooth, while
   `MvPolynomial ℕ ℤ` is formally smooth over the regular ring `ℤ` and is not Noetherian, hence
   not regular, for want of finite presentation.
2. The scalars and base are the source's. Smoothness is that of `S` as an `R`-algebra along
   `algebraMap R S` itself, with no localization of `R` interposed and no extension of residue
   fields; the conclusion is regularity of the ring `S`, read on its own localizations, and is
   base-free.
3. The map the source names is pinned, not merely assumed to exist: `φ` is `algebraMap R S` of the
   `Algebra R S` instance and `Algebra.Smooth R S` is smoothness of that very map; regularity is
   read on the canonical local rings `Localization.AtPrime 𝔭` with their canonical algebra
   structures.
4. The instantiation is not degenerate. `R = ℤ`, `S = ℤ[x]` satisfies the hypotheses — `ℤ` is
   regular and `Algebra.Smooth ℤ ℤ[x]` holds, the polynomial algebra being formally smooth and of
   finite presentation — and the conclusion for them is the regularity of `ℤ[x]`, a nontrivial ring
   of dimension one more than the base. Content beyond Mathlib's polynomial instance is a smooth
   algebra that is not a polynomial algebra, such as a standard smooth `R[x]/(f)` with `f'`
   invertible or a localization `R[1/r]`, and content beyond the local statement is the
   Noetherianness of `S`.

## References

* [StacksProject 07NF](https://stacks.math.columbia.edu/tag/07NF)
* [StacksProject 033A](https://stacks.math.columbia.edu/tag/033A)
* [StacksProject 00TT](https://stacks.math.columbia.edu/tag/00TT)
* [StacksProject 033B](https://stacks.math.columbia.edu/tag/033B)
* [StacksProject 00OD](https://stacks.math.columbia.edu/tag/00OD)

## Tags

regular ring, smooth ring map, smooth algebra, ascent
-/

@[expose] public section

/-- **Regularity ascends along smooth maps of rings** (Stacks Tag 07NF). Let `R → S` be a smooth
ring map. If `R` is a regular ring, then `S` is a regular ring. -/
@[stacks 07NF "The ring map is an `Algebra R S` instance and smoothness of it is Mathlib's \
  `Algebra.Smooth R S` (equivalently `(algebraMap R S).Smooth`, by `RingHom.smooth_algebraMap`), \
  as in the companion statements 033B and 033C; regularity is Mathlib's `IsRegularRing`, \
  Definition 00OD verbatim, which already contains Noetherianness, so the source's standing \
  convention that a regular ring is Noetherian is carried by the predicate on both sides. \
  Mathlib has the polynomial case and transport along ring equivalences, but no ascent along a \
  smooth map. See the module docstring.", sga "1 II 3.1" "regular, O_y ⇒ O_x"]
public theorem Algebra.isRegularRing_of_smooth (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Smooth R S] [IsRegularRing R] : IsRegularRing S :=
  -- `R` does not occur in the conclusion `IsRegularRing S`, so `apply` would leave it a
  -- metavariable and `IsRegularRing ?R` could not be synthesized; pass both explicitly.
  Stacks.Smooth.RegularRingAscent.solution R S

end
