module

import Mathlib.RingTheory.KrullDimension.Regular
import Std.Tactic.BVDecide.Normalize.Prop

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CompleteIntersection.Basic

@[expose] public section

universe w

/-!
# Complete intersection local rings over a field

Let `k` be a field. A local `k`-algebra `S` which is essentially of finite type over `k` is a
*complete intersection over `k`* if it can be cut out of a regular local ring by a regular
sequence: there is a local `k`-algebra `R`, essentially of finite type over `k` and regular
local, and a regular sequence `f₁, …, f_c` of elements of the maximal ideal `m_R`, such that
`S ≅ R/(f₁, …, f_c)` as `k`-algebras. This is Stacks Definition 10.135.5, tag 00SD, and it is
the local counterpart of the two global notions `IsGlobalCompleteIntersection` and
`IsLocalCompleteIntersection` of tag 00S9.

Here "essentially of finite type" is `Algebra.EssFiniteType k R`, that is, `R` is a localization
of a finite type `k`-algebra; "regular local" is `IsRegularLocalRing R`, which already carries
`IsLocalRing R` and Noetherianness; a regular sequence is `RingTheory.Sequence.IsRegular R f` for
a list `f` of elements of `R`, and `c` is its length; and `(f₁, …, f_c)` is `Ideal.ofList f`.

## Main definitions

* `IsCompleteIntersectionLocalRing`: `S` is a complete intersection over `k`, tag 00SD.

## Main results

* `IsCompleteIntersectionLocalRing.isLocalRing`, `.isNoetherianRing` and `.essFiniteType`: the
  standing hypotheses of the source — that `S` be local and essentially of finite type over `k` —
  hold automatically for any `S` satisfying the definition, so they need not be imposed.
* `IsCompleteIntersectionLocalRing.exists_witness`: the data of the definition can always be
  chosen so that, in addition, `dim S + c = dim R`. In other words the number of equations `c` is
  the codimension `dim R - dim S`, which is the numerical shape in which the condition reappears
  in the criteria of tags 00SE, 00SF and 00SC.
* `IsCompleteIntersectionLocalRing.of_algEquiv`: the notion depends only on the isomorphism class
  of `S` as a `k`-algebra.
* `IsRegularLocalRing.isCompleteIntersectionLocalRing`: a regular local `k`-algebra essentially of
  finite type over `k` is a complete intersection over `k`, the case `c = 0`.

## Implementation notes

The source imposes on `S` the standing hypotheses of being local and essentially of finite type
over `k`. They are not imposed here, being consequences of the definition: `S ≅ R/(f₁, …, f_c)`
with `R` local and `(f₁, …, f_c) ⊆ m_R` proper, and a quotient of an algebra essentially of
finite type is again essentially of finite type. See the three results named above.

The auxiliary ring `R` is quantified over `Type (max u v)`, where `k : Type u` and `S : Type v`.
This is the permissive choice: `R` surjects onto `S`, and `R` is essentially of finite type over
`k`, so neither universe alone is visibly large enough to hold it.

## References

* [Stacks 00SD](https://stacks.math.columbia.edu/tag/00SD), Definition 10.135.5.
* [Stacks 00S9](https://stacks.math.columbia.edu/tag/00S9), Definition 10.135.1.
* [Stacks 00SA](https://stacks.math.columbia.edu/tag/00SA), Lemma 10.135.2.
-/

@[expose] public section

universe u v

open IsLocalRing RingTheory.Sequence

/-- A `k`-algebra `S` is a *complete intersection over `k`* if there exist a `k`-algebra `R` and
a list `f = f₁, …, f_c` of elements of `R` such that

* `R` is a regular local ring,
* `R` is essentially of finite type over `k`,
* every `fᵢ` lies in the maximal ideal of `R`,
* `f₁, …, f_c` is a regular sequence in `R`, and
* `S ≅ R/(f₁, …, f_c)` as `k`-algebras.

The source states this for a local `k`-algebra `S` essentially of finite type over `k`; both
hypotheses are consequences here, see `IsCompleteIntersectionLocalRing.isLocalRing` and
`IsCompleteIntersectionLocalRing.essFiniteType`. The length `c` of `f` is unconstrained, and is
forced to be the codimension `dim R - dim S` by
`IsCompleteIntersectionLocalRing.exists_witness`. -/
@[stacks 00SD]
def IsCompleteIntersectionLocalRing (k : Type u) [Field k] (S : Type v) [CommRing S]
    [Algebra k S] : Prop :=
  ∃ (R : Type (max u v)) (_ : CommRing R) (_ : Algebra k R) (_ : IsRegularLocalRing R)
      (_ : Algebra.EssFiniteType k R) (f : List R),
    (∀ x ∈ f, x ∈ maximalIdeal R) ∧ IsRegular R f ∧
      Nonempty (S ≃ₐ[k] R ⧸ Ideal.ofList f)

namespace IsCompleteIntersectionLocalRing

variable {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]

/-- In a complete intersection `S ≅ R/(f₁, …, f_c)` over `k` the ideal `(f₁, …, f_c)` is proper,
being contained in the maximal ideal of `R`. -/
private theorem ofList_ne_top {R : Type*} [CommRing R] [IsLocalRing R] {f : List R}
    (hmem : ∀ x ∈ f, x ∈ maximalIdeal R) : Ideal.ofList f ≠ ⊤ := fun hc ↦
  (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (hc ▸ Submodule.span_le.mpr hmem))

/-- A complete intersection over `k` is essentially of finite type over `k`: it is a quotient of
the auxiliary regular local ring `R`, which is essentially of finite type by assumption. This is
one of the two standing hypotheses of Definition 00SD, so it need not be imposed. -/
theorem essFiniteType (h : IsCompleteIntersectionLocalRing k S) :
    Algebra.EssFiniteType k S := by
  obtain ⟨R, hcr, hal, hrl, hef, f, -, -, ⟨e⟩⟩ := h
  have : Algebra.EssFiniteType k (R ⧸ Ideal.ofList f) :=
    Algebra.EssFiniteType.of_surjective (Ideal.Quotient.mkₐ k _) Ideal.Quotient.mk_surjective
  exact Algebra.EssFiniteType.of_surjective e.symm.toAlgHom e.symm.surjective

/-- A complete intersection over `k` is a local ring: it is the quotient of a local ring by a
proper ideal. This is the other standing hypothesis of Definition 00SD, so it need not be
imposed. -/
theorem isLocalRing (h : IsCompleteIntersectionLocalRing k S) : IsLocalRing S := by
  obtain ⟨R, hcr, hal, hrl, hef, f, hmem, -, ⟨e⟩⟩ := h
  have : Nontrivial (R ⧸ Ideal.ofList f) :=
    Submodule.Quotient.nontrivial_iff.mpr (ofList_ne_top hmem)
  have : IsLocalRing (R ⧸ Ideal.ofList f) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : Nontrivial S := e.toEquiv.nontrivial
  exact IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective

/-- A complete intersection over `k` is Noetherian, being a quotient of a regular local ring. -/
theorem isNoetherianRing (h : IsCompleteIntersectionLocalRing k S) : IsNoetherianRing S := by
  obtain ⟨R, hcr, hal, hrl, hef, f, -, -, ⟨e⟩⟩ := h
  have : IsNoetherianRing R := IsRegularLocalRing.toIsNoetherian
  have : IsNoetherianRing (R ⧸ Ideal.ofList f) := inferInstance
  exact isNoetherianRing_of_surjective _ S e.symm.toRingHom e.symm.surjective

/-- The data witnessing that `S` is a complete intersection over `k` automatically satisfies
`dim S + c = dim R`, where `c` is the number of equations: cutting a Noetherian local ring down
by a regular sequence drops the Krull dimension by the length of the sequence. So `c` is the
codimension `dim R - dim S`, and is in particular the same for every presentation. -/
theorem exists_witness (h : IsCompleteIntersectionLocalRing k S) :
    ∃ (R : Type (max u v)) (_ : CommRing R) (_ : Algebra k R) (_ : IsRegularLocalRing R)
      (_ : Algebra.EssFiniteType k R) (f : List R),
      (∀ x ∈ f, x ∈ maximalIdeal R) ∧ IsRegular R f ∧
        Nonempty (S ≃ₐ[k] R ⧸ Ideal.ofList f) ∧
        ringKrullDim S + f.length = ringKrullDim R := by
  obtain ⟨R, hcr, hal, hrl, hef, f, hmem, hreg, ⟨e⟩⟩ := h
  have : IsNoetherianRing R := IsRegularLocalRing.toIsNoetherian
  refine ⟨R, hcr, hal, hrl, hef, f, hmem, hreg, ⟨e⟩, ?_⟩
  rw [RingEquiv.ringKrullDim e.toRingEquiv]
  exact ringKrullDim_add_length_eq_ringKrullDim_of_isRegular f hreg

/-- Being a complete intersection over `k` depends only on the isomorphism class of `S` as a
`k`-algebra: the same auxiliary ring and regular sequence witness it for any `T ≃ₐ[k] S`. -/
theorem of_algEquiv {T : Type v} [CommRing T] [Algebra k T]
    (h : IsCompleteIntersectionLocalRing k S) (e : S ≃ₐ[k] T) :
    IsCompleteIntersectionLocalRing k T := by
  obtain ⟨R, hcr, hal, hrl, hef, f, hmem, hreg, ⟨e'⟩⟩ := h
  exact ⟨R, hcr, hal, hrl, hef, f, hmem, hreg, ⟨e.symm.trans e'⟩⟩

end IsCompleteIntersectionLocalRing

/-- A regular local `k`-algebra essentially of finite type over `k` is a complete intersection
over `k`: take `R` to be the ring itself and the empty regular sequence, so that `c = 0`. -/
theorem IsRegularLocalRing.isCompleteIntersectionLocalRing {k : Type u} [Field k]
    (R : Type (max u v)) [hcr : CommRing R] [hrl : IsRegularLocalRing R] [hal : Algebra k R]
    [hef : Algebra.EssFiniteType k R] : IsCompleteIntersectionLocalRing k R := by
  refine ⟨R, hcr, hal, hrl, hef, [], by simp, IsRegular.nil R R, ⟨?_⟩⟩
  exact ((Ideal.quotientEquivAlgOfEq k Ideal.ofList_nil).trans (AlgEquiv.quotientBot k R)).symm

/-! ### Localizing a complete intersection, tag 00SA

Stacks Lemma 10.135.2 — a localization `S_g` of a global (respectively local) complete
intersection over `k` is again one — is already proved in
`StacksFrontier.RingTheory.CompleteIntersection.Basic` as
`isGlobalCompleteIntersection_localization` and `isLocalCompleteIntersection_localization`, where
it carries no tag. The two declarations together are the covering set of 00SA, whose two parts
they are, so the tag is recorded on them here rather than restated.
-/

add_to_stacks 00SA "part (1): a localization of a global complete intersection over a field is a
global complete intersection over that field" isGlobalCompleteIntersection_localization

add_to_stacks 00SA "part (2): a localization of a local complete intersection over a field is a
local complete intersection over that field" isLocalCompleteIntersection_localization

/-!
# Local complete intersections and their local rings

Proof of `IsLocalCompleteIntersection.tfae` (Stacks 00SH).

Let `k` be a field and let `S` be a finite type `k`-algebra. The three conditions "`S` is a local
complete intersection over `k`", "every local ring of `S` is a complete intersection over `k`"
and "every localization of `S` at a maximal ideal is a complete intersection over `k`" are
equivalent, and the proof is Lemma 00SG plus the definitions, in the cycle (1) ⇒ (2) ⇒ (3) ⇒ (1).

Two statements carry the argument. The first,
`isCompleteIntersection_iff_exists_notMem_isGlobalCompleteIntersection`, is the equivalence of
items (1) and (3) of Lemma 00SG: a local ring of `S` at a prime `q` is a complete intersection
over `k` exactly when `S_g` is a *global* complete intersection over `k` for some `g ∉ q`. It is
the only part of Lemma 00SG that is used, and it is used in both directions — for (1) ⇒ (2) at a
covering element of Definition 00S9 (2) missing the prime, and for (3) ⇒ (1) to manufacture a
covering element missing a given maximal ideal. The second is
`isLocalCompleteIntersection_iff_forall_isMaximal`: Definition 00S9 (2) holds as soon as every
maximal ideal lies in a basic open with global complete intersection localization. That is what
turns the pointwise information of item (3) into a covering, and closes (3) ⇒ (1). (2) ⇒ (3) is
the inclusion of the maximal ideals among the primes.

## Implementation notes

*The universe of item (4) of Lemma 00SG is instantiated by hand.* Only items (1) and (3) of
`IsCompleteIntersection.localization_atPrime_tfae` are used here, and the universe of the index
type `ι` of the presentations in its item (4) occurs in no other item, so unification leaves it a
universe metavariable; it is fixed to `0`.

*Quasi-compactness of `Spec S` is not used.* The source extracts a finite subcover because it
reads Definition 00S9 (2) as a finite covering; `IsLocalCompleteIntersection` asks for a set
generating the unit ideal, and the set of all good elements is one directly, which is the content
of `isLocalCompleteIntersection_iff_forall_isMaximal`.

## References

* [StacksProject 00SH](https://stacks.math.columbia.edu/tag/00SH), Lemma 10.135.9.
* [StacksProject 00SG](https://stacks.math.columbia.edu/tag/00SG), Lemma 10.135.8, here
  `IsCompleteIntersection.localization_atPrime_tfae`.
* [StacksProject 00S9](https://stacks.math.columbia.edu/tag/00S9), Definition 10.135.1, here
  `IsGlobalCompleteIntersection` and `IsLocalCompleteIntersection`.
-/

@[expose] public section

end

/-!
# Local complete intersections and their local rings

Let `k` be a field and let `S` be a finite type `k`-algebra. The following are equivalent.

1. `S` is a local complete intersection over `k` (Definition 00S9 (2)).
2. Every local ring `S_𝔮` of `S` is a complete intersection over `k` (Definition 00SD).
3. Every localization `S_𝔪` of `S` at a maximal ideal is a complete intersection over `k`.

So being a local complete intersection is detected on local rings, and already on the closed
points: the global covering datum of Definition 00S9 (2) can be manufactured from pointwise
information. This is Stacks Lemma 00SH.

The source's proof. It is Lemma 00SG together with the definitions. For (1) ⇒ (2), a prime `𝔮`
misses one of the covering elements `g` — the covering elements generate the unit ideal — and
`S_g` is a global, hence a local, complete intersection over `k`, so item (2) of Lemma 00SG
applies. (2) ⇒ (3) is the inclusion of the maximal ideals among the primes. For (3) ⇒ (1),
Lemma 00SG produces for each maximal ideal `𝔪` an element `g ∉ 𝔪` with `S_g` a global complete
intersection over `k`; the set of all such `g` lies in no maximal ideal, hence generates the
unit ideal, and is therefore a covering as required by Definition 00S9 (2).

## Main results

* `IsLocalCompleteIntersection.tfae`: the equivalence of (1)–(3).

## Implementation notes

*The local rings are abstract localizations, in the shape of item (1) of Lemma 00SG.* Items (2)
and (3) quantify over any `S`-algebra `Sq` localizing `S` at the prime in question, with its
`k`-algebra structure pinned to the one coming from `S` by `IsScalarTower k S Sq`, rather than
naming the model `Localization.AtPrime 𝔮`. This is the hypothesis block of
`IsCompleteIntersection.localization_atPrime_tfae` verbatim, so each of items (2), (3) reads
"item (1) of Lemma 00SG holds at every prime, resp. at every maximal ideal", and a caller may
use whichever model of the local ring is at hand.

*The models are quantified in the universe of `S`.* Every localization of `S` has a model there,
namely `Localization.AtPrime 𝔮`, so nothing is lost, and both directions stay available: items
(2) and (3) are proved for an arbitrary model in that universe, and can be instantiated at the
standard one. A model in a strictly larger universe would be a `ULift` of one of these, and
leaving the universe free would make the instantiation needed for (3) ⇒ (1) unavailable.

*Quasi-compactness of `Spec S` is not needed, because the covering in Definition 00S9 (2) is by
an arbitrary set.* The source extracts a finite subcover, since it reads the definition as a
finite covering `Spec S = ⋃_{i = 1}^{n} D(g_i)`; `IsLocalCompleteIntersection` asks instead for a
set `s ⊆ S` with `Ideal.span s = ⊤` and `S_g` a global complete intersection over `k` for every
`g ∈ s`, which is the same condition — a unit-ideal-generating set contains a finite
unit-ideal-generating subset — and (3) ⇒ (1) produces such a set directly.

*`Algebra.FiniteType k S` is the source's hypothesis and is not removable.* It occurs in none of
the three items, but the equivalence fails without it: for `k = ℚ` and `S = ℚ(x)` the only prime
is `0` and `S_0 ≅ S` is a regular local ring essentially of finite type over `k`, hence a
complete intersection over `k` by Definition 00SD, so items (2) and (3) hold, while item (1)
fails because a global complete intersection over `k` is of finite type over `k` and `S_g = S`
for every `g ≠ 0`.

Faithfulness. (1) No hypothesis is dead: `Field k` is the base of all three notions (over a
non-field the local rings of a polynomial algebra need not be regular and Lemma 00SC, hence
Lemma 00SG, fails), `Algebra.FiniteType k S` is load-bearing as just shown, and `S` with its
`k`-algebra structure occurs in every item. (2) The scalars and the base are the source's: all
three items are conditions over the field `k`, and the `k`-algebra structure of a local ring is
the one induced from `S`, pinned by `IsScalarTower k S Sq`, not an unrelated one. (3) The
canonical maps are pinned: `Sq` is a localization *of `S` at `𝔮`* as an `S`-algebra
(`IsLocalization.AtPrime Sq 𝔮`), and the localizations `S_g` inside
`IsLocalCompleteIntersection` are `Localization.Away g` as in Definition 00S9; no item merely
asserts that some ring exists. (4) The instantiation is not degenerate, both truth values
occurring: for `S = k[x, y]/(xy)`, a global complete intersection over `k` with `n = 2`, `c = 1`
and `dim S = 1`, all three items hold; for `S = k[x, y, z]/(xy, xz)` all three fail, at the
maximal ideal `(x, y, z)`, where the ideal of relations needs two generators while the
codimension is `3 - 2 = 1`.

## References

* [StacksProject 00SH](https://stacks.math.columbia.edu/tag/00SH), Lemma 10.135.9
  (`algebra-lemma-lci-local`), in the section "Local complete intersections". Definition 00S9 (2)
  is `IsLocalCompleteIntersection`, Definition 00SD is `IsCompleteIntersection`, and Lemma 00SG
  is `IsCompleteIntersection.localization_atPrime_tfae`.
-/

@[expose] public section



end
