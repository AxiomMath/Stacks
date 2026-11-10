module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ExteriorProductCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingMultiplication
public import StacksCore.Tactic.StacksAttribute

/-!
# The graded algebra on the localized bivariant grading

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : Z ⟶ X` be a
closed immersion of schemes locally of finite type over `S`. **Stacks 0FA0** says that

  `A⁽ᵖ⁾(Z ⟶ X) = ∏_{i ≤ p - 1} Aⁱ(X) × ∏_{i ≥ p} Aⁱ(Z ⟶ X)`

"canonically comes equipped with the structure of a graded algebra", and displays more generally a
multiplication into `A⁽ᵐᵃˣ⁽ᵖ⁼ᑫ⁾⁾(Z ⟶ X)`. The group, the three degreewise pairings the source
builds the product from and the product itself are in
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGrading` and
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingMultiplication`. This file
adds
the remaining structure of the graded algebra: the multiplication as a biadditive map, its unit,
and the two unit laws.

## Main definitions

* `Stacks.Chow.localizedBivariantGradingMulHom` — **Stacks 0FA0**, the multiplication
  `A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ʳ⁾(Z ⟶ X)` as a biadditive map, at every `p`, `q` and every
  target `r`.
* `Stacks.Chow.localizedBivariantGradingMulMaxHom`,
  `Stacks.Chow.localizedBivariantGradingInternalMulHom` — the same at the source's displayed target
  `max(p, q)` and at the product internal to `A⁽ᵖ⁾(Z ⟶ X)`.
* `Stacks.Chow.localizedBivariantGradingOne` — **Stacks 0FA0**, the unit of the graded algebra:
  the element of `A⁽ᵖ⁾(Z ⟶ X)` whose degree `0` component is `1 ∈ A⁰(X)` and whose other
  components vanish.
* `Stacks.Chow.localizedBivariantGradingOneOfInvertible`,
  `Stacks.Chow.localizedBivariantGradingInternalMulHomOfInvertible` — the unit and the internal
  multiplication at the Gysin system of the first Chern class rule, where nothing is assumed.

## Main results

* `Stacks.Chow.localizedGrading_add_lt_of_admissible`,
  `Stacks.Chow.localizedGrading_exists_ambient_pair` — the two halves of `p + q ≤ r + 1`: under it
  no pair of ambient degrees `0 ≤ i < p`, `0 ≤ j < q` has `i + j ≥ r` — these being the pairs for
  which the remark prescribes no value — and when it fails (and `p, q ≥ 1`) such a pair exists.
* `Stacks.Chow.localizedGrading_max_admissible_iff`,
  `Stacks.Chow.localizedGrading_self_admissible_iff` — hence the source's displayed target
  `max(p, q)` meets no such pair exactly when `min(p, q) ≤ 1`, and the product internal to
  `A⁽ᵖ⁾(Z ⟶ X)` exactly when `p ≤ 1`.
* `Stacks.Chow.eq_localizedBivariantGradingMulHom` — **Stacks 0FA0, uniqueness of the canonical
  multiplication as a biadditive map**: a biadditive map whose two components are the finite
  convolutions of the source is `Stacks.Chow.localizedBivariantGradingMulHom`. The underlying
  statement, for arbitrary maps and with no additivity used, is
  `Stacks.Chow.LocalizedGrading.IsMul.eq`.
* `Stacks.Chow.bivariantComposite_identityClass_left`,
  `Stacks.Chow.bivariantComposite_identityClass_right` — **the two unit laws for the composition of
  bivariant classes of Stacks 0B75**: `1 ∘ c = c` and `c ∘ 1 = c` for the identity class
  `1 ∈ A⁰(Y)` of Stacks 0FBS.
* `Stacks.Chow.chowCohomologyRestriction_bivariantIdentityClass` — the restriction map of Stacks
  0B7F carries `1 ∈ A⁰(X)` to `1 ∈ A⁰(Z)`.
* `Stacks.Chow.chowCohomologyComposite_identityClass_left`,
  `Stacks.Chow.chowCohomologyComposite_identityClass_right` — the two unit laws for the
  multiplication of `A^*(X)`, and `Stacks.Chow.localizedComposeChowCohomology_identityClass_left`,
  `Stacks.Chow.localizedMulChowBivariant_identityClass_left`,
  `Stacks.Chow.localizedMulBivariantChow_identityClass_right` — the unit law for the composition
  `Aⁱ(Z) × Aʲ(Z ⟶ X) ⟶ Aⁱ⁺ʲ(Z ⟶ X)`, and the unit at the second and the first pairing of
  Stacks 0FA0, which are the two pairings a product by the unit goes through.
* `Stacks.Chow.localizedBivariantGradingInternalMul_one_left`,
  `Stacks.Chow.localizedBivariantGradingInternalMul_one_right` — **Stacks 0FA0, the two unit laws
  of the graded algebra on `A⁽ᵖ⁾(Z ⟶ X)` for every `p ≥ 1`**: `1 · b = b` and `b · 1 = b` on all of
  `A⁽ᵖ⁾(Z ⟶ X)`, and
  `Stacks.Chow.localizedBivariantGradingInternalMul_one_left_ofInvertible`,
  `Stacks.Chow.localizedBivariantGradingInternalMul_one_right_ofInvertible` — the same at the Gysin
  system of the first Chern class rule, with nothing else assumed.
* `Stacks.Chow.localizedMulBivariantChow_zero_left`,
  `Stacks.Chow.localizedMulBivariant_zero_left`,
  `Stacks.Chow.localizedMulChowBivariant_zero_right`,
  `Stacks.Chow.localizedMulBivariant_zero_right` — the pairings kill a zero argument, which is
  what makes every term but one of the sums defining `1 · b` and `b · 1` vanish.
* `Stacks.Chow.localizedBivariantGradingMul_vanishesInNegativeDegrees` — the elements with
  vanishing negative components are closed under the multiplication. Both hypotheses are needed:
  with the index range `Finset.Icc (min 0 n) (max 0 n)` a product in a negative degree is a sum of
  the source's own pairings applied to the factors' negative-degree components.
* `Stacks.Chow.localizedBivariantGradingInternalMul_singleLow_snd` — the degree `n` component of a
  product whose left factor carries a single class `u ∈ Aⁱ(X)`, in a degree with `n - i ≥ p`: it is
  `res(u) ∘ cₙ₋ᵢ` under the source's second pairing.
* `Stacks.Chow.localizedBivariantGradingInternalMul_singleLow_eq_zero`,
  `Stacks.Chow.localizedBivariantGradingInternalMul_singleLow_eq_zero_of_assoc` — the product of
  two classes carried by ambient degrees `i, j < p` with `i + j ≥ p` is zero, so associativity of
  the product internal to `A⁽ᵖ⁾(Z ⟶ X)` at such a pair — which exists exactly for `p ≥ 2` — would
  make every `u · (v · c)` vanish; see the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingMultiplication`.

## Implementation notes

### Which graded-algebra axioms are here, and where the unit lives

The source asserts the graded algebra and omits the verification of associativity. Of the axioms:

* the grading is carried by the types — each of the three pairings of the source takes a degree `i`
  and a degree `j` class to a degree `i + j` class;
* biadditivity is `Stacks.Chow.localizedBivariantGradingMulHom`, which bundles
  `Stacks.Chow.localizedBivariantGradingMul_add_left` and `_add_right`;
* the unit is `Stacks.Chow.localizedBivariantGradingOne` and the unit laws are
  `Stacks.Chow.localizedBivariantGradingInternalMul_one_left` and
  `Stacks.Chow.localizedBivariantGradingInternalMul_one_right`;
* the two component formulas and the uniqueness they give are in
  `StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingMultiplication`
  (`Stacks.Chow.localizedBivariantGradingMul_fst`, `_snd` and
  `Stacks.Chow.LocalizedGrading.IsMul.eq`), with
  `Stacks.Chow.eq_localizedBivariantGradingMulHom` the biadditive form of the uniqueness;
* **associativity is proved**, in
  `StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingProjectionFormula`:
  `Stacks.Chow.localizedBivariantGradingMul_assoc` at every choice of intermediate and common
  targets with `p + q + s ≤ r + 2`, and
  `Stacks.Chow.localizedBivariantGradingInternalMul_assoc` for the product internal to
  `A⁽ᵖ⁾(Z ⟶ X)` with `p ≤ 1`. Stacks 0FA0 writes "We omit the verification that these
  multiplications are associative in a suitable sense", so nothing was owed to the tag; it is
  carried out there anyway, on top of the associativity Stacks 0B75 does assert of the composition
  of bivariant classes, `Stacks.Chow.bivariantComposite_assoc` of
  `StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Associativity`. What associativity
  of the internal product would come to for `p ≥ 2`, where the product multiplies a pair of
  degrees the remark leaves unprescribed, is
  `Stacks.Chow.localizedBivariantGradingInternalMul_singleLow_eq_zero_of_assoc` below. Two earlier
  versions of this note said associativity was not available here.

So the multiplicative structure of the graded algebra **is** installed as a bundled structure of
Mathlib, in that module: `Stacks.Chow.localizedBivariantGradingSemigroup` on all of
`A⁽ᵖ⁾(Z ⟶ X)` for `p ≤ 1`, and `Stacks.Chow.localizedBivariantGradingMonoid` — multiplication,
unit, associativity, both unit laws — at `p = 1`, on all of `A⁽¹⁾(Z ⟶ X)`.
`GradedAlgebra` is a different matter: it asks for the ring structure of `A^*(X)`
and `A^*(Z ⟶ X)`, the content of Stacks 0B7E and Stacks 0FE0, and for a grading by an internal
direct sum, where `Stacks.Chow.localizedBivariantGrading` is a product.

The unit sits in the degree `0` slot of `A⁽ᵖ⁾(Z ⟶ X)`, and which group that slot is depends on `p`:
it is `A⁰(X)` when `p ≥ 1` and `A⁰(Z ⟶ X)` when `p = 0`. The class `1` of Stacks 0FBS is a class
for the identity of `X`, so it is an element of the slot exactly when `p ≥ 1`;
`Stacks.Chow.localizedBivariantGradingOne` is zero in the degree `0` slot when `p = 0`, where
there is no canonical class to put. Both unit laws hold for every `p ≥ 1`. So the one `p` at which
the bundled `Monoid` is available is `p = 1`: `p ≥ 1` from the unit, and `p ≤ 1` from
associativity by `Stacks.Chow.localizedGrading_self_admissible_iff`. That is the case the chapter
uses — Stacks 0FBA multiplies "in the algebra `A⁽¹⁾(Z ⟶ X)`" and Stacks 0FES extends
multiplicatively over `A⁰(X) × ∏_{i ≥ 1} Aⁱ(Z ⟶ X)`.

### The unit laws, and the lemmas they rest on

`Stacks.Chow.localizedBivariantGradingInternalMul_one_left` reduces, degree by degree, to two
facts about the vocabulary of the source's second pairing — the restriction `A⁰(X) ⟶ A⁰(Z)` of
Stacks 0F9Z followed by the composition of Stacks 0B75:

* `Stacks.Chow.chowCohomologyRestriction_bivariantIdentityClass`, that the restriction map carries
  `1` to `1`. The identification of Stacks 0FBS
  (`Stacks.Chow.eq_bivariantIdentityClass_iff`) reduces it to the cap formula of Stacks 0B7F,
  `res(c) ∩ α = c ∩ α`;
* `Stacks.Chow.bivariantComposite_identityClass_left`, that `1 ∘ c = c`. Both sides cap the same
  way: the cap operation of the composite is cap with `c` followed by cap with `1`, pushed forward
  along the pasting isomorphism of pullbacks, and
  `Stacks.Chow.identityBaseChangeIso_inv_comp_pullbackRightPullbackFstIso_hom` identifies that
  pasting isomorphism, preceded by the base change of the identity, with the comparison
  `Z ×_X T ≅ (𝟙 Z ≫ f) ×_X T` of the two readings of the morphism. The implementation notes of
  `StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingMultiplication` record that
  this unit law was not available when the multiplication was built; it is proved here.

`Stacks.Chow.localizedBivariantGradingInternalMul_one_right` goes through the source's *first*
pairing instead — the composition of Stacks 0B75 with no restriction map in front of it — and
rests on `Stacks.Chow.bivariantComposite_identityClass_right`, that `c ∘ 1 = c`. An earlier
version of this note said that this law was left open because it "needs the proper naturality of
`b_n` along the base-change isomorphism of the identity". The diagnosis was right and the
conclusion was wrong: that naturality is condition (1) of Stacks 0B76, which every bivariant class
carries, in the form `Stacks.Chow.BivariantClass.cap_chowPushforwardOfIso`. Cap with `1` is
pushforward along the base change `T ≅ Y ×_Y T` of the identity, moving `c` past it is that
naturality, and what is left is the geometry:
`Stacks.Chow.testBaseChangeIso_comp_pullbackRightPullbackFstIso_hom` identifies the base change of
that isomorphism followed by the pasting isomorphism of pullbacks with the comparison
`X ×_Y T ≅ (f ≫ 𝟙 Y) ×_Y T` of the two readings of the morphism. So the graded algebra is
two-sided unital here, and `Stacks.Chow.localizedBivariantGradingMonoid` is its bundled form.

### Why the unit laws hold on all of `A⁽ᵖ⁾(Z ⟶ X)`

The group Stacks 0FA0 asserts the graded algebra on has negative-degree factors: its product
`∏_{i ≤ p - 1} Aⁱ(X)` runs over **all** integers `i ≤ p - 1`, negative ones included, and the
remark says nothing about whether they vanish, and contains no parenthetical to that effect. So a
unit
law stated on a subgroup cut out by such a vanishing would be narrower than the source's assertion.

Both laws hold on the whole group, and what carries them is the index range of the sums. The degree
`n` component of a product is the sum over `i ∈ Finset.Icc (min 0 n) (max 0 n)` of the products of
the degree `i` and degree `n - i` components, and that range contains `i = 0` and `i = n` in every
degree — positive, zero or negative (`Stacks.Chow.zero_mem_Icc_min_max`,
`Stacks.Chow.self_mem_Icc_min_max`). Those are exactly the indices the two laws need: `1 · b` has
its one surviving term at `i = 0`, the unit being concentrated in degree `0`, and `b · 1` has its
one surviving term at `i = n`. Every other term dies on a zero argument of a pairing
(`Stacks.Chow.localizedMulBivariantChow_zero_left` and the three lemmas beside it) or is one of the
pairs of degrees the remark leaves unprescribed, whose value is `0`. So neither law needs a
hypothesis on `b`, at any `p ≥ 1`, and the carrier of
`Stacks.Chow.localizedBivariantGradingMonoid` is `A⁽¹⁾(Z ⟶ X)` itself.

The narrower range `i ∈ Finset.Icc 0 n` is empty in a negative degree, and under it the right unit
law is false off the elements with vanishing negative components: `b · 1 = b` has to return `b`'s
degree `n` component, carried by the term at `i = n`, and `i = n` lies outside `Finset.Icc 0 n`
exactly when `n < 0`. `Stacks.Chow.LocalizedGrading.VanishesInNegativeDegrees` names that subgroup;
it is a condition of this library and the unit laws no longer mention it. The source's
`∑_{i + j = n}` is a sum over an infinite index set, and the reading taken, the witness that the
index set is infinite with independent summands, and what the reading costs are set out in the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingMultiplication`.

## References

* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FBS](https://stacks.math.columbia.edu/tag/0FBS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The targets at which the remark prescribes every term -/

/-- Under `p + q ≤ r + 1` no pair of degrees `0 ≤ i < p` and `0 ≤ j < q` has `i + j ≥ r`. These
are the pairs for which both factors of a product lie in `A^*(X)` while the degree `i + j` slot of
`A⁽ʳ⁾(Z ⟶ X)` is the localized group, and the source's three pairings give no value for them. -/
theorem localizedGrading_add_lt_of_admissible {p q r : ℕ} (hr : p + q ≤ r + 1) {i j : ℤ}
    (hip : i < (p : ℤ)) (hjq : j < (q : ℤ)) : i + j < (r : ℤ) := by
  omega

/-- When `p + q ≤ r + 1` fails and both `p` and `q` are positive, such a pair of degrees does
exist: `i = p - 1` and `j = q - 1`. So the bound is sharp for `p, q ≥ 1`, and the pairs the remark
leaves unprescribed are not an artefact of how the product is written: the slots are the source's
own, `A⁽ᵖ⁾(Z ⟶ X)` being `∏_{i ≤ p - 1} Aⁱ(X) × ∏_{i ≥ p} Aⁱ(Z ⟶ X)` verbatim. -/
theorem localizedGrading_exists_ambient_pair {p q r : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hr : r + 1 < p + q) :
    ∃ i j : ℤ, 0 ≤ i ∧ i < (p : ℤ) ∧ 0 ≤ j ∧ j < (q : ℤ) ∧ (r : ℤ) ≤ i + j :=
  ⟨(p : ℤ) - 1, (q : ℤ) - 1, by omega, by omega, by omega, by omega, by omega⟩

/-- The source's displayed target `max(p, q)` meets no pair of degrees the remark leaves
unprescribed exactly when `min(p, q) ≤ 1`, since `p + q = min(p, q) + max(p, q)`. -/
theorem localizedGrading_max_admissible_iff (p q : ℕ) : p + q ≤ max p q + 1 ↔ min p q ≤ 1 := by
  omega

/-- The product internal to `A⁽ᵖ⁾(Z ⟶ X)`, which is the target `r = p = q`, meets no pair of
degrees the remark leaves unprescribed exactly when `p ≤ 1`. -/
theorem localizedGrading_self_admissible_iff (p : ℕ) : p + p ≤ p + 1 ↔ p ≤ 1 := by
  omega

/-! ### Transports of a bivariant class, and how they compose -/

section Collapse

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- Transport of a bivariant class along an equality of morphisms, on cap products: it is
pushforward along the comparison isomorphism of the two base changes. -/
theorem bivariantClassCongr_cap {f f' : X ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (hff : f = f') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) (p : ℤ)
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ sY) k)
    (hbase : (pullback.congrHom hff (rfl : t = t)).hom ≫ (pullback.fst f' t ≫ sX) =
      pullback.fst f t ≫ sX) :
    chowPushforwardOfIso C (pullback.fst f t ≫ sX) (pullback.fst f' t ≫ sX)
        (pullback.congrHom hff rfl).hom hbase (k - p) (c.cap t k α) =
      (bivariantClassCongr C G sX sY hff hf hf' p c).cap t k α := by
  subst hff
  rw [chowPushforwardOfIso_congr_apply C (pullback.fst f t ≫ sX) (pullback.fst f t ≫ sX)
    (pullback.congrHom (rfl : f = f) (rfl : t = t)).hom (𝟙 _)
    (by apply pullback.hom_ext <;> simp) hbase (Category.id_comp _) (k - p),
    chowPushforwardOfIso_id]
  rfl

/-- Two transports along mutually inverse equalities of morphisms cancel. -/
theorem bivariantClassCongr_bivariantClassCongr {f f' : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] (hff : f = f') (hgg : f' = f) (hf : f ≫ sY = sX)
    (hf' : f' ≫ sY = sX) (p : ℤ) (c : BivariantClass C G sX sY f hf p) :
    bivariantClassCongr C G sX sY hgg hf' hf p
        (bivariantClassCongr C G sX sY hff hf hf' p c) = c := by
  subst hff
  rfl

/-- Two transports along equalities of degrees compose. -/
theorem bivariantClassDegreeCongr_trans (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
    {p p' p'' : ℤ} (h : p = p') (h' : p' = p'') (c : BivariantClass C G sX sY f hf p) :
    bivariantClassDegreeCongr C G sX sY f hf h'
        (bivariantClassDegreeCongr C G sX sY f hf h c) =
      bivariantClassDegreeCongr C G sX sY f hf (h.trans h') c := by
  subst h
  subst h'
  rfl

/-- A transport along a reflexive equality of degrees is the identity. -/
theorem bivariantClassDegreeCongr_rfl (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX)
    {p : ℤ} (h : p = p) (c : BivariantClass C G sX sY f hf p) :
    bivariantClassDegreeCongr C G sX sY f hf h c = c :=
  rfl

/-- Transports along an equality of morphisms and along an equality of degrees commute. -/
theorem bivariantClassCongr_bivariantClassDegreeCongr {f f' : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] (hff : f = f') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) {p p' : ℤ}
    (h : p = p') (c : BivariantClass C G sX sY f hf p) :
    bivariantClassCongr C G sX sY hff hf hf' p'
        (bivariantClassDegreeCongr C G sX sY f hf h c) =
      bivariantClassDegreeCongr C G sX sY f' hf' h
        (bivariantClassCongr C G sX sY hff hf hf' p c) := by
  subst hff
  subst h
  rfl

end Collapse

/-! ### The unit law for the composition of bivariant classes -/

/-- The base change of the identity of `Y` along `Z ×_X T ⟶ Y`, followed by the pasting
isomorphism `Y ×_Y (Y ×_Z T) ≅ Y ×_Z T` of Stacks 0B75, is the comparison isomorphism of the two
readings `g` and `𝟙 Y ≫ g` of the morphism. -/
theorem identityBaseChangeIso_inv_comp_pullbackRightPullbackFstIso_hom {Y Z T : Scheme.{u}}
    (g : Y ⟶ Z) (t : T ⟶ Z) :
    (identityBaseChangeIso (pullback.fst g t)).inv ≫
        (pullbackRightPullbackFstIso g t (𝟙 Y)).hom =
      (pullback.congrHom (Category.id_comp g).symm (rfl : t = t)).hom := by
  apply pullback.hom_ext <;>
    simp [fst_eq_identityBaseChangeIso_hom (pullback.fst g t)]

/-- The base change along `f : X ⟶ Y` of the identity base change `T ≅ Y ×_Y T`, followed by the
pasting isomorphism `X ×_Y (Y ×_Y T) ≅ X ×_Y T` of Stacks 0B75, is the comparison isomorphism of
the two readings `f` and `f ≫ 𝟙 Y` of the morphism. This is the mirror of
`Stacks.Chow.identityBaseChangeIso_inv_comp_pullbackRightPullbackFstIso_hom` for the identity on
the right. -/
theorem testBaseChangeIso_comp_pullbackRightPullbackFstIso_hom {X Y T : Scheme.{u}} (f : X ⟶ Y)
    (t : T ⟶ Y) (ht : (identityBaseChangeIso t).inv ≫ pullback.fst (𝟙 Y) t = t) :
    (testBaseChangeIso f (pullback.fst (𝟙 Y) t) (identityBaseChangeIso t).inv t ht).hom ≫
        (pullbackRightPullbackFstIso (𝟙 Y) t f).hom =
      (pullback.congrHom (Category.comp_id f).symm (rfl : t = t)).hom := by
  apply pullback.hom_ext <;> simp [testBaseChangeIso]

/-- The cap operation of the identity class `1 ∈ A⁰(X)` of Stacks 0FBS, as a pushforward: it
carries a class on the test scheme to the same class on the base change `X ×_X T`. -/
theorem bivariantIdentityClass_cap_eq (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (G : GysinSystem C)
    (hgysin : IdentityCapRule.TransportGysinNaturality C sX 0 (identityCapRule C sX) G)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) :
    (bivariantIdentityClass C sX G hgysin).cap g k α =
      Eq.mp (congrArg (chowGroup C (pullback.fst (𝟙 X) g ≫ sX)) (sub_zero k).symm)
        (chowPushforwardOfIso C (g ≫ sX) (pullback.fst (𝟙 X) g ≫ sX)
          (identityBaseChangeIso g).inv (identityBaseChangeIso_hom_comp C sX g) k α) := by
  rw [bivariantIdentityClass_cap]
  exact identityCapRule_transport_apply C sX g k α

/-- **The unit law for the composition of bivariant classes of Stacks 0B75**: the composite of the
identity class `1 ∈ A⁰(Y)` of Stacks 0FBS with `c ∈ A^q(Y ⟶ Z)` is `c`, read for the morphism
`𝟙 Y ≫ g` and in the degree `0 + q`.

Both sides cap the same way. The cap operation of the composite is cap with `c` followed by cap
with `1`, pushed forward along the pasting isomorphism of pullbacks; cap with `1` is pushforward
along the base change of the identity, and
`Stacks.Chow.identityBaseChangeIso_inv_comp_pullbackRightPullbackFstIso_hom` identifies the
composite of the two isomorphisms with the comparison isomorphism that the transport of `c` pushes
along. -/
theorem bivariantComposite_identityClass_left (C : ChowSituation.{u}) (G : GysinSystem C)
    {Y Z : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (g : Y ⟶ Z) [LocallyOfFiniteType g] (hg : g ≫ sZ = sY) (q : ℤ)
    (hgysin : IdentityCapRule.TransportGysinNaturality C sY 0 (identityCapRule C sY) G)
    (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) (c : BivariantClass C G sY sZ g hg q) :
    bivariantComposite C G sY sY sZ (𝟙 Y) g (Category.id_comp sY) hg 0 q
        (bivariantIdentityClass C sY G hgysin) c hgys hgysc =
      bivariantClassDegreeCongr C G sY sZ (𝟙 Y ≫ g)
        (comp_comp_structureMorphism_eq (Category.id_comp sY) hg) (zero_add q).symm
        (bivariantClassCongr C G sY sZ (Category.id_comp g).symm hg
          (comp_comp_structureMorphism_eq (Category.id_comp sY) hg) q c) := by
  apply BivariantClass.ext
  intro T t ht k α
  have hbase : (pullback.congrHom (Category.id_comp g).symm (rfl : t = t)).hom ≫
      (pullback.fst (𝟙 Y ≫ g) t ≫ sY) = pullback.fst g t ≫ sY := by
    rw [← Category.assoc]
    simp
  rw [bivariantComposite_cap, bivariantCompositeCap_apply,
    bivariantIdentityClass_cap_eq C sY G hgysin (pullback.fst g t) (k - q) (c.cap t k α),
    properChowPushforward_eq_chowPushforwardOfIso C
      (pullback.fst (𝟙 Y) (pullback.fst g t) ≫ sY) (pullback.fst (𝟙 Y ≫ g) t ≫ sY)
      (pullbackRightPullbackFstIso g t (𝟙 Y)).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sY (𝟙 Y) g t) (k - q - 0) _,
    ← chowPushforwardOfIso_cast C (pullback.fst (𝟙 Y) (pullback.fst g t) ≫ sY)
      (pullback.fst (𝟙 Y ≫ g) t ≫ sY) (pullbackRightPullbackFstIso g t (𝟙 Y)).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sY (𝟙 Y) g t) (sub_zero (k - q)).symm,
    chowPushforwardOfIso_comp_apply C (pullback.fst g t ≫ sY)
      (pullback.fst (𝟙 Y) (pullback.fst g t) ≫ sY) (pullback.fst (𝟙 Y ≫ g) t ≫ sY)
      (identityBaseChangeIso (pullback.fst g t)).inv
      (pullbackRightPullbackFstIso g t (𝟙 Y)).hom
      (identityBaseChangeIso_hom_comp C sY (pullback.fst g t))
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sY (𝟙 Y) g t) (k - q),
    chowPushforwardOfIso_congr_apply C (pullback.fst g t ≫ sY)
      (pullback.fst (𝟙 Y ≫ g) t ≫ sY) _
      (pullback.congrHom (Category.id_comp g).symm (rfl : t = t)).hom
      (identityBaseChangeIso_inv_comp_pullbackRightPullbackFstIso_hom g t) _ hbase (k - q),
    bivariantClassCongr_cap C G sY sZ (Category.id_comp g).symm hg
      (comp_comp_structureMorphism_eq (Category.id_comp sY) hg) q c t k α hbase,
    chowGroupDegreeEquiv_eq_iff_heq]
  exact (chowGroup_cast_heq _ (sub_zero (k - q)).symm _).trans
    (bivariantClassDegreeCongr_cap C G sY sZ (𝟙 Y ≫ g)
      (comp_comp_structureMorphism_eq (Category.id_comp sY) hg) (zero_add q).symm _ t k α).symm

/-- **The unit law for the composition of bivariant classes of Stacks 0B75 on the right**: the
composite of `c ∈ A^p(X ⟶ Y)` with the identity class `1 ∈ A⁰(Y)` of Stacks 0FBS is `c`, read for
the morphism `f ≫ 𝟙 Y` and in the degree `p + 0`.

Where the left unit law reads cap with `1` as the outer operation of the composite, here it is the
inner one, and the proof moves `c` past it: cap with `1` is pushforward along the base change
`T ≅ Y ×_Y T` of the identity, and the cap operation of a bivariant class commutes with
pushforward along an isomorphism of test schemes by condition (1) of Stacks 0B76, in the form
`Stacks.Chow.BivariantClass.cap_chowPushforwardOfIso`. What is left is the geometry:
`Stacks.Chow.testBaseChangeIso_comp_pullbackRightPullbackFstIso_hom` identifies the base change of
that isomorphism, followed by the pasting isomorphism of pullbacks, with the comparison
isomorphism that the transport of `c` pushes along. -/
theorem bivariantComposite_identityClass_right (C : ChowSituation.{u}) (G : GysinSystem C)
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)
    (hgysin : IdentityCapRule.TransportGysinNaturality C sY 0 (identityCapRule C sY) G)
    (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward) (c : BivariantClass C G sX sY f hf p) :
    bivariantComposite C G sX sY sY f (𝟙 Y) hf (Category.id_comp sY) p 0 c
        (bivariantIdentityClass C sY G hgysin) hgys hgysc =
      bivariantClassDegreeCongr C G sX sY (f ≫ 𝟙 Y)
        (comp_comp_structureMorphism_eq hf (Category.id_comp sY)) (add_zero p).symm
        (bivariantClassCongr C G sX sY (Category.comp_id f).symm hf
          (comp_comp_structureMorphism_eq hf (Category.id_comp sY)) p c) := by
  apply BivariantClass.ext
  intro T t ht k α
  have ht' : (identityBaseChangeIso t).inv ≫ pullback.fst (𝟙 Y) t = t := by
    rw [fst_eq_identityBaseChangeIso_hom t, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hbase : (pullback.congrHom (Category.comp_id f).symm (rfl : t = t)).hom ≫
      (pullback.fst (f ≫ 𝟙 Y) t ≫ sX) = pullback.fst f t ≫ sX := by
    rw [← Category.assoc]
    simp
  have hinner : c.cap (pullback.fst (𝟙 Y) t) (k - 0)
        (chowGroupDegreeEquiv C (pullback.fst (𝟙 Y) t ≫ sY) (sub_zero k).symm
          (chowPushforwardOfIso C (t ≫ sY) (pullback.fst (𝟙 Y) t ≫ sY)
            (identityBaseChangeIso t).inv (identityBaseChangeIso_hom_comp C sY t) k α)) =
      chowGroupDegreeEquiv C (pullback.fst f (pullback.fst (𝟙 Y) t) ≫ sX)
        (by ring : k - p = k - 0 - p)
        (c.cap (pullback.fst (𝟙 Y) t) k
          (chowPushforwardOfIso C (t ≫ sY) (pullback.fst (𝟙 Y) t ≫ sY)
            (identityBaseChangeIso t).inv (identityBaseChangeIso_hom_comp C sY t) k α)) :=
    (c.cap_transport_eq (pullback.fst (𝟙 Y) t) (sub_zero k).symm
      (by ring : k - p = k - 0 - p) rfl
        (chowPushforwardOfIso C (t ≫ sY) (pullback.fst (𝟙 Y) t ≫ sY)
          (identityBaseChangeIso t).inv (identityBaseChangeIso_hom_comp C sY t) k α)).symm
  rw [bivariantComposite_cap, bivariantCompositeCap_apply,
    bivariantIdentityClass_cap_eq C sY G hgysin t k α,
    eqMp_chowGroup C (pullback.fst (𝟙 Y) t ≫ sY) (sub_zero k).symm, hinner,
    c.cap_chowPushforwardOfIso (pullback.fst (𝟙 Y) t) (identityBaseChangeIso t).inv t ht'
      (t ≫ sY) rfl k (identityBaseChangeIso_hom_comp C sY t) α α rfl,
    properChowPushforward_eq_chowPushforwardOfIso C
      (pullback.fst f (pullback.fst (𝟙 Y) t) ≫ sX) (pullback.fst (f ≫ 𝟙 Y) t ≫ sX)
      (pullbackRightPullbackFstIso (𝟙 Y) t f).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f (𝟙 Y) t) (k - 0 - p) _,
    ← chowGroupDegreeEquiv_chowPushforwardOfIso C
      (pullback.fst f (pullback.fst (𝟙 Y) t) ≫ sX) (pullback.fst (f ≫ 𝟙 Y) t ≫ sX)
      (pullbackRightPullbackFstIso (𝟙 Y) t f).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f (𝟙 Y) t)
      (by ring : k - p = k - 0 - p),
    chowGroupDegreeEquiv_chowGroupDegreeEquiv,
    chowPushforwardOfIso_comp_apply C (pullback.fst f t ≫ sX)
      (pullback.fst f (pullback.fst (𝟙 Y) t) ≫ sX) (pullback.fst (f ≫ 𝟙 Y) t ≫ sX)
      (testBaseChangeIso f (pullback.fst (𝟙 Y) t) (identityBaseChangeIso t).inv t ht').hom
      (pullbackRightPullbackFstIso (𝟙 Y) t f).hom (by simp)
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f (𝟙 Y) t) (k - p),
    chowPushforwardOfIso_congr_apply C (pullback.fst f t ≫ sX)
      (pullback.fst (f ≫ 𝟙 Y) t ≫ sX) _
      (pullback.congrHom (Category.comp_id f).symm (rfl : t = t)).hom
      (testBaseChangeIso_comp_pullbackRightPullbackFstIso_hom f t ht') _ hbase (k - p),
    bivariantClassCongr_cap C G sX sY (Category.comp_id f).symm hf
      (comp_comp_structureMorphism_eq hf (Category.id_comp sY)) p c t k α hbase,
    chowGroupDegreeEquiv_eq_iff_heq]
  exact (bivariantClassDegreeCongr_cap C G sX sY (f ≫ 𝟙 Y)
    (comp_comp_structureMorphism_eq hf (Category.id_comp sY)) (add_zero p).symm _ t k α).symm

/-- The restriction map `res : A⁰(Y) ⟶ A⁰(Y')` of Stacks 0B7F carries the identity class `1` to
the identity class `1`. By the identification of Stacks 0FBS this is the cap formula
`res(c) ∩ α = c ∩ α` of Stacks 0B7F at `c = 1`. -/
theorem chowCohomologyRestriction_bivariantIdentityClass (C : ChowSituation.{u})
    (G : GysinSystem C) {Y Y' : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : Y' ⟶ Y) [LocallyOfFiniteType f] (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysinY : IdentityCapRule.TransportGysinNaturality C sY 0 (identityCapRule C sY) G)
    (hgysinY' : IdentityCapRule.TransportGysinNaturality C (f ≫ sY) 0
      (identityCapRule C (f ≫ sY)) G) :
    chowCohomologyRestriction C G sY f 0 hgys (bivariantIdentityClass C sY G hgysinY) =
      bivariantIdentityClass C (f ≫ sY) G hgysinY' := by
  rw [eq_bivariantIdentityClass_iff]
  intro T g hg k α
  have hid : 𝟙 T ≫ (g ≫ f ≫ sY) = (g ≫ f) ≫ sY := by
    rw [Category.id_comp, Category.assoc]
  rw [chowCohomologyRestriction_cap C G sY f 0 hgys (bivariantIdentityClass C sY G hgysinY) g k α,
    bivariantIdentityClass_cap_eq C sY G hgysinY (g ≫ f) k
      (chowGroupCongr C (Category.assoc g f sY).symm k α),
    ← chowPushforwardOfIso_cast C (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY) (g ≫ (f ≫ sY))
      (identityBaseChangeIso (g ≫ f)).hom
      (by rw [← Category.assoc]; exact identityBaseChangeIso_hom_comp_base C sY (g ≫ f))
      (sub_zero k).symm,
    chowPushforwardOfIso_comp_apply C ((g ≫ f) ≫ sY) (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY)
      (g ≫ (f ≫ sY)) (identityBaseChangeIso (g ≫ f)).inv
      (identityBaseChangeIso (g ≫ f)).hom (identityBaseChangeIso_hom_comp C sY (g ≫ f))
      (by rw [← Category.assoc]; exact identityBaseChangeIso_hom_comp_base C sY (g ≫ f)) k,
    chowPushforwardOfIso_congr_apply C ((g ≫ f) ≫ sY) (g ≫ (f ≫ sY))
      ((identityBaseChangeIso (g ≫ f)).inv ≫ (identityBaseChangeIso (g ≫ f)).hom) (𝟙 T)
      (Iso.inv_hom_id _) _ hid k,
    chowPushforwardOfIso_id_eq_chowGroupCongr C hid k,
    chowGroupCongr_chowGroupCongr, identityCapRule_apply]
  exact congrArg _ (eq_of_heq (chowGroupCongr_heq C _ k α))

/-! ### The multiplication of Stacks 0FA0 as a biadditive map -/

section MulHom

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hRG : ProperPushforwardFlatPullbackBaseChange C)
  (hgysP : G.IsNaturalUnderProperPushforward)
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)

/-- A function additive in its argument sends `0` to `0`. -/
private theorem map_zero_of_forall_map_add {M N : Type*} [AddZeroClass M] [AddGroup N] (g : M → N)
    (h : ∀ a b, g (a + b) = g a + g b) : g 0 = 0 :=
  (AddMonoidHom.mk' g h).map_zero

/-- The first pairing of Stacks 0FA0 kills a zero localized class. -/
@[simp]
theorem localizedMulBivariantChow_zero_left (i j : ℤ) (b : chowCohomologyComponent C G sX j) :
    localizedMulBivariantChow C G sX f hgys hgysc i j 0 b = 0 :=
  map_zero_of_forall_map_add (localizedMulBivariantChow C G sX f hgys hgysc i j · b) fun a a' ↦
    localizedMulBivariantChow_add_left C G sX f hgys hgysc i j a a' b

/-- The third pairing of Stacks 0FA0 kills a zero left argument. -/
@[simp]
theorem localizedMulBivariant_zero_left (i j : ℤ)
    (d : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedMulBivariant C G sX f hgys hgysc i j 0 d = 0 :=
  map_zero_of_forall_map_add (localizedMulBivariant C G sX f hgys hgysc i j · d) fun c c' ↦
    localizedMulBivariant_add_left C G sX f hgys hgysc i j c c' d

/-- The second pairing of Stacks 0FA0 kills a zero localized class. -/
@[simp]
theorem localizedMulChowBivariant_zero_right (i j : ℤ)
    (a : chowCohomologyComponent C G sX i) :
    localizedMulChowBivariant C G sX f hgys hgysc i j a 0 = 0 :=
  map_zero_of_forall_map_add (localizedMulChowBivariant C G sX f hgys hgysc i j a ·) fun c c' ↦
    localizedMulChowBivariant_add_right C G sX f hgys hgysc i j a c c'

/-- The third pairing of Stacks 0FA0 kills a zero right argument. -/
@[simp]
theorem localizedMulBivariant_zero_right (i j : ℤ)
    (c : BivariantClass C G (f ≫ sX) sX f rfl i) :
    localizedMulBivariant C G sX f hgys hgysc i j c 0 = 0 :=
  map_zero_of_forall_map_add (localizedMulBivariant C G sX f hgys hgysc i j c ·) fun d d' ↦
    localizedMulBivariant_add_right C G sX f hgys hgysc i j c d d'

/-- A term of the localized convolution vanishes when the left factor has no localized half and
every pair of a left ambient class with a localized right class has a zero entry. -/
private theorem localizedGradingMulLocalizedTerm_eq_zero_of_snd_eq_zero (p : ℕ)
    (a b : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) (n t : ℤ)
    (ha : ∀ k, a.2 k = 0)
    (h : ∀ (ht : t < (p : ℤ)) (hk : (p : ℤ) ≤ n - t), a.1 ⟨t, ht⟩ = 0 ∨ b.2 ⟨n - t, hk⟩ = 0) :
    localizedGradingMulLocalizedTerm C G sX f hgys hgysc p p a b n t = 0 := by
  unfold localizedGradingMulLocalizedTerm
  by_cases htp : (p : ℤ) ≤ t
  · rw [dite_eq_left htp, ha]
    by_cases hk : (p : ℤ) ≤ n - t
    · rw [dite_eq_left hk, localizedMulBivariant_zero_left, map_zero]
    · rw [dite_eq_right hk, localizedMulBivariantChow_zero_left, map_zero]
  · by_cases hk : (p : ℤ) ≤ n - t
    · rw [dite_eq_right htp, dite_eq_left hk]
      rcases h (not_le.1 htp) hk with h0 | h0
      · rw [h0, localizedMulChowBivariant_zero_left, map_zero]
      · rw [h0, localizedMulChowBivariant_zero_right, map_zero]
    · rw [dite_eq_right htp, dite_eq_right hk]

/-- **The elements with vanishing negative components are closed under the multiplication of
Stacks 0FA0.** In a negative degree `n` the product is the sum over `n ≤ i ≤ 0`, and each of its
terms pairs a component of one factor in a negative degree with a component of the other: the
index `i = 0` leaves `n - i = n < 0` for the second factor, and every other index is itself
negative. So each term vanishes by `Stacks.Chow.localizedGradingMulAmbientTerm_eq_zero`. No degree
`n < 0` lies at or above the cutoff `r`, so the localized half has nothing to prove.

Unlike the rest of this file the hypotheses are needed: with the index range
`Finset.Icc (min 0 n) (max 0 n)` a product in a negative degree is a sum of terms the source's own
pairings produce from the factors' negative-degree components, and nothing makes those vanish.
`Stacks.Chow.LocalizedGrading.VanishesInNegativeDegrees` is a condition of this library, which the
source does not impose; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingMultiplication`. -/
theorem localizedBivariantGradingMul_vanishesInNegativeDegrees (p q r : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q)
    (ha : LocalizedGrading.VanishesInNegativeDegrees C G sX f p a)
    (hb : LocalizedGrading.VanishesInNegativeDegrees C G sX f q b) :
    LocalizedGrading.VanishesInNegativeDegrees C G sX f r
      (localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r a b) := by
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ absurd hi ?_⟩
  · change ∑ j ∈ Finset.Icc (min 0 i.1) (max 0 i.1),
        localizedGradingMulAmbientTerm C G sX f hRG hgysP hgys hgysc p q a b i.1 j = 0
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    rw [Finset.mem_Icc] at hj
    exact localizedGradingMulAmbientTerm_eq_zero hRG hgysP hgys hgysc ha hb i.1 j (by omega)
  · have := i.2
    omega

/-- **Stacks 0FA0.** The multiplication
`A⁽ᵖ⁾(Z ⟶ X) × A⁽ᑫ⁾(Z ⟶ X) ⟶ A⁽ʳ⁾(Z ⟶ X)` of the remark as a **biadditive map**, at every `p`, `q`
and every target `r`. This is the distributive law of the source's graded algebra, bundled: the
underlying function is `Stacks.Chow.localizedBivariantGradingMul` and the additivity in each
argument is `Stacks.Chow.localizedBivariantGradingMul_add_left` and `_add_right`. -/
@[stacks 0FA0 "the multiplication of the remark's graded algebra as a biadditive map \
A^(p)(Z ⟶ X) ⟶ A^(q)(Z ⟶ X) ⟶ A^(r)(Z ⟶ X), which is its distributive law, at every p, q and \
every target r"]
def localizedBivariantGradingMulHom (p q r : ℕ) :
    localizedBivariantGrading C G (f ≫ sX) sX f rfl p →+
      localizedBivariantGrading C G (f ≫ sX) sX f rfl q →+
        localizedBivariantGrading C G (f ≫ sX) sX f rfl r :=
  AddMonoidHom.mk'
    (fun a ↦ AddMonoidHom.mk'
      (fun b ↦ localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r a b)
      (localizedBivariantGradingMul_add_right hRG hgysP hgys hgysc a))
    (fun a a' ↦ AddMonoidHom.ext fun b ↦
      localizedBivariantGradingMul_add_left hRG hgysP hgys hgysc a a' b)

/-- **Stacks 0FA0.** The multiplication with the target `A⁽ᵐᵃˣ⁽ᵖ⁼ᑫ⁾⁾(Z ⟶ X)` the source displays,
as a biadditive map. -/
@[stacks 0FA0 "the multiplication A^(p)(Z ⟶ X) × A^(q)(Z ⟶ X) ⟶ A^(max(p,q))(Z ⟶ X) displayed in \
the remark as a biadditive map, for every p and q"]
def localizedBivariantGradingMulMaxHom (p q : ℕ) :
    localizedBivariantGrading C G (f ≫ sX) sX f rfl p →+
      localizedBivariantGrading C G (f ≫ sX) sX f rfl q →+
        localizedBivariantGrading C G (f ≫ sX) sX f rfl (max p q) :=
  localizedBivariantGradingMulHom C G sX f hRG hgysP hgys hgysc p q (max p q)

/-- **Stacks 0FA0.** The multiplication internal to `A⁽ᵖ⁾(Z ⟶ X)` — the product of the source's
graded algebra — as a biadditive map, for every `p ≥ 0`. -/
@[stacks 0FA0 "the multiplication internal to A^(p)(Z ⟶ X) of the remark's graded algebra as a \
biadditive map A^(p) ⟶ A^(p) ⟶ A^(p), which is its distributive law, for every p ≥ 0"]
def localizedBivariantGradingInternalMulHom (p : ℕ) :
    localizedBivariantGrading C G (f ≫ sX) sX f rfl p →+
      localizedBivariantGrading C G (f ≫ sX) sX f rfl p →+
        localizedBivariantGrading C G (f ≫ sX) sX f rfl p :=
  localizedBivariantGradingMulHom C G sX f hRG hgysP hgys hgysc p p p

/-- The biadditive multiplication is the multiplication. -/
@[simp]
theorem localizedBivariantGradingMulHom_apply (p q r : ℕ)
    (a : localizedBivariantGrading C G (f ≫ sX) sX f rfl p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl q) :
    localizedBivariantGradingMulHom C G sX f hRG hgysP hgys hgysc p q r a b =
      localizedBivariantGradingMul C G sX f hRG hgysP hgys hgysc p q r a b :=
  rfl

/-- **Stacks 0FA0, uniqueness of the canonical multiplication as a biadditive map.** A biadditive
map whose components are the two finite convolutions of the source — the property
`Stacks.Chow.LocalizedGrading.IsMul` — is `Stacks.Chow.localizedBivariantGradingMulHom`. This is
`Stacks.Chow.LocalizedGrading.IsMul.eq_localizedBivariantGradingMul` read through
`Stacks.Chow.localizedBivariantGradingMulHom_apply`; additivity is not used in the uniqueness, the
component formulas already prescribing every value. -/
@[stacks 0FA0 "uniqueness of the canonical multiplication as a biadditive map: a biadditive map \
satisfying the two finite-convolution formulas of the remark is the multiplication"]
theorem eq_localizedBivariantGradingMulHom (p q r : ℕ)
    (M : localizedBivariantGrading C G (f ≫ sX) sX f rfl p →+
      localizedBivariantGrading C G (f ≫ sX) sX f rfl q →+
        localizedBivariantGrading C G (f ≫ sX) sX f rfl r)
    (hM : LocalizedGrading.IsMul C G sX f hRG hgysP hgys hgysc p q r fun a b ↦ M a b) :
    M = localizedBivariantGradingMulHom C G sX f hRG hgysP hgys hgysc p q r :=
  AddMonoidHom.ext fun a ↦ AddMonoidHom.ext fun b ↦
    congrFun (congrFun (LocalizedGrading.IsMul.eq_localizedBivariantGradingMul C G sX f hRG hgysP
      hgys hgysc hM) a) b

/-! ### What associativity of the internal product forces when `p ≥ 2` -/

/-- From the cutoff on, `Stacks.Chow.localizedGradingSingleLow` vanishes. -/
@[simp]
theorem localizedGradingSingleLow_snd (p : ℕ) (i : {i : ℤ // i < (p : ℤ)})
    (a : chowCohomologyComponent C G sX i.1) (k : {k : ℤ // (p : ℤ) ≤ k}) :
    (localizedGradingSingleLow C G sX f p i a).2 k = 0 :=
  rfl

/-- At its own degree, `Stacks.Chow.localizedGradingSingleLow` is the class it was built from. -/
theorem localizedGradingSingleLow_fst_self (p : ℕ) (i : {i : ℤ // i < (p : ℤ)})
    (a : chowCohomologyComponent C G sX i.1) :
    (localizedGradingSingleLow C G sX f p i a).1 i = a :=
  Pi.single_eq_same (M := fun k : {i : ℤ // i < (p : ℤ)} ↦ chowCohomologyComponent C G sX k.1) i a

/-- In every other degree below the cutoff, `Stacks.Chow.localizedGradingSingleLow` vanishes. -/
theorem localizedGradingSingleLow_fst_of_ne (p : ℕ) (i : {i : ℤ // i < (p : ℤ)})
    (a : chowCohomologyComponent C G sX i.1) (k : {k : ℤ // k < (p : ℤ)}) (hk : k.1 ≠ i.1) :
    (localizedGradingSingleLow C G sX f p i a).1 k = 0 :=
  Pi.single_eq_of_ne (M := fun k : {i : ℤ // i < (p : ℤ)} ↦ chowCohomologyComponent C G sX k.1)
    (fun h ↦ hk (congrArg Subtype.val h)) a

/-- **The product of two classes carried by ambient degrees whose sum reaches the cutoff is zero.**
Let `i, j < p` with `i + j ≥ p` — the pair of degrees for which the remark prescribes no value, and
which exists exactly for `p ≥ 2` (`Stacks.Chow.localizedGrading_exists_ambient_pair` at
`q = r = p`). Then the product internal to `A⁽ᵖ⁾(Z ⟶ X)` of the element carrying `u ∈ Aⁱ(X)` in
degree `i` and the element carrying `v ∈ Aʲ(X)` in degree `j` is zero: in a degree below the cutoff
the convolution has no term, since the only candidate degree is `i + j ≥ p`, and in a degree at or
above it every term is one of the unprescribed ones, whose value is `0`
(`Stacks.Chow.localizedGradingMulLocalizedTerm_of_lt_of_lt`). -/
theorem localizedBivariantGradingInternalMul_singleLow_eq_zero (p : ℕ)
    (i j : {i : ℤ // i < (p : ℤ)}) (hij : (p : ℤ) ≤ i.1 + j.1)
    (u : chowCohomologyComponent C G sX i.1) (v : chowCohomologyComponent C G sX j.1) :
    localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p
        (localizedGradingSingleLow C G sX f p i u)
        (localizedGradingSingleLow C G sX f p j v) = 0 := by
  refine Prod.ext (funext fun d ↦ ?_) (funext fun d ↦ ?_)
  · obtain ⟨dv, hdv⟩ := d
    change ∑ t ∈ Finset.Icc (min 0 dv) (max 0 dv), _ = (0 : chowCohomologyComponent C G sX dv)
    refine Finset.sum_eq_zero fun t _ ↦ ?_
    unfold localizedGradingMulAmbientTerm
    by_cases ht : t = i.1
    · subst ht
      rw [localizedGradingComponentOnAmbient_singleLow_of_ne C G sX f hRG hgysP hgysc p j v
          (dv - i.1) (by omega), chowCohomologyComposite_zero_right, map_zero]
    · rw [localizedGradingComponentOnAmbient_singleLow_of_ne C G sX f hRG hgysP hgysc p i u t ht,
        chowCohomologyComposite_zero_left, map_zero]
  · obtain ⟨dv, hdv⟩ := d
    change ∑ t ∈ Finset.Icc (min 0 dv) (max 0 dv),
        localizedGradingMulLocalizedTerm C G sX f hgys hgysc p p
        (localizedGradingSingleLow C G sX f p i u) (localizedGradingSingleLow C G sX f p j v)
        dv t = (0 : BivariantClass C G (f ≫ sX) sX f rfl dv)
    refine Finset.sum_eq_zero fun t _ ↦ ?_
    refine localizedGradingMulLocalizedTerm_eq_zero_of_snd_eq_zero C G sX f hgys hgysc p _ _ dv t
      (localizedGradingSingleLow_snd C G sX f p i u) fun ht hk ↦ ?_
    by_cases hti : t = i.1
    · exact Or.inr (localizedGradingSingleLow_snd C G sX f p j v ⟨dv - t, hk⟩)
    · exact Or.inl (localizedGradingSingleLow_fst_of_ne C G sX f p i u ⟨t, ht⟩ hti)

/-- **The degree `n` component of a product whose left factor carries a single ambient class in
degree `i`, in a degree whose complement `n - i` reaches the cutoff.** It is the source's second
pairing, `res(u) ∘ cₙ₋ᵢ`: the convolution has the single term at `i`, every other index either
meeting the zero localized half of `Stacks.Chow.localizedGradingSingleLow` or falling on one of
the pairs of degrees the remark leaves unprescribed. Read together with
`Stacks.Chow.localizedBivariantGradingInternalMul_singleLow_eq_zero_of_assoc`, this is what that
theorem's vanishing says about the pairings of the source: applied twice, at `n = i + (j + k)` and
at `j + k`, it writes the degree `n` component of `u · (v · c)` as
`res(u) ∘ (res(v) ∘ cₖ)`. -/
theorem localizedBivariantGradingInternalMul_singleLow_snd (p : ℕ) (i : {i : ℤ // i < (p : ℤ)})
    (hi0 : 0 ≤ i.1) (u : chowCohomologyComponent C G sX i.1)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) (n : ℤ) (hn : (p : ℤ) ≤ n)
    (hin : (p : ℤ) ≤ n - i.1) :
    (localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p
        (localizedGradingSingleLow C G sX f p i u) c).2 ⟨n, hn⟩ =
      bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl (by ring : i.1 + (n - i.1) = n)
        (localizedMulChowBivariant C G sX f hgys hgysc i.1 (n - i.1) u
          (c.2 ⟨n - i.1, hin⟩)) := by
  change ∑ t ∈ Finset.Icc (min 0 n) (max 0 n),
      localizedGradingMulLocalizedTerm C G sX f hgys hgysc p p
        (localizedGradingSingleLow C G sX f p i u) c n t = _
  rw [Finset.sum_eq_single_of_mem i.1 (Finset.mem_Icc.2 ⟨by omega, by omega⟩) ?_]
  · unfold localizedGradingMulLocalizedTerm
    rw [dite_eq_right (not_le.2 i.2), dite_eq_left hin, localizedGradingSingleLow_fst_self]
  · intro t _ ht
    exact localizedGradingMulLocalizedTerm_eq_zero_of_snd_eq_zero C G sX f hgys hgysc p _ _ n t
      (localizedGradingSingleLow_snd C G sX f p i u) fun htp _ ↦
        Or.inl (localizedGradingSingleLow_fst_of_ne C G sX f p i u ⟨t, htp⟩ ht)

/-- **What associativity of the source's graded algebra on `A⁽ᵖ⁾(Z ⟶ X)` would force for
`p ≥ 2`.** Suppose the product internal to `A⁽ᵖ⁾(Z ⟶ X)` is associative on every triple, and let
`i, j < p` be ambient degrees with `i + j ≥ p`, which exist exactly for `p ≥ 2`
(`Stacks.Chow.localizedGrading_exists_ambient_pair`). Then for every `u ∈ Aⁱ(X)`, `v ∈ Aʲ(X)` and
every `c ∈ A⁽ᵖ⁾(Z ⟶ X)` the product `u · (v · c)` vanishes.

The left grouping is zero because `u · v` is
(`Stacks.Chow.localizedBivariantGradingInternalMul_singleLow_eq_zero`), so associativity hands the
vanishing to the right grouping — where no unprescribed pair of degrees occurs at all: by
`Stacks.Chow.localizedGradingMulLocalizedTerm_of_lt` the degree `i + j + k` component of
`u · (v · c)` is `res(u) ∘ (res(v) ∘ cₖ)` under the source's second pairing, for every `k ≥ p`.
So associativity makes every such triple composite of the remark's own pairings vanish. Nothing in
this repository refutes that — it would take a localized group and a nonzero product in it, neither
of which is available here — but for the closed immersion `𝟙 X : X ⟶ X`, where the restriction maps
are the identity and `Aⁱ(X ⟶ X) = Aⁱ(X)`, it reads as `u · v · c = 0` in `A^*(X)`. That is why
`Stacks.Chow.localizedBivariantGradingInternalMul_assoc` is proved for `p ≤ 1`; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingMultiplication`. -/
theorem localizedBivariantGradingInternalMul_singleLow_eq_zero_of_assoc (p : ℕ)
    (hassoc : ∀ a b c : localizedBivariantGrading C G (f ≫ sX) sX f rfl p,
      localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p
          (localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p a b) c =
        localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p a
          (localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p b c))
    (i j : {i : ℤ // i < (p : ℤ)}) (hij : (p : ℤ) ≤ i.1 + j.1)
    (u : chowCohomologyComponent C G sX i.1) (v : chowCohomologyComponent C G sX j.1)
    (c : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) :
    localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p
        (localizedGradingSingleLow C G sX f p i u)
        (localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p
          (localizedGradingSingleLow C G sX f p j v) c) = 0 := by
  rw [← hassoc, localizedBivariantGradingInternalMul_singleLow_eq_zero C G sX f hRG hgysP hgys
    hgysc p i j hij u v]
  unfold localizedBivariantGradingInternalMul
  exact localizedBivariantGradingMul_zero_left hRG hgysP hgys hgysc c

end MulHom

/-! ### The unit of the graded algebra -/

section One

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hgysinX : IdentityCapRule.TransportGysinNaturality C sX 0 (identityCapRule C sX) G)

/-- **Stacks 0FA0, the unit of the graded algebra on `A⁽ᵖ⁾(Z ⟶ X)`:** the element whose degree `0`
component is the class `1 ∈ A⁰(X)` of Stacks 0FBS and whose components in the other degrees
vanish.

For `p ≥ 1` the degree `0` slot of `A⁽ᵖ⁾(Z ⟶ X)` is `A⁰(X)` and this is the unit; for `p = 0` that
slot is `A⁰(Z ⟶ X)`, which holds no canonical class, and this element is zero there. Together with
`Stacks.Chow.localizedGrading_self_admissible_iff` that makes `p = 1` the one `p` at which the
source's graded algebra on `A⁽ᵖ⁾(Z ⟶ X)` is unital. -/
@[stacks 0FA0 "the unit of the remark's graded algebra on A^(p)(Z ⟶ X): the class 1 of A^0(X) in \
the degree 0 slot, which is a slot of A^(p)(Z ⟶ X) exactly for p ≥ 1"]
def localizedBivariantGradingOne (p : ℕ) :
    localizedBivariantGrading C G (f ≫ sX) sX f rfl p :=
  (fun i ↦ if h : (0 : ℤ) = i.1 then
      bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) h
        (bivariantIdentityClass C sX G hgysinX)
    else 0,
    fun _ ↦ 0)

/-- The degree `0` component of the unit is the class `1 ∈ A⁰(X)`. -/
@[simp]
theorem localizedBivariantGradingOne_fst_zero (p : ℕ) (h : (0 : ℤ) < (p : ℤ)) :
    (localizedBivariantGradingOne C G sX f hgysinX p).1 ⟨0, h⟩ =
      bivariantIdentityClass C sX G hgysinX := by
  change (if h' : (0 : ℤ) = (0 : ℤ) then
      bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) h'
        (bivariantIdentityClass C sX G hgysinX)
    else 0) = bivariantIdentityClass C sX G hgysinX
  rw [dite_eq_left (rfl : (0 : ℤ) = (0 : ℤ))]
  rfl

/-- In a nonzero degree below the cutoff the unit vanishes. -/
@[simp]
theorem localizedBivariantGradingOne_fst_of_ne (p : ℕ) {i : ℤ} (h : i < (p : ℤ)) (hi : i ≠ 0) :
    (localizedBivariantGradingOne C G sX f hgysinX p).1 ⟨i, h⟩ = 0 :=
  dite_eq_right fun h0 ↦ hi h0.symm

/-- The component of the unit in a degree *presented as* `0` by an equality of integers is the
class `1 ∈ A⁰(X)`, transported along that equality. This is
`Stacks.Chow.localizedBivariantGradingOne_fst_zero` in the generality the degrees `n - n` and
`0 - 0` produced by the convolution of a product need. -/
theorem localizedBivariantGradingOne_fst_of_eq_zero (p : ℕ) {i : ℤ} (h : i < (p : ℤ))
    (hi : (0 : ℤ) = i) :
    (localizedBivariantGradingOne C G sX f hgysinX p).1 ⟨i, h⟩ =
      bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) hi
        (bivariantIdentityClass C sX G hgysinX) :=
  dite_eq_left hi

/-- From the cutoff onward the unit vanishes. -/
@[simp]
theorem localizedBivariantGradingOne_snd (p : ℕ) (i : {i : ℤ // (p : ℤ) ≤ i}) :
    (localizedBivariantGradingOne C G sX f hgysinX p).2 i = 0 :=
  rfl

/-- The unit has vanishing components in the negative degrees. -/
theorem localizedBivariantGradingOne_vanishesInNegativeDegrees (p : ℕ) :
    LocalizedGrading.VanishesInNegativeDegrees C G sX f p
      (localizedBivariantGradingOne C G sX f hgysinX p) :=
  ⟨fun i hi ↦ localizedBivariantGradingOne_fst_of_ne C G sX f hgysinX p i.2 (by omega),
    fun _ _ ↦ rfl⟩

end One

/-! ### The unit law -/

section UnitLaw

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : Z ⟶ X) [IsClosedImmersion f]
  (hRG : ProperPushforwardFlatPullbackBaseChange C)
  (hgysP : G.IsNaturalUnderProperPushforward)
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)
  (hgysinX : IdentityCapRule.TransportGysinNaturality C sX 0 (identityCapRule C sX) G)
  (hgysinZ : IdentityCapRule.TransportGysinNaturality C (f ≫ sX) 0
    (identityCapRule C (f ≫ sX)) G)

/-- **The unit law for the multiplication of `A^*(X)`**: the composition of bivariant classes for
the identity of `X` has the class `1 ∈ A⁰(X)` of Stacks 0FBS as a left unit. -/
theorem chowCohomologyComposite_identityClass_left (i : ℤ)
    (b : chowCohomologyComponent C G sX i) :
    chowCohomologyComposite C G sX hgys hgysc 0 i (bivariantIdentityClass C sX G hgysinX) b =
      bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) (zero_add i).symm b := by
  unfold chowCohomologyComposite
  rw [bivariantComposite_identityClass_left C G sX sX (𝟙 X) (Category.id_comp sX) i hgysinX
      hgys hgysc b,
    bivariantClassCongr_bivariantClassDegreeCongr, bivariantClassCongr_bivariantClassCongr]

/-- **The unit law for the multiplication of `A^*(X)` on the right**: the composition of bivariant
classes for the identity of `X` has the class `1 ∈ A⁰(X)` of Stacks 0FBS as a right unit. -/
theorem chowCohomologyComposite_identityClass_right (i : ℤ)
    (a : chowCohomologyComponent C G sX i) :
    chowCohomologyComposite C G sX hgys hgysc i 0 a (bivariantIdentityClass C sX G hgysinX) =
      bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) (add_zero i).symm a := by
  unfold chowCohomologyComposite
  rw [bivariantComposite_identityClass_right C G sX sX (𝟙 X) (Category.id_comp sX) i hgysinX
      hgys hgysc a,
    bivariantClassCongr_bivariantClassDegreeCongr, bivariantClassCongr_bivariantClassCongr]

/-- **The unit law for the multiplication of `A^*(X)` on the right**, with the degree of the unit
presented by an equality `0 = j`. This is the form the convolution of a product produces, where
that degree arrives as `n - n` rather than as `0`. -/
theorem chowCohomologyComposite_identityClass_right_of_eq_zero (i : ℤ) {j : ℤ} (hj : (0 : ℤ) = j)
    (a : chowCohomologyComponent C G sX i) :
    chowCohomologyComposite C G sX hgys hgysc i j a
        (bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) hj
          (bivariantIdentityClass C sX G hgysinX)) =
      bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX)
        (by omega : i = i + j) a := by
  subst hj
  rw [bivariantClassDegreeCongr_rfl,
    chowCohomologyComposite_identityClass_right C G sX hgys hgysc hgysinX i a]

/-- The composition `Aⁱ(Z) × Aʲ(Z ⟶ X) ⟶ Aⁱ⁺ʲ(Z ⟶ X)` has the class `1 ∈ A⁰(Z)` as a left
unit. -/
theorem localizedComposeChowCohomology_identityClass_left (j : ℤ)
    (c : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedComposeChowCohomology C G sX f hgys hgysc 0 j
        (bivariantIdentityClass C (f ≫ sX) G hgysinZ) c =
      bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl (zero_add j).symm c := by
  unfold localizedComposeChowCohomology
  rw [bivariantComposite_identityClass_left C G (f ≫ sX) sX f rfl j hgysinZ hgys hgysc c,
    bivariantClassCongr_bivariantClassDegreeCongr, bivariantClassCongr_bivariantClassCongr]

include hgysinZ in
/-- **The second pairing of Stacks 0FA0 at the unit:** pairing `1 ∈ A⁰(X)` with a class in
`Aʲ(Z ⟶ X)` returns that class. The restriction map of Stacks 0F9Z carries `1` to `1`, and `1` is
a left unit for the composition. -/
theorem localizedMulChowBivariant_identityClass_left (j : ℤ)
    (c : BivariantClass C G (f ≫ sX) sX f rfl j) :
    localizedMulChowBivariant C G sX f hgys hgysc 0 j (bivariantIdentityClass C sX G hgysinX) c =
      bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl (zero_add j).symm c := by
  unfold localizedMulChowBivariant
  rw [chowCohomologyRestriction_bivariantIdentityClass C G sX f hgys hgysinX hgysinZ,
    localizedComposeChowCohomology_identityClass_left C G sX f hgys hgysc hgysinZ j c]

/-- **The first pairing of Stacks 0FA0 at the unit:** pairing a class in `Aⁱ(Z ⟶ X)` with
`1 ∈ A⁰(X)` returns that class. The pairing is the composition of bivariant classes, and `1` is a
right unit for it. -/
theorem localizedMulBivariantChow_identityClass_right (i : ℤ)
    (c : BivariantClass C G (f ≫ sX) sX f rfl i) :
    localizedMulBivariantChow C G sX f hgys hgysc i 0 c (bivariantIdentityClass C sX G hgysinX) =
      bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl (add_zero i).symm c := by
  unfold localizedMulBivariantChow
  rw [bivariantComposite_identityClass_right C G (f ≫ sX) sX f rfl i hgysinX hgys hgysc c,
    bivariantClassCongr_bivariantClassDegreeCongr, bivariantClassCongr_bivariantClassCongr]

/-- **The first pairing of Stacks 0FA0 at the unit**, with the degree of the unit presented by an
equality `0 = j`. This is the form the convolution of a product produces, where that degree
arrives as `n - n` rather than as `0`. -/
theorem localizedMulBivariantChow_identityClass_right_of_eq_zero (i : ℤ) {j : ℤ}
    (hj : (0 : ℤ) = j) (c : BivariantClass C G (f ≫ sX) sX f rfl i) :
    localizedMulBivariantChow C G sX f hgys hgysc i j c
        (bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) hj
          (bivariantIdentityClass C sX G hgysinX)) =
      bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl (by omega : i = i + j) c := by
  subst hj
  rw [bivariantClassDegreeCongr_rfl,
    localizedMulBivariantChow_identityClass_right C G sX f hgys hgysc hgysinX i c]

/-- A component of an element of the grading, transported along an equality of degrees, is the
component in the equal degree. -/
theorem localizedBivariantGrading_degreeCongr_snd {p : ℕ}
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) {m n : ℤ} (hmn : m = n)
    (hm : (p : ℤ) ≤ m) (hn : (p : ℤ) ≤ n) :
    bivariantClassDegreeCongr C G (f ≫ sX) sX f rfl hmn (b.2 ⟨m, hm⟩) = b.2 ⟨n, hn⟩ := by
  subst hmn
  rfl

/-- A component below the cutoff, transported along an equality of degrees, is the component in
the equal degree. -/
theorem localizedBivariantGrading_degreeCongr_fst {p : ℕ}
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) {m n : ℤ} (hmn : m = n)
    (hm : m < (p : ℤ)) (hn : n < (p : ℤ)) :
    bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) hmn (b.1 ⟨m, hm⟩) =
      b.1 ⟨n, hn⟩ := by
  subst hmn
  rfl

/-- The degree `0` component of the unit, read in `A^*(X)`, is the class `1 ∈ A⁰(X)` of Stacks
0FBS. For `p ≥ 1` the degree `0` slot of `A⁽ᵖ⁾(Z ⟶ X)` is `A⁰(X)`, so no pushforward intervenes. -/
theorem localizedGradingComponentOnAmbient_localizedBivariantGradingOne_zero (p : ℕ) (hp : 1 ≤ p) :
    localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc p
        (localizedBivariantGradingOne C G sX f hgysinX p) 0 =
      bivariantIdentityClass C sX G hgysinX := by
  unfold localizedGradingComponentOnAmbient
  rw [dite_eq_right (by omega : ¬ (p : ℤ) ≤ (0 : ℤ))]
  exact localizedBivariantGradingOne_fst_zero C G sX f hgysinX p (by omega)

/-- In every nonzero degree the component of the unit, read in `A^*(X)`, vanishes: below the cutoff
because the unit is zero there, and from the cutoff on because its localized half is zero and the
pushforward of Stacks 0EPK is additive. -/
theorem localizedGradingComponentOnAmbient_localizedBivariantGradingOne_of_ne (p : ℕ) (k : ℤ)
    (hk : k ≠ 0) :
    localizedGradingComponentOnAmbient C G sX f hRG hgysP hgysc p
        (localizedBivariantGradingOne C G sX f hgysinX p) k = 0 := by
  unfold localizedGradingComponentOnAmbient
  by_cases hkp : (p : ℤ) ≤ k
  · rw [dite_eq_left hkp, localizedBivariantGradingOne_snd]
    exact localizedGradingPushforward_zero C G sX f hRG hgysP hgysc k
  · rw [dite_eq_right hkp]
    exact localizedBivariantGradingOne_fst_of_ne C G sX f hgysinX p (not_le.1 hkp) hk

include hgysinZ in
/-- **Stacks 0FA0, the unit law of the graded algebra on `A⁽ᵖ⁾(Z ⟶ X)`, for every `p ≥ 1`:**
multiplying by `Stacks.Chow.localizedBivariantGradingOne` on the left returns the element. The
bound `1 ≤ p` is what puts the degree `0` slot, where the unit sits, in `A⁰(X)`; for `p = 0` that
slot is `A⁰(Z ⟶ X)` and holds no canonical class.

Degree by degree the product has a single surviving term, the one at `i = 0`: below the cutoff it
is `1 · bₙ` in `A^*(X)` (`Stacks.Chow.chowCohomologyComposite_identityClass_left`), and from the
cutoff on it is the source's second pairing at the unit
(`Stacks.Chow.localizedMulChowBivariant_identityClass_left`), which is `res(1) ∘ bₙ = bₙ`.

No hypothesis is imposed on `b`: the index range of the sums,
`Finset.Icc (min 0 n) (max 0 n)`, contains the one surviving index `i = 0` in every degree
(`Stacks.Chow.zero_mem_Icc_min_max`), so the law holds on all of `A⁽ᵖ⁾(Z ⟶ X)` — which is the group
the source asserts the graded algebra on, negative-degree factors included. See the implementation
notes of this module. -/
@[stacks 0FA0 "the unit law of the remark's graded algebra on A^(p)(Z ⟶ X) for every p ≥ 1: the \
class 1 of A^0(X) placed in degree 0 is a left unit for the multiplication internal to \
A^(p)(Z ⟶ X), on all of A^(p)(Z ⟶ X)"]
theorem localizedBivariantGradingInternalMul_one_left (p : ℕ) (hp : 1 ≤ p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) :
    localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p
        (localizedBivariantGradingOne C G sX f hgysinX p) b = b := by
  refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
  · obtain ⟨iv, hiv⟩ := i
    change ∑ j ∈ Finset.Icc (min 0 iv) (max 0 iv), _ = _
    rw [Finset.sum_eq_single_of_mem (0 : ℤ) (zero_mem_Icc_min_max iv) ?_]
    · unfold localizedGradingMulAmbientTerm
      rw [localizedGradingComponentOnAmbient_localizedBivariantGradingOne_zero C G sX f hRG
          hgysP hgysc hgysinX p hp,
        localizedGradingComponentOnAmbient_of_lt C G sX f hRG hgysP hgysc p b (iv - 0)
          (by omega),
        chowCohomologyComposite_identityClass_left C G sX hgys hgysc hgysinX (iv - 0) _,
        bivariantClassDegreeCongr_trans]
      exact localizedBivariantGrading_degreeCongr_fst C G sX f b (by omega) (by omega) hiv
    · intro j _ hjne
      unfold localizedGradingMulAmbientTerm
      rw [localizedGradingComponentOnAmbient_localizedBivariantGradingOne_of_ne C G sX f hRG
          hgysP hgysc hgysinX p j hjne, chowCohomologyComposite_zero_left, map_zero]
  · obtain ⟨n, hn⟩ := i
    change ∑ j ∈ Finset.Icc (min 0 n) (max 0 n), _ = _
    rw [Finset.sum_eq_single_of_mem (0 : ℤ) (zero_mem_Icc_min_max n) ?_]
    · unfold localizedGradingMulLocalizedTerm
      rw [dite_eq_right (by omega : ¬ (p : ℤ) ≤ (0 : ℤ)), dite_eq_left (by omega : (p : ℤ) ≤ n - 0),
        localizedBivariantGradingOne_fst_zero C G sX f hgysinX p (by omega),
        localizedMulChowBivariant_identityClass_left C G sX f hgys hgysc hgysinX hgysinZ (n - 0) _,
        bivariantClassDegreeCongr_trans]
      exact localizedBivariantGrading_degreeCongr_snd C G sX f b (sub_zero n) _ hn
    · intro j _ hjne
      exact localizedGradingMulLocalizedTerm_eq_zero_of_snd_eq_zero C G sX f hgys hgysc p _ _ n j
        (localizedBivariantGradingOne_snd C G sX f hgysinX p) fun hjp _ ↦
          Or.inl (localizedBivariantGradingOne_fst_of_ne C G sX f hgysinX p hjp hjne)

/-- **Stacks 0FA0, the unit law of the graded algebra on `A⁽ᵖ⁾(Z ⟶ X)` on the right, for every
`p ≥ 1`:** multiplying by `Stacks.Chow.localizedBivariantGradingOne` on the right returns the
element. Together with `Stacks.Chow.localizedBivariantGradingInternalMul_one_left` this makes
`Stacks.Chow.localizedBivariantGradingOne` a two-sided unit, and with the associativity of
`Stacks.Chow.localizedBivariantGradingInternalMul_assoc` it is what
`Stacks.Chow.localizedBivariantGradingMonoid` is assembled from.

Here the surviving term of the degree `n` component is the one at `i = n`, and the pairing that
applies is the source's *first* one, `Stacks.Chow.localizedMulBivariantChow_identityClass_right`:
`bₙ ∘ 1 = bₙ`.

This law is the sharp test of the index range of the sums: the component of `b` it has to return
in degree `n` is carried by the term at `i = n` alone. The range
`Finset.Icc (min 0 n) (max 0 n)` contains `i = n` in every degree
(`Stacks.Chow.self_mem_Icc_min_max`), so the law needs no hypothesis on `b` and holds on all of
`A⁽ᵖ⁾(Z ⟶ X)`; under the narrower range `0 ≤ i ≤ n` it would fail in every negative degree in which
`b` has a nonzero component. See the implementation notes of this module. -/
@[stacks 0FA0 "the unit law of the remark's graded algebra on A^(p)(Z ⟶ X) on the right for every \
p ≥ 1: the class 1 of A^0(X) placed in degree 0 is a right unit for the multiplication internal to \
A^(p)(Z ⟶ X), on all of A^(p)(Z ⟶ X)"]
theorem localizedBivariantGradingInternalMul_one_right (p : ℕ) (hp : 1 ≤ p)
    (b : localizedBivariantGrading C G (f ≫ sX) sX f rfl p) :
    localizedBivariantGradingInternalMul C G sX f hRG hgysP hgys hgysc p b
        (localizedBivariantGradingOne C G sX f hgysinX p) = b := by
  refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
  · obtain ⟨iv, hiv⟩ := i
    change ∑ j ∈ Finset.Icc (min 0 iv) (max 0 iv), _ = _
    rw [Finset.sum_eq_single_of_mem iv (self_mem_Icc_min_max iv) ?_]
    · unfold localizedGradingMulAmbientTerm
      rw [localizedGradingComponentOnAmbient_of_lt C G sX f hRG hgysP hgysc p b iv hiv,
        localizedGradingComponentOnAmbient_of_lt C G sX f hRG hgysP hgysc p _ (iv - iv)
          (by omega),
        localizedBivariantGradingOne_fst_of_eq_zero C G sX f hgysinX p (by omega) (by omega),
        chowCohomologyComposite_identityClass_right_of_eq_zero C G sX hgys hgysc hgysinX iv
          (by omega : (0 : ℤ) = iv - iv),
        bivariantClassDegreeCongr_trans, bivariantClassDegreeCongr_rfl]
    · intro j _ hjne
      unfold localizedGradingMulAmbientTerm
      rw [localizedGradingComponentOnAmbient_localizedBivariantGradingOne_of_ne C G sX f hRG
          hgysP hgysc hgysinX p (iv - j) (by omega), chowCohomologyComposite_zero_right,
        map_zero]
  · obtain ⟨n, hn⟩ := i
    change ∑ j ∈ Finset.Icc (min 0 n) (max 0 n),
        localizedGradingMulLocalizedTerm C G sX f hgys hgysc p p b
          (localizedBivariantGradingOne C G sX f hgysinX p) n j = _
    rw [Finset.sum_eq_single_of_mem n (self_mem_Icc_min_max n) ?_]
    · unfold localizedGradingMulLocalizedTerm
      rw [dite_eq_left hn, dite_eq_right (by omega : ¬ (p : ℤ) ≤ n - n),
        localizedBivariantGradingOne_fst_of_eq_zero C G sX f hgysinX p (by omega) (by omega),
        localizedMulBivariantChow_identityClass_right_of_eq_zero C G sX f hgys hgysc hgysinX n
          (by omega : (0 : ℤ) = n - n),
        bivariantClassDegreeCongr_trans, bivariantClassDegreeCongr_rfl]
    · intro j hj hjne
      rw [Finset.mem_Icc] at hj
      by_cases hjp : (p : ℤ) ≤ j
      · unfold localizedGradingMulLocalizedTerm
        rw [dite_eq_left hjp]
        by_cases hk : (p : ℤ) ≤ n - j
        · rw [dite_eq_left hk, localizedBivariantGradingOne_snd, localizedMulBivariant_zero_right,
            map_zero]
        · rw [dite_eq_right hk,
            localizedBivariantGradingOne_fst_of_ne C G sX f hgysinX p (not_le.1 hk) (by omega),
            localizedMulBivariantChow_zero_right, map_zero]
      · by_cases hk : (p : ℤ) ≤ n - j
        · unfold localizedGradingMulLocalizedTerm
          rw [dite_eq_right hjp, dite_eq_left hk, localizedBivariantGradingOne_snd,
            localizedMulChowBivariant_zero_right, map_zero]
        · exact localizedGradingMulLocalizedTerm_of_lt_of_lt C G sX f hgys hgysc p p b _ n j
            (not_le.1 hjp) (by omega)

end UnitLaw

/-! ### The graded algebra at the Gysin system of the first Chern class rule -/

section OfInvertible

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (f : Z ⟶ X) [IsClosedImmersion f]

/-- The Gysin axiom that the identity class of Stacks 0FBS carries is a theorem at the Gysin
system of the first Chern class rule; this is the proof
`Stacks.Chow.bivariantIdentityClassOfInvertible` is built with. -/
theorem identityCapRule_transportGysinNaturality_ofInvertible {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] :
    IdentityCapRule.TransportGysinNaturality C sY 0 (identityCapRule C sY)
      (gysinSystemOfInvertible C) :=
  IdentityCapRule.transportGysinNaturality C sY 0 (identityCapRule C sY)
    (gysinSystemOfInvertible C) (identityCapRule_gysinNaturality C sY _)
    (GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C)

/-- **Stacks 0FA0.** The multiplication internal to `A⁽ᵖ⁾(Z ⟶ X)` of the remark's graded algebra
as a biadditive map, at the Gysin system of the first Chern class rule, where nothing is
assumed. -/
@[stacks 0FA0 "the multiplication internal to A^(p)(Z ⟶ X) of the remark's graded algebra as a \
biadditive map, which is its distributive law, at the Gysin system of the first Chern class rule \
with nothing assumed"]
def localizedBivariantGradingInternalMulHomOfInvertible (p : ℕ) :
    localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl p →+
      localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl p →+
        localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl p :=
  localizedBivariantGradingInternalMulHom C (gysinSystemOfInvertible C) sX f
    (properPushforwardFlatPullbackBaseChange C)
    (gysinSystemOfInvertible_isNaturalUnderProperPushforward C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C) p

/-- **Stacks 0FA0, the unit of the graded algebra** at the Gysin system of the first Chern class
rule, where nothing is assumed: its degree `0` component is
`Stacks.Chow.bivariantIdentityClassOfInvertible`. -/
@[stacks 0FA0 "the unit of the remark's graded algebra on A^(p)(Z ⟶ X), at the Gysin system of \
the first Chern class rule with nothing assumed"]
def localizedBivariantGradingOneOfInvertible (p : ℕ) :
    localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl p :=
  localizedBivariantGradingOne C (gysinSystemOfInvertible C) sX f
    (identityCapRule_transportGysinNaturality_ofInvertible C sX) p

/-- **Stacks 0FA0, the unit law of the graded algebra on `A⁽ᵖ⁾(Z ⟶ X)` for every `p ≥ 1`** at the
Gysin system of the first Chern class rule, where nothing at all is assumed: the law holds on all
of `A⁽ᵖ⁾(Z ⟶ X)`. -/
@[stacks 0FA0 "the unit law of the remark's graded algebra on A^(p)(Z ⟶ X) for every p ≥ 1, on \
all of A^(p)(Z ⟶ X), at the Gysin system of the first Chern class rule with NOTHING ASSUMED"]
theorem localizedBivariantGradingInternalMul_one_left_ofInvertible (p : ℕ) (hp : 1 ≤ p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl p) :
    localizedBivariantGradingInternalMulHomOfInvertible C sX f p
        (localizedBivariantGradingOneOfInvertible C sX f p) b = b :=
  localizedBivariantGradingInternalMul_one_left C (gysinSystemOfInvertible C) sX f
    (properPushforwardFlatPullbackBaseChange C)
    (gysinSystemOfInvertible_isNaturalUnderProperPushforward C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)
    (identityCapRule_transportGysinNaturality_ofInvertible C sX)
    (identityCapRule_transportGysinNaturality_ofInvertible C (f ≫ sX)) p hp b

/-- **Stacks 0FA0, the unit law of the graded algebra on `A⁽ᵖ⁾(Z ⟶ X)` on the right, for every
`p ≥ 1`** at the Gysin system of the first Chern class rule, where nothing at all is assumed: the
law holds on all of `A⁽ᵖ⁾(Z ⟶ X)`. -/
@[stacks 0FA0 "the unit law of the remark's graded algebra on A^(p)(Z ⟶ X) on the right for every \
p ≥ 1: the class 1 of A^0(X) placed in degree 0 is a right unit for the multiplication internal \
to A^(p)(Z ⟶ X), on all of A^(p)(Z ⟶ X), at the Gysin system of the first Chern class rule with \
NOTHING ASSUMED"]
theorem localizedBivariantGradingInternalMul_one_right_ofInvertible (p : ℕ) (hp : 1 ≤ p)
    (b : localizedBivariantGrading C (gysinSystemOfInvertible C) (f ≫ sX) sX f rfl p) :
    localizedBivariantGradingInternalMulHomOfInvertible C sX f p b
        (localizedBivariantGradingOneOfInvertible C sX f p) = b :=
  localizedBivariantGradingInternalMul_one_right C (gysinSystemOfInvertible C) sX f
    (properPushforwardFlatPullbackBaseChange C)
    (gysinSystemOfInvertible_isNaturalUnderProperPushforward C)
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C)
    (identityCapRule_transportGysinNaturality_ofInvertible C sX) p hp b

end OfInvertible

end Stacks.Chow

end
