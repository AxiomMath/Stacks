module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseProper
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingAlgebra
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductCapCommuting
public import StacksCore.Tactic.StacksAttribute

/-!
# Associativity of the multiplication of Stacks 0FA0, and the projection formula it rests on

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : Z ⟶ X` be a
closed immersion of schemes locally of finite type over `S`. Stacks 0FA0 puts a multiplication on

  `A⁽ᵖ⁾(Z ⟶ X) = ∏_{i ≤ p - 1} Aⁱ(X) × ∏_{i ≥ p} Aⁱ(Z ⟶ X)`,

built from the three pairings of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingMultiplication`, and says of
it — and of the analogous multiplications of Stacks 0FAK and Stacks 0FAX — "We omit the
verification that these multiplications are associative in a suitable sense."

This file **performs that verification**: `Stacks.Chow.localizedBivariantGradingMul_assoc` is
`(a · b) · c = a · (b · c)` for the multiplication of Stacks 0FA0, at every choice of intermediate
and common targets with `p + q + s ≤ r + 2` — the range in which every term of a triple product is
one of the remark's own three pairings — and
`Stacks.Chow.localizedBivariantGradingInternalMul_assoc` is the associativity of the product
internal to `A⁽ᵖ⁾(Z ⟶ X)` that the source's graded algebra asks for, for `p ≤ 1`. Beyond the
associativity of the composition of bivariant classes (Stacks 0B75,
`Stacks.Chow.bivariantComposite_assoc`) that needs three inputs, the product's terms being
composites not of bivariant classes but of the three *mixed* pairings —

* **the restriction of Stacks 0F9Z is multiplicative**, `res(c ∘ c') = res(c) ∘ res(c')`
  (`Stacks.Chow.chowCohomologyRestriction_chowCohomologyComposite`);
* **the projection formula for the pushforward `f_*` of Stacks 0EPK**, in the three forms the
  three pairings of Stacks 0FA0 call for, together with the identity
  `res(c) ∘ c' = c ∘ f_*(c')` that turns the third pairing into the first. Their joint consequence
  `Stacks.Chow.localizedBivariantGradingMul_isAmbientConvolution` is what the degrees below the
  cutoff of a triple product read off;
* **the restriction of Stacks 0F9Z is the restriction of Stacks 0B7F of the pushforward of Stacks
  0EPK** (`Stacks.Chow.chowCohomologyRestriction_localizedGradingPushforward`), equivalently
  `T₂(f_*(c), c') = T₁(c, f_*(c'))`
  (`Stacks.Chow.localizedMulChowBivariant_localizedGradingPushforward_eq`): a localized factor may
  be pushed into `A^*(X)` before it is multiplied on the left. This is what the degrees in which
  an intermediate product of a triple product was read in `A^*(X)` need, and it is the one input
  the earlier implementation notes of this file did not foresee.

It also proves the **three instances of the associativity of Stacks 0B75 for the pairings**, one
per term type of a triple product, and assembles the multiplicative structure of the source's
graded algebra as a bundled `Monoid`, `Stacks.Chow.localizedBivariantGradingMonoid`: with
associativity here and the two unit laws of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingAlgebra`, every field of one
is available.

## Main definitions

* `Stacks.Chow.localizedGradingPushforwardHom` — the pushforward `Aⁱ(Z ⟶ X) ⟶ Aⁱ(X)` of Stacks
  0EPK as a homomorphism of groups, which is what makes it commute with a finite sum.
* `Stacks.Chow.localizedGradingMulAssocTerm`,
  `Stacks.Chow.localizedGradingMulAssocAmbientTerm` — the `(m, j, l)` term of a triple product of
  Stacks 0FA0, in the localized groups and read in `A^*(X)`: the value both groupings give that
  term.

## Main results

### The cap formulas

Each of the operations Stacks 0FA0 is assembled from is a composite of bivariant classes wrapped
in transports, so the first thing needed of each is its cap operation at an **arbitrary** test
scheme, with the transports collected into a single pushforward:

* `Stacks.Chow.chowCohomologyComposite_cap` — for the multiplication of `A^*(X)`;
* `Stacks.Chow.localizedMulBivariantChow_cap` — for the first pairing of Stacks 0FA0;
* `Stacks.Chow.localizedComposeChowCohomology_cap` — for the composition
  `Aⁱ(Z) × Aʲ(Z ⟶ X) ⟶ Aⁱ⁺ʲ(Z ⟶ X)` the second and third pairings are built from;
* `Stacks.Chow.chowCohomologyRestriction_cap_eq` — for the restriction `Aⁱ(X) ⟶ Aⁱ(Z)` of
  Stacks 0B7F;
* `Stacks.Chow.closedImmersionChowCohomologyRestriction_cap_eq` — for the restriction
  `Aⁱ(Z ⟶ X) ⟶ Aⁱ(Z)` of Stacks 0F9Z along a closed immersion. Stacks 0FA1,
  `Stacks.Chow.closedImmersionChowCohomologyRestriction_cap`, is this at the test scheme `𝟙 Z`;
* `Stacks.Chow.localizedGradingPushforward_cap_eq` — for the pushforward of Stacks 0EPK.

### The first input: the restriction of Stacks 0F9Z is multiplicative

* `Stacks.Chow.chowCohomologyRestriction_chowCohomologyComposite` —
  **`res(c ∘ c') = res(c) ∘ res(c')`** for the restriction `res : A^*(Y) ⟶ A^*(Y')` of
  Stacks 0B7F along an arbitrary morphism
  `f : Y' ⟶ Y` of schemes locally of finite type over the base. This is the clause of Stacks 0B7F
  that says `res` is a map of `ℤ`-algebras, for the multiplication
  `Stacks.Chow.chowCohomologyComposite` of `A^*(X)`.

### The second input: the projection formula for the pushforward of Stacks 0EPK

* `Stacks.Chow.localizedMulBivariant_eq_localizedMulBivariantChow` —
  **`res(c) ∘ c' = c ∘ f_*(c')`**: the third pairing of Stacks 0FA0 is the first pairing applied
  to the pushforward of Stacks 0EPK of its second argument. This is the form the degrees at or
  above the cutoff need: it replaces a product of two localized classes, to which the
  associativity of Stacks 0B75 does not directly apply, by a composite of a localized class with
  a class on `X`, to which it does;
* `Stacks.Chow.localizedGradingPushforward_localizedMulBivariantChow`,
  `Stacks.Chow.localizedGradingPushforward_localizedMulChowBivariant`,
  `Stacks.Chow.localizedGradingPushforward_localizedMulBivariant` — **`f_*` of each of the three
  pairings is the product in `A^*(X)` of the pushed-forward factors**: `f_*(c ∘ b) = f_*(c) · b`,
  `f_*(res(b) ∘ c) = b · f_*(c)` and `f_*(res(c) ∘ c') = f_*(c) · f_*(c')`;
* `Stacks.Chow.localizedGradingPushforward_localizedGradingMulLocalizedTerm` — the three of them
  read on the `(i, n - i)` term of a product: `f_*` carries the term of the localized branch to
  the term of the ambient branch;
* `Stacks.Chow.localizedBivariantGradingMul_isAmbientConvolution` — hence **the multiplication of
  Stacks 0FA0 at a target with `p + q ≤ r + 1` is, read in `A^*(X)` by Stacks 0EPK, the convolution
  the source prescribes, in every degree and not only below the cutoff of the target**.
  Equivalently: the product at the target `A⁽ʳ⁾(Z ⟶ X)` refines the product at the target
  `A⁽ᵖ⁺ᑫ⁾(Z ⟶ X)` of Stacks 0FAL and Stacks 0FAY. Those are the targets none of whose degrees
  `n ≥ r` meets a pair of degrees the remark leaves unprescribed.

### The associativity of Stacks 0B75 at the pairings

* `Stacks.Chow.localizedMulBivariantChow_localizedMulBivariantChow_heq` —
  `T₁(T₁(c, b), b') = T₁(c, b · b')`;
* `Stacks.Chow.localizedMulBivariantChow_localizedComposeChowCohomology_heq` and its reading at a
  restricted class `Stacks.Chow.localizedMulBivariantChow_localizedMulChowBivariant_heq` —
  `T₁(T₂(b, c), b') = T₂(b, T₁(c, b'))`;
* `Stacks.Chow.localizedComposeChowCohomology_chowCohomologyComposite_heq` and its reading at
  restricted classes `Stacks.Chow.localizedMulChowBivariant_chowCohomologyComposite_heq` —
  `T₂(b · b', c) = T₂(b, T₂(b', c))`, which is where the multiplicativity of the restriction of
  Stacks 0F9Z is consumed.

Each is a heterogeneous equality for the same reason `Stacks.Chow.bivariantComposite_assoc` is:
the two sides are indexed by `(i + j) + l` and `i + (j + l)`.
`Stacks.Chow.bivariantClassDegreeCongr_eq_of_heq` turns each into the transported form that the
`(i, n - i)` terms of a product are wrapped in.

### The third input: pushing a left factor into `A^*(X)` loses nothing

* `Stacks.Chow.isIso_bivariantPushforwardBaseChange_comp` — the base change `Z ×_X T ⟶ X ×_X T` of
  the closed immersion `f` along a test morphism that factors through `f` is an isomorphism;
* `Stacks.Chow.chowCohomologyRestriction_localizedGradingPushforward` —
  **`res(c) = f^*(f_*(c))`**: the restriction `A^i(Z ⟶ X) ⟶ A^i(Z)` of Stacks 0F9Z is the
  restriction `A^i(X) ⟶ A^i(Z)` of Stacks 0B7F of the pushforward of Stacks 0EPK;
* `Stacks.Chow.localizedMulChowBivariant_localizedGradingPushforward`,
  `Stacks.Chow.localizedMulChowBivariant_localizedGradingPushforward_eq` — hence
  `T₂(f_*(c), c') = T₃(c, c') = T₁(c, f_*(c'))`.

### The uniform form of a term, and the reindexing

* `Stacks.Chow.localizedGradingMulLocalizedTerm_of_le`,
  `Stacks.Chow.localizedGradingMulLocalizedTerm_of_lt` — the branches of a term of the localized
  convolution, collapsed: a term whose first factor is localized is the first pairing applied to
  the second factor read in `A^*(X)`, whatever the second factor's degree, and a term whose first
  factor is ambient and whose second is localized is the second pairing;
* `Stacks.Chow.sum_Icc_diag_flip` — the two ways of summing a double convolution over the triangle
  `0 ≤ m ≤ i ≤ n`.

### Associativity

* `Stacks.Chow.localizedBivariantGradingMul_fst_left`,
  `Stacks.Chow.localizedBivariantGradingMul_fst_right`,
  `Stacks.Chow.localizedBivariantGradingMul_snd_left`,
  `Stacks.Chow.localizedBivariantGradingMul_snd_right` — each grouping of a triple product,
  degreewise, as a double convolution of the terms of the triple product, below and above the
  cutoff of the target;
* `Stacks.Chow.localizedBivariantGradingMul_assoc` — **Stacks 0FA0, associativity of the canonical
  multiplication**, at every choice of intermediate and common targets with `p + q + s ≤ r + 2`;
* `Stacks.Chow.localizedBivariantGradingInternalMul_assoc` — **Stacks 0FA0**, associativity of the
  product internal to `A⁽ᵖ⁾(Z ⟶ X)` of the source's graded algebra, for `p ≤ 1`; what it would come
  to for `p ≥ 2` is
  `Stacks.Chow.localizedBivariantGradingInternalMul_singleLow_eq_zero_of_assoc` of
  `StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingAlgebra`;
* `Stacks.Chow.localizedBivariantGradingMulOfInvertible_assoc`,
  `Stacks.Chow.localizedBivariantGradingInternalMulOfInvertible_assoc` — the same at the Gysin
  system of the first Chern class rule, where nothing at all is assumed.

### The graded algebra as a bundled structure

* `Stacks.Chow.localizedBivariantGradingSemigroup` — **Stacks 0FA0**, the multiplicative structure
  of the source's graded algebra on `A⁽ᵖ⁾(Z ⟶ X)` as a `Semigroup`, on all of `A⁽ᵖ⁾(Z ⟶ X)` for
  `p ≤ 1`, with nothing assumed beyond the Gysin compatibilities the product carries;
* `Stacks.Chow.localizedBivariantGradingMonoid` — **Stacks 0FA0**, that algebra as a `Monoid` at
  `p = 1`: the product, the unit `Stacks.Chow.localizedBivariantGradingOne`, associativity and the
  two unit laws `Stacks.Chow.localizedBivariantGradingInternalMul_one_left` and
  `Stacks.Chow.localizedBivariantGradingInternalMul_one_right`. `p = 1` is where the three laws
  meet: the unit lies in a slot of `A⁽ᵖ⁾(Z ⟶ X)` for `p ≥ 1` and associativity is proved for
  `p ≤ 1`. Its carrier is all of `A⁽¹⁾(Z ⟶ X)`, the group the source asserts the algebra on; that
  rests on the index range `Finset.Icc (min 0 n) (max 0 n)` of the sums the product is formed
  from, which is the reading of the source's `∑_{i + j = n}` set out in the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingMultiplication`.

## Implementation notes

### How associativity is proved

Write `aᵢ` for the degree `i` component of `a ∈ A⁽ᵖ⁾(Z ⟶ X)`, `μᵢ(a)` for that component read in
`Aⁱ(X)` by Stacks 0EPK (`Stacks.Chow.localizedGradingComponentOnAmbient`), and `T₁`, `T₂`, `T₃`
for the three pairings `Stacks.Chow.localizedMulBivariantChow`,
`Stacks.Chow.localizedMulChowBivariant`, `Stacks.Chow.localizedMulBivariant`. With
`res(c) ∘ c' = c ∘ f_*(c')` above, the degree `n ≥ r` component of a product is

  `∑_{m ≥ p} T₁(aₘ, μ_{n-m}(b)) + ∑_{m < p, n - m ≥ q} T₂(aₘ, b_{n-m})`,

and expanding a triple product `(a · b) · c` and `a · (b · c)` in that shape leaves exactly three
identities to check, one per term type, each an instance of the associativity of the composition
of bivariant classes (`Stacks.Chow.bivariantComposite_assoc`, **Stacks 0B75**) read through the
transports the pairings carry. **All three are proved above**; they are the three results of the
section "The associativity of Stacks 0B75 at the pairings".

The degrees below the cutoff need no further input either: the two groupings are both the double
convolution of `μ(a)`, `μ(b)`, `μ(c)` in `A^*(X)` by
`Stacks.Chow.localizedBivariantGradingMul_isAmbientConvolution`, and the multiplication of
`A^*(X)` is associative by `Stacks.Chow.chowCohomologyComposite_assoc`.

Two pieces of bookkeeping then remain, and they are what
`Stacks.Chow.localizedBivariantGradingMul_assoc` is made of: reindexing the double sum
`∑_{i ∈ Icc 0 n} ∑_{m ∈ Icc 0 i}` of one grouping into the `∑_{m ∈ Icc 0 n} ∑_{j ∈ Icc 0 (n - m)}`
of the other (`Stacks.Chow.sum_Icc_diag_flip`), and turning the heterogeneous equalities above
into the transported form the terms of a product are wrapped in,
`Stacks.Chow.bivariantClassDegreeCongr` along `(i + j) + l = i + (j + l)`
(`Stacks.Chow.bivariantClassDegreeCongr_eq_of_heq`) — the same bookkeeping that makes
`Stacks.Chow.bivariantComposite_assoc` and `Stacks.Chow.chowCohomologyComposite_assoc`
heterogeneous equalities.

Two things make that bookkeeping tractable, and they are the shape of the proof.

First, `Stacks.Chow.localizedGradingMulAssocTerm`, the common `(m, j, l)` term of the two
groupings, takes the three degrees as a *separate decomposition* `m + (j + l) = n` of the total
degree and carries the transport into that degree itself, so its **type does not depend on the
decomposition**. The grouping `(a · b) · c` produces the decomposition `(m, i - m, n - i)` and
`a · (b · c)` the decomposition `(m, j, n - m - j)`; reconciling them is then the ordinary equality
`Stacks.Chow.localizedGradingMulAssocTerm_congr` of two terms of one type, provable by `subst`,
rather than a transport.

Second, the expansion does not split into the eight cases "which of the three factors is
localized", because `Stacks.Chow.localizedGradingMulLocalizedTerm_of_le` collapses the branches of
a term to two. The grouping `a · (b · c)` then expands into the triple terms with no input at all
(`Stacks.Chow.localizedBivariantGradingMul_snd_right`): the pairings it applies are already the
ones the triple term names. The whole content is in the other grouping,
`Stacks.Chow.localizedBivariantGradingMul_snd_left`, which splits on whether the degree `i` of the
inner product `a · b` reaches the cutoff `r₁` of its target — five cases, two above
(`Stacks.Chow.localizedGradingMulAssocTerm_eq_of_le`, the two instances of the associativity of
Stacks 0B75 at the first pairing) and three below
(`Stacks.Chow.localizedGradingMulAssocTerm_eq_of_lt`, the third instance followed, in the two
cases where a factor of the inner product was localized, by the third input above). The
arithmetic reconciling the two splits is `omega` in each case: the admissibility of the targets is
exactly what makes each case's side conditions derivable.

The intermediate targets `r₁` and `r₂` are free, and that is not free of charge: a factor `aₘ`
with `m ≥ p` can have `m + j < r₁`, so the inner product's degree `m + j` component is ambient
although the factor it came from was localized. That is the case the third input above is for, and
without it the statement is false as written — reading a localized factor in `A^*(X)` would lose
the refinement. With it, nothing is lost.

### Why the cap formulas are stated with the transports merged

A bivariant class is determined by its cap operations (`Stacks.Chow.BivariantClass.ext`), so every
identity here is proved by computing both sides' cap operations at an arbitrary test scheme. Each
operation of Stacks 0FA0 is a composite of bivariant classes read through one or two transports,
and the cap operation of a composite is itself a pushforward along a pasting isomorphism; left
unmerged, those transports pile up and the comparison of the two sides becomes a comparison of two
chains of pushforwards of different lengths. The cap formulas above therefore each merge the
transports into a *single* pushforward along an explicit morphism, using the functoriality
`Stacks.Chow.chowPushforwardOfIso_comp_apply`, so that comparing two sides is comparing two
morphisms of fibre products — which `CategoryTheory.Limits.pullback.hom_ext` and `simp` settle.

Where one side carries a genuine proper morphism (the base change of `f` that the pushforward of
Stacks 0EPK pushes along) and the other an isomorphism, the comparison is
`Stacks.Chow.chowPushforwardOfIso_comm_properChowPushforward` or, when a further leading
isomorphism is in the way, `Stacks.Chow.chowPushforwardOfIso_properChowPushforward_comp_eq` below.

### The side conditions

Exactly those of the operations involved, and no more: the two cases of Stacks 02TA for the Gysin
system that `Stacks.Chow.bivariantComposite` and the restriction of Stacks 0F9Z carry, and for the
pushforward of Stacks 0EPK additionally Stacks 02RG on Chow groups and Stacks 02TA along a proper
morphism. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedGradingMultiplication`; at the Gysin
system of the first Chern class rule all four are theorems.

## References

* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0FA1](https://stacks.math.columbia.edu/tag/0FA1)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 0FAL](https://stacks.math.columbia.edu/tag/0FAL)
* [Stacks Project, Tag 0FAY](https://stacks.math.columbia.edu/tag/0FAY)
-/

/-!
# The cap formulas of the composites, and the multiplicativity of the restriction of Stacks 0B7F

The first of the four parts of the verification described above: the three-factor comparison
`Stacks.Chow.chowPushforwardOfIso_properChowPushforward_comp_eq` of two factorizations of one
proper pushforward, the cap formula `Stacks.Chow.chowCohomologyComposite_cap` of the
multiplication of `A^*(X)`, the cap formula `Stacks.Chow.chowCohomologyRestriction_cap_eq` of the
restriction of Stacks 0B7F, and the first input, the multiplicativity
`Stacks.Chow.chowCohomologyRestriction_chowCohomologyComposite` of that restriction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Two factorizations of one proper morphism over the base push cycles forward the same way, in
the shape the projection formula of Stacks 0EPK produces them: an isomorphism, a proper morphism
and an isomorphism on one side, an isomorphism and a proper morphism on the other.

This is the three-factor form of what
`Stacks.Chow.chowPushforwardOfIso_comm_properChowPushforward` says for a commuting square: that
lemma compares `u ≫ v` with `v' ≫ u'` for one proper morphism on each side, while the cap
formulas of Stacks 0FA0 produce a leading isomorphism on one side that would otherwise have to be
merged into the square's vertical leg by hand. -/
theorem chowPushforwardOfIso_properChowPushforward_comp_eq (C : ChowSituation.{u})
    {A B D E D' : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (sE : E ⟶ C.S)
    [LocallyOfFiniteType sE] (sD' : D' ⟶ C.S) [LocallyOfFiniteType sD'] (u : A ⟶ B) [IsIso u]
    (v : B ⟶ D) [IsProper v] (w : D ⟶ E) [IsIso w] (u' : A ⟶ D') [IsIso u'] (v' : D' ⟶ E)
    [IsProper v'] (hcomp : (u ≫ v) ≫ w = u' ≫ v') (hu : u ≫ sB = sA) (hv : v ≫ sD = sB)
    (hw : w ≫ sE = sD) (hu' : u' ≫ sD' = sA) (hv' : v' ≫ sE = sD') (k : ℤ)
    (hfacv : ProperPushforwardFactorsThroughRationalEquivalence C sB sD v hv k)
    (hfacv' : ProperPushforwardFactorsThroughRationalEquivalence C sD' sE v' hv' k)
    (α : chowGroup C sA k) :
    chowPushforwardOfIso C sD sE w hw k
        (properChowPushforward C sB sD v hv k hfacv (chowPushforwardOfIso C sA sB u hu k α)) =
      properChowPushforward C sD' sE v' hv' k hfacv'
        (chowPushforwardOfIso C sA sD' u' hu' k α) := by
  have hbuv : (u ≫ v) ≫ sD = sA := by rw [Category.assoc, hv, hu]
  rw [← properChowPushforward_eq_chowPushforwardOfIso C sA sB u hu k
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sA sB u hu k),
    ← properChowPushforward_eq_chowPushforwardOfIso C sD sE w hw k
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sD sE w hw k),
    ← properChowPushforward_eq_chowPushforwardOfIso C sA sD' u' hu' k
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sA sD' u' hu' k),
    ← properChowPushforward_comp_apply C sA sB sD u v (u ≫ v) rfl hu hv hbuv k
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sA sB u hu k) hfacv
      (properPushforwardFactorsThroughRationalEquivalence_comp C sA sB sD u v hu hv k
        (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sA sB u hu k) hfacv)]
  exact properChowPushforward_comp_eq C sA sD sD' sE (u ≫ v) w u' v' hcomp hbuv hw hu' hv' k
    (properPushforwardFactorsThroughRationalEquivalence_comp C sA sB sD u v hu hv k
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sA sB u hu k) hfacv)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sD sE w hw k)
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sA sD' u' hu' k) hfacv' α

section Ambient

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)

omit [LocallyOfFiniteType sX] in
/-- The comparison isomorphism of the base changes of `𝟙 X ≫ 𝟙 X` and of `𝟙 X` along a test
scheme is a morphism over the base. -/
theorem congrHom_compId_base {T : Scheme.{u}} (t : T ⟶ X) :
    (pullback.congrHom (Category.comp_id (𝟙 X)) (rfl : t = t)).hom ≫
        (pullback.fst (𝟙 X) t ≫ sX) = pullback.fst (𝟙 X ≫ 𝟙 X) t ≫ sX := by
  rw [← Category.assoc]
  simp

omit [LocallyOfFiniteType sX] in
/-- The identification `X ×_X (X ×_X T) ≅ X ×_X T` that the multiplication of `A^*(X)` pushes a
cap product forward along is a morphism over the base. -/
theorem ambientCompositeIso_base {T : Scheme.{u}} (t : T ⟶ X) :
    ((pullbackRightPullbackFstIso (𝟙 X) t (𝟙 X)).hom ≫
          (pullback.congrHom (Category.comp_id (𝟙 X)) (rfl : t = t)).hom) ≫
        (pullback.fst (𝟙 X) t ≫ sX) =
      pullback.fst (𝟙 X) (pullback.fst (𝟙 X) t) ≫ sX := by
  rw [Category.assoc, congrHom_compId_base C sX t]
  exact pullbackRightPullbackFstIso_hom_comp_fst_comp sX (𝟙 X) (𝟙 X) t

/-- The cap operation of the multiplication of `A^*(X)`: cap with the second factor, cap with the
first, and push forward along the canonical identification of `X ×_X (X ×_X T)` with `X ×_X T`. -/
theorem chowCohomologyComposite_cap (i j : ℤ) (a : chowCohomologyComponent C G sX i)
    (b : chowCohomologyComponent C G sX j) {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    (chowCohomologyComposite C G sX hgys hgysc i j a b).cap t k α =
      chowGroupDegreeEquiv C (pullback.fst (𝟙 X) t ≫ sX) (by ring : k - j - i = k - (i + j))
        (chowPushforwardOfIso C (pullback.fst (𝟙 X) (pullback.fst (𝟙 X) t) ≫ sX)
          (pullback.fst (𝟙 X) t ≫ sX)
          ((pullbackRightPullbackFstIso (𝟙 X) t (𝟙 X)).hom ≫
            (pullback.congrHom (Category.comp_id (𝟙 X)) rfl).hom)
          (ambientCompositeIso_base C sX t) (k - j - i)
          (a.cap (pullback.fst (𝟙 X) t) (k - j) (b.cap t k α))) := by
  unfold chowCohomologyComposite
  rw [← bivariantClassCongr_cap C G sX sX (Category.comp_id (𝟙 X))
      (comp_comp_structureMorphism_eq (Category.id_comp sX) (Category.id_comp sX))
      (Category.id_comp sX) (i + j) _ t k α (congrHom_compId_base C sX t),
    bivariantComposite_cap, bivariantCompositeCap_apply,
    properChowPushforward_eq_chowPushforwardOfIso C
      (pullback.fst (𝟙 X) (pullback.fst (𝟙 X) t) ≫ sX) (pullback.fst (𝟙 X ≫ 𝟙 X) t ≫ sX)
      (pullbackRightPullbackFstIso (𝟙 X) t (𝟙 X)).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sX (𝟙 X) (𝟙 X) t) (k - j - i) _,
    ← chowGroupDegreeEquiv_chowPushforwardOfIso C
      (pullback.fst (𝟙 X ≫ 𝟙 X) t ≫ sX) (pullback.fst (𝟙 X) t ≫ sX)
      (pullback.congrHom (Category.comp_id (𝟙 X)) rfl).hom (congrHom_compId_base C sX t)
      (by ring : k - j - i = k - (i + j)),
    chowPushforwardOfIso_comp_apply C (pullback.fst (𝟙 X) (pullback.fst (𝟙 X) t) ≫ sX)
      (pullback.fst (𝟙 X ≫ 𝟙 X) t ≫ sX) (pullback.fst (𝟙 X) t ≫ sX)
      (pullbackRightPullbackFstIso (𝟙 X) t (𝟙 X)).hom
      (pullback.congrHom (Category.comp_id (𝟙 X)) rfl).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sX (𝟙 X) (𝟙 X) t)
      (congrHom_compId_base C sX t) (k - j - i)]

end Ambient

section Restriction

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Y Y' : Scheme.{u}} (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] (f : Y' ⟶ Y) [LocallyOfFiniteType f]
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType f] in
/-- The identification `Y ×_Y T ≅ Y' ×_{Y'} T` of the two base changes of an identity along a test
scheme `g : T ⟶ Y'` and along `g ≫ f` is a morphism over the base. -/
theorem restrictionTestIso_base {T : Scheme.{u}} (g : T ⟶ Y') :
    ((identityBaseChangeIso (g ≫ f)).hom ≫ (identityBaseChangeIso g).inv) ≫
        (pullback.fst (𝟙 Y') g ≫ (f ≫ sY)) = pullback.fst (𝟙 Y) (g ≫ f) ≫ sY := by
  rw [Category.assoc, identityBaseChangeIso_hom_comp C (f ≫ sY) g, ← Category.assoc]
  exact identityBaseChangeIso_hom_comp_base C sY (g ≫ f)

/-- **The cap operation of the restriction `A^p(Y) ⟶ A^p(Y')` of Stacks 0B7F**, at an arbitrary
test scheme and with the transports of its construction merged into a single pushforward: the cap
operation of the class itself at the test morphism composed with `f`. This is the cap formula
`Stacks.Chow.chowCohomologyRestriction_cap` of Stacks 0B7F with the isomorphism on the left-hand
side cancelled. -/
theorem chowCohomologyRestriction_cap_eq (p : ℤ) (c : chowCohomologyComponent C G sY p)
    {T : Scheme.{u}} (g : T ⟶ Y') [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ (f ≫ sY)) k) :
    (chowCohomologyRestriction C G sY f p hgys c).cap g k α =
      chowPushforwardOfIso C (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY)
        (pullback.fst (𝟙 Y') g ≫ (f ≫ sY))
        ((identityBaseChangeIso (g ≫ f)).hom ≫ (identityBaseChangeIso g).inv)
        (restrictionTestIso_base C sY f g) (k - p)
        (c.cap (g ≫ f) k (chowGroupCongr C (Category.assoc g f sY).symm k α)) := by
  have hinv : (identityBaseChangeIso g).inv ≫ (pullback.fst (𝟙 Y') g ≫ (f ≫ sY)) =
      g ≫ (f ≫ sY) := identityBaseChangeIso_hom_comp C (f ≫ sY) g
  have h2 := congrArg (chowPushforwardOfIso C (g ≫ (f ≫ sY))
    (pullback.fst (𝟙 Y') g ≫ (f ≫ sY)) (identityBaseChangeIso g).inv hinv (k - p))
    (chowCohomologyRestriction_cap C G sY f p hgys c g k α)
  rw [chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C (pullback.fst (𝟙 Y') g ≫ (f ≫ sY))
      (pullback.fst (𝟙 Y') g ≫ (f ≫ sY)) _ (𝟙 _) (Iso.hom_inv_id _) _ (Category.id_comp _)
      (k - p),
    chowPushforwardOfIso_id] at h2
  exact h2

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType f] in
/-- The identification `Y ×_Y T ≅ Y' ×_{Y'} T` carries the test morphism of the restriction to the
test morphism of the class: it exhibits `Y ×_Y T ⟶ Y` as `(Y' ×_{Y'} T ⟶ Y') ≫ f` read through
the identification. -/
theorem restrictionTestIso_comp {T : Scheme.{u}} (g : T ⟶ Y') :
    ((identityBaseChangeIso (g ≫ f)).hom ≫ (identityBaseChangeIso g).inv) ≫
        (pullback.fst (𝟙 Y') g ≫ f) = pullback.fst (𝟙 Y) (g ≫ f) := by
  simp only [Category.assoc, fst_eq_identityBaseChangeIso_hom g, Iso.inv_hom_id_assoc]
  exact (fst_eq_identityBaseChangeIso_hom (g ≫ f)).symm

/-- **The restriction map of Stacks 0B7F is multiplicative:** `res(c ∘ c') = res(c) ∘ res(c')` for
the multiplication `Stacks.Chow.chowCohomologyComposite` of `A^*`, and so for the restriction
`Aⁱ(X) ⟶ Aⁱ(Z)` of Stacks 0F9Z that the second pairing of Stacks 0FA0 is built from.

This is the clause of Stacks 0B7F asserting that `res : A^*(Y) ⟶ A^*(Y')` is a map of
`ℤ`-algebras, for the multiplication of `A^*` that this repository has. It is also the first of
the two inputs an associativity proof for the multiplication of Stacks 0FA0 needs: the degree `n`
terms `res(res(c) ∘ c') ∘ c''` and `res(c) ∘ (res(c') ∘ c'')` of the two groupings cannot be
compared without it, however associative the composition of Stacks 0B75 is.

Both sides cap, on a test scheme `g : T ⟶ Y'`, by capping with `c'` and then with `c`, both at
test morphisms over `Y` obtained from `g ≫ f`; the two differ by an isomorphism of test schemes,
which the proper-pushforward axiom of Stacks 0B76 for `c` absorbs. -/
@[stacks 0B7F "the multiplicativity of the canonical map: res(c ∘ c') = res(c) ∘ res(c') for \
the multiplication of A^* that is composition of bivariant classes, which is the clause that the \
map of graded groups is a map of algebras"]
theorem chowCohomologyRestriction_chowCohomologyComposite (i j : ℤ)
    (c : chowCohomologyComponent C G sY i) (c' : chowCohomologyComponent C G sY j) :
    chowCohomologyRestriction C G sY f (i + j) hgys
        (chowCohomologyComposite C G sY hgys hgysc i j c c') =
      chowCohomologyComposite C G (f ≫ sY) hgys hgysc i j
        (chowCohomologyRestriction C G sY f i hgys c)
        (chowCohomologyRestriction C G sY f j hgys c') := by
  apply BivariantClass.ext
  intro T g hg k α
  rw [chowCohomologyRestriction_cap_eq C G sY f hgys (i + j) _ g k α,
    chowCohomologyComposite_cap C G sY hgys hgysc i j c c' (g ≫ f) k _,
    chowCohomologyComposite_cap C G (f ≫ sY) hgys hgysc i j _ _ g k α,
    chowCohomologyRestriction_cap_eq C G sY f hgys j c' g k α,
    chowCohomologyRestriction_cap_eq C G sY f hgys i c (pullback.fst (𝟙 Y') g) (k - j) _,
    chowGroupCongr_chowPushforwardOfIso_target C (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY)
      (Category.assoc (pullback.fst (𝟙 Y') g) f sY).symm
      ((identityBaseChangeIso (g ≫ f)).hom ≫ (identityBaseChangeIso g).inv)
      (restrictionTestIso_base C sY f g)
      (restrictionTestIso_base C sY f g) (k - j),
    BivariantClass.cap_chowPushforwardOfIso c (pullback.fst (𝟙 Y') g ≫ f)
      ((identityBaseChangeIso (g ≫ f)).hom ≫ (identityBaseChangeIso g).inv)
      (pullback.fst (𝟙 Y) (g ≫ f)) (restrictionTestIso_comp f g)
      (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY) rfl (k - j)
      (restrictionTestIso_base C sY f g) _ _ rfl,
    ← chowGroupDegreeEquiv_chowPushforwardOfIso C (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY)
      (pullback.fst (𝟙 Y') g ≫ (f ≫ sY))
      ((identityBaseChangeIso (g ≫ f)).hom ≫ (identityBaseChangeIso g).inv)
      (restrictionTestIso_base C sY f g) (by ring : k - j - i = k - (i + j)),
    chowPushforwardOfIso_comp_apply, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_comp_apply]
  refine congrArg _ (chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ (k - j - i) _)
  refine pullback.hom_ext ?_ ?_ <;>
    simp [fst_eq_identityBaseChangeIso_hom]

end Restriction

end Stacks.Chow

end
