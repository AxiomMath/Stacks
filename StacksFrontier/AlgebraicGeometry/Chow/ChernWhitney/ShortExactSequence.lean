module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedConvolution
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The Whitney sum formula, componentwise on Chow groups

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let

  `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0`

be a short exact sequence of finite locally free `𝒪_X`-modules, of ranks `r₁`, `r₁ + r₂` and
`r₂`. [Stacks, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI) is the Whitney relation
`c(ℰ) = c(ℰ₁) c(ℰ₂)` between the total Chern classes. This file states and proves that relation
**componentwise, as an identity between cap products on Chow groups**: for every `k`, every
class `α ∈ A_k(X)` and every `m`,

  `c_m(ℰ) ∩ α = ∑_{i + j = m} c_i(ℰ₁) ∩ (c_j(ℰ₂) ∩ α)`   in `A_{k-m}(X)`.

## Why componentwise, and not as a product of total classes

The product form cannot be written in this repository, for the reasons recorded at length on
Stacks 02UH in `StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.CapProductRelation`: there is no
ring structure on bivariant classes here and no total Chern class, only the predicate
`Stacks.Chow.IsTotalChernClass`. Expanding the product and comparing coefficients turns the
relation into the displayed identity, which needs no multiplication — only the cap products on
Chow groups, which compose because each is defined on a Chow group and lands in one. That is
also the reduction the source's own proof performs, so nothing is lost.

The right-hand side is the *convolution* of the two Chern cap families, in the sense of
`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedConvolution`; that file proves the
associativity which the induction below consumes.

## The proof, and what it carries

The source proves the relation by induction on `r₁`. The case `r₁ = 1` is Stacks 02UH. For
`r₁ ≥ 2` let `(π : P ⟶ X, 𝒪_P(1))` be the projective space bundle of `ℰ₁`; then `π^*` is
injective on Chow groups by Stacks 02TX, the pullback `π^*ℰ₁` has an invertible quotient
`ℒ = 𝒪_P(1)` with kernel `ℱ` of rank `r₁ - 1`, and with `𝒬 = π^*ℰ/ℱ` the three sequences

  `0 ⟶ ℱ ⟶ π^*ℰ₁ ⟶ ℒ ⟶ 0`,  `0 ⟶ ℱ ⟶ π^*ℰ ⟶ 𝒬 ⟶ 0`,  `0 ⟶ ℒ ⟶ 𝒬 ⟶ π^*ℰ₂ ⟶ 0`

are exact. The induction hypothesis at `r₁ - 1` applied to the first two, and the rank-one case
applied to the third, give `c(π^*ℰ) = c(ℱ) c(𝒬) = c(ℱ) c(ℒ) c(π^*ℰ₂) = c(π^*ℰ₁) c(π^*ℰ₂)`;
the middle equality is the associativity of the convolution. Since `π^*` is injective and
commutes with the cap products by Stacks 02U8, the relation descends to `X`.

Three things are therefore inputs, and are named in the `@[stacks 02UI]` clause:

* `cap`, a `Stacks.Chow.HigherChernCapRule` in every rank. This is `chernClassCapOnChow` of
  Stacks 0B7G, built there from the cap product on cycles of Stacks 02U5 and its invariance
  under rational equivalence, Stacks 02U7; neither is in this repository, so, exactly as in
  `StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic`, the rule is a parameter. The
  relation has to be stated on Chow groups rather than on cycles because its right-hand side
  composes two cap products, and the cap product of Stacks 02U5 is defined on cycles but lands
  in a Chow group.
* `hbase`, the relation when `ℰ₁` has rank at most one. Rank one is Stacks 02UH; that tag is
  proved in this repository, but in the vocabulary of the cap product on *cycles* and under its
  own carried hypotheses, so it does not supply this statement. Rank zero is degenerate and
  needs the normalisation `c_0 = 1` of Stacks 02U0 together with invariance of the cap products
  under an isomorphism of modules, neither of which holds of an arbitrary cap rule.
* `hsplit`, the splitting datum `Stacks.Chow.ChernSplitting` — the projective space bundle with
  its three sequences, the injectivity of Stacks 02TX and the flat pullback compatibility of
  Stacks 02U8. Stacks 02TX is not in this repository (it is carried as a hypothesis wherever it
  is needed, as `Stacks.Chow.ProjectiveBundleRelationInjective` does), and neither is the
  construction of the bundle's twist, Stacks 01O4.

What is *not* carried is the argument: the associativity of the convolution, the descent along
an injective intertwiner and the induction itself are proved here and in
`StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedConvolution`.

## Implementation notes

### The ranks are instance hypotheses

As for Stacks 02UH, the three modules carry their ranks as hypotheses; in particular the middle
term is *assumed* finite locally free of rank `r₁ + r₂` rather than shown to be. That value is
forced: `AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact` proves that a middle term of a
short exact sequence of finite locally free modules of constant ranks has the sum of the outer
ranks. What that lemma does not do — produce the instance from the two outer ones — is not in
this repository.

### The projective bundle is a parameter

Nothing below asserts that `P` is the projective space bundle of `ℰ₁`, nor that `ℒ` is its
twist: those facts enter only through the fields of `Stacks.Chow.ChernSplitting`, which are
exactly the properties the source uses. The statements are therefore more general than the
source's, holding for any flat morphism with an injective pullback compatible with the cap
products and any such filtration of the pulled-back sequence. This is the same generalization
that `StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation` records for
its own bundle data.

## Main definitions

* `Stacks.Chow.chernCapFamilyOnChow` — the Chern class cap products of a finite locally free
  module on Chow groups, indexed by a natural number and extended by zero above the rank: a
  `Stacks.Chow.GradedCapFamily`.
* `Stacks.Chow.WhitneyChernRelation` — the Whitney relation for every short exact sequence whose
  sub-module has a fixed rank, as an identity of graded cap families.
* `Stacks.Chow.ChernSplitting` — the splitting datum of the source's induction.
* `Stacks.Chow.HasChernSplitting` — that such a datum exists for every sequence whose
  sub-module has rank at least two.

## Main results

* `Stacks.Chow.whitneyChernRelation_of_splitting` — the inductive step.
* `Stacks.Chow.whitneyChernRelation_of_hasChernSplitting` — the induction on `r₁`.
* `Stacks.Chow.chernCapOnChow_eq_sum_of_shortExact` — **Stacks 02UI**, componentwise.

## References

* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 02UH](https://stacks.math.columbia.edu/tag/02UH)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U7](https://stacks.math.columbia.edu/tag/02U7)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset

universe u

namespace Stacks.Chow

/-! ### The Chern cap products as a graded cap family -/

/-- **Stacks 0B7G, extended by zero.** Intersection with the `i`-th Chern class of a finite
locally free module of rank `s`, as a homomorphism `A_k(T) ⟶ A_{k-i}(T)` indexed by a natural
number `i`: the cap product of the given rule for `i ≤ s` and zero above the rank, which is the
standard convention and the one the Whitney relation needs in order to be read at every index at
once.

Indexing by a natural number rather than by `Fin (s + 1)` is what lets the relation be stated
without coercions between the three ranks `r₁`, `r₂` and `r₁ + r₂`. -/
def chernCapFamilyOnChow (C : ChowSituation.{u}) (cap : ∀ r : ℕ, HigherChernCapRule C r)
    {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (M : T.Modules) (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M s] :
    GradedCapFamily (chowGroup C q) :=
  fun k i => if h : i ≤ s then cap s q M k ⟨i, Nat.lt_succ_of_le h⟩ else 0

/-- Up to the rank, the extended family is the given cap product. -/
theorem chernCapFamilyOnChow_of_le (C : ChowSituation.{u}) (cap : ∀ r : ℕ, HigherChernCapRule C r)
    {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (M : T.Modules) (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M s] (k : ℤ) {i : ℕ}
    (h : i ≤ s) :
    chernCapFamilyOnChow C cap q M s k i = cap s q M k ⟨i, Nat.lt_succ_of_le h⟩ :=
  dite_eq_left h

/-- Above the rank the extended family is zero. -/
theorem chernCapFamilyOnChow_of_gt (C : ChowSituation.{u}) (cap : ∀ r : ℕ, HigherChernCapRule C r)
    {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (M : T.Modules) (s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M s] (k : ℤ) {i : ℕ}
    (h : ¬ i ≤ s) :
    chernCapFamilyOnChow C cap q M s k i = 0 :=
  dite_eq_right h

/-! ### The Whitney relation -/

/-- **Stacks 02UI at a fixed rank of the sub-module, componentwise.** That for every scheme `T`
locally of finite type over the base and every short exact sequence of finite locally free
modules on it whose sub-module has rank `r₁` and whose quotient has rank `r₂`, the Chern cap
family of the middle term is the convolution of those of the outer terms:

  `c_m(ℰ) ∩ α = ∑_{i + j = m} c_i(ℰ₁) ∩ (c_j(ℰ₂) ∩ α)`.

Stated as an identity of graded cap families rather than pointwise, because that is the form
the induction below substitutes into. -/
def WhitneyChernRelation (C : ChowSituation.{u}) (cap : ∀ r : ℕ, HigherChernCapRule C r)
    (r₁ : ℕ) : Prop :=
  ∀ {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (S : ShortComplex T.Modules),
    S.ShortExact → ∀ (r₂ : ℕ)
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (r₁ + r₂)]
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₂],
      chernCapFamilyOnChow C cap q S.X₂ (r₁ + r₂) =
        convolve (chernCapFamilyOnChow C cap q S.X₁ r₁) (chernCapFamilyOnChow C cap q S.X₃ r₂)

/-! ### The splitting datum of the induction -/

/-- **The datum the source's induction step is run on.** For a short exact sequence
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` whose sub-module has rank `n + 2`: a scheme `P` over `T`, flat of some
relative dimension, whose flat pullback on Chow groups is injective and carries the Chern cap
products of `ℰ₁`, `ℰ` and `ℰ₂` to those of three modules `pullSub`, `pullMid`, `pullQuot` on
`P`, together with a module `F` of rank `n + 1`, an invertible module `L` and a module `Q`, and
three short exact sequences

  `0 ⟶ F ⟶ pullSub ⟶ L ⟶ 0`, `0 ⟶ F ⟶ pullMid ⟶ Q ⟶ 0`, `0 ⟶ L ⟶ Q ⟶ pullQuot ⟶ 0`.

For `ℰ₁` of rank `n + 2` the source takes `P` the projective space bundle of `ℰ₁`, the three
modules on `P` the pullbacks of `ℰ₁`, `ℰ` and `ℰ₂`, `L` the twist `𝒪_P(1)`, `F` its kernel in
`π^*ℰ₁` and `Q` the quotient `π^*ℰ/F`; injectivity of the pullback is Stacks 02TX and its
compatibility with the cap products is Stacks 02U8.

Nothing below uses more about `P` than the fields recorded here, so the induction step is proved
for any such datum. -/
structure ChernSplitting (C : ChowSituation.{u}) (cap : ∀ r : ℕ, HigherChernCapRule C r)
    {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (S : ShortComplex T.Modules)
    (n r₂ : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ (n + 1 + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (n + 1 + 1 + r₂)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₂] where
  /-- The total space of the bundle. -/
  P : Scheme.{u}
  /-- Its structure morphism to the base of the situation. -/
  sP : P ⟶ C.S
  [lftP : LocallyOfFiniteType sP]
  /-- The projection of the bundle. -/
  proj : P ⟶ T
  [lftProj : LocallyOfFiniteType proj]
  [flatProj : Flat proj]
  /-- The projection lies over the base. -/
  base_comp : proj ≫ q = sP
  /-- The relative dimension of the projection. -/
  relDim : ℕ
  /-- The projection has that relative dimension. -/
  has_relDim : AlgebraicGeometry.RelativeDimension proj relDim
  /-- **Stacks 02S1 for the projection**: its flat pullback factors through rational
  equivalence, which is what makes the flat pullback of Stacks 0FVK exist on Chow groups. -/
  flat_factors : ∀ k : ℤ,
    FlatPullbackFactorsThroughRationalEquivalence C sP q proj base_comp relDim has_relDim k
  /-- **Stacks 02TX**: the flat pullback along the projection is injective. -/
  pullback_injective : ∀ k : ℤ,
    Function.Injective
      (flatPullbackChow C sP q proj base_comp relDim has_relDim k (flat_factors k))
  /-- The kernel `ℱ` of the invertible quotient of `π^*ℰ₁`. -/
  F : P.Modules
  /-- The invertible quotient `ℒ = 𝒪_P(1)` of `π^*ℰ₁`. -/
  L : P.Modules
  /-- The pullback `π^*ℰ₁` of the sub-module. -/
  pullSub : P.Modules
  /-- The pullback `π^*ℰ` of the middle term. -/
  pullMid : P.Modules
  /-- The quotient `𝒬 = π^*ℰ/ℱ`. -/
  Q : P.Modules
  /-- The pullback `π^*ℰ₂` of the quotient. -/
  pullQuot : P.Modules
  [rankF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (n + 1)]
  [rankL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
  [rankPullSub :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} pullSub (n + 1 + 1)]
  [rankPullMid :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} pullMid
      (n + 1 + (1 + r₂))]
  [rankQ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q (1 + r₂)]
  [rankPullQuot : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} pullQuot r₂]
  /-- The inclusion `ℱ ⟶ π^*ℰ₁`. -/
  fSub : F ⟶ pullSub
  /-- The projection `π^*ℰ₁ ⟶ ℒ`. -/
  gSub : pullSub ⟶ L
  /-- The two maps compose to zero. -/
  wSub : fSub ≫ gSub = 0
  /-- `0 ⟶ ℱ ⟶ π^*ℰ₁ ⟶ ℒ ⟶ 0` is exact. -/
  exactSub : (ShortComplex.mk fSub gSub wSub).ShortExact
  /-- The inclusion `ℱ ⟶ π^*ℰ`. -/
  fMid : F ⟶ pullMid
  /-- The projection `π^*ℰ ⟶ 𝒬`. -/
  gMid : pullMid ⟶ Q
  /-- The two maps compose to zero. -/
  wMid : fMid ≫ gMid = 0
  /-- `0 ⟶ ℱ ⟶ π^*ℰ ⟶ 𝒬 ⟶ 0` is exact. -/
  exactMid : (ShortComplex.mk fMid gMid wMid).ShortExact
  /-- The inclusion `ℒ ⟶ 𝒬`. -/
  fQuot : L ⟶ Q
  /-- The projection `𝒬 ⟶ π^*ℰ₂`. -/
  gQuot : Q ⟶ pullQuot
  /-- The two maps compose to zero. -/
  wQuot : fQuot ≫ gQuot = 0
  /-- `0 ⟶ ℒ ⟶ 𝒬 ⟶ π^*ℰ₂ ⟶ 0` is exact. -/
  exactQuot : (ShortComplex.mk fQuot gQuot wQuot).ShortExact
  /-- **Stacks 02U8 for the sub-module**: the pullback carries `c_i(ℰ₁) ∩ -` to
  `c_i(π^*ℰ₁) ∩ -`. -/
  compatSub :
    Intertwines
      (fun k => flatPullbackChow C sP q proj base_comp relDim has_relDim k (flat_factors k))
      (chernCapFamilyOnChow C cap q S.X₁ (n + 1 + 1))
      (chernCapFamilyOnChow C cap sP pullSub (n + 1 + 1))
  /-- **Stacks 02U8 for the middle term**. -/
  compatMid :
    Intertwines
      (fun k => flatPullbackChow C sP q proj base_comp relDim has_relDim k (flat_factors k))
      (chernCapFamilyOnChow C cap q S.X₂ (n + 1 + 1 + r₂))
      (chernCapFamilyOnChow C cap sP pullMid (n + 1 + (1 + r₂)))
  /-- **Stacks 02U8 for the quotient**. -/
  compatQuot :
    Intertwines
      (fun k => flatPullbackChow C sP q proj base_comp relDim has_relDim k (flat_factors k))
      (chernCapFamilyOnChow C cap q S.X₃ r₂)
      (chernCapFamilyOnChow C cap sP pullQuot r₂)

/-- That a splitting datum exists for every short exact sequence whose sub-module has rank at
least two. For the source this is the existence of the projective space bundle of `ℰ₁` together
with Stacks 02TX and Stacks 02U8. -/
def HasChernSplitting (C : ChowSituation.{u}) (cap : ∀ r : ℕ, HigherChernCapRule C r) : Prop :=
  ∀ {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (S : ShortComplex T.Modules),
    S.ShortExact → ∀ (n r₂ : ℕ)
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ (n + 1 + 1)]
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (n + 1 + 1 + r₂)]
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₂],
      Nonempty (ChernSplitting C cap q S n r₂)

/-! ### The induction -/

/-- **The inductive step of Stacks 02UI.** Granted the Whitney relation when the sub-module has
rank one and when it has rank `n + 1`, a splitting datum for a sequence whose sub-module has
rank `n + 2` produces the relation for that sequence.

On the bundle the relation reads `c(π^*ℰ) = c(ℱ) c(𝒬)` and `c(𝒬) = c(ℒ) c(π^*ℰ₂)` and
`c(π^*ℰ₁) = c(ℱ) c(ℒ)`, so the associativity of the convolution gives
`c(π^*ℰ) = c(π^*ℰ₁) c(π^*ℰ₂)`; the pullback is injective and intertwines the three families with
the three downstairs, so the relation descends. -/
theorem whitneyChernRelation_of_splitting (C : ChowSituation.{u})
    (cap : ∀ r : ℕ, HigherChernCapRule C r) {n r₂ : ℕ} (hone : WhitneyChernRelation C cap 1)
    (hprev : WhitneyChernRelation C cap (n + 1)) {T : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (S : ShortComplex T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ (n + 1 + 1)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (n + 1 + 1 + r₂)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₂]
    (D : ChernSplitting C cap q S n r₂) :
    chernCapFamilyOnChow C cap q S.X₂ (n + 1 + 1 + r₂) =
      convolve (chernCapFamilyOnChow C cap q S.X₁ (n + 1 + 1))
        (chernCapFamilyOnChow C cap q S.X₃ r₂) := by
  have := D.lftP
  have := D.lftProj
  have := D.flatProj
  have := D.rankF
  have := D.rankL
  have := D.rankPullSub
  have := D.rankPullMid
  have := D.rankQ
  have := D.rankPullQuot
  have hMid : chernCapFamilyOnChow C cap D.sP D.pullMid (n + 1 + (1 + r₂)) =
      convolve (chernCapFamilyOnChow C cap D.sP D.F (n + 1))
        (chernCapFamilyOnChow C cap D.sP D.Q (1 + r₂)) :=
    hprev D.sP (ShortComplex.mk D.fMid D.gMid D.wMid) D.exactMid (1 + r₂)
  have hQuot : chernCapFamilyOnChow C cap D.sP D.Q (1 + r₂) =
      convolve (chernCapFamilyOnChow C cap D.sP D.L 1)
        (chernCapFamilyOnChow C cap D.sP D.pullQuot r₂) :=
    hone D.sP (ShortComplex.mk D.fQuot D.gQuot D.wQuot) D.exactQuot r₂
  have hSub : chernCapFamilyOnChow C cap D.sP D.pullSub (n + 1 + 1) =
      convolve (chernCapFamilyOnChow C cap D.sP D.F (n + 1))
        (chernCapFamilyOnChow C cap D.sP D.L 1) :=
    hprev D.sP (ShortComplex.mk D.fSub D.gSub D.wSub) D.exactSub 1
  have key : chernCapFamilyOnChow C cap D.sP D.pullMid (n + 1 + (1 + r₂)) =
      convolve (chernCapFamilyOnChow C cap D.sP D.pullSub (n + 1 + 1))
        (chernCapFamilyOnChow C cap D.sP D.pullQuot r₂) := by
    rw [hMid, hQuot, convolve_assoc, ← hSub]
  exact eq_convolve_of_intertwines _ D.pullback_injective D.compatSub D.compatQuot D.compatMid key

/-- **Stacks 02UI, by induction on the rank of the sub-module.** Granted the relation when the
sub-module has rank at most one and a splitting datum for every sequence whose sub-module has
rank at least two, the Whitney relation holds at every rank. -/
theorem whitneyChernRelation_of_hasChernSplitting (C : ChowSituation.{u})
    (cap : ∀ r : ℕ, HigherChernCapRule C r)
    (hbase : ∀ r₁ ≤ 1, WhitneyChernRelation C cap r₁) (hsplit : HasChernSplitting C cap)
    (r₁ : ℕ) : WhitneyChernRelation C cap r₁ := by
  induction r₁ using Nat.strong_induction_on with
  | _ r₁ ih =>
    match r₁, ih with
    | 0, _ | 1, _ =>
      intro T q _ S hS r₂ _ _ _
      exact hbase _ (by omega) q S hS r₂
    | (n + 1 + 1), ih =>
      intro T q _ S hS r₂ _ _ _
      exact whitneyChernRelation_of_splitting C cap (hbase 1 (by omega))
        (ih (n + 1) (by omega)) q S (hsplit q S hS n r₂).some

/-! ### Stacks 02UI -/

/-- **Stacks 02UI, componentwise on cap products.** For a short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of finite locally free modules of ranks `r₁`, `r₁ + r₂` and `r₂`,
for every class `α ∈ A_k(X)` and every `m`,

  `c_m(S.X₂) ∩ α = ∑_{i + j = m} c_i(S.X₁) ∩ (c_j(S.X₃) ∩ α)`   in `A_{k-m}(X)`,

the sum being taken over `j ≤ m` with `i = m - j`, and the `i`-th Chern class read as zero above
the rank. Assembling these over `m` and expanding the product, this is the relation
`c(S.X₂) = c(S.X₁) · c(S.X₃)` of the source; see the module documentation for why the product
form cannot be written here.

The hypotheses `hbase` and `hsplit` are the inputs: the relation for a sub-module of rank at
most one, whose rank-one case is Stacks 02UH, and the splitting datum of the source's induction,
which carries the projective space bundle of `S.X₁` together with Stacks 02TX and Stacks 02U8. -/
@[stacks 02UI "CORRECTION OF FORM: the source states c(E) = c(E₁)c(E₂) in the bivariant ring \
  A^*(X). That product is not stated here, and cannot be: this development has no ring \
  structure on bivariant classes and no total Chern class, for the reasons recorded on Stacks \
  02UH in StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.CapProductRelation -- Chern classes \
  are built as operations on X's own cycles rather than as bivariant classes over all Y -> X, \
  and the source's formulation needs proper pushforward on Chow groups, Stacks 0GU8, which this \
  repository does not have. What is proved instead is the componentwise identity \
  c_m(E) cap alpha = sum over i + j = m of c_i(E₁) cap (c_j(E₂) cap alpha), at arbitrary ranks \
  r₁ of E₁ and r₂ of E₂, for every k and every class alpha in A_k(X) -- which is what the \
  product says once it is expanded, and is the reduction the source's own proof performs. \
  Carried: cap, the Chern cap products on Chow groups of Stacks 0B7G (built there from Stacks \
  02U5 and Stacks 02U7, neither of which is in this repository); hbase, the relation when E₁ \
  has rank at most one, whose rank-one case is Stacks 02UH -- proved in this repository, but in \
  the vocabulary of the cap product on cycles and under its own carried hypotheses, so it does \
  not supply this statement -- and whose rank-zero case needs the normalisation c_0 = 1 of \
  Stacks 02U0 together with invariance of the cap products under an isomorphism of modules, \
  neither of which holds of a cap rule that is itself a parameter; and hsplit, the splitting \
  datum of the source's induction, namely the projective space bundle of E₁ with its flat \
  pullback injective (Stacks 02TX) and compatible with the cap products (Stacks 02U8), its \
  twist (Stacks 01O4), and the three short exact sequences the source forms on it. The rank of \
  the middle term is an instance hypothesis rather than derived, as it is for Stacks 02UH; \
  AlgebraicGeometry.SheafOfModules.rank_add_of_shortExact shows r₁ + r₂ is its only possible \
  value. NOT carried, and proved here: the associativity of the convolution, the descent along \
  the injective pullback, and the induction on r₁ itself"]
theorem chernCapOnChow_eq_sum_of_shortExact (C : ChowSituation.{u})
    (cap : ∀ r : ℕ, HigherChernCapRule C r)
    (hbase : ∀ r₁ ≤ 1, WhitneyChernRelation C cap r₁) (hsplit : HasChernSplitting C cap)
    {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (S : ShortComplex T.Modules)
    (hS : S.ShortExact) (r₁ r₂ : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (r₁ + r₂)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₂]
    (k : ℤ) (m : ℕ) (α : chowGroup C q k) :
    chernCapFamilyOnChow C cap q S.X₂ (r₁ + r₂) k m α =
      ∑ j : Fin (m + 1),
        gradedDegreeCast (chowGroup C q)
          (show k - (j.val : ℤ) - ((m - j.val : ℕ) : ℤ) = k - (m : ℤ) from by
            have := j.isLt; omega)
          (chernCapFamilyOnChow C cap q S.X₁ r₁ (k - (j.val : ℤ)) (m - j.val)
            (chernCapFamilyOnChow C cap q S.X₃ r₂ k (j.val) α)) := by
  rw [whitneyChernRelation_of_hasChernSplitting C cap hbase hsplit r₁ q S hS r₂, convolve_apply,
    ← Fin.sum_univ_eq_sum_range
      (fun j => convolveTerm (chernCapFamilyOnChow C cap q S.X₁ r₁)
        (chernCapFamilyOnChow C cap q S.X₃ r₂) k m j α) (m + 1)]
  exact Finset.sum_congr rfl fun j _ =>
    convolveTerm_of_le _ _ k (Nat.lt_succ_iff.mp j.isLt) α

end Stacks.Chow

end
