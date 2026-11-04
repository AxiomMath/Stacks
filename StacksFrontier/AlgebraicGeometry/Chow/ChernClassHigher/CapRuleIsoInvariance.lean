module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ChernClassRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation

/-!
# Iso-invariance of the Chern cap rule from the relation of Stacks 02U6

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL. The cap
product with the Chern classes of a finite locally free module of rank `r` enters this repository
as the parameter `Stacks.Chow.HigherChernCapRule`, a bare family of homomorphisms of Chow groups
indexed by a test scheme and a module on it. Being bare, its values at two *isomorphic* modules
are unrelated data, and the property that they agree —
`Stacks.Chow.HigherChernCapRule.RespectsIso` — is assumed wherever it is needed:
`Stacks.Chow.chowCohomologyRestriction_ch_eq` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ChernClassRestriction`, and in the
equivalent shape of a restriction comparison at
`Stacks.Chow.chernClassArbitraryRank_eq_chernClass` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.ConstantRankComparison`.

This file reduces that property to the rule's own defining equation. In the source the cap
products are not given, they are *solved for*: Definition 42.37.1, Stacks 02U0, defines
`c_j(ℰ) ∩ α` as the unique family `(α_j)_{j ≤ r}` with `α_0 = α` satisfying the
projective-bundle relation

  `∑_{i=0}^{r} (-1)^i c₁(O_P(1))^i ∩ π^*(α_{r-i}) = 0`

on `P = P(ℰ)`, equation 42.37.1.1, Stacks 02U1. That characterization is
`Stacks.Chow.IsChernCapFamily`, Stacks 02U6, and it is unique by
`Stacks.Chow.eq_of_isChernCapFamily`. Crucially, `Stacks.Chow.IsChernCapFamily` **does not
mention the module**: it refers only to the bundle `π : P ⟶ X` and the first Chern class cap
operator of its twist. So a rule that solves the relation at one bundle is pinned there, and two
modules presented by the same bundle receive the same cap operations.

That is the whole content of iso-invariance, and it is why the property is about isomorphic
modules and not about arbitrary ones: `P(ℰ)` with `O(1)` depends on `ℰ` only up to isomorphism,
so isomorphic modules share a presentation, while non-isomorphic modules of the same rank do not
and must not — their Chern classes differ.

## Main definitions

* `Stacks.Chow.ChernCapPresentation` — a projective-bundle presentation over a test scheme: the
  bundle, its projection as a flat morphism of relative dimension `r - 1` with the flat pullback
  of Stacks 0FVK available, a first Chern class cap operator for its twist, and the injectivity
  half of Stacks 02TX.
* `Stacks.Chow.ChernCapPresentation.Solves` — that a `Stacks.Chow.HigherChernCapRule` takes, at a
  given module, values solving the relation of Stacks 02U6 at that presentation. This is Stacks
  02U0 read as a property of the carried rule.
* `Stacks.Chow.HigherChernCapRule.HasCommonPresentation` — that any two isomorphic modules of
  rank `r` on a test scheme admit a *common* presentation at which the rule solves the relation.

## Main results

* `Stacks.Chow.ChernCapPresentation.cap_eq_of_solves` — a cap rule solving the relation of
  Stacks 02U6 at one presentation takes the same value at any two modules it solves the relation
  for there.
* `Stacks.Chow.HigherChernCapRule.respectsIso_of_hasCommonPresentation` —
  **`Stacks.Chow.HigherChernCapRule.RespectsIso` is a consequence of Stacks 02U6**: a cap rule
  with a common presentation on isomorphic modules respects isomorphism.

## Implementation notes

### What this does and does not discharge

`Stacks.Chow.HigherChernCapRule` is unconstrained data, so
`Stacks.Chow.HigherChernCapRule.RespectsIso` is **not** a theorem about it: the type contains
families that take different values at two isomorphic modules, and no declaration of this
repository relates a `Stacks.Chow.HigherChernCapRule` to the families
`Stacks.Chow.IsChernCapFamily` of Stacks 02U6. What is proved here is the *reduction*: the
assumption of iso-invariance is replaced by the assumption that the rule solves the relation of
Stacks 02U6, which is how the source defines it. That is a weaker and more primitive hypothesis —
it is a statement about the Chow-theoretic equation the rule satisfies, not about the rule's
behaviour across the isomorphism — but it is a hypothesis, and
`Stacks.Chow.chowCohomologyRestriction_ch_eq` does not become hypothesis-free.

### Why Stacks 0B7G is not what discharges it

Stacks 0B7G is Lemma 42.38.6, the compatibility of the Chern class cap products with the Gysin
map of an effective Cartier divisor, `c_j(ℰ|_D) ∩ i^*α = i^*(c_j(ℰ) ∩ α)`. It is proved in this
repository as `Stacks.Chow.isChernCapFamily_gysin` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleGysin`. It says nothing
about isomorphic modules, and it is not the construction of the cap product: that is Definition
42.37.1, Stacks 02U0, whose uniqueness clause is Stacks 02U6 and which is what is used here.

### Why the presentation must be common and not merely isomorphic

Two isomorphic modules have canonically isomorphic projective bundles, carrying `O(1)` to `O(1)`.
In this repository the bundle is a parameter and no declaration relates two of them: the first
Chern class cap operators of two bundles are unrelated data, as recorded in the implementation
notes of `StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleBivariantClass`,
and nothing transports `Stacks.Chow.IsChernCapFamily` along an isomorphism of bundles over a
fixed base. So the hypothesis is stated with one presentation serving both modules, which is the
source's situation verbatim — there is only ever one bundle `P(ℰ) = P(ℰ')` — rather than with two
presentations and a comparison between them.

No transport and no `eqToHom` appears below. The value of the cap rule is a homomorphism
`A_k(T) ⟶ A_{k-j}(T)` whose type does not mention the module, so every equality here is a plain
equality of homomorphisms.

## References

* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02U1](https://stacks.math.columbia.edu/tag/02U1)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Projective-bundle presentations -/

/-- A **projective-bundle presentation** of rank `r` over a test scheme `q : T ⟶ C.S`: the data
at which the relation of Stacks 02U6 is read. It is the bundle `π : P ⟶ T`, flat of relative
dimension `r - 1` with the flat pullback of Stacks 0FVK available in every degree, together with
a first Chern class cap operator for its twist and the injectivity half of Stacks 02TX.

The module is *not* part of the datum, exactly as in `Stacks.Chow.IsChernCapFamily`: the relation
of Stacks 02U6 refers to the bundle alone. -/
structure ChernCapPresentation (C : ChowSituation.{u}) (r : ℕ) {T : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] : Type (u + 1) where
  /-- The projective bundle. -/
  bundle : Scheme.{u}
  /-- Its structure morphism to the base of the Chow situation. -/
  str : bundle ⟶ C.S
  [locallyOfFiniteType_str : LocallyOfFiniteType str]
  /-- The projection to the test scheme. -/
  proj : bundle ⟶ T
  [locallyOfFiniteType_proj : LocallyOfFiniteType proj]
  [flat_proj : Flat proj]
  /-- The projection lies over the test scheme. -/
  comp : proj ≫ q = str
  /-- The projection of the projective bundle of a rank-`r` module is flat of relative
  dimension `r - 1`. -/
  relativeDimension : AlgebraicGeometry.RelativeDimension proj (r - 1)
  /-- Stacks 02S1 for the projection, which is what produces the flat pullback of Stacks
  0FVK. -/
  factors : ∀ k : ℤ,
    FlatPullbackFactorsThroughRationalEquivalence C str q proj comp (r - 1) relativeDimension k
  /-- A first Chern class cap operator for the twist `O_P(1)`. -/
  twist : ChernCapOperator C str
  /-- The injectivity half of Stacks 02TX, which makes the relation of Stacks 02U6 determine the
  family it is solved for. -/
  injective : ProjectiveBundleRelationInjective C q str proj comp r relativeDimension factors
    twist

attribute [instance] ChernCapPresentation.locallyOfFiniteType_str
  ChernCapPresentation.locallyOfFiniteType_proj ChernCapPresentation.flat_proj

/-! ### A cap rule solving the relation at a presentation -/

section Presentation

variable {C : ChowSituation.{u}} {r : ℕ} {T : Scheme.{u}} {q : T ⟶ C.S}
  [LocallyOfFiniteType q]

/-- **Stacks 02U0 as a property of the carried cap rule.** That the values of a
`Stacks.Chow.HigherChernCapRule` at the module `F` solve the relation of Stacks 02U6 at the
presentation `p`: for every degree `k` and every class `α ∈ A_k(T)`, the family
`j ↦ cap q F k j α` is the family of Chern class cap products of `α`.

This is what the source's definition of `c_j(ℰ) ∩ α` asserts. -/
def ChernCapPresentation.Solves (p : ChernCapPresentation C r q)
    (cap : HigherChernCapRule C r) (F : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] : Prop :=
  ∀ (k : ℤ) (α : chowGroup C q k),
    IsChernCapFamily C q p.str p.proj p.comp r p.relativeDimension p.factors p.twist k α
      fun j ↦ cap q F k j α

/-- **A cap rule is pinned at a presentation.** If a `Stacks.Chow.HigherChernCapRule` solves the
relation of Stacks 02U6 at one presentation for each of two modules, its values at the two
modules are equal.

The relation of Stacks 02U6 does not mention the module, so the two families solve the same
equation with the same prescribed zeroth member, and the uniqueness
`Stacks.Chow.eq_of_isChernCapFamily` identifies them. -/
theorem ChernCapPresentation.cap_eq_of_solves (p : ChernCapPresentation C r q)
    {cap : HigherChernCapRule C r} {F F' : T.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r]
    (hF : p.Solves cap F) (hF' : p.Solves cap F') (k : ℤ) (j : Fin (r + 1)) :
    cap q F k j = cap q F' k j :=
  AddMonoidHom.ext fun α ↦
    congrFun (eq_of_isChernCapFamily C q p.str p.proj p.comp r p.relativeDimension p.factors
      p.twist p.injective k α (hF k α) (hF' k α)) j

/-! ### Iso-invariance -/

/-- That any two **isomorphic** modules of rank `r` on a test scheme admit a *common*
projective-bundle presentation at which the cap rule solves the relation of Stacks 02U6.

This is the source's situation: the presentation is `P(ℰ)` with its twist `O(1)`, which depends
on `ℰ` only up to isomorphism, so one presentation serves both modules; and that the rule solves
the relation there is Stacks 02U0, the definition of the cap product. The restriction to
isomorphic modules is essential and not a convenience — two non-isomorphic modules of the same
rank have different projective bundles and different Chern classes. -/
def HigherChernCapRule.HasCommonPresentation (C : ChowSituation.{u}) (r : ℕ)
    (cap : HigherChernCapRule C r) : Prop :=
  ∀ {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] (F F' : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' r],
    (F ≅ F') → ∃ p : ChernCapPresentation C r q, p.Solves cap F ∧ p.Solves cap F'

/-- **Iso-invariance of the Chern cap rule follows from the relation of Stacks 02U6.** A
`Stacks.Chow.HigherChernCapRule` which, on any two isomorphic modules of rank `r`, solves the
relation of Stacks 02U6 at a common projective-bundle presentation takes equal values at them —
that is, it satisfies `Stacks.Chow.HigherChernCapRule.RespectsIso`.

This replaces the iso-invariance assumed by
`Stacks.Chow.chowCohomologyRestriction_ch_eq` with the assumption that the rule is what Stacks
02U0 defines it to be. It is a reduction and not a discharge: a
`Stacks.Chow.HigherChernCapRule` is unconstrained data and nothing in this repository relates one
to the families of Stacks 02U6. -/
theorem HigherChernCapRule.respectsIso_of_hasCommonPresentation {cap : HigherChernCapRule C r}
    (h : HigherChernCapRule.HasCommonPresentation C r cap) :
    HigherChernCapRule.RespectsIso C r cap := by
  intro T q _ F F' _ _ e k j
  obtain ⟨p, hF, hF'⟩ := h q F F' e
  exact p.cap_eq_of_solves hF hF' k j

end Presentation

/-! ### The base change compatibility, with iso-invariance replaced by Stacks 02U6 -/

section Restriction

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X X' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f : X' ⟶ X) [LocallyOfFiniteType f]
  (hgys : G.IsNaturalUnderBaseChangeIso)
  {R : ChowCohomologySeriesRing C G sX} {R' : ChowCohomologySeriesRing C G (f ≫ sX)}

/-- **The base change compatibility of the total Chern class in degrees `j ≤ r`, with the
iso-invariance of the cap rule traded for the relation of Stacks 02U6.** This is
`Stacks.Chow.chowCohomologyRestriction_ch_eq` with its hypothesis `hiso` supplied by
`Stacks.Chow.HigherChernCapRule.respectsIso_of_hasCommonPresentation`, so the two hypotheses
beyond the data are now `hcap`, that the two Chern class data use the same cap rule, and
`hcommon`, that the rule is the solution of the relation of Stacks 02U6 — which is what Stacks
02U0 defines it to be.

The hypothesis `hcap` is part of the statement and cannot be dropped: a
`Stacks.Chow.HigherChernCapRule` is already indexed by an arbitrary test scheme and does not
mention `X`, so two data describing one geometry use one rule, and without the hypothesis `D'`
could carry an unrelated rule. -/
theorem chowCohomologyRestriction_ch_eq_of_hasCommonPresentation
    (D : TotalChernClassSeries C G sX R) (D' : TotalChernClassSeries C G (f ≫ sX) R')
    (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (hrank : PullbackPreservesRank E r)
    (hcap : (D.cap r : HigherChernCapRule C r) = (D'.cap r : HigherChernCapRule C r))
    (hcommon : HigherChernCapRule.HasCommonPresentation C r
      (D'.cap r : HigherChernCapRule C r))
    (j : Fin (r + 1)) :
    chowCohomologyRestriction C G sX f ((j : ℕ) : ℤ) hgys (D.ch E (j : ℕ)) =
      D'.ch ((Scheme.Modules.pullback f).obj E) (j : ℕ) :=
  chowCohomologyRestriction_ch_eq C G sX f hgys D D' E r hrank hcap
    (HigherChernCapRule.respectsIso_of_hasCommonPresentation hcommon) j

end Restriction

end Stacks.Chow

end
