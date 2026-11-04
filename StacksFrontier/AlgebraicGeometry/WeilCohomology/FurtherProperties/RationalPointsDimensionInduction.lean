module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsClosedImmersion

/-!
# The induction on the dimension of [Stacks, Tag 0FH7]

Let `k` be a field and `n` an integer. Say that *the difference of two rational points is divisible
by `n` in dimension `d`* if for every proper smooth geometrically irreducible `X ⟶ Spec k` of
dimension `d` and every pair `x, x'` of `k`-rational points of `X`, the class `[x] - [x']` is `n`
times a class of `CH_0(X)`. This file proves that this statement **in dimension one implies it in
every dimension**, by the induction on `dim X` that [Stacks, Tag 0FH7] runs over a separably closed
field: if `dim X ≥ 2`, choose a smooth geometrically irreducible divisor `H ⊆ X` through both
points, apply the inductive hypothesis on `H`, and push the divisibility forward along `H ↪ X`.

The pushing forward is
`Stacks.WeilCohomology.rationalPointChowClass_sub_eq_zsmul_chowPushforward`, which is proved. The
choice of the divisor is **not** proved here; it is carried as the hypothesis
`Stacks.WeilCohomology.BertiniDivisorReduction`, and the sections below say exactly what that
hypothesis asserts, which library declarations supply its parts, and what is missing.

## Main definitions

* `Stacks.WeilCohomology.RationalPointDifferenceDivisible` — the statement being inducted: the
  divisibility of `[x] - [x']` by `n`, for every proper smooth geometrically irreducible scheme of
  a fixed dimension `d` over `k` and every pair of `k`-rational points on it.
* `Stacks.WeilCohomology.BertiniDivisorReduction` — the one-step geometric reduction the induction
  consumes: on a proper smooth geometrically irreducible `X` of dimension `d + 1 ≥ 2` carrying two
  `k`-rational points there is a closed subscheme `H ⊆ X`, again smooth and geometrically
  irreducible over `k` and of dimension exactly `d`, through which both points factor. **Unproved
  here.**

## Main results

* `Stacks.WeilCohomology.rationalPointDifferenceDivisible_succ` — the inductive step: dimension
  `d + 1` from dimension `d`, for `d ≥ 1`.
* `Stacks.WeilCohomology.rationalPointDifferenceDivisible_of_dimOne` — the induction: the
  dimension-one case implies every dimension `d ≥ 1`.

## The two carried hypotheses, and where each is consumed

### The curve case: `RationalPointDifferenceDivisible k n 1`

This is the base case of the source's induction, the sentence "if `dim X = 1` then `X` is a smooth
projective curve and the divisibility comes from the Jacobian". It is carried as the hypothesis
`hcurve` of `Stacks.WeilCohomology.rationalPointDifferenceDivisible_of_dimOne` and is consumed in
exactly one place, the `base` branch of the induction, where it *is* the goal.

It is not proved in this library, and the reason is a single missing prerequisite: the curve case
runs through the Jacobian `Pic⁰` of a smooth projective curve as a group scheme, which is
[Stacks, Tag 0BA0], and no declaration of that tag exists in any build target of this repository.
The step that follows the Jacobian — that a `k`-rational point of an abelian variety over a
separably closed field is `[n]` of a `k`-rational point — *is* available, as
`Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_isSepClosed`, itself carrying the étale clause of
[Stacks, Tag 03RP] as the disclosed hypothesis `Stacks.Groupoids.EtaleZPowIdOfIsUnit`. So the curve
case is blocked on [Stacks, Tag 0BA0] alone, and that is why it is a hypothesis here rather than a
lemma.

### The one-step reduction: `BertiniDivisorReduction k`

This is the Bertini half of the inductive step. It is carried as the hypothesis `hBertini` of both
main results and is consumed in exactly one place, the application that produces `H`, `ι` and the
two factorizations in `Stacks.WeilCohomology.rationalPointDifferenceDivisible_succ`. Its hypothesis
`1 ≤ d` — that is, `dim X ≥ 2` — is consumed there and nowhere else, and it is the hypothesis that
makes the curve case separate: it is what
`Stacks.SectionsVanishingOnSubscheme.geometricallyIrreducible_divisorOnX_of_isAmple` asks for
through the depth condition of [Stacks, Tag 0FD9], and on a curve that condition is false.

**Its conclusion is proved.** The declaration
`exists_bound_forall_exists_smooth_geometricallyIrreducible_divisorOnX_pair` of
`Stacks.SectionsVanishingOnSubscheme` derives all five of its obligations — the closed immersion,
the smoothness, the geometric irreducibility, the equality `dim H = d`, and the two factorizations
of the rational points — for the divisor `H_w` cut out by a member `w` of the vanishing system of
the ideal of the two points. It is nevertheless still carried whole here, for two reasons, and only
two.

1. **The linear system producing `H_w` is not reconstructible from `X`.** Four data remain
   hypotheses of that theorem: an ample invertible module `ℒ` on `X`, which is the projectivity of
   `X` and does not follow from properness; a basis of `V_n`, which [Stacks, Tag 0FD5] needs and
   does not produce, since it does not assert `V_n ≠ 0`; the ambient immersion of
   [Stacks, Tag 0FD6] for the full space of sections; and the numerical bound
   `dim_k Γ(Z, ℒ ^⊗ n|_Z) ≤ 2`, whose left side *is* `2` but which no statement of this library
   evaluates. None of the four follows from "proper, smooth, geometrically irreducible of dimension
   `d + 1`", so the inductive hypothesis cannot hand them to the next application; deriving the
   reduction inside the induction would mean carrying that whole package through it, which is a
   different and larger statement.

   What is *not* missing: the
   ideal sheaf is produced, as the vanishing ideal of `{x, x'}`; the three finiteness conditions
   are instances; the `GeneratesOffSupport` condition and the immersion on the complement of `Z`
   are discharged for all large `n`; and the dimension of the divisor is computed, as an equality
   and not a bound, by
   `Stacks.SectionsVanishingOnSubscheme.topologicalKrullDim_divisorOnX_eq`.
2. **The reduction is proved only over an algebraically closed field**, where [Stacks, Tag 0FH7]
   runs over the separable closure of `k`. This is not a mismatch between the two proved halves:
   `Stacks.SectionsVanishingOnSubscheme.geometricallyIrreducible_divisorOnX_of_isAmple` takes
   smoothness of the divisor as an explicit hypothesis and assumes only `IsSepClosed`, so it
   instantiates freely at `IsAlgClosed` and the halves do compose. It is the smoothness half that
   is genuinely algebraically closed: it rests on the smoothness of a zero scheme at a closed
   point, and over an imperfect separably closed field a closed point of a smooth scheme can have a
   purely inseparable residue field — over `k ⊇ 𝔽_p(t)^sep` with `a ∉ k^p` the affine line has the
   closed point with residue field `k(a^{1/p})` — so the statement with `IsSepClosed` in place of
   `PerfectField` is false there, not merely unproved. Adding `PerfectField` is the maximal
   available weakening and it returns algebraic closedness. Consuming the reduction for
   [Stacks, Tag 0FH7] therefore needs the base change of the whole reduction from `k^sep` to its
   algebraic closure together with a descent of the conclusion, which is not formalized here.

## What is *not* assumed

Neither main result assumes that `k` is separably closed, nor that `n` is invertible in `k`. The
induction uses neither: the transport along a closed immersion and the arithmetic in `CH_0` are
insensitive to both. Both hypotheses of [Stacks, Tag 0FH7] live inside the two carried hypotheses —
separable closedness in each of them, the invertibility of `n` in the curve case, where
`Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_isSepClosed` spends it on the étaleness of
multiplication by `n`.

Integrality of `X` is not assumed either, although the library's Bertini and irreducibility results
ask for it, and it does not have to be: it is recovered from the hypotheses carried here by
`Stacks.SectionsVanishingOnSubscheme.isIntegral_of_smooth_of_geometricallyIrreducible`, from
reducedness of a scheme smooth over a field
(`Stacks.SectionsVanishingOnSubscheme.isReduced_of_smooth_over_field`), irreducibility of a
geometrically irreducible scheme over a field
(`AlgebraicGeometry.GeometricallyIrreducible.irreducibleSpace_of_subsingleton`), and reduced plus
irreducible being integral (`AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced`).

Properness is assumed rather than projectivity, which is weaker than [Stacks, Tag 0FH7]'s
hypothesis and so makes the statement stronger: projectivity gives properness by
`AlgebraicGeometry.isProper_of_isProjectiveMorphism`.

## Implementation notes

The dimension is `topologicalKrullDim`, valued in `WithBot ℕ∞`, and is pinned by an equality
`topologicalKrullDim X = (d : WithBot ℕ∞)` with `d : ℕ` rather than by an inequality. The equality
is what makes the induction a `Nat.le_induction` on `d` with no case analysis: the reduction drops
the index by exactly one, so the inductive hypothesis applies on the nose. An inequality index
would force the step to distinguish "`dim X` is really `d + 1`", where the reduction applies, from
"`dim X ≤ d`", where it does not, and the two cases cannot be separated without deciding the
dimension.

`Stacks.Chow.chowGroup` is formed for `Stacks.Chow.fieldChowSituation k`, whose base scheme is
reducibly `Spec k`, and a `k`-rational point is a section of the structure morphism, as in
`Stacks.WeilCohomology.rationalPointChowClass`. The two section properties of the lifted points are
derived from the factorizations rather than demanded of `BertiniDivisorReduction`, by
associativity; properness of `H ⟶ Spec k` is likewise derived, a closed immersion being proper.

No `@[stacks]` attribute is attached, and in particular [Stacks, Tag 0FH7] is **not** registered
here. The results below carry two hypotheses that the tag does not — the curve case and the
one-step reduction — so a registration would assert a theorem that is not proved here. The tag is
registered unconditionally elsewhere, on
`exists_finiteSeparable_rationalPointChowClass_sub_eq_zsmul_of_isProjectiveMorphism` in the
namespace `Stacks.WeilCohomology`.

## References

* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.WeilCohomology

/-- **The statement [Stacks, Tag 0FH7] inducts on, at a fixed dimension.**
`RationalPointDifferenceDivisible k n d` says: for every scheme `X` proper, smooth and
geometrically irreducible over `k` with `topologicalKrullDim X = d`, and every pair `x, x'` of
`k`-rational points of `X`, the difference `[x] - [x']` of their classes in `CH_0(X)` is `n` times
a class of `CH_0(X)`.

The instances of interest are `d = 1`, the curve case, which rests on the Jacobian of
[Stacks, Tag 0BA0] and is **not** proved in this library; every `d ≥ 1`, which
`Stacks.WeilCohomology.rationalPointDifferenceDivisible_of_dimOne` derives from it; and `d = 0`,
which `Stacks.WeilCohomology.rationalPointDifferenceDivisible_zero` proves outright and which
this induction does not reach.

Neither separable closedness of `k` nor invertibility of `n` in `k` appears: they are hypotheses of
[Stacks, Tag 0FH7] needed to *prove* the dimension-one instance, not to state any instance. -/
def RationalPointDifferenceDivisible (k : Type u) [Field k] (n : ℤ) (d : ℕ) : Prop :=
  ∀ {X : Scheme.{u}} (f : X ⟶ (Stacks.Chow.fieldChowSituation k).S) [IsProper f] [Smooth f]
    [GeometricallyIrreducible f],
    topologicalKrullDim X = (d : WithBot ℕ∞) →
    ∀ (x x' : (Stacks.Chow.fieldChowSituation k).S ⟶ X)
      (hx : x ≫ f = 𝟙 (Stacks.Chow.fieldChowSituation k).S)
      (hx' : x' ≫ f = 𝟙 (Stacks.Chow.fieldChowSituation k).S),
      ∃ c : Stacks.Chow.chowGroup (Stacks.Chow.fieldChowSituation k) f 0,
        rationalPointChowClass k f x hx - rationalPointChowClass k f x' hx' = n • c

/-- **The Bertini step of [Stacks, Tag 0FH7], in the shape its induction consumes.**
`BertiniDivisorReduction k` says: let `X` be proper, smooth and geometrically irreducible over `k`
of dimension `d + 1` with `d ≥ 1`, and let `x, x'` be `k`-rational points of `X`. Then there is a
closed immersion `ι : H ⟶ X` with `H` smooth and geometrically irreducible over `k` of dimension
exactly `d`, and `k`-rational points `x_H`, `x'_H` of `H` with `x_H ≫ ι = x` and `x'_H ≫ ι = x'`.

The hypothesis `1 ≤ d`, that is `dim X ≥ 2`, is what separates the inductive step from the curve
case: it is the dimension bound
`Stacks.SectionsVanishingOnSubscheme.geometricallyIrreducible_divisorOnX_of_isAmple` requires
through the depth condition of [Stacks, Tag 0FD9], and that condition fails on a curve.

**This is not proved in this library**, although its conclusion is. All five obligations — the
closed immersion, the smoothness, the geometric irreducibility, the dimension and the two
factorizations — are discharged by
`exists_bound_forall_exists_smooth_geometricallyIrreducible_divisorOnX_pair` of
`Stacks.SectionsVanishingOnSubscheme`, at the cost of two things this statement does not grant.
The first is the linear system cutting the divisor out: an ample invertible module, a basis of
`V_n`, the ambient immersion of [Stacks, Tag 0FD6] and the numerical bound, none of which is
reconstructible from "proper, smooth, geometrically irreducible of dimension `d + 1`", so the
inductive hypothesis cannot hand them to the next application. The second is the field: the
reduction is proved over `k` *algebraically* closed, while [Stacks, Tag 0FH7] runs over a separable
closure, and the gap is not a removable hypothesis but a base change and a descent. The module
docstring says all of this at length. -/
def BertiniDivisorReduction (k : Type u) [Field k] : Prop :=
  ∀ {X : Scheme.{u}} (f : X ⟶ (Stacks.Chow.fieldChowSituation k).S) [IsProper f] [Smooth f]
    [GeometricallyIrreducible f] (d : ℕ), 1 ≤ d →
    topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞) →
    ∀ (x x' : (Stacks.Chow.fieldChowSituation k).S ⟶ X),
      x ≫ f = 𝟙 (Stacks.Chow.fieldChowSituation k).S →
      x' ≫ f = 𝟙 (Stacks.Chow.fieldChowSituation k).S →
      ∃ (H : Scheme.{u}) (ι : H ⟶ X) (_ : IsClosedImmersion ι) (_ : Smooth (ι ≫ f))
        (_ : GeometricallyIrreducible (ι ≫ f)),
        topologicalKrullDim H = (d : WithBot ℕ∞) ∧
          ∃ x_H x'_H : (Stacks.Chow.fieldChowSituation k).S ⟶ H,
            x_H ≫ ι = x ∧ x'_H ≫ ι = x'

/-- **The inductive step of [Stacks, Tag 0FH7]: dimension `d + 1` from dimension `d`.** Let `d ≥ 1`
and suppose the difference of two rational points is divisible by `n` on every proper smooth
geometrically irreducible `k`-scheme of dimension `d`. Then the same holds in dimension `d + 1`,
granted the one-step reduction `Stacks.WeilCohomology.BertiniDivisorReduction`.

Given `X` of dimension `d + 1` and two `k`-rational points on it, the reduction produces a closed
subscheme `H ⊆ X` of dimension `d`, again proper (a closed immersion is proper), smooth and
geometrically irreducible, through which both points factor. The inductive hypothesis on `H` gives
a class `c` of `CH_0(H)` with `[x_H] - [x'_H] = n c`, and
`Stacks.WeilCohomology.rationalPointChowClass_sub_eq_zsmul_chowPushforward` carries that equation
up to `X` along the pushforward, exhibiting `[x] - [x']` as `n` times `ι_* c`.

The section properties of `x_H` and `x'_H` are not asked of the reduction: they follow from the
factorizations and the section properties of `x` and `x'` by associativity. -/
theorem rationalPointDifferenceDivisible_succ (k : Type u) [Field k] (n : ℤ)
    (hBertini : BertiniDivisorReduction k) {d : ℕ} (hd : 1 ≤ d)
    (ih : RationalPointDifferenceDivisible k n d) :
    RationalPointDifferenceDivisible k n (d + 1) := by
  unfold RationalPointDifferenceDivisible
  intro X f _ _ _ hdim x x' hx hx'
  obtain ⟨H, ι, hι, hsm, hgi, hdimH, x_H, x'_H, hfac, hfac'⟩ :=
    hBertini f d hd hdim x x' hx hx'
  have hx_H : x_H ≫ ι ≫ f = 𝟙 (Stacks.Chow.fieldChowSituation k).S := by
    rw [← Category.assoc, hfac]; exact hx
  have hx'_H : x'_H ≫ ι ≫ f = 𝟙 (Stacks.Chow.fieldChowSituation k).S := by
    rw [← Category.assoc, hfac']; exact hx'
  obtain ⟨c, hc⟩ := ih (ι ≫ f) hdimH x_H x'_H hx_H hx'_H
  exact ⟨Stacks.Chow.chowPushforwardOfIsClosedImmersion (Stacks.Chow.fieldChowSituation k)
      (ι ≫ f) f ι rfl 0 c,
    rationalPointChowClass_sub_eq_zsmul_chowPushforward k f (ι ≫ f) ι rfl x_H x'_H hx_H hx'_H
      x x' hfac hfac' hx hx' n c hc⟩

/-- **The induction on `dim X` of [Stacks, Tag 0FH7].** Suppose the difference of two rational
points is divisible by `n` on every proper smooth geometrically irreducible `k`-scheme of dimension
one — the curve case, which rests on the Jacobian of [Stacks, Tag 0BA0] and is carried here as the
hypothesis `hcurve`. Then, granted the one-step reduction
`Stacks.WeilCohomology.BertiniDivisorReduction`, the same holds in every dimension `d ≥ 1`.

This is `Nat.le_induction` on `d` starting at one, with `hcurve` as the base case — the one place
it is used, where it is the goal verbatim — and
`Stacks.WeilCohomology.rationalPointDifferenceDivisible_succ` as the step.

Dimension zero is outside this induction, and not because it is unavailable: it is proved
separately by `Stacks.WeilCohomology.rationalPointDifferenceDivisible_zero`, for the cheap reason
that a zero-dimensional proper smooth geometrically irreducible scheme over `k` has an isomorphism
for its structure morphism, so the two sections coincide and the difference of the classes is
zero. It cannot be folded in here as a base case: the step
`Stacks.WeilCohomology.rationalPointDifferenceDivisible_succ` itself requires `1 ≤ d`, because the
Bertini reduction it consumes fails on a curve, so dimension one is where this induction has to
start and dimension zero has to be a separate case rather than the one below it. `1 ≤ d` is
therefore still the honest range *of this statement*; it is no longer a restriction on what the
library knows. -/
theorem rationalPointDifferenceDivisible_of_dimOne (k : Type u) [Field k] (n : ℤ)
    (hcurve : RationalPointDifferenceDivisible k n 1) (hBertini : BertiniDivisorReduction k)
    (d : ℕ) (hd : 1 ≤ d) :
    RationalPointDifferenceDivisible k n d := by
  induction d, hd using Nat.le_induction with
  | base => exact hcurve
  | succ d hd ih => exact rationalPointDifferenceDivisible_succ k n hBertini hd ih

end Stacks.WeilCohomology

end
