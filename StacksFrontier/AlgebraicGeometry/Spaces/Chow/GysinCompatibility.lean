module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinOfClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCap

/-!
# The refined Gysin map, proper pushforward and flat pullback

In Situation 0EDT let `X/B` be good and let `(ℒ, s, i : E → X)` be a triple as in Definition
0ER1: `ℒ` an invertible sheaf on `X`, `s` a global section of `ℒ`, and `E = Z(s)` its vanishing
locus with its closed immersion into `X`.  Given a morphism `f : X' ⟶ X` of good algebraic
spaces over `B`, Remark 0ER3 forms the cartesian square

```
E' --i'--> X'
|          |
g          f
|          |
v          v
E  --i-->  X
```

with `E' = Z(f^*s) = f^{-1}(E) = E ×_X X'`, and asks how the refined Gysin maps of the two
triples are related to the maps induced by `f`.

* **Stacks 0ER5**, for `f` proper: `i^* f_* α' = g_* (i')^* α'` for a `(k+1)`-cycle `α'` on `X'`.
* **Stacks 0ER6**, for `f` flat of relative dimension `r`: `(i')^* f^* α = g^* i^* α` for a
  `(k+1)`-cycle `α` on `X`.

The letter `D` is the dimension situation of Stacks 0EDT, so the closed subspace which the source
calls `D` is called `E` here, and its base change `D'` is called `E'`, as in
`AlgebraicGeometry.Space.gysinCycleMap`.

## Main definitions

* `AlgebraicGeometry.Space.gysinBaseChangeSubspace`: the closed subspace `E' = f^{-1}(E)` of `X'`
  of Remark 0ER3, which is the scheme-theoretic base change `E ×_X X'`.
* `AlgebraicGeometry.Space.gysinBaseChangeHom`: the morphism `g : E' ⟶ E` of Remark 0ER3.
* `AlgebraicGeometry.Space.GysinProperPushforwardComparison` and
  `AlgebraicGeometry.Space.GysinFlatPullbackComparison`: the comparison data of the source's two
  proofs — each lemma for a prime cycle, read coefficientwise at the two component parameters of
  Definition 0ER1.  Each is the single hypothesis of its lemma; the docstrings explain why it does
  not follow from the other data.

## Main results

* `AlgebraicGeometry.Space.isPullback_gysinBaseChange`: the square of Remark 0ER3 is cartesian,
  so `E'` really is `E ×_X X'`.
* `AlgebraicGeometry.Space.comp_structure_of_isPullback`: `g` is a morphism over `B`.
* `AlgebraicGeometry.Space.gysinCycleMap_properPushforward_eq_of_comparison`: **Stacks 0ER5**, as
  a plain equality of `k`-cycles on `E`, on the comparison datum alone.
* `AlgebraicGeometry.Space.gysinCycleMap_flatPullbackMap_eq_of_comparison`: **Stacks 0ER6**, as a
  plain equality of `(k+r)`-cycles on `E'`, on the comparison datum alone.
* `AlgebraicGeometry.Space.gysinCycleMap_properPushforward_integralCycle_eq` and
  `AlgebraicGeometry.Space.gysinCycleMap_flatPullbackMap_integralCycle_eq`: the two lemmas for a
  prime cycle, which is the form the comparison datum is stated at.
* `AlgebraicGeometry.Space.gysinCycleMap_properPushforward_eq` and
  `AlgebraicGeometry.Space.gysinCycleMap_flatPullbackMap_eq`: the same two lemmas with the
  prime-cycle case taken as a bare hypothesis `hprime` instead of the comparison datum.  These
  are strictly more general, and are the form to use when the prime-cycle case is available by
  other means.
* `AlgebraicGeometry.Space.gysinCoeff_properPushforward`,
  `AlgebraicGeometry.Space.properPushforward_gysinCoeff`,
  `AlgebraicGeometry.Space.gysinCoeff_flatPullback`,
  `AlgebraicGeometry.Space.flatPullback_gysinCoeff`: the four composites, expanded as a sum over
  the integral closed subspaces of the source of the single-subspace values weighted by the
  coefficients of the cycle.  These are the mathematical content of this file; see the
  implementation notes.

## Implementation notes

### How the square of Remark 0ER3 is formed

The source's `D' = Z(f^*s)` is identified in Remark 0ER3 with the inverse image `f^{-1}(D)`,
which is the fibre product `D ×_X X'`.  That inverse image is Stacks 083Q —
`CategoryTheory.Subfunctor.preimage` — and it *is* the fibre product, by
`CategoryTheory.Subfunctor.isPullback_preimage`; it is a closed subspace by
`AlgebraicGeometry.Space.isClosedSubspace_preimage`.  So `E'` is the scheme-theoretic base change
and not a coarser topological inverse image, and `g` is the canonical projection
`CategoryTheory.Subfunctor.fromPreimage` onto `E`, whose commuting square with `i`, `i'` and `f`
is `CategoryTheory.Subfunctor.fromPreimage_ι`.  This is the route
`AlgebraicGeometry.Space.interOnClosedSubspace` takes for the intersections of Stacks 0ER7.

The identification `Z(f^*s) = f^{-1}(Z(s))` is
`AlgebraicGeometry.Space.zeroScheme_modulePullback_eq_preimage`, read in the dimension situation
as `AlgebraicGeometry.Space.pullbackDivisor_eq_vanishingLocus`, with invertibility of `ℒ` — a
hypothesis of Stacks 0ER1 — as its only input.  The quasi-coherent ideal of the zero scheme of
Stacks 0845 is `AlgebraicGeometry.Space.isQuasicoherentOnSite_zeroSchemeIdealSheaf`, and the
surjectivity half of Stacks 03MB for it is
`AlgebraicGeometry.Space.exists_definingIdealAt_eq_sectionEvaluationIdealAt_of_isInvertible`.

The statements below are nevertheless given for a closed subspace `E ⊆ X` and a closed subspace
`E' ⊆ X'` sitting in a cartesian square over `f` — which is exactly the shape of Remark 0ER3 —
rather than for a pair of zero schemes, and `AlgebraicGeometry.Space.gysinBaseChangeSubspace`
together with `AlgebraicGeometry.Space.isPullback_gysinBaseChange` exhibits the source's `D'` as
such an `E'`.  That is a genuine generalisation rather than a detour: the cartesian square is all
the proofs use, so they apply to the source's pair of zero schemes through the identification
above and to any other cartesian square besides.

### What is proved and what is assumed

The two component inputs of Stacks 0ER1 are explicit parameters here, the fields of
`AlgebraicGeometry.Space.GysinComponentRule`; the triple `(ℒ', s', i' : E' → X')` enters only
through a second such parameter `rule'`.  Since `rule` on `X` and `rule'` on `X'` are therefore
unrelated data, *no* relation between the component cycles on the two spaces is derivable, and
the source's case analysis on a single integral closed subspace — which supplies exactly such a
relation — cannot be carried out here.  That one relation is isolated as the single field of
`AlgebraicGeometry.Space.GysinProperPushforwardComparison`, resp.
`AlgebraicGeometry.Space.GysinFlatPullbackComparison`, whose docstrings name the steps of the
source's proof it stands for.  The prime-cycle form of each lemma, and the extension of that form
over an arbitrary cycle, are proved.

That extension is not formal.  A cycle is an infinite formal sum, so there is no expansion
`α' = ∑ n_j [W'_j]` as a finite sum of elements of `Z_{k+1}(X')` to feed to additivity; the two
composites have to be computed coefficientwise and the resulting double sums exchanged.  The four
lemmas `AlgebraicGeometry.Space.gysinCoeff_properPushforward`,
`AlgebraicGeometry.Space.properPushforward_gysinCoeff`,
`AlgebraicGeometry.Space.gysinCoeff_flatPullback` and
`AlgebraicGeometry.Space.flatPullback_gysinCoeff` do that: each says that the composite is the
weighted sum over the integral closed subspaces of the source of its own single-subspace value.
The exchange is legitimate because the set of pairs contributing a nonzero term is finite, which
is where the hypotheses earn their keep:

* for a pushforward, Stacks 0ENZ —
  `AlgebraicGeometry.Space.locallyFinite_closure_image_pointsMap` — applied to the support of
  the cycle, resp. to the inverse images along `|i'|` of that support, bounds the subspaces of
  `X'` which can contribute at a fixed integral closed subspace of `E`;
* for a pullback, the local finiteness of the support of the cycle `f^*[W]`, resp. of the
  component cycle of `W`, bounds the subspaces of `X'`, resp. of `E`, lying over the generic
  point of a fixed integral closed subspace of `E'`.

The same pattern is used in
`AlgebraicGeometry.Space.firstChernCapCycleMap_add_of_componentCycle_add`, where the pointwise
rule is a hypothesis and everything that follows from it by the local finiteness of a cycle is
proved, and the one-field comparison datum
`AlgebraicGeometry.Space.ProperFlatBaseChangeComparison` for Stacks 0EPD has the same shape.

### Cycles rather than Chow classes

The source states both identities in `CH_k(D)`, resp. `CH_{k+r}(D')`, and remarks that they make
sense because `f_*`, resp. `f^*`, is defined on the level of cycles.  What is proved here is the
finer identity in `Z_k(E)`, resp. `Z_{k+r}(E')`; applying the class map of an
`AlgebraicGeometry.Space.ChowTarget` to it gives the source's identity, exactly as
`AlgebraicGeometry.Space.refinedGysin` is the cycle-level Gysin map composed with that class map.

## References

* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0ER6](https://stacks.math.columbia.edu/tag/0ER6)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0ER7](https://stacks.math.columbia.edu/tag/0ER7)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0ENZ](https://stacks.math.columbia.edu/tag/0ENZ)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP6](https://stacks.math.columbia.edu/tag/0EP6)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The diagram of Remark 0ER3 -/

section BaseChange

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : X' ⟶ X) (E : ClosedSubspaces D.site D.base D.base_mem X)

/-- **Remark 0ER3.** The closed subspace `D' ⊆ X'` of the diagram of Remark 0ER3: the inverse
image `f^{-1}(E)` of Stacks 083Q, which is the scheme-theoretic base change `E ×_X X'` by
`AlgebraicGeometry.Space.isPullback_gysinBaseChange`. -/
abbrev gysinBaseChangeSubspace : ClosedSubspaces D.site D.base D.base_mem X' :=
  ⟨E.1.preimage f, isClosedSubspace_preimage D.site D.base D.base_mem f E.1 hp.1 hp'.1 E.2⟩

/-- **Remark 0ER3.** The morphism `g : D' ⟶ D` of the diagram of Remark 0ER3: the canonical
projection of the inverse image onto `E`. -/
abbrev gysinBaseChangeHom :
    (gysinBaseChangeSubspace D p hp p' hp' f E).1.toFunctor ⟶ E.1.toFunctor :=
  E.1.fromPreimage f

/-- **Remark 0ER3.** The square of Remark 0ER3 is cartesian: `D'` is the fibre product
`D ×_X X'`, by Stacks 083Q. -/
@[stacks 083Q "the square of Remark 0ER3 is cartesian"]
theorem isPullback_gysinBaseChange :
    IsPullback (gysinBaseChangeHom D p hp p' hp' f E)
      (gysinBaseChangeSubspace D p hp p' hp' f E).1.ι E.1.ι f :=
  Subfunctor.isPullback_preimage f E.1

end BaseChange

/-- The corner of a cartesian square as in Remark 0ER3 is a space over `B` and the morphism
`g : D' ⟶ D` is a morphism over `B`: the square commutes and `f` is a morphism over `B`.  This is
what the pushforward and the pullback of cycles along `g` ask for. -/
theorem comp_structure_of_isPullback (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (p' : X' ⟶ D.space) {f : X' ⟶ X} (hfbase : f ≫ p = p')
    {E : ClosedSubspaces D.site D.base D.base_mem X}
    {E' : ClosedSubspaces D.site D.base D.base_mem X'}
    {g : E'.1.toFunctor ⟶ E.1.toFunctor} (hsq : IsPullback g E'.1.ι E.1.ι f) :
    g ≫ (E.1.ι ≫ p) = E'.1.ι ≫ p' := by
  rw [← Category.assoc, hsq.w, Category.assoc, hfbase]

/-! ### Stacks 0ER5: the Gysin map and proper pushforward -/

/-- The comparison datum of the source's proof of Stacks 0ER5: the identity of that lemma for a
prime cycle, read coefficientwise at the two component rules of Definition 0ER1.

The two cycles of Definition 0ER1(1) — `[D ∩ W]_k` of Stacks 0EE9 and `c₁(ℒ|_W) ∩ [W]` of
Stacks 0EQJ — are explicit parameters here, the fields of
`AlgebraicGeometry.Space.GysinComponentRule`; so `rule` on `X` and `rule'` on `X'` are unrelated
data, and this identity does not follow from the other hypotheses.  The source's proof supplies
the relation by the case analysis of Definition 0ER1.  For `W' ⊄ D'` it compares `[D ∩ W]_k`,
for `W` the closure of the image of `W'`, with `g_*[D' ∩ W']_k`, which is the proper pushforward
of the cycle of a closed subspace; `AlgebraicGeometry.Space.closedSubspaceCycle` and
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace` are not related to any morphism.  For
`W' ⊆ D'` it compares `c₁(ℒ|_W) ∩ [W]` with the pushforward of `c₁(ℒ'|_{W'}) ∩ [W']`, which is
Stacks 0EQS; the form of that lemma,
`AlgebraicGeometry.Space.properPushforward_divisorCycleOfSection`, is about the divisor cycle of a
meromorphic section, and does not apply to the free parameter
`AlgebraicGeometry.Space.GysinComponentRule.chernCycle` that stands for the cap product here.

This is the shape of `AlgebraicGeometry.Space.ProperFlatBaseChangeComparison`, the comparison
datum for Stacks 0EPD: one named coefficient identity at a prime cycle, with the passage to an
arbitrary cycle proved. -/
structure GysinProperPushforwardComparison (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : X' ⟶ X) (E : ClosedSubspaces D.site D.base D.base_mem X)
    (hE : D.IsGood (E.1.ι ≫ p)) (E' : ClosedSubspaces D.site D.base D.base_mem X')
    (hE' : D.IsGood (E'.1.ι ≫ p')) (g : E'.1.toFunctor ⟶ E.1.toFunctor) (k : ℤ)
    (rule : GysinComponentRule D p E k) (rule' : GysinComponentRule D p' E' k) where
  /-- **Stacks 0ER5 for a prime cycle, coefficientwise.**  For an integral closed subspace
  `W' ⊆ X'` of δ-dimension `k + 1` and an integral closed subspace `T ⊆ D`, the coefficient at
  `T` of `i^* f_* [W']` — the degree of Stacks 0EP1 times the component cycle of the closure of
  the image of `W'` — agrees with the coefficient at `T` of `g_* (i')^* [W']`. -/
  gysinCoeff_comm : ∀ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
    deltaDimension D p' W' = k + 1 →
    ∀ T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor,
      (∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
          properCycleMult D p' hp' p hp f W' W *
            (gysinComponentCycle D p E hE k rule W).1 T) =
        ∑ᶠ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
          (gysinComponentCycle D p' E' hE' k rule' W').1 T' *
            properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T

/-- Exchanging the sums in `∑ᶠ b, (∑ᶠ a, x a * m a b) * c b` when only finitely many pairs
contribute. -/
private theorem finsum_finsum_mul_mul_comm {A B : Type*} (x : A → ℤ) (m : A → B → ℤ) (c : B → ℤ)
    (h₁ : ∀ b, Function.HasFiniteSupport fun a => x a * m a b)
    (h₂ : {ab : A × B | x ab.1 * m ab.1 ab.2 * c ab.2 ≠ 0}.Finite)
    (h₃ : ∀ a, Function.HasFiniteSupport fun b => m a b * c b) :
    (∑ᶠ b, (∑ᶠ a, x a * m a b) * c b) = ∑ᶠ a, x a * ∑ᶠ b, m a b * c b := by
  rw [finsum_congr fun b => finsum_mul' _ _ (h₁ b),
    finsum_comm_of_finite (fun a b => x a * m a b * c b) h₂]
  exact finsum_congr fun a => by
    rw [mul_finsum' _ _ (h₃ a)]
    exact finsum_congr fun b => mul_assoc _ _ _

/-- The pairs `(a, b)` with `x a * w a b ≠ 0` form a finite set if the first components lie in a
finite set and each `w a` has finite support. -/
private theorem finite_mul_ne_zero_prod {A B : Type*} (x : A → ℤ) (w : A → B → ℤ) {s : Set A}
    (hs : s.Finite) (hw : ∀ a ∈ s, Function.HasFiniteSupport (w a))
    (hmem : ∀ a b, x a * w a b ≠ 0 → a ∈ s) : {ab : A × B | x ab.1 * w ab.1 ab.2 ≠ 0}.Finite := by
  refine (hs.prod (hs.biUnion (t := fun a => Function.support (w a)) hw)).subset ?_
  rintro ⟨a, b⟩ hne
  exact Set.mk_mem_prod (hmem a b hne)
    (Set.mem_biUnion (hmem a b hne) (Function.mem_support.2 (right_ne_zero_of_mul hne)))

/-- The pairing of the cycle `[W]` of an integral closed subspace with a family `F` is `F W`. -/
private theorem finsum_integralCycle_mul (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (p : X ⟶ D.space) (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hW : deltaDimension D p W = k)
    (F : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) :
    (∑ᶠ W', (integralCycle D p k W hW).1 W' * F W') = F W := by
  rw [finsum_eq_single _ W fun W'' hW'' => by
      rw [integralCycle_coe, integralCycleCoeff_eq_zero D W hW'', zero_mul],
    integralCycle_coe, integralCycleCoeff_self, one_mul]

section ProperPushforward

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    {f : X' ⟶ X} (hfbase : f ≫ p = p')
    (hfqc : IsQuasiCompact D.site D.base D.base_mem f)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p))
    (E' : ClosedSubspaces D.site D.base D.base_mem X') (hE' : D.IsGood (E'.1.ι ≫ p'))
    {g : E'.1.toFunctor ⟶ E.1.toFunctor} (hgbase : g ≫ (E.1.ι ≫ p) = E'.1.ι ≫ p')
    (hgqc : IsQuasiCompact D.site D.base D.base_mem g)
    (k : ℤ) (rule : GysinComponentRule D p E k) (rule' : GysinComponentRule D p' E' k)

include hp hp' hfbase hfqc hE hE' hgbase hgqc rule rule'

omit hfbase hfqc hE' hgbase hgqc rule' in
/-- Only the closure of the image of `|W'|` contributes to the Gysin coefficient of `f_*[W']`:
the multiplicity of Stacks 0EP1 vanishes at every other integral closed subspace of `X`. -/
theorem hasFiniteSupport_properCycleMult_mul_gysinComponentCycle
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    Function.HasFiniteSupport fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
      properCycleMult D p' hp' p hp f W' W *
        (gysinComponentCycle D p E hE k rule W).1 T := by
  refine (Set.finite_singleton (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
    hp.1 (D.isDecentSpace_of_isGood p hp) f W')).subset fun W hW => ?_
  have h1 : properCycleMult D p' hp' p hp f W' W ≠ 0 :=
    left_ne_zero_of_mul (Function.mem_support.1 hW)
  exact Set.mem_singleton_iff.2 (((properCycleMult_ne_zero_iff D p' hp' p hp f W' W).1 h1).1).symm

omit hE' hgbase hgqc rule' in
/-- At a fixed integral closed subspace `T ⊆ E` only finitely many pairs `(W', W)` of an integral
closed subspace of `X'` and one of `X` contribute to the Gysin coefficient of `f_*α'`.

A contributing pair has `W` for the closure of the image of `|W'|`, so `W` is determined by `W'`;
and the generic point of `T`, read in `|X|`, lies in `|W| = closure(|f|(|W'|))`.  Only finitely
many `W'` occurring in `α'` have that property, by Stacks 0ENZ. -/
theorem finite_properPushforwardGysinSupport (α' : CycleGroup D p' (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    {a : IntegralClosedSubspace D.site D.base D.base_mem X' ×
        IntegralClosedSubspace D.site D.base D.base_mem X |
      α'.1 a.1 * properCycleMult D p' hp' p hp f a.1 a.2 *
        (gysinComponentCycle D p E hE k rule a.2).1 T ≠ 0}.Finite := by
  obtain ⟨hlf, -⟩ := locallyFinite_closure_image_pointsMap D p' hp' p hp hfbase hfqc
    (cycleSupportFamily D α'.1) (isClosed_cycleSupportFamily D p' hp' α'.1) α'.2.1
  obtain ⟨V, hV, hVfin⟩ := hlf (pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι
    (T.ambientGenericPoint D.site D.base D.base_mem))
  refine (hVfin.image fun W' => (W', IntegralClosedSubspace.closureImage D.site D.base D.base_mem
    hp.1 (D.isDecentSpace_of_isGood p hp) f W')).subset ?_
  rintro ⟨W', W⟩ hne
  have hprod : α'.1 W' * properCycleMult D p' hp' p hp f W' W *
      (gysinComponentCycle D p E hE k rule W).1 T ≠ 0 := hne
  have hα : α'.1 W' ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hprod)
  have hm : properCycleMult D p' hp' p hp f W' W ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hprod)
  have hc : (gysinComponentCycle D p E hE k rule W).1 T ≠ 0 := right_ne_zero_of_mul hprod
  have hWeq : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
      (D.isDecentSpace_of_isGood p hp) f W' = W :=
    ((properCycleMult_ne_zero_iff D p' hp' p hp f W' W).1 hm).1
  refine ⟨W', ⟨_, ?_, mem_of_mem_nhds hV⟩, congrArg (Prod.mk W') hWeq⟩
  have hmem : pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι
      (T.ambientGenericPoint D.site D.base D.base_mem) ∈
      subspacePointSet D.site D.base D.base_mem X W.subspace :=
    subspacePointSet_subset_of_gysinComponentCycle_ne_zero D p E hE k rule W T hc ⟨_, rfl⟩
  rw [← hWeq, ← closure_image_cycleSupportFamily D p hp f α'.1 hα] at hmem
  exact hmem

omit hE' hgbase hgqc rule' in
/-- **The Gysin map of a proper pushforward, expanded.** The coefficient of `i^* f_* α'` at an
integral closed subspace `T ⊆ E` is the `α'`-weighted sum over the integral closed subspaces
`W' ⊆ X'` of the coefficient of `i^* f_* [W']` there.

Both the pushforward and the Gysin map are coefficientwise sums, so the composite is a double
sum, which is exchanged by `AlgebraicGeometry.Space.finite_properPushforwardGysinSupport`. -/
theorem gysinCoeff_properPushforward (α' : CycleGroup D p' (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    (gysinCycleMap D p E hE k rule
        (properCyclePushforward D p' hp' p hp hfbase hfqc (k + 1) α')).1 T =
      ∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
        α'.1 W' * ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
          properCycleMult D p' hp' p hp f W' W *
            (gysinComponentCycle D p E hE k rule W).1 T := by
  exact finsum_finsum_mul_mul_comm α'.1 (properCycleMult D p' hp' p hp f · ·)
    (fun W => (gysinComponentCycle D p E hE k rule W).1 T)
    (hasFiniteSupport_properCycleMult D p' hp' p hp hfbase hfqc α'.1 α'.2.1)
    (finite_properPushforwardGysinSupport D p hp p' hp' hfbase hfqc E hE k rule α' T)
    (hasFiniteSupport_properCycleMult_mul_gysinComponentCycle D p hp p' hp' E hE k rule · T)

omit hp hp' hfbase hfqc rule in
/-- Only finitely many integral closed subspaces of `E'` contribute to the coefficient at `T` of
the pushforward along `g` of the component cycle of a single `W' ⊆ X'`: a contributing one has
`T` for the closure of its image, and Stacks 0ENZ for `g` leaves finitely many of those in the
support of a cycle. -/
theorem hasFiniteSupport_gysinComponentCycle_mul_properCycleMult
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    Function.HasFiniteSupport
      fun T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor =>
        (gysinComponentCycle D p' E' hE' k rule' W').1 T' *
          properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T := by
  refine (finite_properCycleFibre D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc
    (gysinComponentCycle D p' E' hE' k rule' W').1
    (gysinComponentCycle D p' E' hE' k rule' W').2.1 T).subset fun T' hT' => ?_
  have h := Function.mem_support.1 hT'
  exact ⟨left_ne_zero_of_mul h,
    ((properCycleMult_ne_zero_iff D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T).1
      (right_ne_zero_of_mul h)).1⟩

omit hp hfbase hfqc rule in
/-- At a fixed integral closed subspace `T ⊆ E` only finitely many pairs `(W', T')` of an integral
closed subspace of `X'` and one of `E'` contribute to the coefficient of `g_* (i')^* α'`.

A contributing pair has `|T'| ⊆ |i'|^{-1}(|W'|)` and `|T| = closure(|g|(|T'|))`, so the generic
point of `T` lies in the closure of the image under `|g|` of the inverse image along `|i'|` of
`|W'|`.  Those inverse images form a locally finite collection on `|E'|` by Stacks 0EP6, so
Stacks 0ENZ for `g` leaves finitely many `W'`; and for each of them finitely many `T'` remain, by
`AlgebraicGeometry.Space.hasFiniteSupport_gysinComponentCycle_mul_properCycleMult`. -/
theorem finite_gysinProperPushforwardSupport (α' : CycleGroup D p' (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    {a : IntegralClosedSubspace D.site D.base D.base_mem X' ×
        IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor |
      α'.1 a.1 * (gysinComponentCycle D p' E' hE' k rule' a.1).1 a.2 *
        properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g a.2 T ≠ 0}.Finite := by
  obtain ⟨hlf, -⟩ := locallyFinite_closure_image_pointsMap D (E'.1.ι ≫ p') hE'
    (E.1.ι ≫ p) hE hgbase hgqc
    (fun W' : IntegralClosedSubspace D.site D.base D.base_mem X' =>
      pointsMap D.site D.base D.base_mem E'.1.toFunctor E'.1.ι ⁻¹'
        cycleSupportFamily D α'.1 W')
    (fun W' => isClosed_preimage_pointsMap D.site D.base D.base_mem hE'.1 hp'.1 E'.1.ι
      (isClosed_cycleSupportFamily D p' hp' α'.1 W'))
    (locallyFinite_preimage_pointsMap D.site D.base D.base_mem hE'.1 hp'.1 E'.1.ι
      (cycleSupportFamily D α'.1) α'.2.1)
  obtain ⟨V, hV, hVfin⟩ := hlf (T.ambientGenericPoint D.site D.base D.base_mem)
  simp only [mul_assoc]
  refine finite_mul_ne_zero_prod α'.1 _ hVfin
    (fun W' _ => hasFiniteSupport_gysinComponentCycle_mul_properCycleMult
      D p p' E hE E' hE' hgbase hgqc k rule' W' T) ?_
  intro W' T' hne
  have hα : α'.1 W' ≠ 0 := left_ne_zero_of_mul hne
  have hc : (gysinComponentCycle D p' E' hE' k rule' W').1 T' ≠ 0 :=
    left_ne_zero_of_mul (right_ne_zero_of_mul hne)
  have hm : properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T ≠ 0 :=
    right_ne_zero_of_mul (right_ne_zero_of_mul hne)
  have hTeq : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hE.1
      (D.isDecentSpace_of_isGood (E.1.ι ≫ p) hE) g T' = T :=
    ((properCycleMult_ne_zero_iff D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T).1 hm).1
  have hsub : subspacePointSet D.site D.base D.base_mem E'.1.toFunctor T'.subspace ⊆
      pointsMap D.site D.base D.base_mem E'.1.toFunctor E'.1.ι ⁻¹'
        cycleSupportFamily D α'.1 W' := by
    rw [cycleSupportFamily_of_ne_zero D α'.1 hα]
    exact subspacePointSet_subset_of_gysinComponentCycle_ne_zero D p' E' hE' k rule' W' T' hc
  have hmemW' : (T.ambientGenericPoint D.site D.base D.base_mem) ∈
      closure (pointsMap D.site D.base D.base_mem E'.1.toFunctor g ''
        (pointsMap D.site D.base D.base_mem E'.1.toFunctor E'.1.ι ⁻¹'
          cycleSupportFamily D α'.1 W')) := by
    refine closure_mono (Set.image_mono hsub) ?_
    rw [← IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hE.1
      (D.isDecentSpace_of_isGood (E.1.ι ≫ p) hE) g T', hTeq]
    exact ⟨_, rfl⟩
  exact ⟨_, hmemW', mem_of_mem_nhds hV⟩

omit hp hfbase hfqc rule in
/-- **The pushforward of a Gysin map, expanded.** The coefficient of `g_* (i')^* α'` at an
integral closed subspace `T ⊆ E` is the `α'`-weighted sum over the integral closed subspaces
`W' ⊆ X'` of the coefficient of `g_* (i')^* [W']` there. -/
theorem properPushforward_gysinCoeff (α' : CycleGroup D p' (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    (properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
        (gysinCycleMap D p' E' hE' k rule' α')).1 T =
      ∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
        α'.1 W' * ∑ᶠ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
          (gysinComponentCycle D p' E' hE' k rule' W').1 T' *
            properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T := by
  exact finsum_finsum_mul_mul_comm α'.1
    (fun W' T' => (gysinComponentCycle D p' E' hE' k rule' W').1 T')
    (fun T' => properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T)
    (hasFiniteSupport_gysinCoeff D p' E' hE' k rule' α')
    (finite_gysinProperPushforwardSupport D p p' hp' E hE E' hE' hgbase hgqc k rule' α' T)
    (hasFiniteSupport_gysinComponentCycle_mul_properCycleMult
      D p p' E hE E' hE' hgbase hgqc k rule' · T)

omit hE' hgbase hgqc rule' in
/-- The coefficient of `i^* f_* [W']` at an integral closed subspace `T ⊆ E`, for the cycle of a
single integral closed subspace `W' ⊆ X'` of δ-dimension `k + 1`. -/
theorem gysinCoeff_properPushforward_integralCycle
    {W' : IntegralClosedSubspace D.site D.base D.base_mem X'}
    (hW' : deltaDimension D p' W' = k + 1)
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    (gysinCycleMap D p E hE k rule (properCyclePushforward D p' hp' p hp hfbase hfqc (k + 1)
        (integralCycle D p' (k + 1) W' hW'))).1 T =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        properCycleMult D p' hp' p hp f W' W *
          (gysinComponentCycle D p E hE k rule W).1 T := by
  rw [gysinCoeff_properPushforward D p hp p' hp' hfbase hfqc E hE k rule
      (integralCycle D p' (k + 1) W' hW') T,
    finsum_integralCycle_mul]

omit hp hfbase hfqc rule in
/-- The coefficient of `g_* (i')^* [W']` at an integral closed subspace `T ⊆ E`, for the cycle of
a single integral closed subspace `W' ⊆ X'` of δ-dimension `k + 1`. -/
theorem properPushforward_gysinCoeff_integralCycle
    {W' : IntegralClosedSubspace D.site D.base D.base_mem X'}
    (hW' : deltaDimension D p' W' = k + 1)
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    (properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
        (gysinCycleMap D p' E' hE' k rule' (integralCycle D p' (k + 1) W' hW'))).1 T =
      ∑ᶠ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
        (gysinComponentCycle D p' E' hE' k rule' W').1 T' *
          properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T := by
  rw [properPushforward_gysinCoeff D p p' hp' E hE E' hE' hgbase hgqc k rule'
      (integralCycle D p' (k + 1) W' hW') T,
    finsum_integralCycle_mul]

/-- **Stacks 0ER5.** In Situation 0EDT let `f : X' ⟶ X` be a proper morphism of good algebraic
spaces over `B`, let `(ℒ, s, i : E → X)` be as in Definition 0ER1, and form the diagram of
Remark 0ER3, with `E' = E ×_X X'`, `g : E' ⟶ E` and `i' : E' ⟶ X'`.  Then for every
`(k+1)`-cycle `α'` on `X'`

  `i^* f_* α' = g_* (i')^* α'`,

an identity of `k`-cycles on `E`, hence of classes in `CH_k(E)`.

Only quasi-compactness of `f` and of `g` is used, through Stacks 0ENZ; properness, which the
source assumes and from which it gets `g` proper by base change, is not needed for the
pushforwards themselves.  `_hsq` is the cartesian square of Remark 0ER3, which makes `E'` the
scheme-theoretic base change `E ×_X X'`; `hgbase` says that `g` is a morphism over `B`, and is
implied by `_hsq` through `AlgebraicGeometry.Space.comp_structure_of_isPullback`.

**The single-subspace case is the hypothesis `hprime`**, which is this identity for the cycle
`[W']` of one integral closed subspace of δ-dimension `k + 1`: the source proves it by a case
analysis carried out with the two component inputs of Stacks 0ER1, which are explicit parameters
here.  What is proved is its extension over an arbitrary cycle, which is not formal — see the
implementation notes of this file. -/
theorem gysinCycleMap_properPushforward_eq (_hsq : IsPullback g E'.1.ι E.1.ι f)
    (hprime : ∀ (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
      (hW' : deltaDimension D p' W' = k + 1),
      gysinCycleMap D p E hE k rule (properCyclePushforward D p' hp' p hp hfbase hfqc (k + 1)
          (integralCycle D p' (k + 1) W' hW')) =
        properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
          (gysinCycleMap D p' E' hE' k rule' (integralCycle D p' (k + 1) W' hW')))
    (α' : CycleGroup D p' (k + 1)) :
    gysinCycleMap D p E hE k rule (properCyclePushforward D p' hp' p hp hfbase hfqc (k + 1) α') =
      properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
        (gysinCycleMap D p' E' hE' k rule' α') := by
  refine Subtype.ext (funext fun T => ?_)
  rw [gysinCoeff_properPushforward D p hp p' hp' hfbase hfqc E hE k rule α' T,
    properPushforward_gysinCoeff D p p' hp' E hE E' hE' hgbase hgqc k rule'
      α' T]
  refine finsum_congr fun W' => ?_
  by_cases h0 : α'.1 W' = 0
  · rw [h0, zero_mul, zero_mul]
  · rw [← gysinCoeff_properPushforward_integralCycle D p hp p' hp' hfbase hfqc E hE k rule
        (α'.2.2 W' h0) T,
      ← properPushforward_gysinCoeff_integralCycle D p p' hp' E hE E' hE' hgbase hgqc k rule'
        (α'.2.2 W' h0) T,
      hprime W' (α'.2.2 W' h0)]

/-- **Stacks 0ER5 for a prime cycle.**  On the cycle `[W']` of a single integral closed subspace
`W' ⊆ X'` of δ-dimension `k + 1` the identity `i^* f_* [W'] = g_* (i')^* [W']` holds.

Both sides are computed here; what the comparison datum supplies is their agreement, which is
the source's case analysis on `W' ⊆ D'` carried out with the two component inputs of
Definition 0ER1. -/
theorem gysinCycleMap_properPushforward_integralCycle_eq
    (cmp : GysinProperPushforwardComparison D p hp p' hp' f E hE E' hE' g k rule rule')
    {W' : IntegralClosedSubspace D.site D.base D.base_mem X'}
    (hW' : deltaDimension D p' W' = k + 1) :
    gysinCycleMap D p E hE k rule (properCyclePushforward D p' hp' p hp hfbase hfqc (k + 1)
        (integralCycle D p' (k + 1) W' hW')) =
      properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
        (gysinCycleMap D p' E' hE' k rule' (integralCycle D p' (k + 1) W' hW')) := by
  refine Subtype.ext (funext fun T => ?_)
  rw [gysinCoeff_properPushforward_integralCycle D p hp p' hp' hfbase hfqc E hE k rule hW' T,
    properPushforward_gysinCoeff_integralCycle D p p' hp' E hE E' hE' hgbase hgqc k rule' hW' T]
  exact cmp.gysinCoeff_comm W' hW' T

/-- **Stacks 0ER5.** In Situation 0EDT let `f : X' ⟶ X` be a proper morphism of good algebraic
spaces over `B`, let `(ℒ, s, i : E → X)` be as in Definition 0ER1, and form the diagram of
Remark 0ER3, with `E' = E ×_X X'`, `g : E' ⟶ E` and `i' : E' ⟶ X'`.  Then for every
`(k+1)`-cycle `α'` on `X'`

  `i^* f_* α' = g_* (i')^* α'`,

an identity of `k`-cycles on `E`, hence of classes in `CH_k(E)`.

`hsq` is the cartesian square of Remark 0ER3, which makes `E'` the scheme-theoretic base change
`E ×_X X'`.  Only quasi-compactness of `f` and of `g` is used, through Stacks 0ENZ; properness,
which the source assumes and from which it gets `g` proper by base change, is not needed for the
pushforwards themselves.

The single hypothesis beyond the setup is `cmp`, the comparison datum
`AlgebraicGeometry.Space.GysinProperPushforwardComparison`, whose docstring explains why it does
not follow from the other data.  Everything else — in particular the passage from the
prime cycles of the source's case analysis to an arbitrary cycle, which is not formal because a
cycle is an infinite formal sum — is proved. -/
@[stacks 0ER5 "i^*f_*α' = g_*(i')^*α' at the level of cycles, on the single carried input
GysinProperPushforwardComparison: the source's prime-cycle case analysis read coefficientwise at
the two component parameters of Definition 0ER1"]
theorem gysinCycleMap_properPushforward_eq_of_comparison
    (cmp : GysinProperPushforwardComparison D p hp p' hp' f E hE E' hE' g k rule rule')
    (hsq : IsPullback g E'.1.ι E.1.ι f) (α' : CycleGroup D p' (k + 1)) :
    gysinCycleMap D p E hE k rule (properCyclePushforward D p' hp' p hp hfbase hfqc (k + 1) α') =
      properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
        (gysinCycleMap D p' E' hE' k rule' α') :=
  gysinCycleMap_properPushforward_eq D p hp p' hp' hfbase hfqc E hE E' hE' hgbase hgqc k rule
    rule' hsq (fun _ hW' => gysinCycleMap_properPushforward_integralCycle_eq D p hp p' hp'
      hfbase hfqc E hE E' hE' hgbase hgqc k rule rule' cmp hW') α'

end ProperPushforward

/-! ### Stacks 0ER6: the Gysin map and flat pullback -/

/-- The comparison datum of the source's proof of Stacks 0ER6: the identity of that lemma for a
prime cycle, read coefficientwise at the two component rules of Definition 0ER1.

This identity does not follow from the other hypotheses, for the same reason as in
`AlgebraicGeometry.Space.GysinProperPushforwardComparison`: the two cycles of Definition
0ER1(1) are the free fields of `AlgebraicGeometry.Space.GysinComponentRule`, so `rule` on `X`
and `rule'` on `X'` are unrelated data.  The source supplies the relation by the case analysis
of Definition 0ER1.  For `W ⊄ D` it compares `f^*[D ∩ W]_k` with `[D' ∩ f^{-1}(W)]_{k+r}`, which
is the flat pullback of the cycle of a closed subspace.  For `W ⊆ D` it compares the pullback of
`c₁(ℒ|_W) ∩ [W]` with `c₁(ℒ'|_{f^{-1}(W)}) ∩ [f^{-1}(W)]`, which is Stacks 0EQR; the form of
that lemma, `AlgebraicGeometry.Space.flatCyclePullback_firstChernCapCycleMap`, is about its own
component cycle, built from Stacks 0EQE, and does not apply to the free parameter
`AlgebraicGeometry.Space.GysinComponentRule.chernCycle` that stands for the cap product here. -/
structure GysinFlatPullbackComparison (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : X' ⟶ X) (hfbase : f ≫ p = p') (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p))
    (E' : ClosedSubspaces D.site D.base D.base_mem X') (hE' : D.IsGood (E'.1.ι ≫ p'))
    (g : E'.1.toFunctor ⟶ E.1.toFunctor) (hgbase : g ≫ (E.1.ι ≫ p) = E'.1.ι ≫ p')
    (hgflat : IsFlat D.site D.base D.base_mem g)
    (hgr : HasRelativeDimension r D.site D.base D.base_mem g)
    (k : ℤ) (rule : GysinComponentRule D p E k)
    (rule' : GysinComponentRule D p' E' (k + (r : ℤ))) where
  /-- **Stacks 0ER6 for a prime cycle, coefficientwise.**  For an integral closed subspace
  `W ⊆ X` of δ-dimension `k + 1` and an integral closed subspace `T' ⊆ D'`, the coefficient at
  `T'` of `(i')^* f^* [W]` agrees with the coefficient at `T'` of `g^* i^* [W]`. -/
  gysinCoeff_comm : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
    deltaDimension D p W = k + 1 →
    ∀ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
      (∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
          flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' *
            (gysinComponentCycle D p' E' hE' (k + (r : ℤ)) rule' W').1 T') =
        ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor,
          (gysinComponentCycle D p E hE k rule W).1 T *
            flatPullbackMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr T T'

section FlatPullback

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    {f : X' ⟶ X} (hfbase : f ≫ p = p') (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p))
    (E' : ClosedSubspaces D.site D.base D.base_mem X') (hE' : D.IsGood (E'.1.ι ≫ p'))
    {g : E'.1.toFunctor ⟶ E.1.toFunctor} (hgbase : g ≫ (E.1.ι ≫ p) = E'.1.ι ≫ p')
    (hgflat : IsFlat D.site D.base D.base_mem g)
    (hgr : HasRelativeDimension r D.site D.base D.base_mem g)
    (k : ℤ) (rule : GysinComponentRule D p E k)
    (rule' : GysinComponentRule D p' E' (k + (r : ℤ)))

include hp hp' hfbase hflat hr hE hE' hgbase hgflat hgr rule rule'

omit hE hgbase hgflat hgr rule in
/-- Only finitely many integral closed subspaces of `X'` contribute to the Gysin coefficient at
`T'` of the cycle `f^*[W]` of a single `W ⊆ X`: a contributing one occurs in that cycle and
contains the image in `|X'|` of the generic point of `T'`, and the support of a cycle is locally
finite. -/
theorem hasFiniteSupport_flatPullbackMult_mul_gysinComponentCycle
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor) :
    Function.HasFiniteSupport fun W' : IntegralClosedSubspace D.site D.base D.base_mem X' =>
      flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' *
        (gysinComponentCycle D p' E' hE' (k + (r : ℤ)) rule' W').1 T' := by
  obtain ⟨V, hV, hVfin⟩ :=
    (flatPullbackIntegralCycle D p' hp' p hp f hfbase r hflat hr W).2.1
      (pointsMap D.site D.base D.base_mem E'.1.toFunctor E'.1.ι
        (T'.ambientGenericPoint D.site D.base D.base_mem))
  refine hVfin.subset fun W' hW' => ?_
  have h := Function.mem_support.1 hW'
  refine ⟨_, ?_, mem_of_mem_nhds hV⟩
  simp only [Set.mem_ite_empty_left]
  exact ⟨left_ne_zero_of_mul h,
    subspacePointSet_subset_of_gysinComponentCycle_ne_zero D p' E' hE' (k + (r : ℤ)) rule' W' T'
      (right_ne_zero_of_mul h) ⟨_, rfl⟩⟩

omit hE hgbase hgflat hgr rule in
/-- At a fixed integral closed subspace `T' ⊆ E'` only finitely many pairs `(W, W')` of an
integral closed subspace of `X` and one of `X'` contribute to the Gysin coefficient of `f^*α`.

A contributing pair has the generic point of `T'`, read in `|X'|`, inside `|W'| ⊆ |f|^{-1}(|W|)`,
so `W` contains the image of that point and only finitely many such `W` occur in `α`; for each of
them only finitely many `W'` remain, by
`AlgebraicGeometry.Space.hasFiniteSupport_flatPullbackMult_mul_gysinComponentCycle`. -/
theorem finite_flatPullbackGysinSupport (α : CycleGroup D p (k + 1))
    (T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor) :
    {a : IntegralClosedSubspace D.site D.base D.base_mem X ×
        IntegralClosedSubspace D.site D.base D.base_mem X' |
      α.1 a.1 * flatPullbackMult D p' hp' p hp f hfbase r hflat hr a.1 a.2 *
        (gysinComponentCycle D p' E' hE' (k + (r : ℤ)) rule' a.2).1 T' ≠ 0}.Finite := by
  obtain ⟨V, hV, hVfin⟩ := α.2.1 (pointsMap D.site D.base D.base_mem X' f
    (pointsMap D.site D.base D.base_mem E'.1.toFunctor E'.1.ι
      (T'.ambientGenericPoint D.site D.base D.base_mem)))
  simp only [mul_assoc]
  refine finite_mul_ne_zero_prod α.1 _ hVfin
    (fun W _ => hasFiniteSupport_flatPullbackMult_mul_gysinComponentCycle D p hp p' hp' hfbase r
      hflat hr E' hE' k rule' W T') ?_
  intro W W' hne
  have hα : α.1 W ≠ 0 := left_ne_zero_of_mul hne
  have hμ : flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' ≠ 0 :=
    left_ne_zero_of_mul (right_ne_zero_of_mul hne)
  have hc : (gysinComponentCycle D p' E' hE' (k + (r : ℤ)) rule' W').1 T' ≠ 0 :=
    right_ne_zero_of_mul (right_ne_zero_of_mul hne)
  have hz : pointsMap D.site D.base D.base_mem E'.1.toFunctor E'.1.ι
      (T'.ambientGenericPoint D.site D.base D.base_mem) ∈
      subspacePointSet D.site D.base D.base_mem X' W'.subspace :=
    subspacePointSet_subset_of_gysinComponentCycle_ne_zero D p' E' hE' (k + (r : ℤ)) rule' W' T'
      hc ⟨_, rfl⟩
  refine ⟨_, ?_, mem_of_mem_nhds hV⟩
  simp only [Set.mem_ite_empty_left]
  exact ⟨hα, subspacePointSet_subset_of_flatPullbackMult_ne_zero D p' hp' p hp f hfbase r hflat
    hr W W' hμ hz⟩

omit hE hgbase hgflat hgr rule in
/-- **The Gysin map of a flat pullback, expanded.** The coefficient of `(i')^* f^* α` at an
integral closed subspace `T' ⊆ E'` is the `α`-weighted sum over the integral closed subspaces
`W ⊆ X` of the coefficient of `(i')^* f^* [W]` there. -/
theorem gysinCoeff_flatPullback (hkr : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
    (α : CycleGroup D p (k + 1))
    (T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor) :
    (gysinCycleMap D p' E' hE' (k + (r : ℤ)) rule'
        (flatPullbackMap D p' hp' p hp f hfbase r hflat hr (k + 1) (k + (r : ℤ) + 1)
          hkr α)).1 T' =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        α.1 W * ∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
          flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' *
            (gysinComponentCycle D p' E' hE' (k + (r : ℤ)) rule' W').1 T' := by
  exact finsum_finsum_mul_mul_comm α.1
    (flatPullbackMult D p' hp' p hp f hfbase r hflat hr · ·)
    (fun W' => (gysinComponentCycle D p' E' hE' (k + (r : ℤ)) rule' W').1 T')
    (finite_support_flatPullbackTerm D p' hp' p hp f hfbase r hflat hr (k + 1) α)
    (finite_flatPullbackGysinSupport D p hp p' hp' hfbase r hflat hr E' hE' k rule' α T')
    (hasFiniteSupport_flatPullbackMult_mul_gysinComponentCycle D p hp p' hp' hfbase r hflat hr
      E' hE' k rule' · T')

omit hp hp' hfbase hflat hr rule' in
/-- Only finitely many integral closed subspaces of `E` contribute to the coefficient at `T'` of
the flat pullback along `g` of the component cycle of a single `W ⊆ X`: a contributing one occurs
in that component cycle and contains the image under `|g|` of the generic point of `T'`. -/
theorem hasFiniteSupport_gysinComponentCycle_mul_flatPullbackMult
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor) :
    Function.HasFiniteSupport
      fun T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor =>
        (gysinComponentCycle D p E hE k rule W).1 T *
          flatPullbackMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr T T' := by
  obtain ⟨V, hV, hVfin⟩ := (gysinComponentCycle D p E hE k rule W).2.1
    (pointsMap D.site D.base D.base_mem E'.1.toFunctor g
      (T'.ambientGenericPoint D.site D.base D.base_mem))
  refine hVfin.subset fun T hT => ?_
  have h := Function.mem_support.1 hT
  refine ⟨_, ?_, mem_of_mem_nhds hV⟩
  simp only [Set.mem_ite_empty_left]
  exact ⟨left_ne_zero_of_mul h, mem_subspacePointSet_of_flatPullbackMult_ne_zero
    D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr T T'
    (right_ne_zero_of_mul h)⟩

omit hp hp' hfbase hflat hr rule' in
/-- At a fixed integral closed subspace `T' ⊆ E'` only finitely many pairs `(W, T)` of an integral
closed subspace of `X` and one of `E` contribute to the coefficient of `g^* i^* α`.

A contributing pair has the generic point of `T'` carried by `|g|` into `|T|`, and `|T|` carried
by `|i|` into `|W|`, so `W` contains the image in `|X|` of that point and only finitely many such
`W` occur in `α`; for each of them only finitely many `T` remain, by
`AlgebraicGeometry.Space.hasFiniteSupport_gysinComponentCycle_mul_flatPullbackMult`. -/
theorem finite_gysinFlatPullbackSupport (α : CycleGroup D p (k + 1))
    (T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor) :
    {a : IntegralClosedSubspace D.site D.base D.base_mem X ×
        IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor |
      α.1 a.1 * (gysinComponentCycle D p E hE k rule a.1).1 a.2 *
        flatPullbackMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr a.2 T'
          ≠ 0}.Finite := by
  obtain ⟨V, hV, hVfin⟩ := α.2.1 (pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι
    (pointsMap D.site D.base D.base_mem E'.1.toFunctor g
      (T'.ambientGenericPoint D.site D.base D.base_mem)))
  simp only [mul_assoc]
  refine finite_mul_ne_zero_prod α.1 _ hVfin
    (fun W _ => hasFiniteSupport_gysinComponentCycle_mul_flatPullbackMult D p p' r E hE E' hE'
      hgbase hgflat hgr k rule W T') ?_
  intro W T hne
  have hα : α.1 W ≠ 0 := left_ne_zero_of_mul hne
  have hc : (gysinComponentCycle D p E hE k rule W).1 T ≠ 0 :=
    left_ne_zero_of_mul (right_ne_zero_of_mul hne)
  have hμ : flatPullbackMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr T T'
      ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul hne)
  have ht : pointsMap D.site D.base D.base_mem E'.1.toFunctor g
      (T'.ambientGenericPoint D.site D.base D.base_mem) ∈
      subspacePointSet D.site D.base D.base_mem E.1.toFunctor T.subspace :=
    mem_subspacePointSet_of_flatPullbackMult_ne_zero D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase
      r hgflat hgr T T' hμ
  refine ⟨_, ?_, mem_of_mem_nhds hV⟩
  simp only [Set.mem_ite_empty_left]
  exact ⟨hα, subspacePointSet_subset_of_gysinComponentCycle_ne_zero D p E hE k rule W T hc ht⟩

omit hp hp' hfbase hflat hr rule' in
/-- **The flat pullback of a Gysin map, expanded.** The coefficient of `g^* i^* α` at an integral
closed subspace `T' ⊆ E'` is the `α`-weighted sum over the integral closed subspaces `W ⊆ X` of
the coefficient of `g^* i^* [W]` there. -/
theorem flatPullback_gysinCoeff (α : CycleGroup D p (k + 1))
    (T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor) :
    (flatPullbackMap D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr k
        (k + (r : ℤ)) rfl (gysinCycleMap D p E hE k rule α)).1 T' =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        α.1 W * ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor,
          (gysinComponentCycle D p E hE k rule W).1 T *
            flatPullbackMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr T T' := by
  exact finsum_finsum_mul_mul_comm α.1
    (fun W T => (gysinComponentCycle D p E hE k rule W).1 T)
    (fun T => flatPullbackMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr T T')
    (hasFiniteSupport_gysinCoeff D p E hE k rule α)
    (finite_gysinFlatPullbackSupport D p p' r E hE E' hE' hgbase hgflat hgr k rule α T')
    (hasFiniteSupport_gysinComponentCycle_mul_flatPullbackMult D p p' r E hE E' hE' hgbase hgflat
      hgr k rule · T')

omit hE hgbase hgflat hgr rule in
/-- The coefficient of `(i')^* f^* [W]` at an integral closed subspace `T' ⊆ E'`, for the cycle of
a single integral closed subspace `W ⊆ X` of δ-dimension `k + 1`. -/
theorem gysinCoeff_flatPullback_integralCycle (hkr : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor) :
    (gysinCycleMap D p' E' hE' (k + (r : ℤ)) rule'
        (flatPullbackMap D p' hp' p hp f hfbase r hflat hr (k + 1) (k + (r : ℤ) + 1)
          hkr (integralCycle D p (k + 1) W hW))).1 T' =
      ∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X',
        flatPullbackMult D p' hp' p hp f hfbase r hflat hr W W' *
          (gysinComponentCycle D p' E' hE' (k + (r : ℤ)) rule' W').1 T' := by
  rw [gysinCoeff_flatPullback D p hp p' hp' hfbase r hflat hr E' hE' k rule' hkr
      (integralCycle D p (k + 1) W hW) T',
    finsum_integralCycle_mul]

omit hp hp' hfbase hflat hr rule' in
/-- The coefficient of `g^* i^* [W]` at an integral closed subspace `T' ⊆ E'`, for the cycle of a
single integral closed subspace `W ⊆ X` of δ-dimension `k + 1`. -/
theorem flatPullback_gysinCoeff_integralCycle
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor) :
    (flatPullbackMap D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr k
        (k + (r : ℤ)) rfl
        (gysinCycleMap D p E hE k rule (integralCycle D p (k + 1) W hW))).1 T' =
      ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor,
        (gysinComponentCycle D p E hE k rule W).1 T *
          flatPullbackMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr T T' := by
  rw [flatPullback_gysinCoeff D p p' r E hE E' hE' hgbase hgflat hgr k rule
      (integralCycle D p (k + 1) W hW) T',
    finsum_integralCycle_mul]

/-- **Stacks 0ER6.** In Situation 0EDT let `f : X' ⟶ X` be a flat morphism of relative dimension
`r` of good algebraic spaces over `B`, let `(ℒ, s, i : E → X)` be as in Definition 0ER1, and form
the diagram of Remark 0ER3, with `E' = E ×_X X'`, `g : E' ⟶ E` and `i' : E' ⟶ X'`.  Then for every
`(k+1)`-cycle `α` on `X`

  `(i')^* f^* α = g^* i^* α`,

an identity of `(k+r)`-cycles on `E'`, hence of classes in `CH_{k+r}(E')`.

Flatness of `g` and its relative dimension `r` are hypotheses: the source gets them from `f` by
base change along `i`.  `_hsq` is the
cartesian square of Remark 0ER3, which makes `E'` the scheme-theoretic base change `E ×_X X'`;
`hgbase` says that `g` is a morphism over `B`, and is implied by `_hsq` through
`AlgebraicGeometry.Space.comp_structure_of_isPullback`.

**The single-subspace case is the hypothesis `hprime`**, which is this identity for the cycle
`[W]` of one integral closed subspace of δ-dimension `k + 1`: the source proves it by a case
analysis carried out with the two component inputs of Stacks 0ER1, which are explicit parameters
here.  What is proved is its extension over an arbitrary cycle, which is not formal — see the
implementation notes of this file. -/
theorem gysinCycleMap_flatPullbackMap_eq (hkr : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
    (_hsq : IsPullback g E'.1.ι E.1.ι f)
    (hprime : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1),
      gysinCycleMap D p' E' hE' (k + (r : ℤ)) rule'
          (flatPullbackMap D p' hp' p hp f hfbase r hflat hr (k + 1) (k + (r : ℤ) + 1)
            hkr (integralCycle D p (k + 1) W hW)) =
        flatPullbackMap D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr k
          (k + (r : ℤ)) rfl
          (gysinCycleMap D p E hE k rule (integralCycle D p (k + 1) W hW)))
    (α : CycleGroup D p (k + 1)) :
    gysinCycleMap D p' E' hE' (k + (r : ℤ)) rule'
        (flatPullbackMap D p' hp' p hp f hfbase r hflat hr (k + 1) (k + (r : ℤ) + 1)
          hkr α) =
      flatPullbackMap D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr k
        (k + (r : ℤ)) rfl (gysinCycleMap D p E hE k rule α) := by
  refine Subtype.ext (funext fun T' => ?_)
  rw [gysinCoeff_flatPullback D p hp p' hp' hfbase r hflat hr E' hE' k rule' hkr α T',
    flatPullback_gysinCoeff D p p' r E hE E' hE' hgbase hgflat hgr k rule α T']
  refine finsum_congr fun W => ?_
  by_cases h0 : α.1 W = 0
  · rw [h0, zero_mul, zero_mul]
  · rw [← gysinCoeff_flatPullback_integralCycle D p hp p' hp' hfbase r hflat hr E' hE' k rule'
        hkr (α.2.2 W h0) T',
      ← flatPullback_gysinCoeff_integralCycle D p p' r E hE E' hE' hgbase hgflat hgr k rule
        (α.2.2 W h0) T',
      hprime W (α.2.2 W h0)]

/-- **Stacks 0ER6 for a prime cycle.**  On the cycle `[W]` of a single integral closed subspace
`W ⊆ X` of δ-dimension `k + 1` the identity `(i')^* f^* [W] = g^* i^* [W]` holds.

Both sides are computed here; what the comparison datum supplies is their agreement, which is
the source's case analysis on `W ⊆ D` carried out with the two component inputs of
Definition 0ER1. -/
theorem gysinCycleMap_flatPullbackMap_integralCycle_eq
    (hkr : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
    (cmp : GysinFlatPullbackComparison D p hp p' hp' f hfbase r hflat hr E hE E' hE' g hgbase
      hgflat hgr k rule rule')
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) :
    gysinCycleMap D p' E' hE' (k + (r : ℤ)) rule'
        (flatPullbackMap D p' hp' p hp f hfbase r hflat hr (k + 1) (k + (r : ℤ) + 1)
          hkr (integralCycle D p (k + 1) W hW)) =
      flatPullbackMap D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr k
        (k + (r : ℤ)) rfl
        (gysinCycleMap D p E hE k rule (integralCycle D p (k + 1) W hW)) := by
  refine Subtype.ext (funext fun T' => ?_)
  rw [gysinCoeff_flatPullback_integralCycle D p hp p' hp' hfbase r hflat hr E' hE' k rule' hkr
      hW T',
    flatPullback_gysinCoeff_integralCycle D p p' r E hE E' hE' hgbase hgflat hgr k rule hW T']
  exact cmp.gysinCoeff_comm W hW T'

/-- **Stacks 0ER6.** In Situation 0EDT let `f : X' ⟶ X` be a flat morphism of relative dimension
`r` of good algebraic spaces over `B`, let `(ℒ, s, i : E → X)` be as in Definition 0ER1, and form
the diagram of Remark 0ER3, with `E' = E ×_X X'`, `g : E' ⟶ E` and `i' : E' ⟶ X'`.  Then for every
`(k+1)`-cycle `α` on `X`

  `(i')^* f^* α = g^* i^* α`,

an identity of `(k+r)`-cycles on `E'`, hence of classes in `CH_{k+r}(E')`.

`hsq` is the cartesian square of Remark 0ER3, which makes `E'` the scheme-theoretic base change
`E ×_X X'`.  Flatness of `g` and its relative dimension `r` are hypotheses: the source gets them
from `f` by base change along `i`.
`hkr` is the degree bookkeeping `(k+1) + r = (k+r) + 1`, which is the convention of
`AlgebraicGeometry.Space.flatPullbackMap`.

The single hypothesis beyond the setup is `cmp`, the comparison datum
`AlgebraicGeometry.Space.GysinFlatPullbackComparison`, whose docstring explains why it does not
follow from the other data.  Everything else — in particular the passage from the
prime cycles of the source's case analysis to an arbitrary cycle, which is not formal because a
cycle is an infinite formal sum — is proved. -/
@[stacks 0ER6 "(i')^*f^*α = g^*i^*α at the level of cycles, on the single carried input
GysinFlatPullbackComparison: the source's prime-cycle case analysis read coefficientwise at the
two component parameters of Definition 0ER1"]
theorem gysinCycleMap_flatPullbackMap_eq_of_comparison
    (hkr : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
    (cmp : GysinFlatPullbackComparison D p hp p' hp' f hfbase r hflat hr E hE E' hE' g hgbase
      hgflat hgr k rule rule')
    (hsq : IsPullback g E'.1.ι E.1.ι f) (α : CycleGroup D p (k + 1)) :
    gysinCycleMap D p' E' hE' (k + (r : ℤ)) rule'
        (flatPullbackMap D p' hp' p hp f hfbase r hflat hr (k + 1) (k + (r : ℤ) + 1)
          hkr α) =
      flatPullbackMap D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g hgbase r hgflat hgr k
        (k + (r : ℤ)) rfl (gysinCycleMap D p E hE k rule α) :=
  gysinCycleMap_flatPullbackMap_eq D p hp p' hp' hfbase r hflat hr E hE E' hE' hgbase hgflat
    hgr k rule rule' hkr hsq (fun _ hW => gysinCycleMap_flatPullbackMap_integralCycle_eq D p
      hp p' hp' hfbase r hflat hr E hE E' hE' hgbase hgflat hgr k rule rule' hkr cmp hW) α

end FlatPullback

end AlgebraicGeometry.Space

end
