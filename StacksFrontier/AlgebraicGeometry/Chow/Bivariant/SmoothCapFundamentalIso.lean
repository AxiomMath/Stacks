module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksCore.Tactic.StacksAttribute

/-!
# Chow cohomology of a smooth equidimensional scheme and cap product with its fundamental class

Let `k` be a field and let `X` be a smooth scheme over `k`, equidimensional of dimension `d`.
**Stacks 0FC2** says that

  `A^p(X) ⟶ CH_{d-p}(X)`,  `c ↦ c ∩ [X]_d`,

is an isomorphism, and that under it composition of bivariant classes becomes the intersection
product.

This file constructs that map and reduces its injectivity, by Stacks 02UC, to a single
statement about the cap operation. What is *not* here is the bijectivity and the compatibility
with composition; see the implementation notes for why neither is reachable in this repository.

## Main definitions

* `Stacks.Chow.selfFundamentalClass` — the fundamental class `[X]_d`, in the form in which the
  cap operation of a class in `A^p(X) = A^p(X ⟶ X)` consumes it.
* `Stacks.Chow.chowGroupSelfUnitCollapse` — the collapse `CH_{d-p}(X ×_X X) ≃ CH_{d-p}(X)` along
  the first projection of the self-product of the identity.
* `Stacks.Chow.chowCohomologyCapFundamentalClass` — **Stacks 0FC2**, the map
  `A^p(X) ⟶ CH_{d-p}(X)`, `c ↦ c ∩ [X]_d`.

## Main results

* `Stacks.Chow.chowCohomologyCapFundamentalClass_eq_iff`,
  `Stacks.Chow.chowCohomologyCapFundamentalClass_eq_zero_iff` — the map is cap product with
  `[X]_d` up to an isomorphism, so it separates two classes, resp. vanishes, exactly when that
  cap product does.
* `Stacks.Chow.chowCohomologyCapFundamentalClass_injective_iff` — **Stacks 0FC2, injectivity
  reduced to Stacks 02UC**: the map is injective exactly when a class killing `[X]_d` kills the
  fundamental class of every integral scheme locally of finite type over `X`.
* `Stacks.Chow.chowCohomologyCapFundamentalClass_injective_iff_hasBirationalModification` — the
  same reduction through clause (3) of Stacks 02UC.
* `Stacks.Chow.cap_fundamentalChowClass_eq_zero_of_flatPullback` — the one case of that
  criterion which the laws of Stacks 0B76 settle outright: a class killing `[X]_d` kills the
  fundamental class of every test scheme whose fundamental class is a flat pullback of `[X]_d`.

## Implementation notes

### The base, and the degree

The base is kept as a general `Stacks.Chow.ChowSituation`, as in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverField` and
`StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree`, rather than being specialized to
`Stacks.Chow.fieldChowSituation`; every statement below instantiates to a field through that
situation, whose base scheme is `Spec k` reducibly, so no transport along an equality of schemes
appears anywhere.

The degree `d` is an arbitrary integer rather than the dimension of `X`. Nothing below needs it
to be one: the map `c ↦ c ∩ [X]_d` is defined, and the reduction of its injectivity is valid,
for every `d`, and the geometric case of Stacks 0FC2 is the specialization in which `X` is
smooth over a field and equidimensional of dimension `d`. Where smoothness and
equidimensionality are genuinely needed is in the two assertions this file does not prove, and
carrying them as unused hypotheses on the declarations below would only narrow true statements.

### The two fibre products that have to be collapsed

The cap operation of a bivariant class for `f : X ⟶ Y` at a test morphism `g : T ⟶ Y` lands in
the *chosen* categorical pullback `T ×_Y X`. For `A^p(X) = A^p(X ⟶ X)` read on the test morphism
`𝟙 X` that pullback is `X ×_X X`, whose first projection is an isomorphism because the second
leg of the product is the identity; `Stacks.Chow.chowGroupSelfUnitCollapse` is proper
pushforward along it. Likewise the Chow group the cap operation consumes is indexed by the
composite `𝟙 X ≫ sX` rather than by `sX`, so `Stacks.Chow.selfFundamentalClass` presents `[X]_d`
at that composite. Both are the pattern of
`Stacks.Chow.chowGroupBaseUnitCollapse` and `Stacks.Chow.baseFundamentalClass`.

### Why neither clause of Stacks 0FC2 is proved

The source proof factors the map of Stacks 0FC2 as

  `A^p(X) ⟶ A^{p-d}(X ⟶ Spec k) ⟶ CH_{d-p}(X)`,

the first arrow being composition with the smooth pullback class of the structure morphism, an
isomorphism by **Stacks 0FBT**, and the second cap product with `[Spec k]`, an isomorphism by
**Stacks 0FBW**. Of those two the second is partly available: its injectivity is
`Stacks.Chow.bivariantToBaseEval_injective`. The first is not available at all, and not for want
of a hypothesis to carry — neither of the two things it speaks about exists here. The flat
pullback bivariant class of **Stacks 0B78** is not constructed, and neither is the composition
of bivariant classes of **Stacks 0B75**: `Stacks.Chow.IsBivariantClassComposition` characterizes
a composite but nothing inhabits it, the obstruction being **Stacks 0B6Y**. So the factorization
through which injectivity is proved in the source cannot be written down, and what is offered
instead is the honest half: `Stacks.Chow.chowCohomologyCapFundamentalClass_injective_iff`
isolates, against Stacks 02UC, exactly the statement that remains.

Surjectivity is further out. The inverse in the source sends `α ∈ CH_{d-p}(X)` to the class
`β ↦ Δ^!(α × β)`, which needs the Gysin bivariant class `Δ^!` of the diagonal. Only the two
inputs to that class are here, as
`Stacks.Chow.isRegularImmersion_diagonal_of_smooth` and
`Stacks.Chow.gysinMapExists_diagonal_of_smooth` (**Stacks 0FBR**); the class itself requires
the higher-codimension class of **Stacks 0FBK**, which is absent.

The second clause of Stacks 0FC2 — that the isomorphism carries composition of bivariant classes
to the intersection product — is **not stated here**, and deliberately so: the intersection
product `CH_i(X) × CH_j(X) ⟶ CH_{i+j-d}(X)` of **Stacks 0FC0** does not exist in this
repository, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysin` and of
`StacksFrontier.AlgebraicGeometry.Chow.Intersection.CohenMacaulayProperIntersection` also record.
Its right-hand side being absent, the clause has no statement in the present vocabulary, and
introducing a definition in order to state it would make the clause assert something other than
Stacks 0FC2.

## References

* [Stacks Project, Tag 0FC2](https://stacks.math.columbia.edu/tag/0FC2)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FBT](https://stacks.math.columbia.edu/tag/0FBT)
* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
* [Stacks Project, Tag 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (d p : ℤ)

/-! ### The fundamental class, and the collapse of the self-product -/

/-- The fundamental class `[X]_d ∈ CH_d(X)` in the form in which the cap operation of a class in
`A^p(X) = A^p(X ⟶ X)` consumes it: the test scheme is `X` through its identity, so the Chow group
is indexed by the composite `𝟙 X ≫ sX`. -/
abbrev selfFundamentalClass : chowGroup C (𝟙 X ≫ sX) d :=
  fundamentalChowClass C (𝟙 X ≫ sX) d

/-- The collapse `CH_{d-p}(X ×_X X) ≃ CH_{d-p}(X)`: the first projection of a fibre product whose
second leg is the identity is an isomorphism, and the equivalence is proper pushforward along
it. -/
def chowGroupSelfUnitCollapse :
    chowGroup C (pullback.fst (𝟙 X) (𝟙 X) ≫ sX) (d - p) ≃+ chowGroup C sX (d - p) :=
  chowGroupEquivOfIso C (pullback.fst (𝟙 X) (𝟙 X) ≫ sX) sX (pullback.fst (𝟙 X) (𝟙 X)) rfl (d - p)

/-- Cap product with the fundamental class, `c ↦ c ∩ [X]_d`, as an additive map. Its value lives
on the self-product `X ×_X X`, which `Stacks.Chow.chowGroupSelfUnitCollapse` collapses. -/
def capSelfFundamentalClass :
    chowCohomologyComponent C G sX p →+
      chowGroup C (pullback.fst (𝟙 X) (𝟙 X) ≫ sX) (d - p) where
  toFun c := c.cap (𝟙 X) d (selfFundamentalClass C sX d)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The value of `Stacks.Chow.capSelfFundamentalClass` on `c` is the cap product `c ∩ [X]_d` along
the identity of `X`. -/
@[simp]
theorem capSelfFundamentalClass_apply (c : chowCohomologyComponent C G sX p) :
    capSelfFundamentalClass C G sX d p c = c.cap (𝟙 X) d (selfFundamentalClass C sX d) :=
  rfl

/-- **Stacks 0FC2.** The map `A^p(X) ⟶ CH_{d-p}(X)` of Stacks 0FC2: cap product of a bivariant
class for the identity of `X` with the fundamental class `[X]_d`, read through the collapse of
`X ×_X X` onto `X` along its first projection.

For `X` smooth over a field and equidimensional of dimension `d` the source asserts that this map
is an isomorphism. Neither that assertion nor the compatibility of composition with the
intersection product is proved here; what is proved is the reduction of injectivity in
`Stacks.Chow.chowCohomologyCapFundamentalClass_injective_iff`. See the implementation notes of
this module. -/
@[stacks 0FC2 "the map A^p(X) → CH_{d-p}(X), c ↦ c ∩ [X]_d, for an arbitrary degree d over a \
general Chow situation; neither its bijectivity nor the compatibility of composition with the \
intersection product is covered"]
def chowCohomologyCapFundamentalClass :
    chowCohomologyComponent C G sX p →+ chowGroup C sX (d - p) :=
  (chowGroupSelfUnitCollapse C sX d p).toAddMonoidHom.comp
    (capSelfFundamentalClass C G sX d p)

/-- The value of `Stacks.Chow.chowCohomologyCapFundamentalClass` on `c` is the image of the cap
product `c ∩ [X]_d` under `Stacks.Chow.chowGroupSelfUnitCollapse`. -/
@[simp]
theorem chowCohomologyCapFundamentalClass_apply (c : chowCohomologyComponent C G sX p) :
    chowCohomologyCapFundamentalClass C G sX d p c =
      chowGroupSelfUnitCollapse C sX d p (c.cap (𝟙 X) d (selfFundamentalClass C sX d)) :=
  rfl

/-- The map of Stacks 0FC2 is cap product with `[X]_d` up to an isomorphism, so two bivariant
classes have the same image exactly when they cap `[X]_d` to the same Chow class. -/
theorem chowCohomologyCapFundamentalClass_eq_iff (c c' : chowCohomologyComponent C G sX p) :
    chowCohomologyCapFundamentalClass C G sX d p c =
        chowCohomologyCapFundamentalClass C G sX d p c' ↔
      c.cap (𝟙 X) d (selfFundamentalClass C sX d) =
        c'.cap (𝟙 X) d (selfFundamentalClass C sX d) := by
  rw [chowCohomologyCapFundamentalClass_apply, chowCohomologyCapFundamentalClass_apply]
  exact (chowGroupSelfUnitCollapse C sX d p).injective.eq_iff

/-- A bivariant class is in the kernel of the map of Stacks 0FC2 exactly when it caps the
fundamental class `[X]_d` to zero. -/
theorem chowCohomologyCapFundamentalClass_eq_zero_iff (c : chowCohomologyComponent C G sX p) :
    chowCohomologyCapFundamentalClass C G sX d p c = 0 ↔
      c.cap (𝟙 X) d (selfFundamentalClass C sX d) = 0 := by
  have := chowCohomologyCapFundamentalClass_eq_iff C G sX d p c 0
  rwa [map_zero] at this

/-! ### Injectivity, reduced to Stacks 02UC -/

/-- **Stacks 0FC2, injectivity reduced to Stacks 02UC.** The map `A^p(X) ⟶ CH_{d-p}(X)` of
Stacks 0FC2 is injective exactly when every bivariant class killing the fundamental class `[X]_d`
kills the fundamental class of every integral scheme locally of finite type over `X`.

This is the whole of what Stacks 02UC contributes to the injectivity half of Stacks 0FC2, and the
right-hand side is the statement that remains: in the source it is obtained by factoring the map
through `A^{p-d}(X ⟶ Spec k)` using Stacks 0FBT, which is not available here. The equivalence is
not vacuous in either direction — the forward implication uses that the zero class kills every
fundamental class, the backward one uses Stacks 02UC proper. -/
@[stacks 0FC2 "injectivity of the map c ↦ c ∩ [X]_d, reduced by Stacks 02UC to the statement \
that a class killing [X]_d kills the fundamental class of every integral scheme locally of finite \
type over X; the surjectivity of the map and the compatibility of composition with the \
intersection product are not covered"]
theorem chowCohomologyCapFundamentalClass_injective_iff :
    Function.Injective (chowCohomologyCapFundamentalClass C G sX d p) ↔
      ∀ c : chowCohomologyComponent C G sX p,
        c.cap (𝟙 X) d (selfFundamentalClass C sX d) = 0 →
          c.CapsIntegralFundamentalClassesToZero C G sX sX (𝟙 X) (Category.id_comp sX) p := by
  rw [injective_iff_map_eq_zero]
  refine ⟨fun h c hc ↦ ?_, fun h c hc ↦ ?_⟩
  · obtain rfl := h c ((chowCohomologyCapFundamentalClass_eq_zero_iff C G sX d p c).2 hc)
    exact BivariantClass.zero_capsIntegralFundamentalClassesToZero C G sX sX (𝟙 X)
      (Category.id_comp sX) p
  · exact (BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero C G sX sX (𝟙 X)
      (Category.id_comp sX) p c).2
      (h c ((chowCohomologyCapFundamentalClass_eq_zero_iff C G sX d p c).1 hc))

/-- **Stacks 0FC2, injectivity reduced to clause (3) of Stacks 02UC.** The same reduction as
`Stacks.Chow.chowCohomologyCapFundamentalClass_injective_iff`, with the criterion read through
the birational form of Stacks 02UC: it is enough that every integral scheme locally of finite
type over `X` admit a proper birational modification whose fundamental class the class kills. -/
@[stacks 0FC2 "injectivity of the map c ↦ c ∩ [X]_d, reduced by clause (3) of Stacks 02UC to the \
existence of proper birational modifications capping to zero; the surjectivity of the map and \
the compatibility of composition with the intersection product are not covered"]
theorem chowCohomologyCapFundamentalClass_injective_iff_hasBirationalModification :
    Function.Injective (chowCohomologyCapFundamentalClass C G sX d p) ↔
      ∀ c : chowCohomologyComponent C G sX p,
        c.cap (𝟙 X) d (selfFundamentalClass C sX d) = 0 →
          c.HasBirationalModificationCappingToZero C G sX sX (𝟙 X) (Category.id_comp sX) p := by
  rw [chowCohomologyCapFundamentalClass_injective_iff C G sX d p]
  exact forall_congr' fun c ↦ imp_congr_right fun _ ↦
    BivariantClass.capsIntegralFundamentalClassesToZero_iff_hasBirationalModification
      C G sX sX (𝟙 X) (Category.id_comp sX) p c

/-- **Stacks 0FC2, two bivariant classes with the same cap product.** Granted the criterion of
`Stacks.Chow.chowCohomologyCapFundamentalClass_injective_iff`, a class in `A^p(X)` is determined
by `c ∩ [X]_d`. -/
theorem eq_of_capSelfFundamentalClass_eq
    (hcrit : ∀ c : chowCohomologyComponent C G sX p,
      c.cap (𝟙 X) d (selfFundamentalClass C sX d) = 0 →
        c.CapsIntegralFundamentalClassesToZero C G sX sX (𝟙 X) (Category.id_comp sX) p)
    {c c' : chowCohomologyComponent C G sX p}
    (h : c.cap (𝟙 X) d (selfFundamentalClass C sX d) =
      c'.cap (𝟙 X) d (selfFundamentalClass C sX d)) : c = c' :=
  (chowCohomologyCapFundamentalClass_injective_iff C G sX d p).2 hcrit
    ((chowCohomologyCapFundamentalClass_eq_iff C G sX d p c c').2 h)

/-! ### The case of the criterion that the laws of Stacks 0B76 settle -/

/-- **The one case of the injectivity criterion of Stacks 0FC2 that the laws of Stacks 0B76
settle outright.** Let `c ∈ A^p(X)` cap the fundamental class `[X]_d` to zero and let
`v : T ⟶ X` be flat of relative dimension `r`, locally of finite type, with the fundamental class
of `T` in degree `d + r` the flat pullback of `[X]_d` along `v`. Then `c ∩ [T] = 0`: cap product
commutes with flat pullback, which is the second law of Stacks 0B76, so `c ∩ [T]` is the flat
pullback of `c ∩ [X]_d` along the base change of `v`.

This is the step that proves Stacks 0FBW in
`Stacks.Chow.cap_fundamentalChowClass_eq_zero_of_cap_baseFundamentalClass_eq_zero`, where every
integral test scheme is flat over the base because the base is a field. Over `X` it does **not**
suffice: a test morphism `T ⟶ X` need not be flat, and the fundamental class of an integral `T`
over `X` is not in general a flat pullback of `[X]_d` — the closed point of a curve is the
standing counterexample. So this lemma settles the criterion of
`Stacks.Chow.chowCohomologyCapFundamentalClass_injective_iff` only for the test schemes it names,
and the remaining ones are exactly what Stacks 0FBT supplies in the source. -/
theorem cap_fundamentalChowClass_eq_zero_of_flatPullback
    (hS1 : FlatPullbackDescends C) (c : chowCohomologyComponent C G sX p)
    (hc : c.cap (𝟙 X) d (selfFundamentalClass C sX d) = 0)
    {T : Scheme.{u}} (v : T ⟶ X) [LocallyOfFiniteType v] [Flat v] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension v r)
    (hfund : fundamentalChowClass C ((v ≫ 𝟙 X) ≫ sX) (d + (r : ℤ)) =
      flatPullbackChow C ((v ≫ 𝟙 X) ≫ sX) (𝟙 X ≫ sX) v (by simp) r hr d
        (hS1 ((v ≫ 𝟙 X) ≫ sX) (𝟙 X ≫ sX) v (by simp) r hr d)
        (selfFundamentalClass C sX d)) :
    c.cap (v ≫ 𝟙 X) (d + (r : ℤ))
      (fundamentalChowClass C ((v ≫ 𝟙 X) ≫ sX) (d + (r : ℤ))) = 0 := by
  have sq := isPullback_bivariantBaseChangeMap (𝟙 X) (𝟙 X) v
  have : LocallyOfFiniteType (bivariantBaseChangeMap (𝟙 X) (𝟙 X) v) :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have : Flat (bivariantBaseChangeMap (𝟙 X) (𝟙 X) v) :=
    MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  have hr' : AlgebraicGeometry.RelativeDimension (bivariantBaseChangeMap (𝟙 X) (𝟙 X) v) r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback sq hr
  have hnat := c.flat_naturality (𝟙 X) v r hr (bivariantBaseChangeMap (𝟙 X) (𝟙 X) v) sq
    (bivariantBaseChangeMap_fst (𝟙 X) (𝟙 X) v) d hr' (hS1 _ _ v _ r hr d)
    (hS1 _ _ (bivariantBaseChangeMap (𝟙 X) (𝟙 X) v) _ r hr' (d - p))
    (selfFundamentalClass C sX d)
  rw [hc, map_zero] at hnat
  rw [hfund]
  exact chowGroup_eq_zero_of_heq_zero C
    (show d + (r : ℤ) - p = d - p + (r : ℤ) by ring) hnat

end Stacks.Chow

end
