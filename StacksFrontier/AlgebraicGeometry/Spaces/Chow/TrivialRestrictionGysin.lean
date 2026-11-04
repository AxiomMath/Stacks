module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalGysinRule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The Gysin map on cycles when the sheaf is trivial on the divisor

In the situation of Stacks 0EDT let `X/B` be good, let `ℒ` be an invertible sheaf on `X` with a
global section `s`, let `E = Z(s)` be the vanishing locus of `s` and let `i : E → X` be the
closed immersion, as in Stacks 0ER1.  Stacks 0ER2 observes that if `ℒ|_E ≅ 𝒪_E` then there is a
canonical map on *cycles*

  `i^* : Z_{k+1}(X) ⟶ Z_k(E)`,

obtained by requiring that `i^*[W] = 0` whenever `W ⊆ E`.

The letter `D` is taken by the dimension situation of Stacks 0EDT, so the closed subspace which
the source calls `D` is called `E` throughout this file, as in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection`.

## Main definitions

* `AlgebraicGeometry.Space.trivialRestrictionRule`: the component rule of Stacks 0ER1 with the
  case `W ⊆ E` replaced by zero, which is the prescription of Stacks 0ER2.
* `AlgebraicGeometry.Space.trivialRestrictionGysinCycleMap`: the resulting map
  `Z_{k+1}(X) ⟶ Z_k(E)` on cycles.
* `AlgebraicGeometry.Space.canonicalTrivialRestrictionRule`: the component rule of Stacks 0ER2
  with both of its clauses built — clause (1)(a) of Stacks 0ER1 is the cycle `[E ∩ W]_k` of
  Stacks 0EE9 of the scheme-theoretic intersection `E ∩ W = i^{-1}(W)`, and clause (1)(b) is the
  zero cycle, which is the requirement `i^*[W] = 0` of this remark.
* `AlgebraicGeometry.Space.restrictToVanishingLocus` and
  `AlgebraicGeometry.Space.IsTrivialOnVanishingLocus`: the restriction `ℒ|_E` and the hypothesis
  `ℒ|_E ≅ 𝒪_E` of the source.
* `AlgebraicGeometry.Space.trivialRestrictionGysin`: the map on cycles of Stacks 0ER2 in the form
  which takes the component rule of Stacks 0ER1 as a parameter, together with the data of the
  triple of Stacks 0ER1.
* `AlgebraicGeometry.Space.canonicalTrivialRestrictionGysin`: **Stacks 0ER2**, the canonical map
  `i^* : Z_{k+1}(X) ⟶ Z_k(E)` on cycles of a pair `(ℒ, s)` of Stacks 0ER1, built from `(ℒ, s)`
  and `k` alone.

## Main results

* `AlgebraicGeometry.Space.isGood_closedSubspace` and
  `AlgebraicGeometry.Space.isGood_vanishingLocus`: a closed subspace of a good algebraic space
  over the base, in particular the vanishing locus `E = Z(s)`, is again good over the base.
* `AlgebraicGeometry.Space.canonicalTrivialRestrictionGysin_integralCycle_of_le`: the defining
  requirement `i^*[W] = 0` for `W ⊆ E`.
* `AlgebraicGeometry.Space.canonicalTrivialRestrictionGysin_integralCycle_of_not_le`: the
  remaining values `i^*[W] = [E ∩ W]_k` for `W ⊄ E`, which Stacks 0ER1(1)(a) forces, the
  right-hand side being the cycle of Stacks 0EE9 of the scheme-theoretic intersection.
* `AlgebraicGeometry.Space.gysinCycleMap_eq_canonicalTrivialRestrictionGysin`: canonicity.  Those
  two prescriptions determine the map: a component rule whose cycle map takes the prescribed
  values on the cycle of every integral closed subspace has the same cycle map.
* `AlgebraicGeometry.Space.refinedGysin_integralCycle_eq_canonicalTrivialRestriction_of_not_le`:
  the canonical map lifts the refined Gysin homomorphism of Stacks 0ER1 off the divisor, with no
  hypothesis on `ℒ` at all.
* `AlgebraicGeometry.Space.cls_gysinComponentCycle_eq_of_cls_chernCycle_eq_zero`,
  `AlgebraicGeometry.Space.refinedGysin_integralCycle_eq_trivialRestriction` and
  `AlgebraicGeometry.Space.refinedGysin_integralCycle_eq_canonicalTrivialRestriction`: the lift
  over the divisor.  Once the class of `i'_*(c₁(ℒ|_W) ∩ [W])` vanishes for `W ⊆ E`, the class of
  this cycle map is the refined Gysin homomorphism of Stacks 0ER1 everywhere.
* `AlgebraicGeometry.Space.gysinCycleMap_eq_trivialRestriction` and
  `AlgebraicGeometry.Space.gysinCycleMap_eq_trivialRestrictionGysin`: the same canonicity for the
  parametrised form of the map.

## Implementation notes

The map of Stacks 0ER2 is `AlgebraicGeometry.Space.gysinCycleMap` of Stacks 0ER1 at the
component rule whose `W ⊆ E` case is the zero cycle.  The source's `Z_k(D)` is
`AlgebraicGeometry.Space.CycleGroup` of `E` over the base, and the map is valued there: the class
map of an `AlgebraicGeometry.Space.ChowTarget` is *not* applied.

The case `W ⊄ E` is not a choice either.  Stacks 0ER1(1)(a) prescribes `i^*[W] = [E ∩ W]_k`
there, and that is already a `k`-cycle on `E`, so the only clause the source has to state is the
one for `W ⊆ E`.  Here that cycle is `AlgebraicGeometry.Space.gysinIntersectionCycle`, the cycle
of Stacks 0EE9 of the scheme-theoretic intersection `E ∩ W = i^{-1}(W)`, whose δ-dimension bound
and support property are proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalGysinRule`.  So both clauses of
`AlgebraicGeometry.Space.canonicalTrivialRestrictionRule` are built, and
`AlgebraicGeometry.Space.canonicalTrivialRestrictionGysin` depends on `(ℒ, s)` and on `k` alone.
The goodness of `E` over the base is proved from the goodness of `X` rather than assumed, by
`AlgebraicGeometry.Space.isGood_vanishingLocus`.

`AlgebraicGeometry.Space.trivialRestrictionGysin` is the same map in the form which leaves the
component rule of Stacks 0ER1 a parameter, and takes the triple of Stacks 0ER1 in full.

### The source's hypothesis `ℒ|_E ≅ 𝒪_E`

`AlgebraicGeometry.Space.IsTrivialOnVanishingLocus` is the hypothesis `ℒ|_E ≅ 𝒪_E` of the
source.  The map of Stacks 0ER2 does not use it, and
`AlgebraicGeometry.Space.canonicalTrivialRestrictionGysin` does not take it: the two values
`i^*[W] = 0` for `W ⊆ E` and `i^*[W] = [E ∩ W]_k` for `W ⊄ E` are cycles on `E` determined by
`(ℒ, s)`, so they are theorems about that map rather than data put into it.

What the hypothesis gives the source is that this map *lifts* the refined Gysin homomorphism of
Stacks 0ER1.  Off the divisor the two agree for any `ℒ`, which is
`AlgebraicGeometry.Space.refinedGysin_integralCycle_eq_canonicalTrivialRestriction_of_not_le`.
Over the divisor the value of Stacks 0ER1 is the class of `i'_*(c₁(ℒ|_W) ∩ [W])`, and
`ℒ|_W ≅ 𝒪_W` makes `c₁(ℒ|_W) ∩ [W]` zero in `CH_k(W)` by the second assertion of Stacks 0EQK
(`AlgebraicGeometry.Space.canonicalFirstChernCap_tensorUnit_eq_zero`).

`AlgebraicGeometry.Space.refinedGysin_integralCycle_eq_canonicalTrivialRestriction` takes the
component cycle as an arbitrary `AlgebraicGeometry.Space.FirstChernComponentCycleRule` and the
Chow group of `E` as an arbitrary `AlgebraicGeometry.Space.ChowTarget`, whose
`principalDivisors` is a set parameter.  On these `ℒ|_E ≅ 𝒪_E` has no bearing, so the vanishing
of the class is the hypothesis `hchern`.

## References

* [Stacks Project, Tag 0ER2](https://stacks.math.columbia.edu/tag/0ER2)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w v

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-! ### The prescription of Stacks 0ER2 -/

section TrivialRestriction

variable (p : X ⟶ D.space) (E : ClosedSubspaces D.site D.base D.base_mem X)
    (hE : D.IsGood (E.1.ι ≫ p)) (k : ℤ) (rule : GysinComponentRule D p E k)

/-- The component rule of Stacks 0ER1 with the case `W ⊆ E` replaced by the zero cycle, which is
the prescription `i^*[W] = 0` of Stacks 0ER2.  The case `W ⊄ E` is unchanged, Stacks 0ER1(1)(a)
prescribing `[E ∩ W]_k` there. -/
def trivialRestrictionRule : GysinComponentRule D p E k where
  intersectionCycle := rule.intersectionCycle
  intersectionCycle_support := rule.intersectionCycle_support
  chernCycle := fun _ _ _ => 0

@[simp]
theorem trivialRestrictionRule_intersectionCycle
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1) :
    (trivialRestrictionRule D p E k rule).intersectionCycle W hW hWE =
      rule.intersectionCycle W hW hWE :=
  rfl

@[simp]
theorem trivialRestrictionRule_chernCycle
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) (hWE : W.subspace ≤ E.1) :
    (trivialRestrictionRule D p E k rule).chernCycle W hW hWE = 0 :=
  rfl

/-- The component cycle of the prescription of Stacks 0ER2 vanishes on a subspace contained in
the divisor. -/
theorem gysinComponentCycle_trivialRestrictionRule_of_le
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) (hWE : W.subspace ≤ E.1) :
    gysinComponentCycle D p E hE k (trivialRestrictionRule D p E k rule) W = 0 := by
  rw [gysinComponentCycle_of_le D p E hE k _ hW hWE, trivialRestrictionRule_chernCycle,
    map_zero]

/-- **Stacks 0ER2.** The canonical map `i^* : Z_{k+1}(X) ⟶ Z_k(E)` on cycles: the additive
extension of the component rule of Stacks 0ER1 whose `W ⊆ E` case is zero. -/
def trivialRestrictionGysinCycleMap :
    CycleGroup D p (k + 1) →+ CycleGroup D (E.1.ι ≫ p) k :=
  gysinCycleMap D p E hE k (trivialRestrictionRule D p E k rule)

/-- **Stacks 0ER2.** The defining requirement: the map vanishes on the cycle of an integral
closed subspace of δ-dimension `k + 1` contained in the divisor. -/
theorem trivialRestrictionGysinCycleMap_integralCycle_of_le
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) (hWE : W.subspace ≤ E.1) :
    trivialRestrictionGysinCycleMap D p E hE k rule (integralCycle D p (k + 1) W hW) = 0 := by
  rw [trivialRestrictionGysinCycleMap, gysinCycleMap_integralCycle,
    gysinComponentCycle_trivialRestrictionRule_of_le D p E hE k rule hW hWE]

/-- **Stacks 0ER1(1)(a).** On the cycle of an integral closed subspace of δ-dimension `k + 1`
not contained in the divisor the map is `[E ∩ W]_k`, as in Stacks 0ER1. -/
theorem trivialRestrictionGysinCycleMap_integralCycle_of_not_le
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1) :
    trivialRestrictionGysinCycleMap D p E hE k rule (integralCycle D p (k + 1) W hW) =
      rule.intersectionCycle W hW hWE := by
  rw [trivialRestrictionGysinCycleMap, gysinCycleMap_integralCycle,
    gysinComponentCycle_of_not_le D p E hE k _ hW hWE, trivialRestrictionRule_intersectionCycle]

/-- Two component rules with the same component cycles have the same cycle map. -/
theorem gysinCycleMap_congr (rule' : GysinComponentRule D p E k)
    (h : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      gysinComponentCycle D p E hE k rule W = gysinComponentCycle D p E hE k rule' W) :
    gysinCycleMap D p E hE k rule = gysinCycleMap D p E hE k rule' := by
  refine AddMonoidHom.ext fun α => Subtype.ext (funext fun Z => ?_)
  rw [gysinCycleMap_apply, gysinCycleMap_apply]
  exact finsum_congr fun W => by rw [h W]

/-- An additive map takes the component cycle of a rule `rule'` to that of the rule of
Stacks 0ER2 as soon as it vanishes on its `W ⊆ E` components and takes the values of `rule` on
the others. -/
private theorem map_gysinComponentCycle_trivialRestrictionRule {β : Type*} [AddCommGroup β]
    (F : CycleGroup D (E.1.ι ≫ p) k →+ β) (rule' : GysinComponentRule D p E k)
    (hle : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X),
      deltaDimension D p W = k + 1 → W.subspace ≤ E.1 →
      F (gysinComponentCycle D p E hE k rule' W) = 0)
    (hnotle : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1),
      F (gysinComponentCycle D p E hE k rule' W) = F (rule.intersectionCycle W hW hWE))
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    F (gysinComponentCycle D p E hE k rule' W) =
      F (gysinComponentCycle D p E hE k (trivialRestrictionRule D p E k rule) W) := by
  by_cases hW : deltaDimension D p W = k + 1
  · by_cases hWE : W.subspace ≤ E.1
    · rw [hle W hW hWE, gysinComponentCycle_trivialRestrictionRule_of_le D p E hE k rule hW hWE,
        map_zero]
    · rw [hnotle W hW hWE, gysinComponentCycle_of_not_le D p E hE k _ hW hWE,
        trivialRestrictionRule_intersectionCycle]
  · rw [gysinComponentCycle_of_deltaDimension_ne D p E hE k rule' hW,
      gysinComponentCycle_of_deltaDimension_ne D p E hE k _ hW]

/-- **Stacks 0ER2, canonicity.** The two prescriptions determine the map: a component rule whose
cycle map is zero on the cycle of every integral closed subspace of δ-dimension `k + 1`
contained in the divisor, and is `[E ∩ W]_k` on the cycle of every other one, has the cycle map
of Stacks 0ER2. -/
theorem gysinCycleMap_eq_trivialRestriction (rule' : GysinComponentRule D p E k)
    (hle : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1), W.subspace ≤ E.1 →
      gysinCycleMap D p E hE k rule' (integralCycle D p (k + 1) W hW) = 0)
    (hnotle : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1),
      gysinCycleMap D p E hE k rule' (integralCycle D p (k + 1) W hW) =
        rule.intersectionCycle W hW hWE) :
    gysinCycleMap D p E hE k rule' = trivialRestrictionGysinCycleMap D p E hE k rule := by
  refine gysinCycleMap_congr D p E hE k rule' _ <|
    map_gysinComponentCycle_trivialRestrictionRule D p E hE k rule (AddMonoidHom.id _) rule'
      (fun W hW hWE => ?_) fun W hW hWE => ?_
  · rw [AddMonoidHom.id_apply, ← gysinCycleMap_integralCycle D p E hE k rule' hW]
    exact hle W hW hWE
  · rw [AddMonoidHom.id_apply, ← gysinCycleMap_integralCycle D p E hE k rule' hW]
    exact hnotle W hW hWE

/-- The class of the component cycle of Stacks 0ER1 agrees with the class of the component cycle
of Stacks 0ER2 as soon as the class of `i'_*(c₁(ℒ|_W) ∩ [W])` vanishes for `W ⊆ E`. -/
theorem cls_gysinComponentCycle_eq_of_cls_chernCycle_eq_zero {CH : Type w} [AddCommGroup CH]
    (chow : ChowTarget.{u, w, v} D (E.1.ι ≫ p) hE k CH)
    (hchern : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1) (hWE : W.subspace ≤ E.1),
      chow.cls (containedPushforward D p E hE k hWE (rule.chernCycle W hW hWE)) = 0)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    chow.cls (gysinComponentCycle D p E hE k rule W) =
      chow.cls (gysinComponentCycle D p E hE k (trivialRestrictionRule D p E k rule) W) := by
  refine map_gysinComponentCycle_trivialRestrictionRule D p E hE k rule chow.cls rule
    (fun W hW hWE => ?_) (fun W hW hWE => ?_) W
  · rw [gysinComponentCycle_of_le D p E hE k rule hW hWE]
    exact hchern W hW hWE
  · rw [gysinComponentCycle_of_not_le D p E hE k rule hW hWE]

end TrivialRestriction

/-! ### The component rule of Stacks 0ER2, with both clauses built -/

section CanonicalRule

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (k : ℤ)

include hp in
/-- A closed subspace of a good algebraic space over the base is again good over the base. -/
theorem isGood_closedSubspace : D.IsGood (E.1.ι ≫ p) :=
  ⟨E.2.1,
    isQuasiSeparated_comp D.site D.base D.base_mem E.2.1 hp.1 _ _
      (isQuasiSeparated_of_isClosedImmersion D.site D.base D.base_mem E.2.2) hp.2.1,
    isLocallyOfFiniteType_comp D.site D.base D.base_mem E.2.1 hp.1 D.isAlgebraicSpace _ _
      (isLocallyOfFiniteType_of_isClosedImmersion D.site D.base D.base_mem _ E.2.2) hp.2.2⟩

/-- **The component rule of Stacks 0ER2.** Clause (1)(a) of Stacks 0ER1 is the cycle
`[E ∩ W]_k` of Stacks 0EE9 of the scheme-theoretic intersection, as in
`AlgebraicGeometry.Space.canonicalGysinComponentRule`, and clause (1)(b) is the zero cycle,
which is the prescription `i^*[W] = 0` of Stacks 0ER2.

Neither clause is free data: the first is the cycle of the source and the second is the
prescription of the remark, so the rule — and with it the cycle map of Stacks 0ER2 — is
determined by `E` and by `k` alone. -/
def canonicalTrivialRestrictionRule : GysinComponentRule D p E k :=
  trivialRestrictionRule D p E k
    (canonicalGysinComponentRule D p hp E (isGood_closedSubspace D p hp E) k fun _ _ => 0)

@[simp]
theorem canonicalTrivialRestrictionRule_intersectionCycle
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1) :
    (canonicalTrivialRestrictionRule D p hp E k).intersectionCycle W hW hWE =
      gysinIntersectionCycle D p hp E (isGood_closedSubspace D p hp E) k W hW hWE :=
  rfl

@[simp]
theorem canonicalTrivialRestrictionRule_chernCycle
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) (hWE : W.subspace ≤ E.1) :
    (canonicalTrivialRestrictionRule D p hp E k).chernCycle W hW hWE = 0 :=
  rfl

/-- The prescription of Stacks 0ER2 discards the component datum of Stacks 0EQJ: replacing
clause (1)(b) of the built rule of Stacks 0ER1 by the zero cycle gives the rule of
Stacks 0ER2, whichever datum clause (1)(b) was built from. -/
theorem trivialRestrictionRule_canonicalGysinComponentRule
    (chern : FirstChernComponentCycleRule D p k) :
    trivialRestrictionRule D p E k
        (canonicalGysinComponentRule D p hp E (isGood_closedSubspace D p hp E) k chern) =
      canonicalTrivialRestrictionRule D p hp E k :=
  rfl

end CanonicalRule

/-! ### The triple of Stacks 0ER1 with the sheaf trivial on the divisor -/

section ZeroScheme

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections) (k : ℤ)

/-- The closed immersion `i : E → X` of the vanishing locus of `s`, as a morphism of algebraic
spaces over the base scheme. -/
def vanishingLocusInclusion :
    (⟨(vanishingLocus D p hp L s).1.toFunctor, (vanishingLocus D p hp L s).2.1⟩ :
      AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hp.1⟩ :=
  ObjectProperty.homMk (vanishingLocus D p hp L s).1.ι

/-- The restriction `ℒ|_E` of a sheaf of modules on `X` to the vanishing locus `E = Z(s)`, that
is, its inverse image along the closed immersion `i : E → X`. -/
abbrev restrictToVanishingLocus :=
  (modulePullback D.site D.base D.base_mem (vanishingLocusInclusion D p hp L s)).obj L

/-- The hypothesis `ℒ|_E ≅ 𝒪_E` of Stacks 0ER2: the restriction of `ℒ` to the vanishing locus of
`s` is isomorphic, as a module over the structure sheaf of `E`, to that structure sheaf. -/
abbrev IsTrivialOnVanishingLocus : Prop :=
  Stacks.SheafOfModules.IsTrivial
    (smallEtaleRingedSite D.site D.base D.base_mem (vanishingLocus D p hp L s).1.toFunctor
      (vanishingLocus D p hp L s).2.1).O.obj
    (structureRingSheaf D.site D.base D.base_mem
      ⟨(vanishingLocus D p hp L s).1.toFunctor, (vanishingLocus D p hp L s).2.1⟩).property
    (restrictToVanishingLocus D p hp L s)

/-- The vanishing locus `E = Z(s)` of a global section of a sheaf of modules on a good algebraic
space over the base is itself good over the base, being a closed subspace. -/
theorem isGood_vanishingLocus : D.IsGood ((vanishingLocus D p hp L s).1.ι ≫ p) :=
  isGood_closedSubspace D p hp (vanishingLocus D p hp L s)

variable (hE : D.IsGood ((vanishingLocus D p hp L s).1.ι ≫ p))

/-- The map `i^* : Z_{k+1}(X) ⟶ Z_k(E)` of Stacks 0ER2 for a triple `(ℒ, s, i : E → X)` of
Stacks 0ER1, in the form which takes the component rule of Stacks 0ER1 as a parameter: the
additive extension of that rule with its `W ⊆ E` clause replaced by the zero cycle. -/
def trivialRestrictionGysin (_hL : IsInvertibleSheaf D p hp L)
    (_hTriv : IsTrivialOnVanishingLocus D p hp L s)
    (rule : GysinComponentRule D p (vanishingLocus D p hp L s) k) :
    CycleGroup D p (k + 1) →+ CycleGroup D ((vanishingLocus D p hp L s).1.ι ≫ p) k :=
  trivialRestrictionGysinCycleMap D p (vanishingLocus D p hp L s) hE k rule

/-- **Stacks 0ER2.** The defining requirement for the triple of Stacks 0ER1: the canonical map
on cycles vanishes on the cycle of an integral closed subspace contained in `E`. -/
theorem trivialRestrictionGysin_integralCycle_of_le (hL : IsInvertibleSheaf D p hp L)
    (hTriv : IsTrivialOnVanishingLocus D p hp L s)
    (rule : GysinComponentRule D p (vanishingLocus D p hp L s) k)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : W.subspace ≤ (vanishingLocus D p hp L s).1) :
    trivialRestrictionGysin D p hp L s k hE hL hTriv rule (integralCycle D p (k + 1) W hW) = 0 :=
  trivialRestrictionGysinCycleMap_integralCycle_of_le D p (vanishingLocus D p hp L s) hE k rule
    hW hWE

/-- **Stacks 0ER1(1)(a)** for the canonical map of Stacks 0ER2: on the cycle of an integral
closed subspace not contained in `E` the map is `[E ∩ W]_k`. -/
theorem trivialRestrictionGysin_integralCycle_of_not_le (hL : IsInvertibleSheaf D p hp L)
    (hTriv : IsTrivialOnVanishingLocus D p hp L s)
    (rule : GysinComponentRule D p (vanishingLocus D p hp L s) k)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    trivialRestrictionGysin D p hp L s k hE hL hTriv rule (integralCycle D p (k + 1) W hW) =
      rule.intersectionCycle W hW hWE :=
  trivialRestrictionGysinCycleMap_integralCycle_of_not_le D p (vanishingLocus D p hp L s) hE k
    rule hW hWE

/-- **Stacks 0ER2, canonicity** for the triple of Stacks 0ER1: a component rule whose cycle map
takes the two prescribed values on the cycle of every integral closed subspace has the canonical
map of Stacks 0ER2 as its cycle map. -/
theorem gysinCycleMap_eq_trivialRestrictionGysin (hL : IsInvertibleSheaf D p hp L)
    (hTriv : IsTrivialOnVanishingLocus D p hp L s)
    (rule rule' : GysinComponentRule D p (vanishingLocus D p hp L s) k)
    (hle : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1), W.subspace ≤ (vanishingLocus D p hp L s).1 →
      gysinCycleMap D p (vanishingLocus D p hp L s) hE k rule'
        (integralCycle D p (k + 1) W hW) = 0)
    (hnotle : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1)
      (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1),
      gysinCycleMap D p (vanishingLocus D p hp L s) hE k rule'
        (integralCycle D p (k + 1) W hW) = rule.intersectionCycle W hW hWE) :
    gysinCycleMap D p (vanishingLocus D p hp L s) hE k rule' =
      trivialRestrictionGysin D p hp L s k hE hL hTriv rule :=
  gysinCycleMap_eq_trivialRestriction D p (vanishingLocus D p hp L s) hE k rule rule' hle hnotle

/-- The refined Gysin homomorphism of Stacks 0ER1 on the cycle of an integral closed subspace is
the class of the cycle map of Stacks 0ER2 there, once the classes of the `W ⊆ E` components
vanish. -/
private theorem refinedGysin_integralCycle_eq_cls_trivialRestrictionGysinCycleMap
    (hL : IsInvertibleSheaf D p hp L)
    (rule : GysinComponentRule D p (vanishingLocus D p hp L s) k)
    {CH : Type w} [AddCommGroup CH]
    (chow : ChowTarget.{u, w, v} D ((vanishingLocus D p hp L s).1.ι ≫ p) hE k CH)
    (hchern : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1)
      (hWE : W.subspace ≤ (vanishingLocus D p hp L s).1),
      chow.cls (containedPushforward D p (vanishingLocus D p hp L s) hE k hWE
        (rule.chernCycle W hW hWE)) = 0)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) :
    refinedGysin D p hp L s k hE hL rule chow (integralCycle D p (k + 1) W hW) =
      chow.cls (trivialRestrictionGysinCycleMap D p (vanishingLocus D p hp L s) hE k rule
        (integralCycle D p (k + 1) W hW)) := by
  rw [refinedGysin, AddMonoidHom.comp_apply,
    gysinCycleMap_integralCycle D p (vanishingLocus D p hp L s) hE k rule hW,
    trivialRestrictionGysinCycleMap,
    gysinCycleMap_integralCycle D p (vanishingLocus D p hp L s) hE k _ hW]
  exact cls_gysinComponentCycle_eq_of_cls_chernCycle_eq_zero D p (vanishingLocus D p hp L s) hE k
    rule chow hchern W

/-- Consistency with Stacks 0ER1: once the class of `i'_*(c₁(ℒ|_W) ∩ [W])` vanishes for `W ⊆ E`,
the class of the canonical map of Stacks 0ER2 on the cycle of an integral closed subspace is the
refined Gysin homomorphism of Stacks 0ER1 there. -/
theorem refinedGysin_integralCycle_eq_trivialRestriction (hL : IsInvertibleSheaf D p hp L)
    (hTriv : IsTrivialOnVanishingLocus D p hp L s)
    (rule : GysinComponentRule D p (vanishingLocus D p hp L s) k)
    {CH : Type w} [AddCommGroup CH]
    (chow : ChowTarget.{u, w, v} D ((vanishingLocus D p hp L s).1.ι ≫ p) hE k CH)
    (hchern : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1)
      (hWE : W.subspace ≤ (vanishingLocus D p hp L s).1),
      chow.cls (containedPushforward D p (vanishingLocus D p hp L s) hE k hWE
        (rule.chernCycle W hW hWE)) = 0)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) :
    refinedGysin D p hp L s k hE hL rule chow (integralCycle D p (k + 1) W hW) =
      chow.cls (trivialRestrictionGysin D p hp L s k hE hL hTriv rule
        (integralCycle D p (k + 1) W hW)) :=
  refinedGysin_integralCycle_eq_cls_trivialRestrictionGysinCycleMap D p hp L s k hE hL rule chow
    hchern hW

end ZeroScheme

/-! ### The pair of Stacks 0ER1 and the canonical map on cycles -/

section CanonicalZeroScheme

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections) (k : ℤ)

/-- For a pair `(ℒ, s)` as in Stacks 0ER1, with `E = Z(s)` the vanishing locus
of `s` and `i : E → X` its closed immersion, the canonical map `i^* : Z_{k+1}(X) ⟶ Z_k(E)` on
cycles: the additive extension of the rule which sends the cycle of an integral closed subspace
`W ⊆ X` of δ-dimension `k + 1` to the cycle `[E ∩ W]_k` of the scheme-theoretic intersection
when `W ⊄ E`, as Stacks 0ER1(1)(a) prescribes, and to `0` when `W ⊆ E`, which is the requirement
of Stacks 0ER2. -/
@[stacks 0ER2 "the canonical map i^* : Z_{k+1}(X) → Z_k(D) on cycles of a pair (L, s) of
Definition 0ER1 with D = Z(s), constructed with clause (1)(a) of Stacks 0ER1 given by the cycle
[D ∩ W]_k of Stacks 0EE9 of the scheme-theoretic intersection D ∩ W = i^{-1}(W) and clause
(1)(b) by the zero cycle, which is the requirement i^*[W] = 0 for W ⊆ D of this remark; both
values are then proved of the map, in
canonicalTrivialRestrictionGysin_integralCycle_of_not_le and
canonicalTrivialRestrictionGysin_integralCycle_of_le, and determine it, in
gysinCycleMap_eq_canonicalTrivialRestrictionGysin"]
def canonicalTrivialRestrictionGysin :
    CycleGroup D p (k + 1) →+ CycleGroup D ((vanishingLocus D p hp L s).1.ι ≫ p) k :=
  trivialRestrictionGysinCycleMap D p (vanishingLocus D p hp L s)
    (isGood_vanishingLocus D p hp L s) k
    (canonicalTrivialRestrictionRule D p hp (vanishingLocus D p hp L s) k)

/-- The defining requirement for the pair of Stacks 0ER1: the canonical map on
cycles vanishes on the cycle of an integral closed subspace contained in `E`. -/
@[stacks 0ER2 "the defining requirement i^*[W] = 0 for W ⊆ D, proved of the canonical map on
cycles of the pair of Definition 0ER1"]
theorem canonicalTrivialRestrictionGysin_integralCycle_of_le
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : W.subspace ≤ (vanishingLocus D p hp L s).1) :
    canonicalTrivialRestrictionGysin D p hp L s k (integralCycle D p (k + 1) W hW) = 0 :=
  trivialRestrictionGysinCycleMap_integralCycle_of_le D p (vanishingLocus D p hp L s)
    (isGood_vanishingLocus D p hp L s) k _ hW hWE

/-- On the cycle of an integral closed subspace not contained in `E` the canonical map is the
cycle `[E ∩ W]_k` of Stacks 0EE9 of the scheme-theoretic intersection, as Stacks 0ER1(1)(a)
prescribes. -/
@[stacks 0ER2 "the remaining value i^*[W] = [D ∩ W]_k of Stacks 0ER1(1)(a), proved of the
canonical map on cycles, the right-hand side being the cycle of Stacks 0EE9 of the
scheme-theoretic intersection"]
theorem canonicalTrivialRestrictionGysin_integralCycle_of_not_le
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    canonicalTrivialRestrictionGysin D p hp L s k (integralCycle D p (k + 1) W hW) =
      gysinIntersectionCycle D p hp (vanishingLocus D p hp L s)
        (isGood_vanishingLocus D p hp L s) k W hW hWE :=
  trivialRestrictionGysinCycleMap_integralCycle_of_not_le D p (vanishingLocus D p hp L s)
    (isGood_vanishingLocus D p hp L s) k _ hW hWE

/-- Canonicity for the pair of Stacks 0ER1: a component rule whose cycle map
takes the two prescribed values on the cycle of every integral closed subspace has the canonical
map of Stacks 0ER2 as its cycle map. -/
@[stacks 0ER2 "canonicity of the canonical map on cycles of the pair of Definition 0ER1: the
requirement i^*[W] = 0 for W ⊆ D, together with the value [D ∩ W]_k of Stacks 0ER1(1)(a) on the
remaining integral closed subspaces, determines the map on cycles"]
theorem gysinCycleMap_eq_canonicalTrivialRestrictionGysin
    (rule' : GysinComponentRule D p (vanishingLocus D p hp L s) k)
    (hle : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1), W.subspace ≤ (vanishingLocus D p hp L s).1 →
      gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k rule'
        (integralCycle D p (k + 1) W hW) = 0)
    (hnotle : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1)
      (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1),
      gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k rule'
          (integralCycle D p (k + 1) W hW) =
        gysinIntersectionCycle D p hp (vanishingLocus D p hp L s)
          (isGood_vanishingLocus D p hp L s) k W hW hWE) :
    gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k rule' =
      canonicalTrivialRestrictionGysin D p hp L s k :=
  gysinCycleMap_eq_trivialRestriction D p (vanishingLocus D p hp L s)
    (isGood_vanishingLocus D p hp L s) k _ rule' hle hnotle

/-- The canonical map of Stacks 0ER2 lifts the refined Gysin homomorphism of Stacks 0ER1 off the
divisor, with no hypothesis on `ℒ`: on the cycle of an integral closed subspace of δ-dimension
`k + 1` not contained in `E` both are the class of the cycle `[E ∩ W]_k` of the scheme-theoretic
intersection. -/
theorem refinedGysin_integralCycle_eq_canonicalTrivialRestriction_of_not_le
    (hL : IsInvertibleSheaf D p hp L) (chern : FirstChernComponentCycleRule D p k)
    {CH : Type w} [AddCommGroup CH]
    (chow : ChowTarget.{u, w, v} D ((vanishingLocus D p hp L s).1.ι ≫ p)
      (isGood_vanishingLocus D p hp L s) k CH)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    refinedGysin D p hp L s k (isGood_vanishingLocus D p hp L s) hL
        (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s)
          (isGood_vanishingLocus D p hp L s) k chern) chow
        (integralCycle D p (k + 1) W hW) =
      chow.cls (canonicalTrivialRestrictionGysin D p hp L s k
        (integralCycle D p (k + 1) W hW)) := by
  rw [refinedGysin_integralCycle_of_not_le D p hp L s k (isGood_vanishingLocus D p hp L s) hL _
      chow hW hWE,
    canonicalTrivialRestrictionGysin_integralCycle_of_not_le D p hp L s k hW hWE,
    canonicalGysinComponentRule_intersectionCycle]

/-- The canonical map of Stacks 0ER2 lifts the refined Gysin homomorphism of Stacks 0ER1 over the
divisor too, once the class of `i'_*(c₁(ℒ|_W) ∩ [W])` vanishes for `W ⊆ E`: then the class of
this map on the cycle of an integral closed subspace of δ-dimension `k + 1` is the refined Gysin
homomorphism of Stacks 0ER1 there, in both cases of Stacks 0ER1(1).

The hypothesis is what the source's `ℒ|_E ≅ 𝒪_E` supplies through the second assertion of
Stacks 0EQK. -/
theorem refinedGysin_integralCycle_eq_canonicalTrivialRestriction
    (hL : IsInvertibleSheaf D p hp L) (chern : FirstChernComponentCycleRule D p k)
    {CH : Type w} [AddCommGroup CH]
    (chow : ChowTarget.{u, w, v} D ((vanishingLocus D p hp L s).1.ι ≫ p)
      (isGood_vanishingLocus D p hp L s) k CH)
    (hchern : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1)
      (hWE : W.subspace ≤ (vanishingLocus D p hp L s).1),
      chow.cls (containedPushforward D p (vanishingLocus D p hp L s)
        (isGood_vanishingLocus D p hp L s) k hWE (chern W hW)) = 0)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) :
    refinedGysin D p hp L s k (isGood_vanishingLocus D p hp L s) hL
        (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s)
          (isGood_vanishingLocus D p hp L s) k chern) chow
        (integralCycle D p (k + 1) W hW) =
      chow.cls (canonicalTrivialRestrictionGysin D p hp L s k
        (integralCycle D p (k + 1) W hW)) :=
  refinedGysin_integralCycle_eq_cls_trivialRestrictionGysinCycleMap D p hp L s k
    (isGood_vanishingLocus D p hp L s) hL _ chow hchern hW

end CanonicalZeroScheme

end AlgebraicGeometry.Space

end
