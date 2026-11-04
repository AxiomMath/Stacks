module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowGroupDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence

/-!
# The Gysin homomorphism on Chow groups

In the situation of Stacks 0EDT let `X/B` be good and let `(ℒ, s, i : E → X)` be as in Definition
0ER1: `ℒ` an invertible sheaf on `X`, `s` a global section and `E = Z(s)` its vanishing locus
with its closed immersion into `X`.  Stacks 0ER1 builds the Gysin homomorphism on *cycles*,
`i^* : Z_{k+1}(X) ⟶ Z_k(E)`, which is `AlgebraicGeometry.Space.gysinCycleMap`.  Stacks 0ERA
asserts that it factors through rational equivalence, so that it descends to

  `i^* : CH_{k+1}(X) ⟶ CH_k(E)`.

The letter `D` is the dimension situation of Stacks 0EDT, so the closed subspace which the source
calls `D` is called `E` here, as in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection`.

**Stacks 0ERA is not proved here, and no declaration below carries its tag.**  What is proved is
that the assertion of Stacks 0ERA and the existence of the descended map are the *same*
statement, `AlgebraicGeometry.Space.gysinCycleMapFactorsThroughRationalEquivalence_iff`, together
with the descended map itself and its uniqueness.  The geometric half — the vanishing — is a
genuine gap of chapter 82 in this repository; the inputs it needs are listed in the
implementation notes.  Whoever proves them obtains Stacks 0ERA by feeding the result to
`AlgebraicGeometry.Space.gysinChowGroupMap`, and that is where the tag belongs.

## Main definitions

* `AlgebraicGeometry.Space.GysinCycleMapFactorsThroughRationalEquivalence`: the assertion of
  Stacks 0ERA at the level of cycles — the Gysin cycle map carries a cycle rationally equivalent
  to zero on `X` to a cycle rationally equivalent to zero on `E`.
* `AlgebraicGeometry.Space.gysinChowGroupMap`: the descended map `i^* : CH_{k+1}(X) ⟶ CH_k(E)`,
  given that assertion.
* `AlgebraicGeometry.Space.refinedGysinChowGroupMap`: the same for the refined Gysin homomorphism
  of Stacks 0ER1 valued in an arbitrary `AlgebraicGeometry.Space.ChowTarget` for `E`.

## Main results

* `AlgebraicGeometry.Space.gysinCycleMapFactorsThroughRationalEquivalence_iff`: **the assertion
  of Stacks 0ERA is exactly the descent.**  The Gysin cycle map carries rational equivalences to
  rational equivalences if and only if there is a homomorphism of Chow groups sending the class of
  `α` to the class of `i^*α`.  So nothing is lost by isolating the geometric content as the
  vanishing, and nothing beyond the vanishing is needed to produce the map.
* `AlgebraicGeometry.Space.gysinChowGroupMap_chowClass` and
  `AlgebraicGeometry.Space.eq_gysinChowGroupMap`: the descended map sends the class of `α` to the
  class of `i^*α`, and is the only homomorphism of Chow groups which does.
* `AlgebraicGeometry.Space.gysinCycleMapFactorsThroughRationalEquivalence_of_cycleFamilySum`: the
  assertion need only be checked on the cycles `∑ (i_j)_* div(f_j)` of Stacks 0EQ6 part (1),
  which is the form in which the source's proof begins.
* `AlgebraicGeometry.Space.refinedGysin_chowTarget`: at the constructed Chow group of Stacks 0EQ6
  part (4) the refined Gysin homomorphism of Stacks 0ER1 is the class map after the Gysin cycle
  map, so the two readings of `i^*` are the same map.
* `AlgebraicGeometry.Space.refinedGysin_chowTarget_eq_zero_iff`: there, the hypothesis of
  `AlgebraicGeometry.Space.refinedGysinChowGroupMap` is the assertion of Stacks 0ERA.

## Implementation notes

### What the vanishing needs, and why it is not here

The source's proof of Stacks 0ERA writes a cycle rationally equivalent to zero as
`α = ∑ i_{j,*} div_{W_j}(f_j)` over a locally finite family of integral closed subspaces `W_j` of
δ-dimension `k + 2`, forms `X' = ∐ W_j` with the square of Remark 0ER3, and then uses, in order:

* **Stacks 0ER5**, that the Gysin map commutes with proper pushforward, `i^* p_* = q_* (i')^*`.
  In this repository that identity is available only with the comparison it asserts carried as a
  structure parameter — `AlgebraicGeometry.Space.GysinProperPushforwardComparison` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinCompatibility` — so it is not a proved input.
* **Stacks 0EQC**, that proper pushforward factors through rational equivalence.  There is no
  declaration for it; proper pushforward on Chow groups of algebraic spaces does not exist here,
  which is also what stops the source's reduction from being carried out on classes.
* **Stacks 0EQY**, that `c₁(ℒ) ∩ α` is rationally equivalent to zero for `α = div(f)`, used in
  the case `E = X`.  Its local input is available: the cap product of Stacks 0EQJ is constructed,
  `AlgebraicGeometry.Space.canonicalFirstChernCap` from the constructed component cycle
  `AlgebraicGeometry.Space.canonicalFirstChernRule`, and at those choices it already kills a
  principal divisor cycle on a good integral algebraic space
  (`AlgebraicGeometry.Space.canonicalFirstChernCap_eq_zero_of_isPrincipalDivisorCycle`,
  `StacksFrontier/AlgebraicGeometry/Spaces/Chow/FirstChernCapPrincipalDivisor.lean:264`), which is
  what the source's proof needs on each member `W_j` of the family.  What is missing is the
  projection formula of Stacks 0EQT along `i_j : W_j ⟶ X`, which carries that conclusion from
  `W_j` to `X`.
* **Stacks 0ER9**, that `i^* div_X(f) = c₁(𝒪_E) ∩ [E]_{n-1}` in `CH_k(E)`, used in the case
  `E ≠ X`.  Absent.  Only the step *after* it is available: the source closes that case with
  "capping with `c₁(𝒪_E)` is the zero map", which is the second assertion of Stacks 0EQK and is
  proved unconditionally as `AlgebraicGeometry.Space.canonicalFirstChernCap_tensorUnit_eq_zero`
  (`StacksFrontier/AlgebraicGeometry/Spaces/Chow/CanonicalFirstChernCapAdditive.lean:609`).  So the
  case `E ≠ X` is blocked by Stacks 0ER9 alone.

None of these is a matter of effort in this file: each is a separate gap.  The vanishing is
therefore left as an explicit, named `Prop` rather than put into a field of the Gysin datum — a
field would make every consumer of the datum carry the assertion silently, which is the opposite
of what is wanted while the gap is open.

### The statement is made for an arbitrary component rule

`AlgebraicGeometry.Space.gysinCycleMap` is built from an arbitrary
`AlgebraicGeometry.Space.GysinComponentRule`, whose two clauses stand in for Stacks 0EE9 and
Stacks 0EQJ.  For an arbitrary rule the vanishing is plainly false — the values of the rule on
the subspaces contained in `E` are whatever the rule says — so it could not be a theorem at this
generality even with the four inputs above in hand.  That is a second reason it is a hypothesis
here: it becomes a theorem only once the rule is the canonical one, which is where Stacks 0ERA
will be registered.

### The descent itself is not redone here

The universal property of the quotient at the subgroup
`AlgebraicGeometry.Space.rationalEquivalences` is `AlgebraicGeometry.Space.chowGroupLift` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowGroupDescent`, and both constructions below are
that lemma applied — the Gysin cycle map and the refined Gysin homomorphism of Stacks 0ER1 both
already land in an abelian group, which is the shape `chowGroupLift` takes.  Reducing the
assertion to the cycles of Stacks 0EQ6 part (1) is likewise
`AlgebraicGeometry.Space.eq_zero_of_isRationallyEquivalentToZero` of that module.  Nothing in
this file re-derives either.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
* [Stacks Project, Tag 0ERA](https://stacks.math.columbia.edu/tag/0ERA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-! ### Factoring the Gysin cycle map through rational equivalence -/

section Factoring

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p)) (k : ℤ)
    (rule : GysinComponentRule D p E k)

/-- The assertion of **Stacks 0ERA** at the level of cycles: the Gysin cycle map
`i^* : Z_{k+1}(X) ⟶ Z_k(E)` of Stacks 0ER1 carries a cycle rationally equivalent to zero on `X`
to a cycle rationally equivalent to zero on `E`.

This is *not* proved in this repository.  The four inputs the source's proof needs — Stacks 0ER5,
0EQC, 0EQY and 0ER9 — are all missing or only conditionally available for algebraic spaces here;
see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupFactoring`.  It is also false for an
arbitrary component rule, which is why it is a named assertion and not a property derived from
`(ℒ, s)`. -/
def GysinCycleMapFactorsThroughRationalEquivalence : Prop :=
  ∀ α : CycleGroup D p (k + 1), IsRationallyEquivalentToZero.{v} D p hp (k + 1) α →
    IsRationallyEquivalentToZero.{v} D (E.1.ι ≫ p) hE k (gysinCycleMap D p E hE k rule α)

/-- The Gysin homomorphism on Chow groups, `i^* : CH_{k+1}(X) ⟶ CH_k(E)`: the Gysin cycle map of
Stacks 0ER1 descended through the quotients of Stacks 0EQ6 part (4), given that it factors
through rational equivalence. -/
def gysinChowGroupMap
    (hfac : GysinCycleMapFactorsThroughRationalEquivalence.{v} D p hp E hE k rule) :
    chowGroup.{v} D p hp (k + 1) →+ chowGroup.{v} D (E.1.ι ≫ p) hE k :=
  chowGroupLift D p hp (k + 1)
    ((chowClass.{v} D (E.1.ι ≫ p) hE k).comp (gysinCycleMap D p E hE k rule))
    fun α hα => (chowClass_eq_zero_iff.{v} D (E.1.ι ≫ p) hE k _).2 (hfac α hα)

/-- The descended Gysin map sends the class of a cycle `α` to the class of `i^*α`. -/
@[simp]
theorem gysinChowGroupMap_chowClass
    (hfac : GysinCycleMapFactorsThroughRationalEquivalence.{v} D p hp E hE k rule)
    (α : CycleGroup D p (k + 1)) :
    gysinChowGroupMap.{v} D p hp E hE k rule hfac (chowClass.{v} D p hp (k + 1) α) =
      chowClass.{v} D (E.1.ι ≫ p) hE k (gysinCycleMap D p E hE k rule α) :=
  rfl

/-- The descended Gysin map, composed with the class map of `X`, is the class map of `E` after
the Gysin cycle map.  This is the factorization asserted by Stacks 0ERA. -/
theorem gysinChowGroupMap_comp_chowClass
    (hfac : GysinCycleMapFactorsThroughRationalEquivalence.{v} D p hp E hE k rule) :
    (gysinChowGroupMap.{v} D p hp E hE k rule hfac).comp (chowClass.{v} D p hp (k + 1)) =
      (chowClass.{v} D (E.1.ι ≫ p) hE k).comp (gysinCycleMap D p E hE k rule) :=
  rfl

/-- The descended Gysin map is the only homomorphism of Chow groups sending the class of `α` to
the class of `i^*α`: the class map of `X` is surjective. -/
theorem eq_gysinChowGroupMap
    (hfac : GysinCycleMapFactorsThroughRationalEquivalence.{v} D p hp E hE k rule)
    (F : chowGroup.{v} D p hp (k + 1) →+ chowGroup.{v} D (E.1.ι ≫ p) hE k)
    (hF : F.comp (chowClass.{v} D p hp (k + 1)) =
      (chowClass.{v} D (E.1.ι ≫ p) hE k).comp (gysinCycleMap D p E hE k rule)) :
    F = gysinChowGroupMap.{v} D p hp E hE k rule hfac :=
  QuotientAddGroup.addMonoidHom_ext _ hF

/-- **The assertion of Stacks 0ERA is exactly the descent.**  The Gysin cycle map of Stacks 0ER1
carries cycles rationally equivalent to zero to cycles rationally equivalent to zero if and only
if there is a homomorphism `CH_{k+1}(X) ⟶ CH_k(E)` sending the class of `α` to the class of
`i^*α`.

So the content of Stacks 0ERA is the vanishing and nothing else: the map it produces is free once
the vanishing is known, and unique by `AlgebraicGeometry.Space.eq_gysinChowGroupMap`. -/
theorem gysinCycleMapFactorsThroughRationalEquivalence_iff :
    GysinCycleMapFactorsThroughRationalEquivalence.{v} D p hp E hE k rule ↔
      ∃ F : chowGroup.{v} D p hp (k + 1) →+ chowGroup.{v} D (E.1.ι ≫ p) hE k,
        F.comp (chowClass.{v} D p hp (k + 1)) =
          (chowClass.{v} D (E.1.ι ≫ p) hE k).comp (gysinCycleMap D p E hE k rule) := by
  refine ⟨fun hfac => ⟨gysinChowGroupMap.{v} D p hp E hE k rule hfac,
    gysinChowGroupMap_comp_chowClass.{v} D p hp E hE k rule hfac⟩, fun ⟨F, hF⟩ α hα => ?_⟩
  refine (chowClass_eq_zero_iff.{v} D (E.1.ι ≫ p) hE k _).1 ?_
  have h : F (chowClass.{v} D p hp (k + 1) α) =
      chowClass.{v} D (E.1.ι ≫ p) hE k (gysinCycleMap D p E hE k rule α) :=
    DFunLike.congr_fun hF α
  rw [← h, (chowClass_eq_zero_iff.{v} D p hp (k + 1) α).2 hα, map_zero]

/-- The assertion of Stacks 0ERA need only be checked on the cycles `∑ (i_j)_* div(f_j)` of
Stacks 0EQ6 part (1) — the form in which the source's proof begins — because by part (2) those
cycles are exactly the cycles rationally equivalent to zero.  This is
`AlgebraicGeometry.Space.eq_zero_of_isRationallyEquivalentToZero` read through
`AlgebraicGeometry.Space.chowClass_eq_zero_iff`. -/
theorem gysinCycleMapFactorsThroughRationalEquivalence_of_cycleFamilySum
    (h : ∀ (J : Type v) (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
      (hWfin : LocallyFinite fun j : J =>
        subspacePointSet D.site D.base D.base_mem X (W j).subspace)
      (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ p) (k + 1)),
      (∀ j, deltaDimension D p (W j) = k + 1 + 1) →
      (∀ j, IsPrincipalDivisorCycle D ((W j).subspace.ι ≫ p) (k + 1) (c j)) →
      IsRationallyEquivalentToZero.{v} D (E.1.ι ≫ p) hE k
        (gysinCycleMap D p E hE k rule (cycleFamilySum D p hp W hWfin (k + 1) c))) :
    GysinCycleMapFactorsThroughRationalEquivalence.{v} D p hp E hE k rule := fun α hα =>
  (chowClass_eq_zero_iff.{v} D (E.1.ι ≫ p) hE k _).1
    (eq_zero_of_isRationallyEquivalentToZero D p hp (k + 1)
      ((chowClass.{v} D (E.1.ι ≫ p) hE k).comp (gysinCycleMap D p E hE k rule))
      (fun J W hWfin c hWdim hWprin =>
        (chowClass_eq_zero_iff.{v} D (E.1.ι ≫ p) hE k _).2 (h J W hWfin c hWdim hWprin))
      α hα)

end Factoring

/-! ### The refined Gysin homomorphism of Stacks 0ER1 on Chow groups -/

section ZeroScheme

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections) (k : ℤ)
    (hE : D.IsGood ((vanishingLocus D p hp L s).1.ι ≫ p)) (hL : IsInvertibleSheaf D p hp L)
    (rule : GysinComponentRule D p (vanishingLocus D p hp L s) k)

/-- At the constructed Chow group of Stacks 0EQ6 part (4) the refined Gysin homomorphism of
Stacks 0ER1 is the class map after the Gysin cycle map: the two readings of `i^*` are the same
map, so a statement about either is a statement about the other. -/
theorem refinedGysin_chowTarget :
    refinedGysin D p hp L s k hE hL rule
        (chowTarget.{v} D ((vanishingLocus D p hp L s).1.ι ≫ p) hE k) =
      (chowClass.{v} D ((vanishingLocus D p hp L s).1.ι ≫ p) hE k).comp
        (gysinCycleMap D p (vanishingLocus D p hp L s) hE k rule) :=
  rfl

/-- The refined Gysin homomorphism of Stacks 0ER1, valued in an arbitrary
`AlgebraicGeometry.Space.ChowTarget` for `E`, descended to a homomorphism out of `CH_{k+1}(X)`
once it kills the cycles rationally equivalent to zero.

At the constructed Chow group of Stacks 0EQ6 part (4) the hypothesis is the assertion of Stacks
0ERA, by `AlgebraicGeometry.Space.refinedGysin_chowTarget_eq_zero_iff`. -/
def refinedGysinChowGroupMap {CH : Type w} [AddCommGroup CH]
    (chow : ChowTarget.{u, w, v} D ((vanishingLocus D p hp L s).1.ι ≫ p) hE k CH)
    (hfac : ∀ α : CycleGroup D p (k + 1), IsRationallyEquivalentToZero.{v} D p hp (k + 1) α →
      refinedGysin D p hp L s k hE hL rule chow α = 0) :
    chowGroup.{v} D p hp (k + 1) →+ CH :=
  chowGroupLift D p hp (k + 1) (refinedGysin D p hp L s k hE hL rule chow) hfac

/-- The descended refined Gysin homomorphism computes the refined Gysin homomorphism of Stacks
0ER1 on the class of a cycle. -/
@[simp]
theorem refinedGysinChowGroupMap_chowClass {CH : Type w} [AddCommGroup CH]
    (chow : ChowTarget.{u, w, v} D ((vanishingLocus D p hp L s).1.ι ≫ p) hE k CH)
    (hfac : ∀ α : CycleGroup D p (k + 1), IsRationallyEquivalentToZero.{v} D p hp (k + 1) α →
      refinedGysin D p hp L s k hE hL rule chow α = 0)
    (α : CycleGroup D p (k + 1)) :
    refinedGysinChowGroupMap.{v} D p hp L s k hE hL rule chow hfac
        (chowClass.{v} D p hp (k + 1) α) =
      refinedGysin D p hp L s k hE hL rule chow α :=
  rfl

/-- The descended refined Gysin homomorphism is the only homomorphism out of `CH_{k+1}(X)` which
computes the refined Gysin homomorphism of Stacks 0ER1 on the class of a cycle. -/
theorem eq_refinedGysinChowGroupMap {CH : Type w} [AddCommGroup CH]
    (chow : ChowTarget.{u, w, v} D ((vanishingLocus D p hp L s).1.ι ≫ p) hE k CH)
    (hfac : ∀ α : CycleGroup D p (k + 1), IsRationallyEquivalentToZero.{v} D p hp (k + 1) α →
      refinedGysin D p hp L s k hE hL rule chow α = 0)
    (F : chowGroup.{v} D p hp (k + 1) →+ CH)
    (hF : F.comp (chowClass.{v} D p hp (k + 1)) = refinedGysin D p hp L s k hE hL rule chow) :
    F = refinedGysinChowGroupMap.{v} D p hp L s k hE hL rule chow hfac :=
  QuotientAddGroup.addMonoidHom_ext _ hF

/-- For the constructed Chow group of Stacks 0EQ6 part (4), the hypothesis of
`AlgebraicGeometry.Space.refinedGysinChowGroupMap` is the assertion of Stacks 0ERA. -/
theorem refinedGysin_chowTarget_eq_zero_iff :
    (∀ α : CycleGroup D p (k + 1), IsRationallyEquivalentToZero.{v} D p hp (k + 1) α →
        refinedGysin D p hp L s k hE hL rule
          (chowTarget.{v} D ((vanishingLocus D p hp L s).1.ι ≫ p) hE k) α = 0) ↔
      GysinCycleMapFactorsThroughRationalEquivalence.{v} D p hp (vanishingLocus D p hp L s) hE k
        rule :=
  forall_congr' fun _ => forall_congr' fun _ =>
    chowClass_eq_zero_iff.{v} D ((vanishingLocus D p hp L s).1.ι ≫ p) hE k _

end ZeroScheme

end AlgebraicGeometry.Space

end
