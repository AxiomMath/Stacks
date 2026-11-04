module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupFactoring
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceCanonical
public import StacksFrontier.Topology.LocallyFinite.Sigma

/-!
# The Gysin homomorphism against rational equivalence at the canonical embeddings

In the situation of Stacks 0EDT let `X/B` be good and let `(ℒ, s, i : E → X)` be as in
Definition 0ER1.  Stacks 0ER1 builds the Gysin homomorphism on *cycles*,
`i^* : Z_{k+1}(X) ⟶ Z_k(E)`, which is `AlgebraicGeometry.Space.gysinCycleMap`, and **Stacks
0ERA** asserts that it factors through rational equivalence, giving

  `i^* : CH_{k+1}(X) ⟶ CH_k(E)`.

The letter `D` is the dimension situation of Stacks 0EDT, so the closed subspace which the
source calls `D` is called `E` here, as in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection`.

`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinChowGroupFactoring` carries out the descent over
`AlgebraicGeometry.Space.chowGroup`, the quotient by the cycles rationally equivalent to zero in
the reading in which the embeddings `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK are quantified
existentially with no compatibility condition.  This file is the same descent over
`AlgebraicGeometry.Space.chowGroupCanonical` at **both** ends: the cycle rationally equivalent to
zero is one of `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical`, so its summands
arrive as `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood`, which is the predicate the
vanishing statements of this development consume
(`AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_eq_zero_of_isPrincipalDivisorCycleOfGood`
of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapPrincipalDivisorCanonical`), and the
conclusion is in `AlgebraicGeometry.Space.chowGroupCanonical` as well.  A map
`chowGroupCanonical (k+1) →+ chowGroup k` would be provable but would weaken the conclusion.

## Main definitions

* `AlgebraicGeometry.Space.GysinCycleMapFactorsThroughRationalEquivalenceCanonical`: the
  assertion of Stacks 0ERA at the level of cycles, with rational equivalence read at the
  canonical embeddings on both `X` and `E`.
* `AlgebraicGeometry.Space.gysinChowGroupMapCanonical`: the descended map
  `i^* : CH_{k+1}(X) ⟶ CH_k(E)` at the canonical embeddings, given that assertion.

## Main results

* `AlgebraicGeometry.Space.gysinCycleMap_cycleFamilySum_apply`: the Gysin cycle map of the cycle
  `∑_j (i_j)_* c_j` attached to a locally finite family `{W_j ⊆ X}` is, coefficientwise, the
  locally finite sum of the Gysin cycle maps of the summands.  Unconditional.
* `AlgebraicGeometry.Space.gysinCycleMapFactorsThroughRationalEquivalenceCanonical_iff`: the
  assertion is exactly the descent — it holds if and only if there is a homomorphism
  `CH_{k+1}(X) ⟶ CH_k(E)` sending the class of `α` to the class of `i^*α`, both classes taken at
  the canonical embeddings.
* `gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_pushforwardDivisor`:
  **the reduction to one member.**  The assertion follows from the statement that for a single
  integral closed subspace `V ⊆ X` of δ-dimension `k + 2` and a single principal divisor cycle
  `d` on `V` read at the canonical embeddings, `i^*((i_V)_* d)` is presented as a locally finite
  sum of principal divisor cycles on integral closed subspaces of `E` lying in `i^{-1}|V|`, again
  read at the canonical embeddings.

## Implementation notes

### The reduction runs on presentations

The source's proof of Stacks 0ERA writes a cycle rationally equivalent to zero as
`α = ∑ i_{j,*} div_{W_j}(f_j)` over a locally finite family of integral closed subspaces `W_j` of
δ-dimension `k + 2`, forms `X' = ∐ W_j` with the square of Remark 0ER3, moves `i^*` across `p_*`
by Lemma 0ER5, and then discards the pushforward by Lemma 0EQC (proper pushforward factors
through rational equivalence), which leaves the case of integral `X` with `α = div(f)`.

`gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_pushforwardDivisor`
replaces the last of those steps.  Assembling the per-member presentations into one presentation
on `E` is done here directly, from local finiteness of `{i^{-1}|W_j|}` — which is local
finiteness of `{|W_j|}` pulled back along the continuous `|E| → |X|` — and the reindexing of a
sum over `Σ j, K j` as an iterated sum.  So Stacks 0EQC, which the source uses to discard the
pushforward on classes, is not needed on presentations.

### The statement is made for an arbitrary component rule

`AlgebraicGeometry.Space.gysinCycleMap` is built from an arbitrary
`AlgebraicGeometry.Space.GysinComponentRule`, whose two clauses stand in for Stacks 0EE9 and
Stacks 0EQJ.  For an arbitrary rule the factoring assertion is false — the values of the rule on
the subspaces contained in `E` are whatever the rule says — so it is a named assertion and a
hypothesis, not a property derived from `(ℒ, s)`; it becomes a theorem only once the rule is the
canonical one of `AlgebraicGeometry.Space.canonicalGysinComponentRule`, which is where Stacks
0ERA belongs.  The reduction below is stated at the same generality, so it applies to the
canonical rule in particular.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
* [Stacks Project, Tag 0EQK](https://stacks.math.columbia.edu/tag/0EQK)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
* [Stacks Project, Tag 0ERA](https://stacks.math.columbia.edu/tag/0ERA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p)) (k : ℤ)
    (rule : GysinComponentRule D p E k)

/-! ### The Gysin cycle map of a locally finite sum of pushforwards -/

/-- At a fixed integral closed subspace `T ⊆ E` only finitely many pairs `(V, j)` contribute to
the coefficient of `i^*(∑_j (i_j)_* c_j)`: a nonzero coefficient of the component cycle of `V` at
`T` puts the image in `|X|` of the generic point of `T` inside `|V|`, because the component cycle
of `V` is carried by `i^{-1}(V)`, and a nonzero coefficient of `(i_j)_* c_j` at `V` puts `|V|`
inside `|W_j|`, so that point lies in `|W_j|`; local finiteness of the family `{|W_j|}` leaves
finitely many `j`, and local finiteness of the support of `(i_j)_* c_j` leaves finitely many `V`
for each. -/
theorem finite_support_gysinComponentCycle_mul_pushforward {J : Type v}
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ p) (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    (Function.support fun s : IntegralClosedSubspace D.site D.base D.base_mem X × J =>
      (integralClosedSubspacePushforward D p hp (W s.2) (k + 1) (c s.2)).1 s.1 *
        (gysinComponentCycle D p E hE k rule s.1).1 T).Finite := by
  classical
  set t : points D.site D.base D.base_mem E.1.toFunctor :=
    pointsMap D.site D.base D.base_mem T.subspace.toFunctor T.subspace.ι
      (T.genericPoint D.site D.base D.base_mem) with ht
  have htT : t ∈ subspacePointSet D.site D.base D.base_mem E.1.toFunctor T.subspace := ⟨_, rfl⟩
  set ξ : points D.site D.base D.base_mem X :=
    pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι t with hξ
  obtain ⟨V₀, hV₀, hV₀fin⟩ := hWfin ξ
  choose U hU hUfin using fun j : J =>
    locallyFinite_pushforward_support D p hp (W j) (k + 1) (c j) ξ
  refine (hV₀fin.biUnion fun j _ => (hUfin j).image fun V =>
    ((V, j) : IntegralClosedSubspace D.site D.base D.base_mem X × J)).subset ?_
  rintro ⟨V, j⟩ hVj
  have hterm : (integralClosedSubspacePushforward D p hp (W j) (k + 1) (c j)).1 V *
      (gysinComponentCycle D p E hE k rule V).1 T ≠ 0 := hVj
  have hpj := left_ne_zero_of_mul hterm
  have hξV : ξ ∈ subspacePointSet D.site D.base D.base_mem X V.subspace :=
    subspacePointSet_subset_of_gysinComponentCycle_ne_zero D p E hE k rule V T
      (right_ne_zero_of_mul hterm) htT
  have hξW : ξ ∈ subspacePointSet D.site D.base D.base_mem X (W j).subspace :=
    subspacePointSet_subset_of_pushforward_ne_zero D p hp (W j) (k + 1) (c j) V hpj hξV
  have hjf : j ∈ {j : J |
      (subspacePointSet D.site D.base D.base_mem X (W j).subspace ∩ V₀).Nonempty} :=
    ⟨_, hξW, mem_of_mem_nhds hV₀⟩
  refine Set.mem_biUnion hjf ⟨V, ⟨_, ?_, mem_of_mem_nhds (hU j)⟩, rfl⟩
  simp only [Set.mem_ite_empty_left]
  exact ⟨hpj, hξV⟩

/-- **Stacks 0ER1(2) against Stacks 0EQ6, part (1).**  The Gysin cycle map of the cycle
`∑_j (i_j)_* c_j` attached to a locally finite family `{W_j ⊆ X}` of integral closed subspaces
is, coefficientwise, the locally finite sum of the Gysin cycle maps `i^*((i_j)_* c_j)` of the
summands. -/
theorem gysinCycleMap_cycleFamilySum_apply {J : Type v}
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ p) (k + 1))
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    (gysinCycleMap D p E hE k rule (cycleFamilySum D p hp W hWfin (k + 1) c)).1 T =
      ∑ᶠ j : J, (gysinCycleMap D p E hE k rule
        (integralClosedSubspacePushforward D p hp (W j) (k + 1) (c j))).1 T := by
  calc (gysinCycleMap D p E hE k rule (cycleFamilySum D p hp W hWfin (k + 1) c)).1 T
      = ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
          (cycleFamilySum D p hp W hWfin (k + 1) c).1 V *
            (gysinComponentCycle D p E hE k rule V).1 T := rfl
    _ = ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X, ∑ᶠ j : J,
          (integralClosedSubspacePushforward D p hp (W j) (k + 1) (c j)).1 V *
            (gysinComponentCycle D p E hE k rule V).1 T :=
        finsum_congr fun V => by rw [cycleFamilySum_apply, finsum_mul]
    _ = ∑ᶠ j : J, ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
          (integralClosedSubspacePushforward D p hp (W j) (k + 1) (c j)).1 V *
            (gysinComponentCycle D p E hE k rule V).1 T :=
        Stacks.Chow.finsum_finsum_comm_of_finite_support _
          (finite_support_gysinComponentCycle_mul_pushforward D p hp E hE k rule W hWfin c T)
    _ = ∑ᶠ j : J, (gysinCycleMap D p E hE k rule
          (integralClosedSubspacePushforward D p hp (W j) (k + 1) (c j))).1 T := rfl

/-! ### Factoring the Gysin cycle map through rational equivalence at the canonical embeddings -/

/-- The assertion of **Stacks 0ERA** at the level of cycles, with rational equivalence read at
the canonical embeddings of Stacks 0ENK on both sides: the Gysin cycle map
`i^* : Z_{k+1}(X) ⟶ Z_k(E)` of Stacks 0ER1 carries a cycle rationally equivalent to zero on `X`
to a cycle rationally equivalent to zero on `E`.

`AlgebraicGeometry.Space.GysinCycleMapFactorsThroughRationalEquivalence` is the same assertion
with both readings existentially quantified.  Neither implies the other: the hypothesis here is
the weaker one and the conclusion the stronger one, and the subgroup
`AlgebraicGeometry.Space.rationalEquivalencesCanonical` is contained in
`AlgebraicGeometry.Space.rationalEquivalences` with no reverse inclusion
(`AlgebraicGeometry.Space.rationalEquivalencesCanonical_le_rationalEquivalences`).  This is the
form the source states, because the `div_{W_j}(f_j)` of its part (1) is read at the canonical
embedding. -/
def GysinCycleMapFactorsThroughRationalEquivalenceCanonical : Prop :=
  ∀ α : CycleGroup D p (k + 1), IsRationallyEquivalentToZeroCanonical.{v} D p hp (k + 1) α →
    IsRationallyEquivalentToZeroCanonical.{v} D (E.1.ι ≫ p) hE k
      (gysinCycleMap D p E hE k rule α)

/-- The Gysin homomorphism on Chow groups at the canonical embeddings,
`i^* : CH_{k+1}(X) ⟶ CH_k(E)`: the Gysin cycle map of Stacks 0ER1 descended through the quotients
of Stacks 0EQ6 part (4) read at the canonical embeddings, given that it factors through rational
equivalence there. -/
def gysinChowGroupMapCanonical
    (hfac : GysinCycleMapFactorsThroughRationalEquivalenceCanonical.{v} D p hp E hE k rule) :
    chowGroupCanonical.{v} D p hp (k + 1) →+ chowGroupCanonical.{v} D (E.1.ι ≫ p) hE k :=
  chowGroupCanonicalLift D p hp (k + 1)
    ((chowClassCanonical.{v} D (E.1.ι ≫ p) hE k).comp (gysinCycleMap D p E hE k rule))
    fun α hα => (chowClassCanonical_eq_zero_iff.{v} D (E.1.ι ≫ p) hE k _).2 (hfac α hα)

/-- The descended Gysin map sends the class of a cycle `α` to the class of `i^*α`. -/
@[simp]
theorem gysinChowGroupMapCanonical_chowClassCanonical
    (hfac : GysinCycleMapFactorsThroughRationalEquivalenceCanonical.{v} D p hp E hE k rule)
    (α : CycleGroup D p (k + 1)) :
    gysinChowGroupMapCanonical.{v} D p hp E hE k rule hfac
        (chowClassCanonical.{v} D p hp (k + 1) α) =
      chowClassCanonical.{v} D (E.1.ι ≫ p) hE k (gysinCycleMap D p E hE k rule α) :=
  rfl

/-- The descended Gysin map, composed with the class map of `X`, is the class map of `E` after
the Gysin cycle map.  This is the factorization asserted by Stacks 0ERA. -/
theorem gysinChowGroupMapCanonical_comp_chowClassCanonical
    (hfac : GysinCycleMapFactorsThroughRationalEquivalenceCanonical.{v} D p hp E hE k rule) :
    (gysinChowGroupMapCanonical.{v} D p hp E hE k rule hfac).comp
        (chowClassCanonical.{v} D p hp (k + 1)) =
      (chowClassCanonical.{v} D (E.1.ι ≫ p) hE k).comp (gysinCycleMap D p E hE k rule) :=
  rfl

/-- The descended Gysin map is the only homomorphism of Chow groups at the canonical embeddings
sending the class of `α` to the class of `i^*α`: the class map of `X` is surjective. -/
theorem eq_gysinChowGroupMapCanonical
    (hfac : GysinCycleMapFactorsThroughRationalEquivalenceCanonical.{v} D p hp E hE k rule)
    (F : chowGroupCanonical.{v} D p hp (k + 1) →+ chowGroupCanonical.{v} D (E.1.ι ≫ p) hE k)
    (hF : F.comp (chowClassCanonical.{v} D p hp (k + 1)) =
      (chowClassCanonical.{v} D (E.1.ι ≫ p) hE k).comp (gysinCycleMap D p E hE k rule)) :
    F = gysinChowGroupMapCanonical.{v} D p hp E hE k rule hfac :=
  AddMonoidHom.ext fun c => QuotientAddGroup.induction_on c fun α =>
    congrFun (congrArg DFunLike.coe hF) α

/-- **The assertion of Stacks 0ERA is exactly the descent, at the canonical embeddings.**  The
Gysin cycle map of Stacks 0ER1 carries cycles rationally equivalent to zero to cycles rationally
equivalent to zero, both read at the canonical embeddings of Stacks 0ENK, if and only if there is
a homomorphism `CH_{k+1}(X) ⟶ CH_k(E)` of the corresponding Chow groups sending the class of `α`
to the class of `i^*α`.

So the content of Stacks 0ERA is the vanishing and nothing else: the map it produces is free once
the vanishing is known, and unique by
`AlgebraicGeometry.Space.eq_gysinChowGroupMapCanonical`. -/
theorem gysinCycleMapFactorsThroughRationalEquivalenceCanonical_iff :
    GysinCycleMapFactorsThroughRationalEquivalenceCanonical.{v} D p hp E hE k rule ↔
      ∃ F : chowGroupCanonical.{v} D p hp (k + 1) →+
          chowGroupCanonical.{v} D (E.1.ι ≫ p) hE k,
        F.comp (chowClassCanonical.{v} D p hp (k + 1)) =
          (chowClassCanonical.{v} D (E.1.ι ≫ p) hE k).comp (gysinCycleMap D p E hE k rule) := by
  refine ⟨fun hfac => ⟨gysinChowGroupMapCanonical.{v} D p hp E hE k rule hfac,
    gysinChowGroupMapCanonical_comp_chowClassCanonical.{v} D p hp E hE k rule hfac⟩,
    fun ⟨F, hF⟩ α hα => ?_⟩
  refine (chowClassCanonical_eq_zero_iff.{v} D (E.1.ι ≫ p) hE k _).1 ?_
  have h : F (chowClassCanonical.{v} D p hp (k + 1) α) =
      chowClassCanonical.{v} D (E.1.ι ≫ p) hE k (gysinCycleMap D p E hE k rule α) :=
    congrFun (congrArg DFunLike.coe hF) α
  rw [← h, (chowClassCanonical_eq_zero_iff.{v} D p hp (k + 1) α).2 hα, map_zero]

/-! ### The reduction to one member of the presenting family -/

/-- **The factoring assertion of Stacks 0ERA reduces to one member of the presenting family.**
Suppose that for every integral closed subspace `V ⊆ X` of δ-dimension `k + 2` and every
`(k+1)`-cycle `d` on `V` which is a principal divisor cycle in the canonical reading of part (1)
of Stacks 0EQ6, the Gysin cycle map of the pushforward `(i_V)_* d` is presented as the locally
finite sum `∑_l (i_{U_l})_* e_l` of principal divisor cycles — again in the canonical reading —
over integral closed subspaces `U_l ⊆ E` of δ-dimension `k` whose point sets lie in `i^{-1}|V|`.
Then the Gysin cycle map carries every cycle rationally equivalent to zero on `X` at the
canonical embeddings to a cycle rationally equivalent to zero on `E` at the canonical embeddings.
-/
theorem gysinCycleMapFactorsThroughRationalEquivalenceCanonical_of_pushforwardDivisor
    (hgys : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D p V = k + 1 + 1 →
      ∀ d : CycleGroup D (V.subspace.ι ≫ p) (k + 1),
        IsPrincipalDivisorCycleOfGood D (V.subspace.ι ≫ p)
            (isGood_integralClosedSubspace D p hp V) V.isIntegralSpace (k + 1) d →
          ∃ (K : Type v) (U : K → IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor)
            (hUfin : LocallyFinite fun l : K =>
              subspacePointSet D.site D.base D.base_mem E.1.toFunctor (U l).subspace)
            (e : ∀ l, CycleGroup D ((U l).subspace.ι ≫ (E.1.ι ≫ p)) k),
            (∀ l, subspacePointSet D.site D.base D.base_mem E.1.toFunctor (U l).subspace ⊆
                pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹'
                  subspacePointSet D.site D.base D.base_mem X V.subspace) ∧
              (∀ l, deltaDimension D (E.1.ι ≫ p) (U l) = k + 1) ∧
                (∀ l, IsPrincipalDivisorCycleOfGood D ((U l).subspace.ι ≫ (E.1.ι ≫ p))
                  (isGood_integralClosedSubspace D (E.1.ι ≫ p) hE (U l)) (U l).isIntegralSpace k
                  (e l)) ∧
                  gysinCycleMap D p E hE k rule
                      (integralClosedSubspacePushforward D p hp V (k + 1) d) =
                    cycleFamilySum D (E.1.ι ≫ p) hE U hUfin k e) :
    GysinCycleMapFactorsThroughRationalEquivalenceCanonical.{v} D p hp E hE k rule := by
  intro α hα
  obtain ⟨J, W, hWfin, c, hdim, hprin, hsum⟩ := hα
  choose K U hUfin e hsub hUdim hUprin heq using
    fun j : J => hgys (W j) (hdim j) (c j) (hprin j)
  have hTfin : LocallyFinite fun j : J =>
      pointsMap D.site D.base D.base_mem E.1.toFunctor E.1.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X (W j).subspace :=
    hWfin.preimage_continuous (continuous_pointsMap D.site D.base D.base_mem E.1.ι)
  have hVfin : LocallyFinite fun s : (j : J) × K j =>
      subspacePointSet D.site D.base D.base_mem E.1.toFunctor (U s.1 s.2).subspace :=
    locallyFinite_sigma_of_subset hTfin hUfin hsub
  refine ⟨(j : J) × K j, fun s => U s.1 s.2, hVfin, fun s => e s.1 s.2,
    fun s => hUdim s.1 s.2, fun s => hUprin s.1 s.2, Subtype.ext (funext fun T => ?_)⟩
  have hterm : ∀ j : J, (gysinCycleMap D p E hE k rule
      (integralClosedSubspacePushforward D p hp (W j) (k + 1) (c j))).1 T =
        ∑ᶠ l : K j,
          (integralClosedSubspacePushforward D (E.1.ι ≫ p) hE (U j l) k (e j l)).1 T := fun j => by
    rw [heq j]
    exact cycleFamilySum_apply D (E.1.ι ≫ p) hE (U j) (hUfin j) k (e j) T
  rw [hsum, gysinCycleMap_cycleFamilySum_apply D p hp E hE k rule W hWfin c T,
    finsum_congr hterm]
  exact (Stacks.Chow.finsum_sigma (fun s : (j : J) × K j =>
    (integralClosedSubspacePushforward D (E.1.ι ≫ p) hE (U s.1 s.2) k (e s.1 s.2)).1 T)
    (finite_support_cycleFamilyCoeff D (E.1.ι ≫ p) hE (fun s : (j : J) × K j => U s.1 s.2) hVfin k
      (fun s => e s.1 s.2) T)).symm

end AlgebraicGeometry.Space

end
