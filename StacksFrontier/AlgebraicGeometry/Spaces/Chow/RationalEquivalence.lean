module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceFamilySums
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFibreSum
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldEmbedding

/-!
# Rational equivalence and the Chow group of an algebraic space

In the situation of Stacks 0EDT let `X/B` be good and let `k ∈ ℤ`. A `k`-cycle `α ∈ Z_k(X)` is
*rationally equivalent to zero* when it is a sum `∑ (i_j)_* div(f_j)` of the kind produced by
part (1) of Stacks 0EQ6: the index runs over a locally finite family `{W_j ⊆ X}` of integral
closed subspaces of δ-dimension `k + 1`, and `f_j ∈ R(W_j)^*`. Two cycles are *rationally
equivalent* when their difference is rationally equivalent to zero, and the *Chow group*
`CH_k(X)` is the quotient of `Z_k(X)` by rational equivalence.

This file is parts (2), (3) and (4) of Stacks 0EQ6. Part (1) — that the sum is a well-defined
`k`-cycle — is `AlgebraicGeometry.Space.cycleFamilySum` of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceFamilySums`, and is used here as it
stands.

## Main definitions

* `AlgebraicGeometry.Space.IsPrincipalDivisorCycle`: the predicate "this `k`-cycle on `W` is the
  principal divisor `div(f)` of some `f ∈ R(W)^*`", that is, the condition the source puts on
  the summands.
* `AlgebraicGeometry.Space.IsRationallyEquivalentToZero`: **Stacks 0EQ6, part (2)**.
* `AlgebraicGeometry.Space.rationalEquivalences`: **Stacks 0EQ6, part (2)**, the same as a
  subgroup of `Z_k(X)`.
* `AlgebraicGeometry.Space.RationallyEquivalent`: **Stacks 0EQ6, part (3)**.
* `AlgebraicGeometry.Space.chowGroup`: **Stacks 0EQ6, part (4)**, the Chow group `CH_k(X)`.
* `AlgebraicGeometry.Space.chowClass`: **Stacks 0EQ6, part (4)**, the class map
  `Z_k(X) → CH_k(X)`.
* `AlgebraicGeometry.Space.chowTarget`: the Chow group of part (4) packaged as an inhabitant of
  `AlgebraicGeometry.Space.ChowTarget`, so that the results parameterized by an abstract Chow
  group can be instantiated at the constructed one.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.ord_one` and
  `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_neg_of_mul_eq_one`: the order of vanishing of `1`
  is zero, and `ord_Z(f⁻¹) = -ord_Z(f)`, both from additivity of the order of vanishing.
* `AlgebraicGeometry.Space.isPrincipalDivisorCycle_neg`: the negative of a principal divisor is
  the principal divisor of the inverse function.
* `AlgebraicGeometry.Space.rationallyEquivalent_equivalence`: **Stacks 0EQ6, part (3)**, rational
  equivalence is an equivalence relation.
* `AlgebraicGeometry.Space.chowClass_cycleFamilySum_eq_zero`: **Stacks 0EQ6, parts (2) and (4)**,
  the class in `CH_k(X)` of a sum `∑ (i_j)_* div(f_j)` of principal divisors is zero. This is a
  theorem about the constructed group, not a hypothesis about an assumed one.
* `AlgebraicGeometry.Space.chowClass_eq_iff_rationallyEquivalent`: two cycles have the same class
  exactly when they are rationally equivalent.

## Implementation notes

### The summand condition uses the canonical embedding of Stacks 0ENK

The source's summand is `div(f_j)` for `f_j ∈ R(W_j)^*`, the coefficient at a prime divisor
`Z ⊆ W_j` with generic point `ξ` being the order of vanishing of the image of `f_j` under the
*canonical* map `R(W_j) → Q(𝒪^h_{W_j, ξ})` of Stacks 0ENK. That map is
`AlgebraicGeometry.Space.genericFractionEmbedding`, built for a decent, locally Noetherian,
integral algebraic space; its fields also supply the three instance hypotheses of
`AlgebraicGeometry.Space.PrimeDivisor.ord` on the henselian local rings. The embedding is fixed,
not chosen: with an arbitrary ring map per prime divisor in its place one could take
`can_p ∘ (s ↦ s²)` at a point `p` of `ℙ¹` and the canonical map elsewhere, making `2[p] - [q]`
as well as `[p] - [q]` principal, so `[p] ∼_rat 0` and `CH_0(ℙ¹) = 0`.

What remains existential in `AlgebraicGeometry.Space.IsPrincipalDivisorCycle` is the goodness
and the integrality of `W_j` over the base — which hold for every integral closed subspace of a
good space, by `AlgebraicGeometry.Space.isGood_integralClosedSubspace` and the field
`isIntegralSpace` — and the unit `f_j` itself. Goodness and integrality are propositions, so
they cannot change which cycle a given `f_j` produces: the canonical embedding, the decency
`AlgebraicGeometry.Space.IsIntegralSpace.isDecentSpace` and the local Noetherianity
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isGood` are computed from
them, and any two proofs of a proposition are equal.

### `f ∈ R(W)^*` is a unit of `R(W)`

The source's `f_j ∈ R(W_j)^*` is read as a unit `f : R(W_j)ˣ` of the ring of rational functions.
`AlgebraicGeometry.Space.principalDivisorCycleSet` instead asks only that each image `emb W f`
be a unit, which for an integral `W` is the same condition but is formally weaker; the stronger
reading is used here because it is the source's, and because it is what makes the set of cycles
rationally equivalent to zero closed under negation: `div(f⁻¹) = -div(f)` needs an inverse of
`f` itself, the ring of rational functions of this repository being a commutative ring and not
a field.

### The quotient is by the set, not by the subgroup it generates

`AlgebraicGeometry.Space.rationalEquivalences` has as its carrier exactly the set of cycles the
source calls rationally equivalent to zero: the three closure properties are proved — the empty
family for `0`, the disjoint union of two families for a sum, and the inverse functions for a
negative — so `CH_k(X)` is the honest quotient `Z_k(X)/∼_{rat}` and not a quotient by a larger
generated subgroup.

### The index universe

The source's family `{W_j}_{j ∈ J}` has an unrestricted index set. Here `J` ranges over a
universe `v` which is a parameter of the definitions, so that
`AlgebraicGeometry.Space.chowGroup` is the quotient by the families indexed in that universe,
and the same `v` is the index universe of `AlgebraicGeometry.Space.ChowTarget`.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENL](https://stacks.math.columbia.edu/tag/0ENL)
* [Stacks Project, Tag 0ENP](https://stacks.math.columbia.edu/tag/0ENP)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### A sum over a disjoint union of index types -/


/-! ### The order of vanishing of an inverse -/

section OrdInverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
variable (hdec : IsDecentSpace B S hS Y) (Z : PrimeDivisor B S hS Y)
variable [Nontrivial ↥(Z.genericHenselianLocalRing B S hS hY hdec)]
variable [IsNoetherianRing ↥(Z.genericHenselianLocalRing B S hS hY hdec)]
variable [Ring.KrullDimLE 1 ↥(Z.genericHenselianLocalRing B S hS hY hdec)]

/-- The order of vanishing of `1` along a prime divisor is zero: it is its own double, by
additivity of the order of vanishing. -/
theorem PrimeDivisor.ord_one : Z.ord B S hS hY hdec 1 isUnit_one = 0 := by
  have h := PrimeDivisor.ord_mul B S hS hY hdec Z 1 1 isUnit_one isUnit_one
  rw [PrimeDivisor.ord_congr B S hS hY hdec Z (isUnit_one.mul isUnit_one) isUnit_one
    (one_mul 1)] at h
  omega

/-- Two units of the total ring of fractions whose product is `1` have opposite orders of
vanishing: `ord_Z(f⁻¹) = -ord_Z(f)`. -/
theorem PrimeDivisor.ord_eq_neg_of_mul_eq_one
    {x y : Z.genericTotalFractionRing B S hS hY hdec} (hx : IsUnit x) (hy : IsUnit y)
    (hxy : x * y = 1) :
    Z.ord B S hS hY hdec x hx = -Z.ord B S hS hY hdec y hy := by
  have h := PrimeDivisor.ord_mul B S hS hY hdec Z x y hx hy
  rw [PrimeDivisor.ord_congr B S hS hY hdec Z (hx.mul hy) isUnit_one hxy,
    PrimeDivisor.ord_one B S hS hY hdec Z] at h
  omega

end OrdInverse

/-! ### Principal divisors on an integral closed subspace -/

section PrincipalDivisorCycle

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The coefficient families of `div(f)` and `div(g)` are opposite when `f g = 1`: at a prime
divisor this is `AlgebraicGeometry.Space.PrimeDivisor.ord_eq_neg_of_mul_eq_one`, and elsewhere
both coefficients vanish. -/
theorem principalDivisorCycleCoefficients_of_mul_eq_one (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hdec : IsDecentSpace D.site D.base D.base_mem Y)
    [∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdec)]
    [∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdec)]
    (emb : ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      rationalFunctions D.site D.base D.base_mem hY.1 →+*
        W.genericTotalFractionRing D.site D.base D.base_mem hY.1 hdec)
    (f g : rationalFunctions D.site D.base D.base_mem hY.1)
    (hf : ∀ W : PrimeDivisor D.site D.base D.base_mem Y, IsUnit (emb W f))
    (hg : ∀ W : PrimeDivisor D.site D.base D.base_mem Y, IsUnit (emb W g))
    (hfg : f * g = 1) :
    principalDivisorCycleCoefficients D sY hY hdec emb f hf =
      -principalDivisorCycleCoefficients D sY hY hdec emb g hg := by
  funext Z
  by_cases h : codimension
      (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 Z) = 1
  · simp only [Pi.neg_apply, principalDivisorCycleCoefficients, h, ↓reduceDIte]
    exact PrimeDivisor.ord_eq_neg_of_mul_eq_one D.site D.base D.base_mem hY.1 hdec _ _ _
      (by rw [← map_mul, hfg, map_one])
  · simp only [Pi.neg_apply, principalDivisorCycleCoefficients, h, ↓reduceDIte, neg_zero]

/-- A `k`-cycle on an algebraic space `W/B` is a *principal divisor* when it is `div(f)` for a
rational function `f ∈ R(W)^*`: `W` is good and integral over the base, and the coefficient family
of the cycle is `AlgebraicGeometry.Space.principalDivisorCycleCoefficients` of a unit `f` of
`R(W)`, read through the **canonical** embeddings `R(W) → Q(𝒪^h_{W,ξ})` of Stacks 0ENK,
`AlgebraicGeometry.Space.genericFractionEmbedding`.

This is the condition the source puts on the summands of part (1) of Stacks 0EQ6. The embedding
is the canonical one and is not quantified: an arbitrary ring map per prime divisor would make
the condition far weaker than the source's — with `can_p ∘ (s ↦ s²)` at one point `p` of `ℙ¹`
both `2[p] - [q]` and `[p] - [q]` would be principal, so `CH_0(ℙ¹)` would be zero. The
quantified goodness and integrality of `W` are propositions, so they do not change which `f`
gives which cycle; the decency of `W` is `AlgebraicGeometry.Space.IsIntegralSpace.isDecentSpace`,
its local Noetherianity is
`AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isGood`, and the instance
hypotheses on the henselian local rings are the fields of the canonical embedding. -/
def IsPrincipalDivisorCycle (sY : Y ⟶ D.space) (k : ℤ) (c : CycleGroup D sY k) : Prop :=
  ∃ (hY : D.IsGood sY) (hint : IsIntegralSpace D.site D.base D.base_mem Y)
    (f : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ),
    letI E := genericFractionEmbedding D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
    letI := E.nontrivial
    letI := E.isNoetherianRing
    letI := E.krullDimLE
    (c : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) =
      principalDivisorCycleCoefficients D sY hY hint.isDecentSpace E.emb
        (f : rationalFunctions D.site D.base D.base_mem hY.1) fun W => f.isUnit.map (E.emb W)

/-- The negative of a principal divisor is a principal divisor: `-div(f) = div(f⁻¹)`, the inverse
being taken in the ring of rational functions, where `f` is a unit. -/
theorem isPrincipalDivisorCycle_neg (sY : Y ⟶ D.space) (k : ℤ) {c : CycleGroup D sY k}
    (h : IsPrincipalDivisorCycle D sY k c) : IsPrincipalDivisorCycle D sY k (-c) := by
  obtain ⟨hY, hint, f, heq⟩ := h
  let E := genericFractionEmbedding D.site D.base D.base_mem hY.1 hint.isDecentSpace hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY)
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  refine ⟨hY, hint, f⁻¹, ?_⟩
  have key := principalDivisorCycleCoefficients_of_mul_eq_one D sY hY hint.isDecentSpace E.emb
    (↑f⁻¹ : rationalFunctions D.site D.base D.base_mem hY.1)
    (f : rationalFunctions D.site D.base D.base_mem hY.1)
    (fun W => f⁻¹.isUnit.map (E.emb W)) (fun W => f.isUnit.map (E.emb W)) f.inv_mul
  change ((-c : CycleGroup D sY k) :
      IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) = _
  rw [show ((-c : CycleGroup D sY k) :
      IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) =
    -(c : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) from rfl, heq, key]

end PrincipalDivisorCycle

/-! ### Rational equivalence -/

section RationalEquivalence

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EQ6, part (2).** A `k`-cycle on a good algebraic space `X/B` is *rationally
equivalent to zero* when it is the cycle `∑ (i_j)_* div(f_j)` of part (1): there is a locally
finite family `{W_j ⊆ X}` of integral closed subspaces with `dim_δ(W_j) = k + 1`, and on each a
principal divisor `div(f_j)`, `f_j ∈ R(W_j)^*`, whose pushforwards sum to the cycle.

The sum is `AlgebraicGeometry.Space.cycleFamilySum`, which is part (1) of the source. -/
@[stacks 0EQ6 "part (2): rationally equivalent to zero. The sum is part (1), \
AlgebraicGeometry.Space.cycleFamilySum; the index type ranges over the universe v"]
def IsRationallyEquivalentToZero (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (α : CycleGroup D sX k) : Prop :=
  ∃ (J : Type v) (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k),
    (∀ j, deltaDimension D sX (W j) = k + 1) ∧
      (∀ j, IsPrincipalDivisorCycle D ((W j).subspace.ι ≫ sX) k (c j)) ∧
        α = cycleFamilySum D sX hX W hWfin k c

/-- The zero cycle is rationally equivalent to zero, via the empty family. -/
theorem isRationallyEquivalentToZero_zero (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :
    IsRationallyEquivalentToZero.{v} D sX hX k 0 := by
  have hcoeff : cycleFamilySumCoeff D sX hX (fun j : PEmpty.{v + 1} => nomatch j) k
      (fun j => nomatch j) = 0 := funext fun _ => finsum_of_isEmpty _
  exact ⟨PEmpty.{v + 1}, (fun j => nomatch j), locallyFinite_of_finite _, (fun j => nomatch j),
    (fun j => nomatch j), (fun j => nomatch j), Subtype.ext hcoeff.symm⟩

/-- The sum of two cycles rationally equivalent to zero is rationally equivalent to zero, via the
disjoint union of the two families. -/
theorem isRationallyEquivalentToZero_add (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    {α β : CycleGroup D sX k} (hα : IsRationallyEquivalentToZero.{v} D sX hX k α)
    (hβ : IsRationallyEquivalentToZero.{v} D sX hX k β) :
    IsRationallyEquivalentToZero.{v} D sX hX k (α + β) := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, hWsum⟩ := hα
  obtain ⟨K, V, hVfin, e, hVdim, hVprin, hVsum⟩ := hβ
  have hfin : LocallyFinite fun s : J ⊕ K =>
      subspacePointSet D.site D.base D.base_mem X (Sum.elim W V s).subspace := by
    have hsets : (fun s : J ⊕ K =>
        subspacePointSet D.site D.base D.base_mem X (Sum.elim W V s).subspace) =
        Sum.elim (fun j => subspacePointSet D.site D.base D.base_mem X (W j).subspace)
          (fun l => subspacePointSet D.site D.base D.base_mem X (V l).subspace) :=
      funext fun s => by cases s <;> rfl
    rw [hsets]
    exact hWfin.sumElim hVfin
  refine ⟨J ⊕ K, Sum.elim W V, hfin,
    (fun s => match s with | .inl j => c j | .inr l => e l),
    (fun s => match s with | .inl j => hWdim j | .inr l => hVdim l),
    (fun s => match s with | .inl j => hWprin j | .inr l => hVprin l), ?_⟩
  refine Subtype.ext (funext fun Z => ?_)
  have hsplit : (fun s : J ⊕ K => (integralClosedSubspacePushforward D sX hX
        (Sum.elim W V s) k (match s with | .inl j => c j | .inr l => e l)).1 Z) =
      Sum.elim (fun j => (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z)
        (fun l => (integralClosedSubspacePushforward D sX hX (V l) k (e l)).1 Z) :=
    funext fun s => by cases s <;> rfl
  change (α + β).1 Z = _
  rw [cycleFamilySum_apply, hsplit, Stacks.Chow.finsum_sum_elim _ _
      (finite_support_cycleFamilyCoeff D sX hX W hWfin k c Z)
      (finite_support_cycleFamilyCoeff D sX hX V hVfin k e Z)]
  rw [hWsum, hVsum]
  change (cycleFamilySum D sX hX W hWfin k c).1 Z + (cycleFamilySum D sX hX V hVfin k e).1 Z = _
  rw [cycleFamilySum_apply, cycleFamilySum_apply]

/-- The negative of a cycle rationally equivalent to zero is rationally equivalent to zero, via
the inverses of the same rational functions on the same family of subspaces. -/
theorem isRationallyEquivalentToZero_neg (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    {α : CycleGroup D sX k} (hα : IsRationallyEquivalentToZero.{v} D sX hX k α) :
    IsRationallyEquivalentToZero.{v} D sX hX k (-α) := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, hWsum⟩ := hα
  refine ⟨J, W, hWfin, (fun j => -c j), hWdim,
    (fun j => isPrincipalDivisorCycle_neg D _ k (hWprin j)), ?_⟩
  refine Subtype.ext (funext fun Z => ?_)
  change -α.1 Z = _
  rw [hWsum]
  show -(cycleFamilySum D sX hX W hWfin k c).1 Z = _
  rw [cycleFamilySum_apply, cycleFamilySum_apply, ← finsum_neg_distrib]
  refine finsum_congr fun j => ?_
  rw [map_neg]
  rfl

/-- **Stacks 0EQ6, part (2).** The subgroup of `k`-cycles rationally equivalent to zero. Its
carrier is exactly the set of cycles of the form `∑ (i_j)_* div(f_j)` of part (1); that this set
is a subgroup is the content of the three closure proofs. -/
@[stacks 0EQ6 "part (2): the cycles rationally equivalent to zero, as a subgroup of Z_k(X); the \
carrier is exactly the set of sums of part (1)"]
def rationalEquivalences (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :
    AddSubgroup (CycleGroup D sX k) where
  carrier := {α | IsRationallyEquivalentToZero.{v} D sX hX k α}
  zero_mem' := isRationallyEquivalentToZero_zero.{v} D sX hX k
  add_mem' := isRationallyEquivalentToZero_add.{v} D sX hX k
  neg_mem' := isRationallyEquivalentToZero_neg.{v} D sX hX k

/-- Membership in the subgroup of cycles rationally equivalent to zero is being rationally
equivalent to zero. -/
@[simp]
theorem mem_rationalEquivalences (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (α : CycleGroup D sX k) :
    α ∈ rationalEquivalences.{v} D sX hX k ↔ IsRationallyEquivalentToZero.{v} D sX hX k α :=
  Iff.rfl

/-- **Stacks 0EQ6, part (3).** Two `k`-cycles are *rationally equivalent* when their difference
is rationally equivalent to zero. -/
@[stacks 0EQ6 "part (3): α ∼_rat β, defined as α - β being rationally equivalent to zero"]
def RationallyEquivalent (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (α β : CycleGroup D sX k) : Prop :=
  IsRationallyEquivalentToZero.{v} D sX hX k (α - β)

/-- **Stacks 0EQ6, part (3).** Rational equivalence is an equivalence relation on `Z_k(X)`:
reflexivity, symmetry and transitivity are the three closure properties of the subgroup of
cycles rationally equivalent to zero, applied to `α - α = 0`, `β - α = -(α - β)` and
`α - γ = (α - β) + (β - γ)`. -/
@[stacks 0EQ6 "part (3): ∼_rat is an equivalence relation, from the subgroup property of the \
cycles rationally equivalent to zero"]
theorem rationallyEquivalent_equivalence (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :
    Equivalence (RationallyEquivalent.{v} D sX hX k) where
  refl α := by
    have h := isRationallyEquivalentToZero_zero.{v} D sX hX k
    rwa [← sub_self α] at h
  symm {α β} h := by
    have h' := isRationallyEquivalentToZero_neg.{v} D sX hX k h
    rwa [neg_sub] at h'
  trans {α β γ} h h' := by
    have h'' := isRationallyEquivalentToZero_add.{v} D sX hX k h h'
    rwa [sub_add_sub_cancel] at h''

end RationalEquivalence

/-! ### The Chow group -/

section ChowGroup

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EQ6, part (4).** The *Chow group of `k`-cycles on `X`*, that is the Chow group of
`k`-cycles modulo rational equivalence,

`CH_k(X) = Z_k(X)/∼_rat`,

the quotient of the group of `k`-cycles of a good algebraic space `X/B` by the subgroup of
cycles rationally equivalent to zero. -/
@[stacks 0EQ6 "part (4): CH_k(X) = Z_k(X)/∼_rat, the quotient of Z_k(X) by the subgroup of \
cycles rationally equivalent to zero"]
abbrev chowGroup (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :=
  CycleGroup D sX k ⧸ rationalEquivalences.{v} D sX hX k

/-- **Stacks 0EQ6, part (4).** The class map `Z_k(X) → CH_k(X)`, the quotient homomorphism. -/
@[stacks 0EQ6 "part (4): the class map Z_k(X) → CH_k(X) of the quotient by ∼_rat"]
def chowClass (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :
    CycleGroup D sX k →+ chowGroup.{v} D sX hX k :=
  QuotientAddGroup.mk' (rationalEquivalences.{v} D sX hX k)

/-- A cycle has class zero in `CH_k(X)` exactly when it is rationally equivalent to zero. -/
@[simp]
theorem chowClass_eq_zero_iff (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (α : CycleGroup D sX k) :
    chowClass.{v} D sX hX k α = 0 ↔ IsRationallyEquivalentToZero.{v} D sX hX k α := by
  rw [chowClass, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact Iff.rfl

/-- Two cycles have the same class in `CH_k(X)` exactly when they are rationally equivalent;
this is what makes `CH_k(X)` the quotient of `Z_k(X)` by `∼_rat`. -/
theorem chowClass_eq_iff_rationallyEquivalent (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (α β : CycleGroup D sX k) :
    chowClass.{v} D sX hX k α = chowClass.{v} D sX hX k β ↔
      RationallyEquivalent.{v} D sX hX k α β := by
  rw [← sub_eq_zero, ← map_sub, chowClass_eq_zero_iff]
  exact Iff.rfl

/-- **Stacks 0EQ6, parts (2) and (4).** The class in `CH_k(X)` of the cycle
`∑ (i_j)_* div(f_j)` of part (1) is zero: a sum of principal divisors on a locally finite family
of integral closed subspaces of δ-dimension `k + 1` is rationally equivalent to zero, hence dies
in the quotient. -/
@[stacks 0EQ6 "parts (2) and (4): the class map kills ∑ (i_j)_* div(f_j), the cycle of part (1); \
proved for the constructed CH_k(X), not assumed"]
theorem chowClass_cycleFamilySum_eq_zero (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    {J : Type v} (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k)
    (hWdim : ∀ j, deltaDimension D sX (W j) = k + 1)
    (hWprin : ∀ j, IsPrincipalDivisorCycle D ((W j).subspace.ι ≫ sX) k (c j)) :
    chowClass.{v} D sX hX k (cycleFamilySum D sX hX W hWfin k c) = 0 :=
  (chowClass_eq_zero_iff.{v} D sX hX k _).2 ⟨J, W, hWfin, c, hWdim, hWprin, rfl⟩

/-- The Chow group of part (4) as an inhabitant of `AlgebraicGeometry.Space.ChowTarget`, the
parameter bundle through which the results of this repository that need a Chow group receive
one. Its class map is `AlgebraicGeometry.Space.chowClass` and its vanishing field is the theorem
`AlgebraicGeometry.Space.chowClass_cycleFamilySum_eq_zero`, so those results can now be
instantiated at a constructed group rather than at an assumed one.

The `principalDivisors` field carries, besides the principal-divisor condition on the cycle, the
source's condition `dim_δ(W) = k + 1` on the subspace it lives on, which the field of
`AlgebraicGeometry.Space.ChowTarget` does not record separately. -/
def chowTarget (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :
    ChowTarget.{u, u + 1, v} D sX hX k (chowGroup.{v} D sX hX k) where
  cls := chowClass.{v} D sX hX k
  principalDivisors W :=
    {c | IsPrincipalDivisorCycle D (W.subspace.ι ≫ sX) k c ∧
      deltaDimension D sX W = k + 1}
  cls_cycleFamilySum_eq_zero W hWfin c hc :=
    chowClass_cycleFamilySum_eq_zero.{v} D sX hX k W hWfin c (fun j => (hc j).2)
      (fun j => (hc j).1)

end ChowGroup

end AlgebraicGeometry.Space

end
