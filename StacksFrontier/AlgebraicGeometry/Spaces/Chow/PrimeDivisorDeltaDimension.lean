module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Cycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.DeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.InducedDimensionFunction

/-!
# Prime divisors of an integral good algebraic space have δ-dimension one less

In Situation 0EDT let `X/B` be good and assume `X` is integral with `dim_δ(X) = n`. For an
integral closed subspace `Z ⊆ X` the three conditions

* `Z` is a prime divisor of `X`, in the sense of Stacks 0ENJ,
* `|Z|` has codimension one in `|X|`,
* `dim_δ(Z) = n - 1`

are equivalent. This is **Stacks 0EPZ, part (1)**, and it is what makes the principal divisor of
a rational function on `X` a cycle of δ-dimension `n - 1`.

The mathematical content is purely topological: on a sober space carrying a dimension function
`δ` which is irreducible with generic point `η`, an irreducible closed subset is the closure of
a point `x`, and its codimension is one exactly when `δ x = δ η - 1`. One direction is the
strict antitonicity of `δ` along nontrivial specializations; the other is the unit step of `δ`
along an immediate specialization, together with the observation that a point of codimension one
admits no point strictly between it and `η`.

## Main results

* `codimension_closureSingleton_eq_one_iff_dimensionFunction`: the topological statement, for an
  irreducible sober space with a dimension function.
* `AlgebraicGeometry.Space.isPrimeDivisor_tfae`: **Stacks 0EPZ, part (1)**, at the hypotheses of
  the source.
* `AlgebraicGeometry.Space.isPrimeDivisor_tfae_of_isIntegralSpace`: the same equivalence with a
  bundled dimension function on `|X|` supplied by the caller, the form in which the rest of the
  development uses it.

## Implementation notes

Codimension is `codimension` of Stacks 02I3, the coheight in the poset of irreducible closed
subsets, which is the form in which `AlgebraicGeometry.Space.PrimeDivisor` of Stacks 0ENJ
records it. The topological lemma is proved by transporting that coheight to the coheight of the
point in the specialization order along the order isomorphism `irreducibleSetEquivPoints` of a
sober space, where Mathlib's `Order.coheight_le_coe_iff` turns the bound `codimension ≤ 1` into
the statement that every point strictly above `x` is maximal, i.e. is the generic point. That
transport is a `private` lemma here because the two copies of it already in the library,
in `StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.AffineComplement` and in
`StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.NormalCriterion`, are themselves private;
the public form in `StacksFrontier.AlgebraicGeometry.CodimensionOneDivisor.Basic` is stated for a
scheme, not for a general sober space.

The dimension function `δ_{X/B}` of the situation enters the topological argument as a *bundled*
`TopologicalSpace.DimensionFunction` on `|X|` together with the hypothesis that its underlying
function is `AlgebraicGeometry.Space.BaseSpaceDimensionSituation.deltaValue`. That `δ_{X/B}` *is*
a dimension function is the assertion of Stacks 0EDN which Situation 0EDT invokes, and it is a
theorem of this library,
`AlgebraicGeometry.Space.exists_dimensionFunction_inducedDimensionValue`, whose hypotheses are
the standing data of Situation 0EDT together with goodness of `X/B`: decency of `X` is
`AlgebraicGeometry.Space.isDecentSpace_of_isGood` and decency of the base follows from its
quasi-separatedness. So `AlgebraicGeometry.Space.isPrimeDivisor_tfae` assumes no dimension
function: it produces one and feeds it to
`AlgebraicGeometry.Space.isPrimeDivisor_tfae_of_isIntegralSpace`, which keeps the bundled
function as an explicit argument because the rest of the development already has one at hand and
threads the same bundle through many steps.

The δ-dimension of `X` itself is `AlgebraicGeometry.Space.deltaDimensionClosed` at the whole
space of points, matching the source's `dim_δ(X) = dim_δ(|X|)`; it is an honest integer here
because `|X|` is irreducible.

Part (2) of Stacks 0EPZ, that an irreducible component of an effective Cartier divisor on `X`
has δ-dimension `n - 1`, is not proved in this module; it is
`AlgebraicGeometry.Space.deltaDimensionIrreducible_closureSingleton_isEffectiveCartierDivisor`
of `StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierComponentDeltaDimension`.

## References

* [Stacks Project, Tag 02I3](https://stacks.math.columbia.edu/tag/02I3)
* [Stacks Project, Tag 02I9](https://stacks.math.columbia.edu/tag/02I9)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0ENJ](https://stacks.math.columbia.edu/tag/0ENJ)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-! ### Codimension one on a sober space with a dimension function -/

/-- On a sober space the codimension of the closure of a point is the coheight of that point in
the specialization order: taking generic points is an order isomorphism from the irreducible
closed subsets onto the points. -/
private theorem codimension_closureSingleton_eq_coheight {α : Type*} [TopologicalSpace α]
    [QuasiSober α] [T0Space α] (x : α) :
    letI := specializationOrder α
    codimension (IrreducibleCloseds.closureSingleton x) = Order.coheight x := by
  let _ := specializationOrder α
  rw [codimension_eq_coheight,
    show IrreducibleCloseds.closureSingleton x = irreducibleSetEquivPoints.symm x from
      IrreducibleCloseds.ext rfl, Order.coheight_orderIso]

/-- On an irreducible sober space carrying a dimension function `δ`, the closure of a point `x`
has codimension one exactly when `δ x` is one less than the value of `δ` at the generic point.

For the forward implication, codimension one means that no point lies strictly between the
generic point and `x`, so the generic point specializes immediately to `x` and `δ` drops by
exactly one. For the converse, `δ` drops strictly along every nontrivial specialization, so a
point strictly above `x` has `δ`-value strictly between `δ x` and `δ` of the generic point,
hence must be the generic point itself; and the closure of `x` is a proper subset of the whole
space because `δ` separates `x` from the generic point. -/
theorem codimension_closureSingleton_eq_one_iff_dimensionFunction {α : Type*}
    [TopologicalSpace α] [QuasiSober α] [T0Space α] [IrreducibleSpace α]
    (δ : DimensionFunction α) (x : α) :
    codimension (IrreducibleCloseds.closureSingleton x) = 1 ↔
      δ x = δ (genericPoint α) - 1 := by
  let _ := specializationOrder α
  have hηmax : Order.coheight (genericPoint α) = 0 :=
    Order.IsMax.coheight_eq_zero fun b _ => genericPoint_specializes b
  have hcodim := codimension_closureSingleton_eq_coheight (α := α) x
  constructor
  · intro h
    have hcoh : Order.coheight x = ((1 : ℕ) : ℕ∞) := by
      rw [← hcodim, h, Nat.cast_one]
    have hxη : x ≠ genericPoint α := by
      intro hh
      rw [hh, hηmax] at hcoh
      exact absurd hcoh (by simp)
    have hmax : ∀ y : α, x < y → IsMax y := by
      intro y hy
      exact Order.coheight_eq_zero.mp
        (Order.lt_one_iff.mp (by simpa using Order.coheight_le_coe_iff.mp hcoh.le y hy))
    have himm : IsImmediateSpecialization (genericPoint α) x := by
      refine ⟨genericPoint_specializes x, Ne.symm hxη, fun z _ hzx => ?_⟩
      by_cases hz : z = x
      · exact Or.inr hz
      refine Or.inl (Specializes.antisymm ?_ (genericPoint_specializes z)).eq
      exact hmax z (lt_of_le_of_ne hzx (Ne.symm hz)) (genericPoint_specializes z)
    have := δ.step_immediate himm
    omega
  · intro h
    have hxη : x ≠ genericPoint α := by
      intro hh
      rw [hh] at h
      omega
    have hgt : x < genericPoint α := lt_of_le_of_ne (genericPoint_specializes x) hxη
    have hlow : (1 : ℕ∞) ≤ Order.coheight x := by
      have hstep := Order.coheight_add_one_le hgt
      rwa [hηmax, zero_add] at hstep
    have hhigh : Order.coheight x ≤ ((1 : ℕ) : ℕ∞) := by
      refine Order.coheight_le_coe_iff.mpr fun y hy => ?_
      have hlt1 : δ x < δ y := δ.strictAnti_specializes hy.le (ne_of_gt hy)
      have hyη : y = genericPoint α := by
        by_contra hc
        have hlt2 := δ.strictAnti_specializes (genericPoint_specializes y) (Ne.symm hc)
        omega
      rw [hyη, hηmax]
      simp
    rw [hcodim]
    refine le_antisymm ?_ hlow
    simpa using hhigh

/-! ### Prime divisors of an integral good algebraic space -/

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- The equivalence of Stacks 0EPZ, part (1), with a bundled dimension function on `|X|` supplied
by the caller. In Situation 0EDT let `X/B` be good and assume `X` integral with `dim_δ(X) = n`,
and let `d` be a dimension function on `|X|` whose underlying function is `δ_{X/B}`. For an
integral closed subspace `Z ⊆ X` the following are equivalent: `Z` is a prime divisor of `X`;
the set of points of `Z` has codimension one in `|X|`; and `dim_δ(Z) = n - 1`.

The first two are equivalent because a prime divisor of Stacks 0ENJ is by definition an integral
closed subspace whose generic point has codimension one, and the generic point of an integral
closed subspace of a good algebraic space is unique. The last two are equivalent by
`codimension_closureSingleton_eq_one_iff_dimensionFunction`, applied to `|X|`, which is sober
and irreducible, and to the dimension function `δ_{X/B}`.

The pair `d`, `hd` is not an input of Stacks 0EPZ, and it is not an assumption of this
development either: for a good `X/B` it is produced by Stacks 0EDN,
`AlgebraicGeometry.Space.exists_dimensionFunction_inducedDimensionValue`. The registered form of
part (1), with no dimension function among its hypotheses, is `isPrimeDivisor_tfae` below; this
declaration is the engine it calls, kept at the bundled form because the rest of the development
threads one bundle through many steps. -/
theorem isPrimeDivisor_tfae_of_isIntegralSpace (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (d : DimensionFunction (points D.site D.base D.base_mem X))
    (hd : ∀ x, d x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    List.TFAE
      [∃ W : PrimeDivisor D.site D.base D.base_mem X, W.subspace = Z.subspace,
        codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1,
        deltaDimension D sX Z = n - 1] := by
  have _hsober : QuasiSober (points D.site D.base D.base_mem X) :=
    quasiSober_points_of_isGood D sX hX
  have _ht0 : T0Space (points D.site D.base D.base_mem X) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX)
  have _hirr : IrreducibleSpace (points D.site D.base D.base_mem X) := hint.2.2
  obtain ⟨ξ, hgen⟩ : ∃ ξ : points D.site D.base D.base_mem X,
      IsGenericPoint ξ (subspacePointSet D.site D.base D.base_mem X Z.subspace) :=
    ⟨_, isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hX.1 Z⟩
  have hsupp : integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z =
      IrreducibleCloseds.closureSingleton ξ :=
    IrreducibleCloseds.ext hgen.symm
  have hZd : deltaDimension D sX Z = d ξ :=
    (deltaDimension_eq_of_isGenericPoint D sX hX.1 Z ξ hgen).trans (hd ξ).symm
  have hη : d (genericPoint (points D.site D.base D.base_mem X)) = n := by
    let T : IrreducibleCloseds (points D.site D.base D.base_mem X) :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
    rw [hd]
    exact (deltaDimensionIrreducible_eq_of_isGenericPoint D sX hX T
      (genericPoint_spec (points D.site D.base D.base_mem X))).symm.trans
        (WithBotTop.coe_injective
          ((deltaDimensionClosed_eq_deltaDimensionIrreducible D sX hX T).symm.trans hn))
  have hkey := codimension_closureSingleton_eq_one_iff_dimensionFunction d ξ
  tfae_have 1 ↔ 2 := by
    constructor
    · rintro ⟨W, hW⟩
      obtain ⟨ξ', hξ'gen, hξ'cod⟩ := W.codimension_one
      rw [hW] at hξ'gen
      rwa [hsupp, ← hξ'gen.eq hgen]
    · intro h
      exact ⟨⟨Z.subspace, Z.isClosedSubspace, Z.isIntegralSpace, ⟨ξ, hgen, by rwa [← hsupp]⟩⟩, rfl⟩
  tfae_have 2 ↔ 3 := by rwa [hsupp, hZd, ← hη]
  tfae_finish

/-- **Stacks 0EPZ, part (1).** In Situation 0EDT let `X/B` be good and assume `X` integral with
`dim_δ(X) = n`. For an integral closed subspace `Z ⊆ X` the following are equivalent: `Z` is a
prime divisor of `X`; the set of points of `Z` has codimension one in `|X|`; and
`dim_δ(Z) = n - 1`.

These are the hypotheses of the source and nothing else. The equivalence itself is
`isPrimeDivisor_tfae_of_isIntegralSpace`, which also takes a dimension function on `|X|` with
underlying function `δ_{X/B}`; that is not an input of Stacks 0EPZ but the conclusion of Stacks
0EDN, `exists_dimensionFunction_inducedDimensionValue`, applied to the standing data of
Situation 0EDT: the base is a quasi-separated, locally Noetherian, universally catenary
algebraic space with a dimension function, a quasi-separated algebraic space is decent, and a
good `X/B` is decent and locally of finite type over the base. -/
@[stacks 0EPZ "part (1)"]
theorem isPrimeDivisor_tfae (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    List.TFAE
      [∃ W : PrimeDivisor D.site D.base D.base_mem X, W.subspace = Z.subspace,
        codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1,
        deltaDimension D sX Z = n - 1] := by
  obtain ⟨d, hd⟩ := exists_dimensionFunction_inducedDimensionValue D.site D.base D.base_mem
    D.isAlgebraicSpace
    (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
      D.isAlgebraicSpace D.quasiSeparated)
    D.locallyNoetherian D.universallyCatenary D.delta hX.1 (isDecentSpace_of_isGood D sX hX) sX
    hX.2.2
  exact isPrimeDivisor_tfae_of_isIntegralSpace D sX hX hint d hd hn Z

end AlgebraicGeometry.Space

end
