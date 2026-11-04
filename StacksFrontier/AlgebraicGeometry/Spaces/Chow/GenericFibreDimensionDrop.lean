module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EqualDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FunctionFieldAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreChartPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorDeltaDimensionOfGood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.InducedDimensionAntitone
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeMonotone

/-!
# The generic fibre in the dimension-drop case has local rings of dimension at most one

In Situation 0EDT let `V` and `V'` be good integral algebraic spaces over the base and let
`q : V ⟶ V'` be a morphism over the base with

```
dim_δ(V) = dim_δ(V') + 1 = k + 1.
```

This file proves that every point of `V` lying over the generic point `ξ'` of `V'` has local
ring of dimension at most one, and that the only such point of dimension zero is the generic
point of `V`. Read through the homeomorphism of Stacks 0AC8 between the point space of the
fibre `V_{ξ'}` and the set-theoretic fibre of `|q|` over `ξ'`, this says that *the generic
fibre of `q` is one-dimensional* — the step of the proof of **Stacks 0EQC** that feeds
Stacks 0ADD in the branch `dim_δ(p(W)) = k`.

## Main results

* `AlgebraicGeometry.Space.localRingDimension_eq_one_of_deltaValue_eq`: in a good integral
  space of δ-dimension `k + 1`, a point where the induced dimension function of Stacks 0EDN
  takes the value `k` has local ring of dimension exactly one. This is Stacks 0ED1 read
  through the equivalence of Stacks 0EDX between codimension one and δ-dimension `k`.
* `AlgebraicGeometry.Space.deltaValue_eq_of_pointsMap_eq_genericPoint`: **the δ-dichotomy on
  the generic fibre.** A point of `V` over `ξ'` other than the generic point of `V` has
  δ-value exactly `k`.
* `AlgebraicGeometry.Space.localRingDimension_le_one_of_pointsMap_eq_genericPoint`: **the
  generic fibre is one-dimensional**, in the form Stacks 0ADD consumes.

## The argument

The source of Stacks 0EQC says only that "the δ-values are `k` or `k + 1`". Both halves of
that dichotomy are genuine inequalities and they come from opposite directions:

* *Above by* `k + 1`: the generic point of `V` specializes to every point of `|V|`, and the
  induced dimension function of Stacks 0EDN drops strictly along a nontrivial specialization
  (`AlgebraicGeometry.Space.lt_inducedDimensionValue_of_specializes`, the antitonicity clause).
  So a point other than the generic point has δ-value at most `k`.
* *Below by* `k`: the δ-value of a point is the δ-value of its image plus the relative
  transcendence degree, and the relative transcendence degree can only grow along `V ⟶ V'`
  (`AlgebraicGeometry.Space.inducedDimensionValue_le_of_comp`). A point over `ξ'` therefore
  has δ-value at least that of `ξ'`, which is `k`.

The second of these is where the hypothesis that `x` lies over the *generic* point is used; it
is also why `q` is not assumed quasi-finite. For a quasi-finite `q` the two δ-values would be
*equal* (`BaseSpaceDimensionSituation.deltaValue_comp_of_isLocallyQuasiFinite`), and the fibre
would be zero-dimensional — that is the case of Stacks 0EQ4, already available as
`AlgebraicGeometry.Space.exists_isPullback_residueFieldMorphism_genericPoint`.

With the δ-value pinned at `k`, the reduced induced closed subspace on the closure of `x` is an
integral closed subspace of δ-dimension `k`, hence of codimension one by Stacks 0EDX
(`AlgebraicGeometry.Space.isPrimeDivisor_tfae_of_isIntegralSpace'`), hence the local ring at
`x` has dimension one by Stacks 0ED1
(`AlgebraicGeometry.Space.codimension_eq_localRingDimension`). At the generic point itself the
local ring has dimension zero.

## What this does and does not give

Stacks 0EQC's dimension-drop branch needs the fibre `V_{ξ'} = V ×_{V'} Spec R(V')` to be a
*scheme*, by Stacks 0ADD, and then descends that along the limit presentation of `Spec R(V')`
by the nonempty affine opens of `V'`, by Stacks 07SR, so as to apply the scheme case
Stacks 02S2. What is proved here is the dimension input to Stacks 0ADD, measured on `V`
itself. Three things are still owed before Stacks 0ADD can be applied to the fibre:

1. the fibre as an object — the pullback of `V` along the residue field morphism of `V'` at
   `ξ'`, which `AlgebraicGeometry.Space.residueFieldMorphism` supplies on the base of the
   square but which no declaration in this repository forms for a `q` that is merely proper
   (`AlgebraicGeometry.Space.exists_isPullback_residueFieldMorphism_genericPoint` forms it for
   a *finite* `q`, where it is relatively representable by Stacks 03ZQ);
2. the comparison of local rings across that square: the local ring of `V'` at `ξ'` is already
   a field, so the fibre's local ring at a point over `x` agrees with that of `V` at `x`, and
   the bound proved here transfers;
3. separatedness and local Noetherianness of the fibre, which hold because the fibre is proper
   over a field, and which are *not* available on `V` itself — a good space need not be
   separated. This is why the source's argument passes to the fibre rather than staying on `V`.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0ED1](https://stacks.math.columbia.edu/tag/0ED1)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})

/-! ### A point one step below the generic point has local ring of dimension one -/

section OneStepDown

variable {V : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sV : V ⟶ D.space)
    (hV : D.IsGood sV) (hVint : IsIntegralSpace D.site D.base D.base_mem V)

/-- **A point of δ-value `k` in a good integral space of δ-dimension `k + 1` has local ring of
dimension one.**

The reduced induced closed subspace on the closure of `x` is an integral closed subspace whose
generic point is `x`, so its δ-dimension is the δ-value at `x`, namely `k`. By Stacks 0EDX that
is equivalent to its support having codimension one, and by Stacks 0ED1 the codimension of that
support is the dimension of the local ring at its generic point. -/
theorem localRingDimension_eq_one_of_deltaValue_eq (k : ℤ)
    (hVd : D.deltaValue sV (genericPoint D.site D.base D.base_mem hV.1 hVint) = k + 1)
    (x : points D.site D.base D.base_mem V) (hx : D.deltaValue sV x = k) :
    localRingDimension D.site D.base D.base_mem x = 1 := by
  have hdec : IsDecentSpace D.site D.base D.base_mem V := isDecentSpace_of_isGood D sV hV
  have hgen : IsGenericPoint x (subspacePointSet D.site D.base D.base_mem V
      (integralClosedSubspaceOfPoint D.site D.base D.base_mem hV.1 hdec x).subspace) :=
    isGenericPoint_integralClosedSubspaceOfPoint D.site D.base D.base_mem hV.1 hdec x
  have hn : deltaDimensionClosed D sV hV Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt) :=
    (deltaDimensionClosed_univ_eq_inducedDimensionValue_genericPoint D sV hV hVint).trans
      (congrArg (fun n : ℤ => (n : EInt)) hVd)
  have hδ : deltaDimension D sV
      (integralClosedSubspaceOfPoint D.site D.base D.base_mem hV.1 hdec x) = k + 1 - 1 := by
    rw [deltaDimension_eq_of_isGenericPoint D sV hV.1 _ x hgen, hx]
    ring
  have hcod : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hV.1
      (integralClosedSubspaceOfPoint D.site D.base D.base_mem hV.1 hdec x)) = 1 :=
    ((isPrimeDivisor_tfae_of_isIntegralSpace' D sV hV hVint hn
      (integralClosedSubspaceOfPoint D.site D.base D.base_mem hV.1 hdec x)).out 2 3).mpr hδ
  have hsupp : integralClosedSubspaceSupport D.site D.base D.base_mem hV.1
      (integralClosedSubspaceOfPoint D.site D.base D.base_mem hV.1 hdec x) =
      IrreducibleCloseds.closureSingleton x :=
    IrreducibleCloseds.ext hgen.symm
  have hxgen : IsGenericPoint x
      ((IrreducibleCloseds.closureSingleton x :
        IrreducibleCloseds (points D.site D.base D.base_mem V)) :
          Set (points D.site D.base D.base_mem V)) :=
    (IrreducibleCloseds.coe_closureSingleton x).symm
  rw [← codimension_eq_localRingDimension D.site D.base D.base_mem hV.1 hdec
    (IrreducibleCloseds.closureSingleton x) x hxgen, ← hsupp]
  exact hcod

end OneStepDown

/-! ### The δ-dichotomy on the generic fibre -/

section GenericFibre

variable {V V' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sV : V ⟶ D.space) (hV : D.IsGood sV)
    (hVint : IsIntegralSpace D.site D.base D.base_mem V)
    (sV' : V' ⟶ D.space) (hV' : D.IsGood sV')
    (hV'int : IsIntegralSpace D.site D.base D.base_mem V')
    (q : V ⟶ V') (hq : q ≫ sV' = sV)

include hV hq in
/-- **The δ-value of a point over the generic point of the target is at least the δ-dimension of
the target.** The δ-value of a point is the value of `δ` at its image in the base plus the
relative transcendence degree over that image, and the relative transcendence degree can only
grow when the structure morphism is factored through `q`; this is the monotonicity clause of
Stacks 0EDN. -/
theorem le_deltaValue_of_pointsMap_eq (hV' : D.IsGood sV')
    (x : points D.site D.base D.base_mem V) :
    D.deltaValue sV' (pointsMap D.site D.base D.base_mem V q x) ≤ D.deltaValue sV x := by
  have hft : IsLocallyOfFiniteType D.site D.base D.base_mem (q ≫ sV') := by
    rw [hq]; exact hV.2.2
  have h := inducedDimensionValue_le_of_comp D.site D.base D.base_mem hV.1 hV'.1
    D.isAlgebraicSpace D.delta.toFun q sV' hft hV'.2.2 x
  rw [hq] at h
  exact h

include hV hVint in
/-- **A point of a good integral space other than its generic point has δ-value at most one less
than the δ-dimension.** The generic point specializes to every point of the space, and the
induced dimension function of Stacks 0EDN drops strictly along a nontrivial specialization. -/
theorem deltaValue_le_of_ne_genericPoint (k : ℤ)
    (hVd : D.deltaValue sV (genericPoint D.site D.base D.base_mem hV.1 hVint) = k + 1)
    (x : points D.site D.base D.base_mem V)
    (hne : x ≠ genericPoint D.site D.base D.base_mem hV.1 hVint) :
    D.deltaValue sV x ≤ k := by
  have hlt : D.deltaValue sV x <
      D.deltaValue sV (genericPoint D.site D.base D.base_mem hV.1 hVint) :=
    lt_inducedDimensionValue_of_specializes D.site D.base D.base_mem hV.1
      (isDecentSpace_of_isGood D sV hV) D.isAlgebraicSpace
      (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
        D.isAlgebraicSpace D.quasiSeparated)
      D.locallyNoetherian D.universallyCatenary D.delta sV hV.2.2
      ((isGenericPoint_genericPoint D.site D.base D.base_mem hV.1 hVint).specializes
        (Set.mem_univ x))
      (Ne.symm hne)
  omega

include hV hVint hV' hV'int hq in
/-- **The δ-dichotomy on the generic fibre of Stacks 0EQC.** For `q : V ⟶ V'` a morphism over
the base of good integral algebraic spaces with `dim_δ(V) = dim_δ(V') + 1 = k + 1`, a point of
`V` lying over the generic point of `V'` and distinct from the generic point of `V` has δ-value
exactly `k`.

This is the source's "the δ-values are `k` or `k + 1`" made precise: the value is at most `k`
because the point is a nontrivial specialization of the generic point of `V`, and at least `k`
because it lies over a point of δ-value `k`. -/
theorem deltaValue_eq_of_pointsMap_eq_genericPoint (k : ℤ)
    (hVd : D.deltaValue sV (genericPoint D.site D.base D.base_mem hV.1 hVint) = k + 1)
    (hV'd : D.deltaValue sV' (genericPoint D.site D.base D.base_mem hV'.1 hV'int) = k)
    (x : points D.site D.base D.base_mem V)
    (hx : pointsMap D.site D.base D.base_mem V q x =
      genericPoint D.site D.base D.base_mem hV'.1 hV'int)
    (hne : x ≠ genericPoint D.site D.base D.base_mem hV.1 hVint) :
    D.deltaValue sV x = k := by
  have hge := le_deltaValue_of_pointsMap_eq D sV hV sV' q hq hV' x
  rw [hx, hV'd] at hge
  have hle := deltaValue_le_of_ne_genericPoint D sV hV hVint k hVd x hne
  omega

include hV hVint hV' hV'int hq in
/-- **The generic fibre of Stacks 0EQC's dimension-drop branch is one-dimensional.** For
`q : V ⟶ V'` a morphism over the base of good integral algebraic spaces with
`dim_δ(V) = dim_δ(V') + 1`, every point of `V` lying over the generic point of `V'` has local
ring of dimension at most one.

By Stacks 0AC8 the point space of the fibre `V ×_{V'} Spec R(V')` is homeomorphic to the
set-theoretic fibre of `|q|` over the generic point of `V'`, so this is the statement that that
fibre is one-dimensional, which is the dimension hypothesis of Stacks 0ADD.

The generic point of `V` is the only point of the fibre whose local ring has dimension zero;
every other one has local ring of dimension exactly one, by
`AlgebraicGeometry.Space.deltaValue_eq_of_pointsMap_eq_genericPoint` and
`AlgebraicGeometry.Space.localRingDimension_eq_one_of_deltaValue_eq`. -/
theorem localRingDimension_le_one_of_pointsMap_eq_genericPoint (k : ℤ)
    (hVd : D.deltaValue sV (genericPoint D.site D.base D.base_mem hV.1 hVint) = k + 1)
    (hV'd : D.deltaValue sV' (genericPoint D.site D.base D.base_mem hV'.1 hV'int) = k)
    (x : points D.site D.base D.base_mem V)
    (hx : pointsMap D.site D.base D.base_mem V q x =
      genericPoint D.site D.base D.base_mem hV'.1 hV'int) :
    localRingDimension D.site D.base D.base_mem x ≤ 1 := by
  by_cases hne : x = genericPoint D.site D.base D.base_mem hV.1 hVint
  · subst hne
    exact le_of_eq_of_le (localRingDimension_genericPoint_eq_zero D.site D.base D.base_mem hV.1
      hVint) zero_le_one
  · exact le_of_eq (localRingDimension_eq_one_of_deltaValue_eq D sV hV hVint k hVd x
      (deltaValue_eq_of_pointsMap_eq_genericPoint D sV hV hVint sV' hV' hV'int q hq k hVd hV'd
        x hx hne))

end GenericFibre

end AlgebraicGeometry.Space

end
