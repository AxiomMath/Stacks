module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalGysinRule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeGenericPoints

/-!
# The degree count on the proper side of Stacks 0ER5, at the generic points

In Situation 0EDT let `X/B` and `X'/B` be good, let `f : X' ⟶ X` be proper, let `E ⊆ X` be a
closed subspace with closed immersion `i : E → X`, and form the diagram of Remark 0ER3

```
E' --i'--> X'
|          |
g          f
|          |
v          v
E  --i-->  X
```

with `E' = f^{-1}(E)` and `g : E' ⟶ E`.  **Stacks 0ER5** is the identity
`i^* f_* α' = g_* (i')^* α'` of `k`-cycles on `E`, which
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinCompatibility` proves from one carried
coefficient identity at a prime cycle, the single field
`AlgebraicGeometry.Space.GysinProperPushforwardComparison.gysinCoeff_comm`.

With the component rule of `AlgebraicGeometry.Space.canonicalGysinComponentRule` on both sides,
that field at an integral closed subspace `W' ⊆ X'` **not** contained in `E'` is the degree
count

`deg(W'/W) · m_T(E ∩ W) = ∑_{T' ⊆ E'} m_{T'}(E' ∩ W') · deg(T'/T)`,

for `W` the closure of the image of `W'` under `f` and `T ⊆ E` an integral closed subspace; the
multiplicities are those of Stacks 0EE9 and the degrees those of Stacks 0EP1.  **This file
proves that identity**, so the non-contained branch of the comparison field is no longer
carried.  What is carried instead is the *dictionary* between the four numbers and invariants of
two rings, `AlgebraicGeometry.Space.GysinProperPushforwardGenericPointDatum`, exactly as
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeGenericPoints` does for the
degree count of Stacks 0EPD.  The arithmetic is the same one, Stacks 02M0 against freeness, and
is reused rather than reproved: it is
`Stacks.Length.finrank_mul_length_eq_sum_finrank_mul_length_localizedModule`.

## What the identity is, locally

Write `ζ` for the generic point of `W`, `t` for the generic point of `T`, which lies over `ζ`.
Let `A` be the local ring of the scheme-theoretic intersection `E ∩ W = i^{-1}(W)` at `t`, so
that `m_T(E ∩ W) = length_A(A)`.  Over `ζ` the morphism `f` restricted to `W'` is the finite
extension of function fields `R(W')/R(W)`, of degree `deg(W'/W)`; hence the ring `B` of
`E' ∩ W' = (i')^{-1}(W')` along the fibre of `g` over `t` is the base change
`R(W') ⊗_{R(W)} A`, a finite *free* `A`-algebra of rank `deg(W'/W)`.  Its maximal ideals are the
generic points `T'` of `E' ∩ W'` above `t`, with `m_{T'}(E' ∩ W') = length_{B_𝔮}(B_𝔮)` and
`deg(T'/T) = [κ(𝔮) : κ(A)]`.  So the identity reads

`rank_A(B) · length_A(A) = ∑_𝔮 [κ(𝔮) : κ(A)] · length_{B_𝔮}(B_𝔮)`,

which is `length_A(B)` computed in two ways.

## Main definitions

* `AlgebraicGeometry.Space.gysinIntersectionMult`: the multiplicity `m_T(E ∩ W)` of Stacks 0EE9
  of an integral closed subspace `T ⊆ E` in the scheme-theoretic intersection `E ∩ W`, which is
  the coefficient of clause (1)(a) of Stacks 0ER1.
* `AlgebraicGeometry.Space.GysinProperPushforwardGenericPointDatum`: **the carried
  hypothesis.** The two rings above, together with the identification of the four numbers of the
  degree count with their invariants.  It carries no sum and no identity between the numbers.

## Main results

* `AlgebraicGeometry.Space.not_le_closureImage_of_not_le`: **the other half of the case matching
  of Stacks 0ER5.**  If `W' ⊄ E'` then the closure `W` of the image of `W'` is not contained in
  `E`, so the non-contained branch of Stacks 0ER1 on `X'` forces the non-contained branch on
  `X`.  This is the converse direction of `AlgebraicGeometry.Space.closureImage_le_of_le`, and
  like it rests on Stacks 03JJ through
  `AlgebraicGeometry.Space.le_of_subspacePointSet_subset_of_integral`.
* `AlgebraicGeometry.Space.properCycleDegree_mul_gysinIntersectionMult_eq_finsum`: **the degree
  count on the proper side of Stacks 0ER5, proved** from one datum at one pair.
* `AlgebraicGeometry.Space.gysinCoeff_comm_of_genericPointData_of_not_le`: **the non-contained
  branch of `AlgebraicGeometry.Space.GysinProperPushforwardComparison.gysinCoeff_comm`**, at the
  canonical component rules, discharged.
* `AlgebraicGeometry.Space.gysinProperPushforwardComparison_of_genericPointData`: an inhabitant
  of `AlgebraicGeometry.Space.GysinProperPushforwardComparison` from the generic-point data at
  the non-contained pairs together with the contained branch as a hypothesis.
* `AlgebraicGeometry.Space.gysinCycleMap_properPushforward_eq_of_genericPointData`:
  **Stacks 0ER5** as a plain equality of `k`-cycles on `E`, with the non-contained branch of the
  comparison no longer assumed.

## Implementation notes

### Which branch is closed, and which is not

The source's proof of Stacks 0ER5 splits on whether `W' ⊆ D'`.

* `W' ⊄ D'`: the source identifies `[D' ∩ W']_k` with `div_{ℒ'|_{W'}}(s'|_{W'})` and
  `[D ∩ W]_k` with `div_{ℒ|_W}(s|_W)` and appeals to the first assertion of Stacks 0EQS, whose
  statement is `f_*(div_{f^*ℒ}(f^*s)) = [R(X) : R(Y)] div_ℒ(s)` — a degree count, with the
  degree `[R(W') : R(W)] = deg(W'/W)`.  **This is the branch closed here**, and it is closed on
  the multiplicities of Stacks 0EE9 themselves rather than through the source's two
  identifications with divisors of sections: those identifications are the first assertion of
  Stacks 0EQF, whose coefficient identity at a prime divisor is *not* available in this
  repository — see the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.Chow.DivisorOfSectionCycle` — and they would in addition
  need the restriction of `ℒ` and of `s` to `W`, that is a pullback of modules along a morphism
  of algebraic spaces, which does not exist here either.  Going through the lengths directly
  avoids both, at the price of the dictionary this file carries.
* `W' ⊆ D'`: the source appeals to the second assertion of Stacks 0EQS, which compares
  `f_*(c₁(ℒ'|_{W'}) ∩ [W'])` with `c₁(ℒ|_W) ∩ [W]`.  Clause (1)(b) of Stacks 0ER1 is the free
  parameter `AlgebraicGeometry.Space.GysinComponentRule.chernCycle`, which
  `AlgebraicGeometry.Space.canonicalGysinComponentRule` passes along unchanged as the component
  datum of Stacks 0EQJ; `chern` on `X` and `chern'` on `X'` are therefore unrelated data and
  **this branch stays a hypothesis**, `hchern` below.  The scheme-theoretic half of its case
  matching is proved: `AlgebraicGeometry.Space.closureImage_le_of_le`.

### What is proved and what is carried

Proved: the whole numerical identity, that is the passage from the four local invariants to the
equality of the degree count, including the collapse of the sum over all integral closed
subspaces of `E'` to the finite sum over the maximal ideals of `fibre`, and the collapse of the
sum over all integral closed subspaces of `X` on the left to the single image closure.  Carried:
the geometric dictionary, in the shape
`AlgebraicGeometry.Space.GysinProperPushforwardGenericPointDatum`.

Producing a datum needs the stalk of a fibre product of algebraic spaces at a geometric point —
the identification of the local ring of `E' ∩ W'` with `R(W') ⊗_{R(W)} A` — and the
identification of the multiplicities of Stacks 0EE9, which are geometric lengths, with lengths
of those rings.  Neither exists here: there is no pushforward and no inverse image of
`AlgebraicGeometry.Space.Modules` along a morphism of algebraic spaces, and the independence of
a geometric length of the geometric point chosen above a point of the space is Stacks 0EE1,
which this repository does not have.  This is the same wall the degree count of Stacks 0EPD
meets, and the same reason the source's own route to it is unavailable.

### The base change is read on points

The diagram of Remark 0ER3 has `E' = f^{-1}(E)`, and the only thing the case matching needs of
it is that its point set is `|f|^{-1}|E|`.  That is the hypothesis `hpt` below, rather than `E'`
being literally `AlgebraicGeometry.Space.gysinBaseChangeSubspace`, so the statements apply to
any closed subspace `E' ⊆ X'` whose point set is the inverse image — in particular to the
subspace of Remark 0ER3, for which `hpt` is
`AlgebraicGeometry.Space.subspacePointSet_preimage`.

### Universes

The two rings live in an arbitrary universe `v`, independent of the universe `u` of the site,
because no declaration here relates them to the spaces by anything but the four numerical
equalities.

## References

* [Stacks Project, Tag 0ER5](https://stacks.math.columbia.edu/tag/0ER5)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 02M0](https://stacks.math.columbia.edu/tag/02M0)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section ProperGysinGenericPoints

variable (D : BaseSpaceDimensionSituation.{u})
    {X X' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (p' : X' ⟶ D.space) (hp' : D.IsGood p')
    (f : X' ⟶ X)
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p))
    (E' : ClosedSubspaces D.site D.base D.base_mem X') (hE' : D.IsGood (E'.1.ι ≫ p'))
    (g : E'.1.toFunctor ⟶ E.1.toFunctor) (k : ℤ)

/-! ### The multiplicity of clause (1)(a) of Stacks 0ER1 -/

/-- The multiplicity `m_T(E ∩ W)` of Stacks 0EE9 with which an integral closed subspace
`T ⊆ E` occurs in the scheme-theoretic intersection `E ∩ W = i^{-1}(W)` of `E` with an integral
closed subspace `W ⊆ X`.

This is the coefficient at `T` of the cycle `[E ∩ W]_k` of clause (1)(a) of Stacks 0ER1, by
`AlgebraicGeometry.Space.gysinIntersectionMult_eq_coe`; unlike that cycle it needs no
δ-dimension bound to be formed, so it is the shape the degree count below is stated at.

The geometric representative is the canonical one: Stacks 0EE1 makes the multiplicity
independent of the choice, so no choice is carried here, matching
`AlgebraicGeometry.Space.gysinIntersectionCycle`. -/
def gysinIntersectionMult (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) : ℤ :=
  cycleCoeffOfClosedSubspace D (E.1.ι ≫ p) hE (gysinIntersectionSubspace D p hp E hE W).1
    (gysinIntersectionSubspace D p hp E hE W).2 k
    (canonicalGeometricPoint D.site D.base D.base_mem
      (gysinIntersectionSubspace D p hp E hE W).1.toFunctor) T

/-- The multiplicity of `T` in `E ∩ W` is the coefficient of `T` in the cycle `[E ∩ W]_k` of
clause (1)(a) of Stacks 0ER1, wherever that cycle is defined. -/
theorem gysinIntersectionMult_eq_coe
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1)
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    gysinIntersectionMult D p hp E hE k W T =
      (gysinIntersectionCycle D p hp E hE k W hW hWE).1 T :=
  rfl

/-- The coefficient at `T` of the component cycle of Stacks 0ER1 at the canonical component rule
is the multiplicity of `T` in `E ∩ W`, for an integral closed subspace `W` of δ-dimension
`k + 1` not contained in `E`. -/
theorem gysinComponentCycle_canonical_coe_eq_gysinIntersectionMult
    (chern : FirstChernComponentCycleRule D p k)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ E.1)
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    (gysinComponentCycle D p E hE k (canonicalGysinComponentRule D p hp E hE k chern) W).1 T =
      gysinIntersectionMult D p hp E hE k W T := by
  rw [gysinComponentCycle_of_not_le D p E hE k
    (canonicalGysinComponentRule D p hp E hE k chern) hW hWE,
    canonicalGysinComponentRule_intersectionCycle]
  rfl

/-! ### The other half of the case matching of Stacks 0ER5 -/

include hp' in
/-- **The other half of the proper-pushforward case matching of Stacks 0ER5.** In the diagram of
Remark 0ER3, an integral closed subspace `W' ⊆ X'` *not* contained in `E'` has the closure `W`
of its image under `f` not contained in `E`.

So the non-contained branch of Stacks 0ER1 on `X'` forces the non-contained branch on `X`,
which is what the source's first case needs; `AlgebraicGeometry.Space.closureImage_le_of_le` is
the contained branch of the same matching.  The argument is the contrapositive: if `W ⊆ E` then
every point of `|W'|` maps into `|W| ⊆ |E|`, so `|W'| ⊆ |f|^{-1}|E| = |E'|`, and a point-set
containment upgrades to a containment of subspaces because `W'` is integral — Stacks 03JJ,
through `AlgebraicGeometry.Space.le_of_subspacePointSet_subset_of_integral`. -/
theorem not_le_closureImage_of_not_le
    (hpt : subspacePointSet D.site D.base D.base_mem X' E'.1 =
      pointsMap D.site D.base D.base_mem X' f ⁻¹'
        subspacePointSet D.site D.base D.base_mem X E.1)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (hW'E' : ¬ W'.subspace ≤ E'.1) :
    ¬ (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
        (D.isDecentSpace_of_isGood p hp) f W').subspace ≤ E.1 := by
  intro hle
  refine hW'E' (le_of_subspacePointSet_subset_of_integral D hp'.1 E'.1 E'.2 W' ?_)
  rw [hpt]
  intro x hx
  refine subspacePointSet_mono_of_le D hle ?_
  rw [IntegralClosedSubspace.subspacePointSet_closureImage]
  exact subset_closure ⟨x, hx, rfl⟩

/-! ### The local data at the generic points -/

/-- **The local data at the generic points which the degree count on the proper side of Stacks
0ER5 is derived from.**  Fix an integral closed subspace `W' ⊆ X'`, write `W` for the closure of
its image under `f`, and fix an integral closed subspace `T ⊆ E`.  A datum consists of

* `base`, the local ring of the scheme-theoretic intersection `E ∩ W` at the generic point of
  `T`, and
* `fibre`, the ring of the intersection `E' ∩ W'` along the fibre of `g` over that generic
  point, finite and free over `base`,

together with the dictionary between the four numbers of the degree count and invariants of
those two rings: `degree_eq` reads the degree `deg(W'/W)` of Stacks 0EP1 as the rank of `fibre`
over `base`, `mult_eq` reads the multiplicity `m_T(E ∩ W)` of Stacks 0EE9 as the length of
`base`, and `componentMult_eq` and `componentDegree_eq` read the multiplicity
`m_{T'}(E' ∩ W')` and the degree `deg(T'/T)` at the subspace `component 𝔮` attached to a
maximal ideal `𝔮` of `fibre` as the length of the localization and as the residue degree
`[κ(𝔮) : κ(base)]`.

**No field relates the numbers to one another**: the degree count itself is proved from this
datum, by
`AlgebraicGeometry.Space.properCycleDegree_mul_gysinIntersectionMult_eq_finsum`.  What the datum
supplies is the comparison of the geometric multiplicities of Stacks 0EE9 with lengths of the
stalks of a fibre product, which is what this repository is missing — see the implementation
notes of this file.  The analogous degree
count for Stacks 0EPD needs no such datum: it is the theorem
`AlgebraicGeometry.Space.properCycleDegree_mul_flatPullbackMult_eq_finsum`
(`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeGenericPoints`), proved from
Stacks 0EP3(1), 073K(1) in degree zero and 02M1. The
same route may discharge the datum below. -/
structure GysinProperPushforwardGenericPointDatum
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) where
  /-- The local ring of `E ∩ W` at the generic point of `T`. -/
  base : Type v
  [commRingBase : CommRing base]
  [isLocalRingBase : IsLocalRing base]
  /-- The ring of `E' ∩ W'` along the fibre of `g` over the generic point of `T`. -/
  fibre : Type v
  [commRingFibre : CommRing fibre]
  [algebraFibre : Algebra base fibre]
  [finiteFibre : Module.Finite base fibre]
  [freeFibre : Module.Free base fibre]
  [artinianFibre : IsArtinian fibre fibre]
  [fintypeMaximalSpectrum : Fintype (MaximalSpectrum fibre)]
  [isLocalHomLocalization : ∀ q : MaximalSpectrum fibre,
    IsLocalHom (algebraMap base (Localization.AtPrime q.asIdeal))]
  /-- The integral closed subspace of `E'` at the maximal ideal `q` of `fibre`. -/
  component : MaximalSpectrum fibre →
    IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor
  /-- Distinct maximal ideals name distinct subspaces. -/
  injective_component : Function.Injective component
  /-- The multiplicity `m_T(E ∩ W)`, as a natural number. -/
  mult : ℕ
  /-- That number is the length of `base`. -/
  length_base : Module.length base base = mult
  /-- The multiplicity `m_{component q}(E' ∩ W')`, as a natural number. -/
  componentMult : MaximalSpectrum fibre → ℕ
  /-- That number is the length of the localization of `fibre` at `q`. -/
  length_localization : ∀ q : MaximalSpectrum fibre,
    Module.length (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl fibre) = componentMult q
  /-- The degree `deg(W'/W)` of Stacks 0EP1 is the rank of `fibre` over `base`. -/
  degree_eq : properCycleDegree D p' hp' p hp f W' = (Module.finrank base fibre : ℤ)
  /-- The multiplicity `m_T(E ∩ W)` of Stacks 0EE9 is `mult`. -/
  mult_eq : gysinIntersectionMult D p hp E hE k
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
        (D.isDecentSpace_of_isGood p hp) f W') T = (mult : ℤ)
  /-- The multiplicity of `component q` in `E' ∩ W'` is `componentMult q`. -/
  componentMult_eq : ∀ q : MaximalSpectrum fibre,
    gysinIntersectionMult D p' hp' E' hE' k  W' (component q) = (componentMult q : ℤ)
  /-- The degree of `component q` over `T` is the residue degree at `q`. -/
  componentDegree_eq : ∀ q : MaximalSpectrum fibre,
    properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g (component q) T =
      (Module.finrank (IsLocalRing.ResidueField base)
        (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) : ℤ)
  /-- An integral closed subspace of `E'` which is not one of the `component q` contributes
  nothing to the right-hand side of the degree count. -/
  vanishing : ∀ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
    (∀ q : MaximalSpectrum fibre, component q ≠ T') →
      gysinIntersectionMult D p' hp' E' hE' k  W' T' *
        properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T = 0

/-! ### The degree count -/

/-- **The degree count on the proper side of Stacks 0ER5 at one pair of generic points,
proved.**  For an integral closed subspace `W' ⊆ X'` with `f`-image closure `W`, and an integral
closed subspace `T ⊆ E`,

`deg(W'/W) · m_T(E ∩ W) = ∑_{T' ⊆ E'} m_{T'}(E' ∩ W') · deg(T'/T)`,

granted one `AlgebraicGeometry.Space.GysinProperPushforwardGenericPointDatum` at that pair.
This is the non-contained branch of the single field of
`AlgebraicGeometry.Space.GysinProperPushforwardComparison`, read off in
`AlgebraicGeometry.Space.gysinCoeff_comm_of_genericPointData_of_not_le`.

The sum on the right is over *all* integral closed subspaces of `E'`; the datum confines its
support to the finitely many subspaces named by the maximal ideals of `fibre`, so it collapses
to a finite sum over `MaximalSpectrum fibre`.  There the identity is
`Stacks.Length.finrank_mul_length_eq_sum_finrank_mul_length_localizedModule`, that is
`length_{base}(fibre)` computed by freeness on one side and by Stacks 02M0 on the other. -/
theorem properCycleDegree_mul_gysinIntersectionMult_eq_finsum
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor)
    (data : GysinProperPushforwardGenericPointDatum.{u, v} D p hp p' hp' f E hE E' hE' g k W' T) :
    properCycleDegree D p' hp' p hp f W' *
        gysinIntersectionMult D p hp E hE k
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
            (D.isDecentSpace_of_isGood p hp) f W') T =
      ∑ᶠ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
        gysinIntersectionMult D p' hp' E' hE' k  W' T' *
          properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T := by
  classical
  obtain ⟨A, B, comp, hcomp, m, hlenA, cm, hlenB, hdeg, hmult, hcm, hcd, hvan⟩ := data
  have hsub : (Function.support
      fun T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor =>
        gysinIntersectionMult D p' hp' E' hE' k  W' T' *
          properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T) ⊆
      ((Finset.univ.image comp :
        Finset (IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor)) : Set _) := by
    intro T' hT'
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    by_contra hc
    exact hT' (hvan T' fun q hq => hc ⟨q, hq⟩)
  rw [finsum_eq_finsetSum_of_support_subset _ hsub,
    Finset.sum_image fun x _ y _ hxy => hcomp hxy, hdeg, hmult,
    Finset.sum_congr rfl fun q _ => by rw [hcm q, hcd q]]
  have hring := Stacks.Length.finrank_mul_length_eq_sum_finrank_mul_length_localizedModule A B
    fun q => by rw [hlenB q]; exact ENat.natCast_ne_top _
  rw [hlenA] at hring
  simp only [hlenB] at hring
  have hnat : Module.finrank A B * m =
      ∑ q : MaximalSpectrum B, Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) * cm q := by
    have hcast : ((Module.finrank A B * m : ℕ) : ℕ∞) =
        ((∑ q : MaximalSpectrum B, Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) * cm q : ℕ) : ℕ∞) := by
      push_cast
      exact hring
    exact_mod_cast hcast
  have hlhs : (Module.finrank A B : ℤ) * (m : ℤ) = ((Module.finrank A B * m : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hlhs, hnat]
  push_cast
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

/-! ### The non-contained branch of the comparison of Stacks 0ER5 -/

/-- **The non-contained branch of the comparison datum of Stacks 0ER5, discharged.**  At the
canonical component rules of `AlgebraicGeometry.Space.canonicalGysinComponentRule` on both
sides, the coefficient identity which
`AlgebraicGeometry.Space.GysinProperPushforwardComparison` carries holds at every integral
closed subspace `W' ⊆ X'` of δ-dimension `k + 1` **not** contained in `E'`, granted the local
data at the generic points.

The sum on the left collapses to the closure `W` of the image of `W'`, the multiplicity of
Stacks 0EP1 vanishing elsewhere; `W` is not contained in `E` by
`AlgebraicGeometry.Space.not_le_closureImage_of_not_le`, and has δ-dimension `k + 1` as soon as
the degree is nonzero, so both sides are the two sides of the degree count
`AlgebraicGeometry.Space.properCycleDegree_mul_gysinIntersectionMult_eq_finsum`. -/
theorem gysinCoeff_comm_of_genericPointData_of_not_le
    (hpt : subspacePointSet D.site D.base D.base_mem X' E'.1 =
      pointsMap D.site D.base D.base_mem X' f ⁻¹'
        subspacePointSet D.site D.base D.base_mem X E.1)
    (chern : FirstChernComponentCycleRule D p k)
    (chern' : FirstChernComponentCycleRule D p' k)
    (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
    (hW' : deltaDimension D p' W' = k + 1) (hW'E' : ¬ W'.subspace ≤ E'.1)
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor)
    (data : GysinProperPushforwardGenericPointDatum.{u, v} D p hp p' hp' f E hE E' hE' g k W' T) :
    (∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        properCycleMult D p' hp' p hp f W' W *
          (gysinComponentCycle D p E hE k
            (canonicalGysinComponentRule D p hp E hE k chern) W).1 T) =
      ∑ᶠ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
        (gysinComponentCycle D p' E' hE' k
            (canonicalGysinComponentRule D p' hp' E' hE' k chern') W').1 T' *
          properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T := by
  set W := IntegralClosedSubspace.closureImage D.site D.base D.base_mem hp.1
    (D.isDecentSpace_of_isGood p hp) f W' with hWdef
  have hWE : ¬ W.subspace ≤ E.1 :=
    not_le_closureImage_of_not_le D p hp p' hp' f E E' hpt W' hW'E'
  have hleft : (∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      properCycleMult D p' hp' p hp f W' V *
        (gysinComponentCycle D p E hE k
          (canonicalGysinComponentRule D p hp E hE k chern) V).1 T) =
      properCycleDegree D p' hp' p hp f W' *
        gysinIntersectionMult D p hp E hE k  W T := by
    rw [finsum_eq_single _ W fun V hV => by
      rw [properCycleMult_eq_zero_of_ne D p' hp' p hp f W' (hWdef ▸ Ne.symm hV), zero_mul],
      properCycleMult_closureImage D p' hp' p hp f W']
    rcases eq_or_ne (properCycleDegree D p' hp' p hp f W') 0 with h0 | h0
    · rw [h0, zero_mul, zero_mul]
    · have hWdim : deltaDimension D p W = k + 1 := by
        rw [hWdef, deltaDimension_closureImage_of_properCycleDegree_ne_zero D p' hp' p hp f h0]
        exact hW'
      rw [gysinComponentCycle_canonical_coe_eq_gysinIntersectionMult D p hp E hE k chern
        hWdim hWE T]
  have hright : (∑ᶠ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
      (gysinComponentCycle D p' E' hE' k
          (canonicalGysinComponentRule D p' hp' E' hE' k chern') W').1 T' *
        properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T) =
      ∑ᶠ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
        gysinIntersectionMult D p' hp' E' hE' k  W' T' *
          properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T :=
    finsum_congr fun T' => by
      rw [gysinComponentCycle_canonical_coe_eq_gysinIntersectionMult D p' hp' E' hE' k chern'
        hW' hW'E' T']
  rw [hleft, hright]
  exact properCycleDegree_mul_gysinIntersectionMult_eq_finsum D p hp p' hp' f E hE E' hE' g k
      W' T data

/-- **An inhabitant of `AlgebraicGeometry.Space.GysinProperPushforwardComparison`.**  The local
data at the generic points of every pair `(W', T)` with `W' ⊄ E'` discharges the non-contained
branch of the single field that structure carries; the contained branch, which is the second
assertion of Stacks 0EQS for the free parameter
`AlgebraicGeometry.Space.GysinComponentRule.chernCycle`, stays the hypothesis `hchern`. -/
theorem gysinProperPushforwardComparison_of_genericPointData
    (hpt : subspacePointSet D.site D.base D.base_mem X' E'.1 =
      pointsMap D.site D.base D.base_mem X' f ⁻¹'
        subspacePointSet D.site D.base D.base_mem X E.1)
    (chern : FirstChernComponentCycleRule D p k)
    (chern' : FirstChernComponentCycleRule D p' k)
    (hdata : ∀ (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
        (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor),
      ¬ W'.subspace ≤ E'.1 →
        Nonempty (GysinProperPushforwardGenericPointDatum.{u, v} D p hp p' hp' f E hE E' hE' g k
            W' T))
    (hchern : ∀ (W' : IntegralClosedSubspace D.site D.base D.base_mem X'),
      deltaDimension D p' W' = k + 1 → W'.subspace ≤ E'.1 →
      ∀ T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor,
        (∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
            properCycleMult D p' hp' p hp f W' W *
              (gysinComponentCycle D p E hE k
                (canonicalGysinComponentRule D p hp E hE k chern) W).1 T) =
          ∑ᶠ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
            (gysinComponentCycle D p' E' hE' k
                (canonicalGysinComponentRule D p' hp' E' hE' k chern') W').1 T' *
              properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T) :
    GysinProperPushforwardComparison D p hp p' hp' f E hE E' hE' g k
      (canonicalGysinComponentRule D p hp E hE k chern)
      (canonicalGysinComponentRule D p' hp' E' hE' k chern') where
  gysinCoeff_comm W' hW' T := by
    by_cases hle : W'.subspace ≤ E'.1
    · exact hchern W' hW' hle T
    · exact gysinCoeff_comm_of_genericPointData_of_not_le D p hp p' hp' f E hE E' hE' g k
        hpt chern chern' W' hW' hle T (hdata W' T hle).some

/-- **Stacks 0ER5, with the non-contained branch of the comparison proved rather than carried.**
In Situation 0EDT let `f : X' ⟶ X` be a quasi-compact morphism of good algebraic spaces over
`B`, let `E ⊆ X` be a closed subspace with closed immersion `i : E → X`, and form the diagram of
Remark 0ER3, with `E'` a closed subspace of `X'` whose point set is `|f|^{-1}|E|`, sitting in a
cartesian square with `g : E' ⟶ E` and `i' : E' ⟶ X'`.  Then for every `(k+1)`-cycle `α'` on
`X'`

`i^* f_* α' = g_* (i')^* α'`,

an identity of `k`-cycles on `E`, hence of classes in `CH_k(E)`, for the refined Gysin maps of
Stacks 0ER1 built on the canonical component rule of
`AlgebraicGeometry.Space.canonicalGysinComponentRule`.

Two things are carried.  `hdata`, the local dictionary at the generic points of the pairs with
`W' ⊄ E'` — from which **the degree count of the source's first case is proved**, by
`AlgebraicGeometry.Space.properCycleDegree_mul_gysinIntersectionMult_eq_finsum`.  And `hchern`,
the source's second case, which compares the cap products of Stacks 0EQJ on `X` and on `X'`:
clause (1)(b) of Stacks 0ER1 is the free parameter
`AlgebraicGeometry.Space.GysinComponentRule.chernCycle`, so `chern` and `chern'` are unrelated
data and no relation between them is derivable here.  See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinProperPushforwardGenericPoints`. -/
@[stacks 0ER5 "i^*f_*α' = g_*(i')^*α' in Z_k(E) at the canonical component rule, with the
  W' ⊄ E' branch PROVED from the generic-point dictionary (the degree count, from Stacks 02M0);
  only the W' ⊆ E' branch, the chern comparison of Stacks 0EQS(2), is carried"]
theorem gysinCycleMap_properPushforward_eq_of_genericPointData
    (hfbase : f ≫ p = p') (hfqc : IsQuasiCompact D.site D.base D.base_mem f)
    (hgbase : g ≫ (E.1.ι ≫ p) = E'.1.ι ≫ p')
    (hgqc : IsQuasiCompact D.site D.base D.base_mem g)
    (hsq : IsPullback g E'.1.ι E.1.ι f)
    (hpt : subspacePointSet D.site D.base D.base_mem X' E'.1 =
      pointsMap D.site D.base D.base_mem X' f ⁻¹'
        subspacePointSet D.site D.base D.base_mem X E.1)
    (chern : FirstChernComponentCycleRule D p k)
    (chern' : FirstChernComponentCycleRule D p' k)
    (hdata : ∀ (W' : IntegralClosedSubspace D.site D.base D.base_mem X')
        (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor),
      ¬ W'.subspace ≤ E'.1 →
        Nonempty (GysinProperPushforwardGenericPointDatum.{u, v} D p hp p' hp' f E hE E' hE' g k
            W' T))
    (hchern : ∀ (W' : IntegralClosedSubspace D.site D.base D.base_mem X'),
      deltaDimension D p' W' = k + 1 → W'.subspace ≤ E'.1 →
      ∀ T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor,
        (∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
            properCycleMult D p' hp' p hp f W' W *
              (gysinComponentCycle D p E hE k
                (canonicalGysinComponentRule D p hp E hE k chern) W).1 T) =
          ∑ᶠ T' : IntegralClosedSubspace D.site D.base D.base_mem E'.1.toFunctor,
            (gysinComponentCycle D p' E' hE' k
                (canonicalGysinComponentRule D p' hp' E' hE' k chern') W').1 T' *
              properCycleMult D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE g T' T)
    (α' : CycleGroup D p' (k + 1)) :
    gysinCycleMap D p E hE k (canonicalGysinComponentRule D p hp E hE k chern)
        (properCyclePushforward D p' hp' p hp hfbase hfqc (k + 1) α') =
      properCyclePushforward D (E'.1.ι ≫ p') hE' (E.1.ι ≫ p) hE hgbase hgqc k
        (gysinCycleMap D p' E' hE' k
          (canonicalGysinComponentRule D p' hp' E' hE' k chern') α') :=
  gysinCycleMap_properPushforward_eq_of_comparison D p hp p' hp' hfbase hfqc E hE E' hE' hgbase
    hgqc k (canonicalGysinComponentRule D p hp E hE k chern)
    (canonicalGysinComponentRule D p' hp' E' hE' k chern')
    (gysinProperPushforwardComparison_of_genericPointData D p hp p' hp' f E hE E' hE' g k
      hpt chern chern' hdata hchern)
    hsq α'

end ProperGysinGenericPoints

end AlgebraicGeometry.Space

end
