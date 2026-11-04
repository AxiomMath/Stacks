module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentIndex
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.KrullDimension

/-!
# The minimal primes of the local ring index the components of delta-dimension `k + 1`

Let `X` be locally of finite type over the base of a Chow situation with `dim_δ(X) ≤ k + 1`, and
let `ξ` be a point of delta-dimension `k` lying in a closed nowhere dense subset of `X`. That is
the local situation of part (4) of
[Stacks, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW), and
`Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes_bot` already identifies the minimal primes of
`𝒪_{X, ξ}` with the generic points of the irreducible components of `X` through `ξ`. This file
adds the one thing that identification was missing for part (4): **every such component has
delta-dimension exactly `k + 1`**, so that the index set really is the set of components the
right-hand side of part (4) sums over,

  `minimalPrimes 𝒪_{X, ξ} ≃ {η ∈ genericPoints X | η ⤳ ξ and δ(η) = k + 1}`.

The reason is the one already spent on the Krull dimension of the stalk: a component through `ξ`
has a generic point `η` which avoids the nowhere dense subset, so `η ≠ ξ`, so `ξ < η` and the
dimension function of [Stacks, Tag 02JW] drops strictly from `η` to `ξ`; since `δ(ξ) = k` and
`δ` is bounded by `k + 1` on all of `X`, `δ(η) = k + 1`.

With `ℱ` of full support the two conditions on `η` are exactly membership in the index
`Stacks.Chow.topSupportPoints C f ℱ (k + 1)` of the presentation `[ℱ]_{k+1} = ∑ᵢ mᵢ [Xᵢ]` of
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.CoherentCyclePresentation`, which is the
form in which part (4) names its components and multiplicities: `η` lies in the support, which is
all of `X`, and has delta-dimension `k + 1`.

## Main results

* `Stacks.Chow.relativeDimension_eq_of_lt` — a proper generization of a point of
  delta-dimension `k` on a scheme of delta-dimension at most `k + 1` has delta-dimension
  `k + 1`.
* `Stacks.Chow.isMax_fromSpecStalk_of_mem_minimalPrimes` and
  `Stacks.Chow.mem_genericPoints_fromSpecStalk_of_mem_minimalPrimes` — the point of `X`
  attached to a minimal prime of `𝒪_{X, ξ}` is maximal for specialization, that is, a generic
  point of an irreducible component of `X`.
* `Stacks.Chow.lt_fromSpecStalk_of_mem_minimalPrimes` — it is a *proper* generization of `ξ`.
* `Stacks.Chow.relativeDimension_fromSpecStalk_eq_of_mem_minimalPrimes` — its delta-dimension is
  `k + 1`.
* `Stacks.Chow.componentGenericPointsThrough_eq_topDimensional` — the two descriptions of the
  index set agree, which is the statement the re-indexing is rewritten along.
* `Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes_topDimensional` — the displayed bijection.
* `Stacks.Chow.finsum_topDimensionalComponentGenericPoints_eq` — a sum over the components of
  delta-dimension `k + 1` through `ξ` is the sum over the minimal primes of `𝒪_{X, ξ}`.

## Implementation notes

The non-maximality of `ξ` is what the nowhere dense subset supplies, through
`Stacks.Chow.StalkLocalSituation.not_isMax_of_mem_of_isNowhereDense`; it is also what makes `ξ`
itself *not* a member of the index set, which is why the set equality below holds on the nose
rather than up to the point `ξ`. `HasNoEmbeddedPoints X` plays no part: see the implementation
notes of `StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.KrullDimension`.

`Stacks.Chow.relativeDimension_eq_of_lt` is the value computed inside the proof of
`Stacks.Chow.StalkLocalSituation.isMax_of_lt_of_relativeDimension_eq`, which concludes only
maximality of the generization and discards the value. It is restated rather than extracted,
because extracting it would change that statement.

The two set descriptions are plain `Set`s carrying no instances, so the bijection and the
re-indexing are moved across their equality by `rewrite`; this is the same move
`StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentIndex` makes and for the same
reason.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The delta-dimension of a proper generization -/

/-- **A proper generization of a point of delta-dimension `k` on a scheme of delta-dimension at
most `k + 1` has delta-dimension `k + 1`.** The dimension function of [Stacks, Tag 02JW] drops
strictly along the specialization, so the generization has delta-dimension at least `k + 1`, and
every point of `X` has delta-dimension at most `k + 1`. -/
theorem relativeDimension_eq_of_lt (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {ξ y : X}
    (hξ : relativeDimension C.dimensionFunction f ξ = k) (hy : ξ < y) :
    relativeDimension C.dimensionFunction f y = k + 1 := by
  obtain ⟨d, hd⟩ :=
    relativeDimension_isDimensionFunction C.isUniversallyCatenary C.dimensionFunction f
  have hlt := d.strictAnti_specializes hy.le hy.ne'
  rw [hd ξ, hd y, hξ] at hlt
  have hb := StalkLocalSituation.relativeDimension_le_of_schemeDeltaDimension_le C f hdim y
  omega

/-! ### The point attached to a minimal prime -/

variable {X : Scheme.{u}}

/-- **The point of `X` attached to a minimal prime of `𝒪_{X, ξ}` is maximal for the
specialization order.** This is the second clause of the target set of
`Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes_bot`, read as maximality. -/
theorem isMax_fromSpecStalk_of_mem_minimalPrimes (ξ : X)
    {q : PrimeSpectrum (X.presheaf.stalk ξ)}
    (hq : q.asIdeal ∈ minimalPrimes (X.presheaf.stalk ξ)) :
    IsMax (X.fromSpecStalk ξ q) :=
  fun _ hb => le_of_eq (((bijOn_fromSpecStalk_minimalPrimes_bot ξ).1 hq).2 _ hb)

/-- **The point of `X` attached to a minimal prime of `𝒪_{X, ξ}` is a generic point of an
irreducible component of `X`.** -/
theorem mem_genericPoints_fromSpecStalk_of_mem_minimalPrimes (ξ : X)
    {q : PrimeSpectrum (X.presheaf.stalk ξ)}
    (hq : q.asIdeal ∈ minimalPrimes (X.presheaf.stalk ξ)) :
    X.fromSpecStalk ξ q ∈ genericPoints X :=
  mem_genericPoints_of_isMax (isMax_fromSpecStalk_of_mem_minimalPrimes ξ hq)

/-- A non-maximal point below a maximal point is strictly below it. -/
private theorem lt_of_not_isMax_of_le_of_isMax {α : Type*} [Preorder α] {x y : α}
    (hx : ¬ IsMax x) (hle : x ≤ y) (hy : IsMax y) : x < y :=
  lt_iff_le_not_ge.mpr ⟨hle, fun hge => hx fun _ hb => (hy (hge.trans hb)).trans hge⟩

/-- **The point attached to a minimal prime is a proper generization of `ξ`**, provided `ξ` is
not itself maximal for specialization. Were `ξ` a generization of it in turn, `ξ` would be
maximal. -/
theorem lt_fromSpecStalk_of_mem_minimalPrimes {ξ : X} (hmax : ¬ IsMax ξ)
    {q : PrimeSpectrum (X.presheaf.stalk ξ)}
    (hq : q.asIdeal ∈ minimalPrimes (X.presheaf.stalk ξ)) :
    ξ < X.fromSpecStalk ξ q :=
  lt_of_not_isMax_of_le_of_isMax hmax ((bijOn_fromSpecStalk_minimalPrimes_bot ξ).1 hq).1
    (isMax_fromSpecStalk_of_mem_minimalPrimes ξ hq)

/-- **The irreducible component of `X` indexed by a minimal prime of `𝒪_{X, ξ}` has
delta-dimension `k + 1`.** All the hypotheses are the geometric ones of [Stacks, Tag 02SW]: the
bound on the delta-dimension of `X`, the closed nowhere dense subset containing `ξ`, and the
value of the dimension function at `ξ`. -/
theorem relativeDimension_fromSpecStalk_eq_of_mem_minimalPrimes (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {T : Set X} (hT : IsClosed T)
    (hT' : IsNowhereDense T) {ξ : X} (hξT : ξ ∈ T)
    (hδ : relativeDimension C.dimensionFunction f ξ = k)
    {q : PrimeSpectrum (X.presheaf.stalk ξ)}
    (hq : q.asIdeal ∈ minimalPrimes (X.presheaf.stalk ξ)) :
    relativeDimension C.dimensionFunction f (X.fromSpecStalk ξ q) = k + 1 :=
  relativeDimension_eq_of_lt C f hdim hδ
    (lt_fromSpecStalk_of_mem_minimalPrimes
      (StalkLocalSituation.not_isMax_of_mem_of_isNowhereDense X hT hT' hξT) hq)

/-! ### The index set of part (4) -/

/-- **The generic points of the irreducible components of `X` through `ξ` are exactly the generic
points of the components of delta-dimension `k + 1` through `ξ`.** The left-hand side is the
target set of `Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes_bot`, written as "generizes `ξ` and
is maximal for specialization"; the right-hand side is the index set the right-hand side of part
(4) of [Stacks, Tag 02SW] sums over. -/
theorem componentGenericPointsThrough_eq_topDimensional (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {T : Set X} (hT : IsClosed T)
    (hT' : IsNowhereDense T) {ξ : X} (hξT : ξ ∈ T)
    (hδ : relativeDimension C.dimensionFunction f ξ = k) :
    {η : X | η ⤳ ξ ∧ ∀ η' : X, η' ⤳ η → η' = η} =
      {η : X | η ∈ genericPoints X ∧ η ⤳ ξ ∧
        relativeDimension C.dimensionFunction f η = k + 1} := by
  have hmax : ¬ IsMax ξ := StalkLocalSituation.not_isMax_of_mem_of_isNowhereDense X hT hT' hξT
  refine Set.eq_of_subset_of_subset (fun η hη => ?_) (fun η hη => ?_)
  · have hηmax : IsMax η := fun _ hb => le_of_eq (hη.2 _ hb)
    refine ⟨mem_genericPoints_of_isMax hηmax, hη.1, ?_⟩
    exact relativeDimension_eq_of_lt C f hdim hδ (lt_of_not_isMax_of_le_of_isMax hmax hη.1 hηmax)
  · have hηmax : IsMax η := isMax_of_mem_genericPoints ⟨η, hη.1⟩
    exact ⟨hη.2.1, fun η' hb => (Specializes.antisymm hb (hηmax hb)).eq⟩

/-- **The minimal primes of `𝒪_{X, ξ}` are the generic points of the irreducible components of
`X` of delta-dimension `k + 1` through `ξ`.** This is the first of the two identifications that
part (4) of [Stacks, Tag 02SW] needs: it says that the index set of the sum the length formula
of [Stacks, Tag 02QH] produces is the index set of the sum part (4) states. -/
theorem bijOn_fromSpecStalk_minimalPrimes_topDimensional (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {T : Set X} (hT : IsClosed T)
    (hT' : IsNowhereDense T) {ξ : X} (hξT : ξ ∈ T)
    (hδ : relativeDimension C.dimensionFunction f ξ = k) :
    Set.BijOn ⇑(X.fromSpecStalk ξ)
      {q : PrimeSpectrum (X.presheaf.stalk ξ) | q.asIdeal ∈ minimalPrimes (X.presheaf.stalk ξ)}
      {η : X | η ∈ genericPoints X ∧ η ⤳ ξ ∧
        relativeDimension C.dimensionFunction f η = k + 1} := by
  rw [← componentGenericPointsThrough_eq_topDimensional C f hdim hT hT' hξT hδ]
  exact bijOn_fromSpecStalk_minimalPrimes_bot ξ

/-- **A sum over the generic points of the components of delta-dimension `k + 1` through `ξ` is
the corresponding sum over the minimal primes of `𝒪_{X, ξ}`.** As in
`Stacks.Chow.finsum_componentGenericPoints_eq`, the summand is arbitrary and no finiteness of
either index set is needed. -/
theorem finsum_topDimensionalComponentGenericPoints_eq (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {T : Set X} (hT : IsClosed T)
    (hT' : IsNowhereDense T) {ξ : X} (hξT : ξ ∈ T)
    (hδ : relativeDimension C.dimensionFunction f ξ = k) {M : Type*} [AddCommMonoid M]
    (g : X → M) :
    ∑ᶠ η ∈ {η : X | η ∈ genericPoints X ∧ η ⤳ ξ ∧
        relativeDimension C.dimensionFunction f η = k + 1}, g η =
      ∑ᶠ q ∈ {q : PrimeSpectrum (X.presheaf.stalk ξ) |
          q.asIdeal ∈ minimalPrimes (X.presheaf.stalk ξ)}, g (X.fromSpecStalk ξ q) := by
  rw [← componentGenericPointsThrough_eq_topDimensional C f hdim hT hT' hξT hδ]
  have hb := bijOn_fromSpecStalk_minimalPrimes_bot ξ
  rw [← hb.image_eq]
  exact finsum_mem_image hb.2.1

end Stacks.Chow

end
