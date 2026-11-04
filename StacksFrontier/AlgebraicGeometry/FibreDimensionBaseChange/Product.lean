module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Composite
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.FibreDimensionTotal
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# Dimension of a product of locally algebraic schemes

Let `k` be a field and let `X` and `Y` be locally algebraic `k`-schemes, that is, schemes
equipped with a morphism to `Spec k` which is locally of finite type. The dimension of the
product `X × Y = X ×_{Spec k} Y` is the sum of the dimensions of the factors, both locally at
each point and globally:

```
dim_z (X × Y) = dim_x X + dim_y Y   for z lying over (x, y),
dim (X × Y)   = dim X + dim Y.
```

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_pullback` is part (1) of **Stacks Tag 0B2M**: the
  local dimension of the product at a point is the sum of the local dimensions of the factors at
  its two images.
* `AlgebraicGeometry.topologicalKrullDim_pullback` is part (2) of **Stacks Tag 0B2M**: the
  dimension of the product is the sum of the dimensions of the factors.
* `AlgebraicGeometry.topologicalKrullDim_eq_of_isPullback_of_subsingleton` and
  `AlgebraicGeometry.topologicalKrullDim_pullback_spec_algebraMap`: the dimension of a locally
  algebraic scheme is unchanged by enlarging the base field.

## Implementation notes

A locally algebraic `k`-scheme is recorded, as elsewhere in this development, by its structure
morphism `X ⟶ Spec k` together with a `LocallyOfFiniteType` instance; the product is the
categorical pullback of the two structure morphisms. A point `z` of the product determines its
images `x = pr₁ z` and `y = pr₂ z` canonically, so part (1) is stated for those images rather than
for an abstract pair `(x, y)` below `z`.

Part (1) follows the source: the second projection `p : X × Y ⟶ Y` is flat, being a base change
of `X ⟶ Spec k`, which is flat because its target is the spectrum of a field; the local dimension
of the fibre of `p` through `z` is the local dimension of `X` at `x`, because that fibre is a base
change of `X ⟶ Spec k` (part (1) of Stacks Tag 02FY); and the dimension of a fibre of the
composition `X × Y ⟶ Y ⟶ Spec k` splits as the sum of the dimensions of the two successive fibres
because `p` is flat (Stacks Tag 02JS). Since `Spec k` has a single point, each fibre over `Spec k`
is the whole scheme, which is `topologicalKrullDimAt_eq_fiber_of_subsingleton`.

Dimensions take values in `WithBot ℕ∞`, where `⊥` is the dimension of the empty scheme. Part (2)
is deduced from part (1) by writing each dimension as the supremum of the local dimensions, the
hard direction being that the sum of the two suprema is bounded by the supremum over the product.
This needs no finiteness hypothesis: the local dimension of a nonempty space is never `⊥`, so the
two suprema may be computed in `ℕ∞`, where addition distributes over suprema; and when a factor
is empty so is the product, both sides being `⊥`. The source states no side condition and none is
assumed here.

The invariance of the dimension under a base-field extension is the same supremum argument run
on part (1) of Stacks Tag 02FY rather than on Tag 0B2M: the local dimensions agree pointwise
along the projection `X' ⟶ X`, which is surjective because `Spec K ⟶ Spec k` is. It carries no
`@[stacks]` attribute: the clause of Tag 02FY it rests on is part (1), which is already
registered faithfully and in full generality on
`AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_isPullback`, and the global statement over
a one-point base is a corollary of it, not a further clause of the tag.

## References

* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
* [Stacks Project, Tag 02JS](https://stacks.math.columbia.edu/tag/02JS)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The dimension of a topological space is the supremum of its local dimensions. This is
`TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim` read through the identification of
`localKrullDim` with `topologicalKrullDimAt`. -/
private alias topologicalKrullDim_eq_iSup_topologicalKrullDimAt :=
  AlgebraicGeometry.topologicalKrullDim_eq_iSup_dimAt

/-- A bound on the sum of two suprema in `WithBot ℕ∞` can be checked on pairs of indices, provided
neither family takes the value `⊥`: the two suprema are then computed in `ℕ∞`, where addition
commutes with suprema over nonempty index types. -/
private lemma iSup_add_iSup_le_of_ne_bot {I J : Type*} [Nonempty I] [Nonempty J]
    {a : I → WithBot ℕ∞} {b : J → WithBot ℕ∞} (ha : ∀ i, a i ≠ ⊥) (hb : ∀ j, b j ≠ ⊥)
    {c : WithBot ℕ∞} (h : ∀ i j, a i + b j ≤ c) : (⨆ i, a i) + (⨆ j, b j) ≤ c := by
  choose a' hae using fun i => WithBot.ne_bot_iff_exists.mp (ha i)
  choose b' hbe using fun j => WithBot.ne_bot_iff_exists.mp (hb j)
  have hsupA : (⨆ i, a i) = ((⨆ i, a' i : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_iSup (by bddDefault)]; simp_rw [hae]
  have hsupB : (⨆ j, b j) = ((⨆ j, b' j : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_iSup (by bddDefault)]; simp_rw [hbe]
  rw [hsupA, hsupB, ← WithBot.coe_add, ENat.iSup_add]
  simp_rw [ENat.add_iSup]
  rw [WithBot.coe_iSup (by bddDefault)]
  refine iSup_le fun i => ?_
  rw [WithBot.coe_iSup (by bddDefault)]
  refine iSup_le fun j => ?_
  simpa only [WithBot.coe_add, hae i, hbe j] using h i j

/-- **Stacks Project, Tag 0B2M, part (1).** Let `X` and `Y` be locally algebraic schemes over a
field `k`. At a point `z` of the product `X ×_{Spec k} Y`, the local dimension of the product is
the sum of the local dimensions of `X` and of `Y` at the two images of `z`. -/
@[stacks 0B2M "part (1)"]
theorem topologicalKrullDimAt_pullback (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (z : ↑(pullback f g)) :
    topologicalKrullDimAt ↑(pullback f g) z =
      topologicalKrullDimAt X ((pullback.fst f g) z) +
        topologicalKrullDimAt Y ((pullback.snd f g) z) := by
  have hflat : IsFlatAt (pullback.snd f g).toLRSHom.toShHom z := Flat.stalkMap _ z
  have hcomp := topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt
    (pullback.snd f g) g z hflat
  have hfib := topologicalKrullDimAt_fiber_eq_of_isPullback
    (IsPullback.of_hasPullback f g) z
  rw [topologicalKrullDimAt_eq_fiber_of_subsingleton (pullback.snd f g ≫ g) z, hcomp, hfib,
    ← topologicalKrullDimAt_eq_fiber_of_subsingleton f ((pullback.fst f g) z),
    ← topologicalKrullDimAt_eq_fiber_of_subsingleton g ((pullback.snd f g) z)]

/-- **Stacks Project, Tag 0B2M, part (2).** Let `X` and `Y` be locally algebraic schemes over a
field `k`. The dimension of the product `X ×_{Spec k} Y` is the sum of the dimensions of `X` and
of `Y`. -/
@[stacks 0B2M "part (2)", ega "IV 4.1.5"]
theorem topologicalKrullDim_pullback (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    topologicalKrullDim ↑(pullback f g) = topologicalKrullDim X + topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt,
    topologicalKrullDim_eq_iSup_topologicalKrullDimAt X,
    topologicalKrullDim_eq_iSup_topologicalKrullDimAt Y]
  refine le_antisymm (iSup_le fun z => ?_) ?_
  · rw [topologicalKrullDimAt_pullback k f g z]
    exact add_le_add (le_iSup _ _) (le_iSup _ _)
  · rcases isEmpty_or_nonempty X with hX | hX
    · simp
    rcases isEmpty_or_nonempty Y with hY | hY
    · simp
    refine iSup_add_iSup_le_of_ne_bot (topologicalKrullDimAt_ne_bot (X := X))
      (topologicalKrullDimAt_ne_bot (X := Y)) fun x y => ?_
    obtain ⟨z, hzX, hzY⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y (Subsingleton.elim _ _)
    rw [← hzX, ← hzY, ← topologicalKrullDimAt_pullback k f g z]
    exact le_iSup _ z

/-! ### Dimension is unchanged by enlarging a one-point base -/

/-- **The dimension of a scheme over a one-point base is unchanged by base change along a
surjection of one-point bases.** In a fibre product diagram with `f` locally of finite type and
both bases one-point spaces, the base change `X'` has the same dimension as `X` as soon as
`S' ⟶ S` is surjective.

Both dimensions are suprema of local dimensions, which agree pointwise along `g'` by part (1)
of [Stacks, Tag 02FY] in the one-point form
`AlgebraicGeometry.topologicalKrullDimAt_eq_of_isPullback_of_subsingleton`; the two suprema are
then equal because `g'` is surjective, being a base change of `g`. -/
theorem topologicalKrullDim_eq_of_isPullback_of_subsingleton {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (hsq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] [Subsingleton S] [Subsingleton S'] [Surjective g] :
    topologicalKrullDim X' = topologicalKrullDim X := by
  have hg' : Surjective g' := MorphismProperty.of_isPullback hsq.flip ‹Surjective g›
  rw [topologicalKrullDim_eq_iSup_topologicalKrullDimAt X',
    topologicalKrullDim_eq_iSup_topologicalKrullDimAt X]
  refine le_antisymm (iSup_le fun x' => ?_) (iSup_le fun x => ?_)
  · rw [← topologicalKrullDimAt_eq_of_isPullback_of_subsingleton hsq x']
    exact le_iSup _ _
  · obtain ⟨x', rfl⟩ := hg'.surj x
    rw [topologicalKrullDimAt_eq_of_isPullback_of_subsingleton hsq x']
    exact le_iSup _ _

/-- **The dimension of a locally algebraic scheme is unchanged by enlarging the base field.**
For `X` locally of finite type over `k` and `K/k` a field extension, the base change `X_K` has
the same dimension as `X`.

This is the form in which part (1) of [Stacks, Tag 02FY] is used to reduce a dimension count
over `k` to the same count over a bigger field. -/
theorem topologicalKrullDim_pullback_spec_algebraMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    topologicalKrullDim ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) =
      topologicalKrullDim X :=
  topologicalKrullDim_eq_of_isPullback_of_subsingleton (IsPullback.of_hasPullback _ _)

end AlgebraicGeometry

end
