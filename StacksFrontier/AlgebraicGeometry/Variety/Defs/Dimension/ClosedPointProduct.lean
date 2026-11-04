module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint

/-!
# The local ring of a product at a closed point

Let `k` be a field and let `X` and `Y` be schemes locally of finite type over `k`. At a point
`z` of `X ×_{Spec k} Y` lying over closed points `x` of `X` and `y` of `Y`, the Krull dimension
of the local ring of the product is the sum of the Krull dimensions of the local rings of the
factors:

`dim(𝒪_{X ×_k Y, z}) = dim(𝒪_{X, x}) + dim(𝒪_{Y, y})`.

The closedness of `x` and `y` cannot be dropped: for `X = Y` a curve over `k` and `z` the generic
point of the diagonal of `X ×_k X`, which lies over the generic point of `X` twice, the left side
is `1` and the right side is `0`. The local dimensions of the spaces add at every point
(`AlgebraicGeometry.topologicalKrullDimAt_pullback`, [Stacks, Tag 0B2M]), but they agree with the
dimensions of the local rings only at closed points
(`AlgebraicGeometry.topologicalKrullDimAt_eq_krullDimOfRing_stalk`, [Stacks, Tag 0A21]).

## Main results

* `AlgebraicGeometry.ringKrullDim_stalk_fiber_eq_of_isPullback_of_isClosed`: at closed points of
  the fibres, the local ring of a fibre of a base change has the dimension of the local ring of
  the corresponding fibre of the original morphism.
* `AlgebraicGeometry.isClosed_singleton_pullback_of_isClosed`: a point of the product lying over
  two closed points is itself closed.
* `AlgebraicGeometry.ringKrullDim_stalk_pullback_of_isClosed`: the dimension of the local ring
  of the product at a point over two closed points is the sum of the dimensions of the local
  rings of the factors.
* `AlgebraicGeometry.ringKrullDim_stalk_pullback_self_of_isClosed`: the same with the two
  factors and the two points equal, `dim(𝒪_{X ×_k X, z}) = 2 dim(𝒪_{X, x})`, which is used in the
  proof of [Stacks, Tag 0DS9].

## Implementation notes

A scheme locally of finite type over `k` is recorded by its structure morphism to `Spec k`
together with a `LocallyOfFiniteType` instance, and the product is the pullback of the two
structure morphisms. Dimensions are `ringKrullDim`-valued, in `WithBot ℕ∞`, so the doubled
statement is a sum of two copies rather than a product with `2`.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- At a closed point of a fibre, the local dimension of the fibre as a space is the dimension of
its local ring. -/
private theorem topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) (hcl : IsClosed ({f.asFiber x} : Set (f.fiber (f x)))) :
    topologicalKrullDimAt ↥(f.fiber (f x)) (f.asFiber x) =
      ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (f x)))
    infer_instance
  exact topologicalKrullDimAt_eq_krullDimOfRing_stalk ↥(S.residueField (f x))
    (f.fiber (f x)) (f.fiberToSpecResidueField (f x)) _ hcl

/-- **At closed points of the fibres, the local ring of a fibre of a base change has the
dimension of the local ring of the corresponding fibre of the original morphism.**

The closedness hypotheses cannot be dropped: base change `A¹_k ⟶ Spec k` along `Spec L ⟶ Spec k`
with `L` algebraically closed containing an element transcendental over `k`, and take the
`L`-point of `A¹_L` at that element; it is a closed point, with a one-dimensional local ring,
whose image in `A¹_k` is the generic point, with a zero-dimensional one. -/
theorem ringKrullDim_stalk_fiber_eq_of_isPullback_of_isClosed {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (hsq : IsPullback g' f' f g) [LocallyOfFiniteType f] (x' : X')
    (hcl' : IsClosed ({f'.asFiber x'} : Set (f'.fiber (f' x'))))
    (hcl : IsClosed ({f.asFiber (g' x')} : Set (f.fiber (f (g' x'))))) :
    ringKrullDim ((f'.fiber (f' x')).presheaf.stalk (f'.asFiber x')) =
      ringKrullDim ((f.fiber (f (g' x'))).presheaf.stalk (f.asFiber (g' x'))) := by
  have : LocallyOfFiniteType f' :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback hsq ‹_›
  rw [← topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk f' x' hcl',
    ← topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk f (g' x') hcl,
    topologicalKrullDimAt_fiber_eq_of_isPullback hsq x']

/-- **A point of a product lying over two closed points is itself closed.** -/
theorem isClosed_singleton_pullback_of_isClosed (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (z : ↑(pullback f g))
    (hx : IsClosed ({(pullback.fst f g) z} : Set X))
    (hy : IsClosed ({(pullback.snd f g) z} : Set Y)) :
    IsClosed ({z} : Set ↑(pullback f g)) := by
  let : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    ⟨fun _ _ hp hq => have := hp; have := hq; inferInstance⟩
  have hix : IsClosedImmersion (X.fromSpecResidueField ((pullback.fst f g) z)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hiy : IsClosedImmersion (Y.fromSpecResidueField ((pullback.snd f g) z)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  have hafin : IsFinite (X.fromSpecResidueField ((pullback.fst f g) z) ≫ f) :=
    isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr inferInstance
  have hart : IsLocallyArtinian
      (pullback (X.fromSpecResidueField ((pullback.fst f g) z) ≫ f)
        (Y.fromSpecResidueField ((pullback.snd f g) z) ≫ g)) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd _ _)
  let m := pullback.map (X.fromSpecResidueField ((pullback.fst f g) z) ≫ f)
    (Y.fromSpecResidueField ((pullback.snd f g) z) ≫ g) f g
    (X.fromSpecResidueField ((pullback.fst f g) z))
    (Y.fromSpecResidueField ((pullback.snd f g) z)) (𝟙 _)
    ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl)
  have hui : IsClosedImmersion m := MorphismProperty.pullbackMap hix hiy rfl rfl
  obtain ⟨w, hw⟩ : z ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]
    simp [Scheme.range_fromSpecResidueField]
  rw [← hw, ← Set.image_singleton]
  exact hui.isClosedEmbedding.isClosedMap _ (isClosed_discrete _)

/-- **The dimension of the local ring of a product at a point over two closed points** is the
sum of the dimensions of the local rings of the two factors. -/
theorem ringKrullDim_stalk_pullback_of_isClosed (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (z : ↑(pullback f g))
    (hx : IsClosed ({(pullback.fst f g) z} : Set X))
    (hy : IsClosed ({(pullback.snd f g) z} : Set Y)) :
    ringKrullDim ((pullback f g).presheaf.stalk z) =
      ringKrullDim (X.presheaf.stalk ((pullback.fst f g) z)) +
        ringKrullDim (Y.presheaf.stalk ((pullback.snd f g) z)) := by
  rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k (pullback f g)
      (pullback.snd f g ≫ g) z (isClosed_singleton_pullback_of_isClosed k f g z hx hy),
    ← topologicalKrullDimAt_eq_krullDimOfRing_stalk k X f _ hx,
    ← topologicalKrullDimAt_eq_krullDimOfRing_stalk k Y g _ hy]
  exact topologicalKrullDimAt_pullback k f g z

/-- **The dimension of the local ring of `X ×_k X` at a point over a closed point `x` taken
twice is `2 dim(𝒪_{X, x})`**, written as a sum of two copies because `ringKrullDim` is valued
in `WithBot ℕ∞`. -/
theorem ringKrullDim_stalk_pullback_self_of_isClosed (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (z : ↑(pullback f f)) (x : X)
    (hfst : (pullback.fst f f) z = x) (hsnd : (pullback.snd f f) z = x)
    (hx : IsClosed ({x} : Set X)) :
    ringKrullDim ((pullback f f).presheaf.stalk z) =
      ringKrullDim (X.presheaf.stalk x) + ringKrullDim (X.presheaf.stalk x) := by
  rw [ringKrullDim_stalk_pullback_of_isClosed k f f z (hfst ▸ hx) (hsnd ▸ hx), hfst, hsnd]

end AlgebraicGeometry

end
