module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# The dimension-of-fibres function of a morphism of schemes

A morphism of schemes `f : X ⟶ Y` has, at every point `y` of its target, a scheme-theoretic
fibre `f.fiber y`; its dimension is a function on `Y`. This file introduces that function and
proves that it is unchanged by base change: the dimension of the fibre of a base change
`X ×_Y Y' ⟶ Y'` at `y'` is the dimension of the fibre of `f` at the image of `y'`.

The function takes values in `WithBot ℕ∞`, the codomain of `TopologicalSpace.topologicalKrullDim`,
so that the empty fibres — the points outside the image of `f` — have dimension `⊥`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.fiberDimension` is the function assigning to a point of the
  target the dimension of the fibre over it.

## Main results

* `AlgebraicGeometry.Scheme.Hom.fiberDimension_eq_of_isPullback` is the base-change formula: the
  dimension-of-fibres function of a base change of a morphism locally of finite type is the
  composite of the original function with the morphism of bases.
* `AlgebraicGeometry.Scheme.Hom.fiberDimension_pullback_snd` is the same statement for the
  chosen pullback.
* `AlgebraicGeometry.Scheme.Hom.fiberDimension_le_iff` compares the dimension of a fibre with the
  local dimensions of the fibres at the points of the source lying over the given point.

## Implementation notes

The dimension of the fibre at a point of the source — the quantity written `dim_x(X_{f(x)})` in
the source — is `topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)`, as in
`AlgebraicGeometry.isOpen_setOf_fiberDimensionAt_le` and
`AlgebraicGeometry.RelativeDimensionLEAt`. Since the dimension of a space is the supremum of its
local dimensions, `fiberDimension` is determined by those local dimensions; the comparison is
`AlgebraicGeometry.Scheme.Hom.fiberDimension_le_iff`, which also avoids the dependent-type
bookkeeping of the point of `f.fiber y` attached to a point of the source.

The base-change formula is stated for an arbitrary pullback square rather than only for the
chosen pullback, and is deduced from the pointwise invariance of the local dimension of the
fibre, `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_isPullback`, together with the
surjectivity of a pullback of schemes onto the pairs of points with a common image.

## References

* [Stacks Project, Tag 05F8](https://stacks.math.columbia.edu/tag/05F8)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The dimension-of-fibres function of a morphism of schemes assigns to a point of the target
the dimension of the scheme-theoretic fibre over it. Points outside the image of the morphism
have empty fibre, hence dimension `⊥`. -/
@[stacks 05F8 "the function `n_{X/Y}`", ega "IV 14.2.4"]
public noncomputable def fiberDimension (f : X ⟶ Y) : Y → WithBot ℕ∞ :=
  fun y ↦ topologicalKrullDim (f.fiber y)

/-- The dimension of a fibre is `⊥` exactly when that fibre is empty. -/
public lemma fiberDimension_eq_bot_iff_isEmpty (f : X ⟶ Y) (y : Y) :
    f.fiberDimension y = ⊥ ↔ IsEmpty (f.fiber y) :=
  topologicalKrullDim_eq_bot_iff_isEmpty _

/-- Transporting a point of a fibre along an equality of base points commutes with the inclusion
of the fibre into the source. -/
public lemma fiberι_cast (f : X ⟶ Y) {x : X} {y : Y} (h : f x = y) (z : f.fiber (f x)) :
    f.fiberι y (h ▸ z) = f.fiberι (f x) z := by cases h; rfl

/-- The point of the fibre over `y` determined by a point of the source lying over `y` is, after
transport along the equality of base points, the point one started from. -/
public lemma cast_asFiber_fiberι (f : X ⟶ Y) (y : Y) (z : f.fiber y)
    (h : f (f.fiberι y z) = y) : h ▸ f.asFiber (f.fiberι y z) = z := by
  apply (f.fiberHomeo y).injective
  apply Subtype.ext
  simp only [Scheme.Hom.fiberHomeo_apply, fiberι_cast, Scheme.Hom.fiberι_asFiber]

/-- The local dimension of a fibre is unchanged by transporting its base point along an
equality. -/
private lemma topologicalKrullDimAt_fiber_cast (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      topologicalKrullDimAt (f.fiber y) (h ▸ f.asFiber x) := by cases h; rfl

/-- The local dimension of the fibre through a point of the source, computed at a point of the
fibre over a given base point, is the local dimension of that fibre at that point. -/
public lemma topologicalKrullDimAt_fiber_fiberι (f : X ⟶ Y) (y : Y) (z : f.fiber y) :
    topologicalKrullDimAt (f.fiber (f (f.fiberι y z))) (f.asFiber (f.fiberι y z)) =
      topologicalKrullDimAt (f.fiber y) z := by
  rw [topologicalKrullDimAt_fiber_cast f _ y (apply_fiberι f y z),
    cast_asFiber_fiberι f y z (apply_fiberι f y z)]

/-- The dimension of a fibre is bounded by `d` exactly when the local dimension of the fibre
through every point of the source lying over the base point is. -/
public lemma fiberDimension_le_iff (f : X ⟶ Y) (y : Y) (d : WithBot ℕ∞) :
    f.fiberDimension y ≤ d ↔
      ∀ x : X, f x = y → topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ d := by
  rw [fiberDimension, topologicalKrullDim_eq_iSup_localKrullDim, iSup_le_iff]
  constructor
  · intro h x hx
    subst y
    simpa only [topologicalKrullDimAt_eq_localKrullDim] using h (f.asFiber x)
  · intro h z
    have hz := h (f.fiberι y z) (apply_fiberι f y z)
    rwa [topologicalKrullDimAt_fiber_fiberι, topologicalKrullDimAt_eq_localKrullDim] at hz

/-- The local dimension of the fibre through a point of the source is at most the dimension of
that fibre. -/
public lemma topologicalKrullDimAt_fiber_le_fiberDimension (f : X ⟶ Y) {x : X} {y : Y}
    (h : f x = y) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ f.fiberDimension y :=
  (fiberDimension_le_iff f y _).mp le_rfl x h

/-- A lower bound for the local dimension of the fibre through a point of the source is a lower
bound for the dimension of that fibre. -/
public lemma le_fiberDimension_of_le_topologicalKrullDimAt_fiber (f : X ⟶ Y) {x : X} {y : Y}
    {d : WithBot ℕ∞} (h : f x = y)
    (hd : d ≤ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)) :
    d ≤ f.fiberDimension y :=
  hd.trans (topologicalKrullDimAt_fiber_le_fiberDimension f h)

/-- Isomorphic objects over a scheme have the same dimension-of-fibres function. -/
public lemma fiberDimension_eq_of_over_iso {S : Scheme.{u}} {A B : Over S} (e : A ≅ B) :
    fiberDimension A.hom = fiberDimension B.hom := by
  funext y
  have h := Scheme.homeoOfIso ((Over.forget _).mapIso
    ((Over.pullback (S.fromSpecResidueField y)).mapIso e))
  change topologicalKrullDim (A.hom.fiber y) = topologicalKrullDim (B.hom.fiber y)
  exact IsHomeomorph.topologicalKrullDim_eq _ h.isHomeomorph

/-- **Stacks Project, Tag 05F8.** The dimension-of-fibres function of a morphism locally of
finite type is unchanged by base change: for a pullback square with `f` locally of finite type,
the dimension-of-fibres function of the base change is the composite of that of `f` with the
morphism of bases. -/
@[stacks 05F8 "the base-change formula `n_{X'/Y'} = n_{X/Y} ∘ g`"]
public lemma fiberDimension_eq_of_isPullback {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (hsq : IsPullback g' f' f g) [LocallyOfFiniteType f] :
    f'.fiberDimension = f.fiberDimension ∘ g := by
  funext y'
  refine le_antisymm ((fiberDimension_le_iff _ _ _).mpr fun x' hx' ↦ ?_) ?_
  · have hw : f (g' x') = g (f' x') := by
      simpa only [← Scheme.Hom.comp_apply] using congrArg (fun r : X' ⟶ Y ↦ r.base x') hsq.w
    rw [topologicalKrullDimAt_fiber_eq_of_isPullback hsq x']
    exact le_fiberDimension_of_le_topologicalKrullDimAt_fiber f (hw.trans (congrArg g hx'))
      le_rfl
  · refine (fiberDimension_le_iff _ _ _).mpr fun x hx ↦ ?_
    obtain ⟨x', hx'g, hx'f⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y' hx
    let z : X' := hsq.isoPullback.inv x'
    have hz : g' z = x := (congrArg (· x') hsq.isoPullback_inv_fst).trans hx'g
    have hzf : f' z = y' := (congrArg (· x') hsq.isoPullback_inv_snd).trans hx'f
    rw [← hz, ← topologicalKrullDimAt_fiber_eq_of_isPullback hsq z]
    exact le_fiberDimension_of_le_topologicalKrullDimAt_fiber f' hzf le_rfl

/-- **Stacks Project, Tag 05F8** for the chosen pullback: the dimension-of-fibres function of
the base change of a morphism locally of finite type along `g` is the composite of its own with
`g`. -/
public lemma fiberDimension_pullback_snd {Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyOfFiniteType f] :
    (pullback.snd f g).fiberDimension = f.fiberDimension ∘ g :=
  fiberDimension_eq_of_isPullback (IsPullback.of_hasPullback f g)

end Scheme.Hom

end AlgebraicGeometry

end
