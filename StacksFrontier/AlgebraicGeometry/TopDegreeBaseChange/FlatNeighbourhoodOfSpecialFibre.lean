module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FibrewiseFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.AlgebraicGeometry.ProperFibreDimensionNeighbourhood.Basic

/-!
# A neighbourhood of a special fibre carrying flatness and a fibre-dimension bound

Let `X --f--> Y --q--> S` be morphisms of schemes and let `s` be a point of `S`. Write
`f_s : X_s ⟶ Y_s` for the induced morphism of fibres over `s`, which is
`Stacks.Flatness.fiberHom f q s`. Assume `X ⟶ S` is locally of finite presentation and flat at
every point of `X_s`, that `f` is proper, and that the fibres of `f_s` have dimension at most
one. Then there is an open `Y_s ⊂ V ⊂ Y` with

* (a) `f⁻¹(V)` flat over `S`, and
* (b) `dim(X_y) ≤ 1` for every `y ∈ V`, a bound which persists after an arbitrary base change
  `Y' ⟶ V`.

These are the first two conclusions of [Stacks, Tag 0E7J] together with the base-change half of
the second; the remaining two are added in `SpecialFibreNeighbourhood.lean`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.exists_isOpen_flat_and_fibreDimension_le`:
  the neighbourhood, for a general dimension bound `d`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.exists_isOpen_flat_and_fibreDimension_le_one`:
  the case `d = 1` of the source, which is clauses (a) and (b) of [Stacks, Tag 0E7J].

Auxiliary, and of independent use:

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topologicalKrullDim_fiber_le_of_specialFibre`:
  a bound on the fibres of `f_s` bounds the fibres of `f` over every point of `Y` lying over `s`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topologicalKrullDim_fiber_le_of_isPullback`:
  the dimension of a single fibre of a base change is bounded by that of the fibre it lies over.

## Implementation notes

The source's two openings coincide: both the locus in `X` where `X ⟶ S` is flat
(`AlgebraicGeometry.isOpen_setOf_isFlatAt`, [Stacks, Tag 0399] for the structure sheaf) and the
locus where the fibre of `f` has local dimension at most `d`
(`AlgebraicGeometry.isOpen_setOf_fiberDimensionAt_le`, [Stacks, Tag 02FZ]) are open and contain
`X_s`, so the complement of the image of the complement of their intersection is a single open
`V` of `Y` which works for both clauses — `f` is proper, hence closed, which is what makes that
complement open, and `X_s` lies in both loci, which is what makes it contain `Y_s`.

Passing from the hypothesis on the fibres of `f_s` to a bound on the fibres of `f` over points of
`Y` lying over `s` uses that `X_s` is the fibre product of `X` over `Y` with `Y_s`
(`Stacks.Flatness.isPullback_fiberHom`) and that local fibre dimension is invariant along a
fibre-product square ([Stacks, Tag 02FY], `topologicalKrullDimAt_fiber_eq_of_isPullback`). The
same invariance, read in the other direction, is the base-change persistence of clause (b).

**The tag itself** is registered on
`exists_isOpen_flat_fibreDimension_vanishing_epi_near_specialFibre` in
`SpecialFibreNeighbourhood.lean`, which assembles all four conclusions and their persistence on
one open, starting from the open produced here.

## References

* [Stacks Project, Tag 0E7J](https://stacks.math.columbia.edu/tag/0E7J)
* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable {X Y S : Scheme.{u}}

/-- **The local fibre-dimension bound along the special fibre.** If the fibres of the induced
morphism `f_s : X_s ⟶ Y_s` have dimension at most `d`, then the fibre of `f` through a point `x`
of `X` lying over `s` has local dimension at most `d` at `x`.

The fibre of `f_s` through the point of `X_s` determined by `x` is the fibre of `f` through `x`,
because `X_s` is the fibre product of `X` over `Y` with `Y_s`. -/
theorem topologicalKrullDimAt_fiber_le_of_specialFibre (f : X ⟶ Y) (q : Y ⟶ S) (s : S)
    [LocallyOfFiniteType f] (d : ℕ)
    (hdim : ∀ y : q.fiber s,
      topologicalKrullDim ((Stacks.Flatness.fiberHom f q s).fiber y) ≤ (d : WithBot ℕ∞))
    {x : X} (hx : (f ≫ q) x = s) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (d : WithBot ℕ∞) := by
  subst hx
  have heq := topologicalKrullDimAt_fiber_eq_of_isPullback
    (Stacks.Flatness.isPullback_fiberHom f q ((f ≫ q) x)).flip ((f ≫ q).asFiber x)
  rw [Scheme.Hom.fiberι_asFiber] at heq
  rw [← heq]
  exact (topologicalKrullDimAt_le_topologicalKrullDim _).trans (hdim _)

/-- **The fibre-dimension bound over the whole special fibre.** If the fibres of
`f_s : X_s ⟶ Y_s` have dimension at most `d`, then so does the fibre of `f` over every point of
`Y` lying over `s`. -/
theorem topologicalKrullDim_fiber_le_of_specialFibre (f : X ⟶ Y) (q : Y ⟶ S) (s : S)
    [LocallyOfFiniteType f] (d : ℕ)
    (hdim : ∀ y : q.fiber s,
      topologicalKrullDim ((Stacks.Flatness.fiberHom f q s).fiber y) ≤ (d : WithBot ℕ∞))
    (y : Y) (hy : q y = s) :
    topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞) :=
  ProperFibreDimension.topologicalKrullDim_fiber_le_of_forall f y d fun x hx =>
    topologicalKrullDimAt_fiber_le_of_specialFibre f q s d hdim
      (by rw [Scheme.Hom.comp_apply, hx, hy])

/-- **A fibre-dimension bound passes to a base change, one fibre at a time.** In a fibre product
square, the fibre of the base change over `s'` has dimension at most that of the fibre of the
original morphism over the image of `s'`.

This is the pointwise invariance of [Stacks, Tag 02FY] converted at both ends between the local
dimension of a fibre and the dimension of the whole fibre. -/
theorem topologicalKrullDim_fiber_le_of_isPullback {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (hsq : IsPullback g' f' f g) [LocallyOfFiniteType f] (d : ℕ) (s' : S')
    (hdim : topologicalKrullDim (f.fiber (g s')) ≤ (d : WithBot ℕ∞)) :
    topologicalKrullDim (f'.fiber s') ≤ (d : WithBot ℕ∞) := by
  refine ProperFibreDimension.topologicalKrullDim_fiber_le_of_forall f' s' d fun x' hx' => ?_
  rw [topologicalKrullDimAt_fiber_eq_of_isPullback hsq x']
  refine ProperFibreDimension.topologicalKrullDimAt_asFiber_le f (y := g s') ?_ d hdim
  have hw := congrArg (fun r : X' ⟶ S => r x') hsq.w
  simp only [Scheme.Hom.comp_apply] at hw
  rw [hw, hx']

/-- **Clauses (a) and (b) of [Stacks, Tag 0E7J], with the base-change half of (b), for a general
dimension bound.** Let `X --f--> Y --q--> S` be morphisms of schemes with `X ⟶ S` locally of
finite presentation and flat at every point of `X_s`, with `f` proper, and with the fibres of
`f_s : X_s ⟶ Y_s` of dimension at most `d`. Then there is an open `V` of `Y` containing the image
of `Y_s` such that `f⁻¹(V)` is flat over `S`, the fibres of `f` over points of `V` have dimension
at most `d`, and that dimension bound persists after base change along any `Y' ⟶ V`.

The flat locus of `X ⟶ S` and the locus where the fibre of `f` has local dimension at most `d`
are both open and both contain `X_s`; `V` is the complement of the image of the complement of
their intersection, which is open because a proper morphism is closed. -/
theorem exists_isOpen_flat_and_fibreDimension_le (f : X ⟶ Y) (q : Y ⟶ S) (s : S)
    [LocallyOfFinitePresentation (f ≫ q)] [IsProper f] (d : ℕ)
    (hflat : ∀ x : X, (f ≫ q) x = s → IsFlatAt (f ≫ q).toLRSHom.toShHom x)
    (hdim : ∀ y : q.fiber s,
      topologicalKrullDim ((Stacks.Flatness.fiberHom f q s).fiber y) ≤ (d : WithBot ℕ∞)) :
    ∃ V : Y.Opens, (∀ y : Y, q y = s → y ∈ V) ∧
      Flat ((f ⁻¹ᵁ V).ι ≫ (f ≫ q)) ∧
      (∀ y : Y, y ∈ V → topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) ∧
      ∀ (Y' : Scheme.{u}) (g : Y' ⟶ V.toScheme) (y' : Y'),
        topologicalKrullDim ((pullback.snd f (g ≫ V.ι)).fiber y') ≤ (d : WithBot ℕ∞) := by
  set Ωflat : Set X := {x : X | IsFlatAt (f ≫ q).toLRSHom.toShHom x} with hΩflat
  set Ωdim : Set X :=
    {x : X | topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (d : WithBot ℕ∞)} with hΩdim
  have hΩ : IsOpen (Ωflat ∩ Ωdim) :=
    (isOpen_setOf_isFlatAt (f ≫ q)).inter (isOpen_setOf_fiberDimensionAt_le f d)
  set V : Y.Opens := ⟨(f '' (Ωflat ∩ Ωdim)ᶜ)ᶜ,
    (f.isClosedMap _ hΩ.isClosed_compl).isOpen_compl⟩ with hV
  have hmem : ∀ x : X, f x ∈ V → x ∈ Ωflat ∩ Ωdim := fun x hx =>
    by_contra fun hcon => hx ⟨x, hcon, rfl⟩
  have hdimV : ∀ y : Y, y ∈ V → topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞) :=
    fun y hy => ProperFibreDimension.topologicalKrullDim_fiber_le_of_forall f y d fun x hx =>
      (hmem x (hx ▸ hy)).2
  refine ⟨V, fun y hy => ?_, ?_, hdimV, fun Y' g y' => ?_⟩
  · rintro ⟨x, hx, hxy⟩
    have hxs : (f ≫ q) x = s := by rw [Scheme.Hom.comp_apply, hxy, hy]
    exact hx ⟨hflat x hxs, topologicalKrullDimAt_fiber_le_of_specialFibre f q s d hdim hxs⟩
  · exact flat_of_subset_setOf_isFlatAt (f ≫ q) (f ⁻¹ᵁ V) fun x hx => (hmem x hx).1
  · exact topologicalKrullDim_fiber_le_of_isPullback
      (IsPullback.of_hasPullback f (g ≫ V.ι)) d y'
      (hdimV _ (by exact (g y').property))

/-- **Clauses (a) and (b) of [Stacks, Tag 0E7J], with the base-change half of (b).** Let
`X --f--> Y --q--> S` be morphisms of schemes and `s` a point of `S`. Assume `X ⟶ S` is locally
of finite presentation and flat at the points of `X_s`, that `f` is proper, and that the fibres
of `f_s : X_s ⟶ Y_s` have dimension at most one. Then there is an open `Y_s ⊂ V ⊂ Y` such that
`f⁻¹(V)` is flat over `S`, `dim(X_y) ≤ 1` for `y ∈ V`, and the latter remains true after base
change by any `Y' ⟶ V`.

The two remaining conclusions of the tag, on `R¹f_*𝒪_X|_V` and on `𝒪_V ⟶ f_*𝒪_X|_V`, are added
in `SpecialFibreNeighbourhood.lean`, where the tag is registered. The vanishing
`R¹f_{s,*}𝒪_{X_s} = 0` of the tag's hypothesis (3) and its hypothesis (4) on
`𝒪_{Y_s} ⟶ f_{s,*}𝒪_{X_s}` are not needed for these two clauses and are not assumed. -/
theorem exists_isOpen_flat_and_fibreDimension_le_one (f : X ⟶ Y) (q : Y ⟶ S) (s : S)
    [LocallyOfFinitePresentation (f ≫ q)] [IsProper f]
    (hflat : ∀ x : X, (f ≫ q) x = s → IsFlatAt (f ≫ q).toLRSHom.toShHom x)
    (hdim : ∀ y : q.fiber s,
      topologicalKrullDim ((Stacks.Flatness.fiberHom f q s).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    ∃ V : Y.Opens, (∀ y : Y, q y = s → y ∈ V) ∧
      Flat ((f ⁻¹ᵁ V).ι ≫ (f ≫ q)) ∧
      (∀ y : Y, y ∈ V → topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞)) ∧
      ∀ (Y' : Scheme.{u}) (g : Y' ⟶ V.toScheme) (y' : Y'),
        topologicalKrullDim ((pullback.snd f (g ≫ V.ι)).fiber y') ≤ ((1 : ℕ) : WithBot ℕ∞) :=
  exists_isOpen_flat_and_fibreDimension_le f q s 1 hflat hdim

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
