module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.BaseChangeLocus
public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.StalkCriterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The étale locus of a base change

Let
```
X' → X
↓    ↓
S' → S
```
be a cartesian diagram of schemes, and let `W ⊆ X`, respectively `W' ⊆ X'`, be the locus of
points where `f : X ⟶ S`, respectively the base-changed morphism `f' : X' ⟶ S'`, is étale. Both
are open. This file proves that `W'` is the inverse image of `W` under `g' : X' ⟶ X` as soon as
`f` is locally of finite presentation and, in addition, either `f` is flat or `g : S' ⟶ S` is
flat.

## Main results

* `AlgebraicGeometry.isOpen_setOf_etaleAt`: the locus where a morphism is étale is open, so that
  it is an open subscheme of the source.
* `AlgebraicGeometry.etaleAt_iff_of_isPullback`: étaleness of the base-changed morphism at a
  point is étaleness of the original morphism at the image point.
* `AlgebraicGeometry.setOf_etaleAt_eq_preimage_of_isPullback`: the resulting equality of the two
  loci.

## Implementation notes

Étaleness at a point is smoothness together with unramifiedness there
(`AlgebraicGeometry.etaleAt_iff_smoothAt_and_unramifiedAt`), and each of those two conditions is
separately unchanged by the base change: unramifiedness by
`AlgebraicGeometry.unramifiedAt_iff_of_isPullback`, which needs no flatness hypothesis at all,
and smoothness by `AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_preimage_of_isPullback`, which
needs precisely the flatness disjunction of the source. The source instead splits étaleness as
flatness together with G-unramifiedness and quotes the unramified locus under base change; the
flatness bookkeeping of that route is what the smooth locus already carries here.

The two alternatives of the source are a single disjunctive hypothesis `Flat f ∨ Flat g`, as for
the smooth analogue; local finite presentation of `f`, assumed in both alternatives, is an
instance argument. Local finite presentation of `f'` is not assumed: it follows from the square
by `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback`.

The open subschemes `W` and `W'` of the source are their underlying sets of points, so their
equality is an equality of sets; openness is recorded separately, and is formal because
`AlgebraicGeometry.EtaleAt` is witnessed by an affine chart that witnesses every point of
itself.

## References

* [Stacks Project, Tag 0476](https://stacks.math.columbia.edu/tag/0476)
* [Stacks Project, Tag 02V4](https://stacks.math.columbia.edu/tag/02V4), the smooth analogue.
* [Stacks Project, Tag 0475](https://stacks.math.columbia.edu/tag/0475), the unramified analogue.
* [Stacks Project, Tag 02GK](https://stacks.math.columbia.edu/tag/02GK), étale is smooth and
  unramified.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S S' X' : Scheme.{u}}

/-- The locus where a morphism of schemes is étale is open; it is the open subscheme `W` of the
source referred to by Tag 0476. -/
theorem isOpen_setOf_etaleAt (f : X ⟶ S) : IsOpen {x : X | EtaleAt f x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨U, hU, hxU, V, hV, e, hEt⟩
  exact ⟨U, fun y hy ↦ ⟨U, hU, hy, V, hV, e, hEt⟩, U.2, hxU⟩

/-- For a morphism locally of finite presentation, étaleness at a point is membership of the
smooth locus together with unramifiedness at that point. -/
@[ega "IV 17.6.1", ega "IV 17.6.2" "more general", sga "3 XI 1.4" "more general"]
theorem etaleAt_iff_mem_smoothLocus_and_unramifiedAt (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (x : X) :
    EtaleAt f x ↔ (x ∈ f.smoothLocus ∧ UnramifiedAt f x) := by
  have hsm : InfinitesimalLifting.SmoothAt f x ↔ x ∈ f.smoothLocus :=
    Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus f x
  rw [etaleAt_iff_smoothAt_and_unramifiedAt f x]
  exact and_congr_left' hsm

/-- **Stacks Project, Tag 0476, pointwise.** Let
```
X' → X
↓    ↓
S' → S
```
be a cartesian diagram of schemes with `f : X ⟶ S` locally of finite presentation, and let
`f' : X' ⟶ S'` be the base change of `f` along `g : S' ⟶ S`. Assume that `f` is flat, or that `g`
is flat. Then a point `x'` of `X'` is a point of étaleness of `f'` if and only if its image
`g' x'` in `X` is a point of étaleness of `f`. -/
theorem etaleAt_iff_of_isPullback {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
    [LocallyOfFinitePresentation f] (sq : IsPullback g' f' f g) (hflat : Flat f ∨ Flat g)
    (x' : X') :
    EtaleAt f (g'.base x') ↔ EtaleAt f' x' := by
  have _ : LocallyOfFinitePresentation f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq ‹LocallyOfFinitePresentation f›
  have hsm : x' ∈ f'.smoothLocus ↔ g'.base x' ∈ f.smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_preimage_of_isPullback sq hflat]
    exact Iff.rfl
  rw [etaleAt_iff_mem_smoothLocus_and_unramifiedAt f (g'.base x'),
    etaleAt_iff_mem_smoothLocus_and_unramifiedAt f' x', hsm,
    unramifiedAt_iff_of_isPullback sq x']

/-- **Stacks Project, Tag 0476.** Let
```
X' → X
↓    ↓
S' → S
```
be a cartesian diagram of schemes, and let `W ⊆ X`, respectively `W' ⊆ X'`, be the open
subscheme of points where `f : X ⟶ S`, respectively the base-changed morphism `f' : X' ⟶ S'`, is
étale. Then `W' = (g')⁻¹(W)` provided `f` is locally of finite presentation and, in addition,
either `f` is flat — the source's case (1) — or `g : S' ⟶ S` is flat — the source's case (2). -/
@[stacks 0476, ega "IV 17.7.4" "(vi)", ega "IV 17.7.1" "(ii) étale"]
theorem setOf_etaleAt_eq_preimage_of_isPullback {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'}
    {g' : X' ⟶ X} [LocallyOfFinitePresentation f] (sq : IsPullback g' f' f g)
    (hflat : Flat f ∨ Flat g) :
    {x' : X' | EtaleAt f' x'} = g'.base ⁻¹' {x : X | EtaleAt f x} := by
  ext x'
  exact (etaleAt_iff_of_isPullback sq hflat x').symm

end AlgebraicGeometry

end
