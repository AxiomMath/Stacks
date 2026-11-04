module

public import StacksFrontier.AlgebraicGeometry.Flatness.FibreFlatnessSpecialization
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatAtAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativeFlatnessGeneralization
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated

/-!
# Checking relative flatness along the closed fibre of a local scheme

Let `S` be a local scheme with closed point `s`, let `f : X ⟶ S` be locally of finite type and
let `F` be a finite type quasi-coherent `𝒪_X`-module. If every point of the relative assassin
`Ass_{X/S}(F)` specializes to a point of the closed fibre `X_s`, and `F` is flat over `S` at
every point of `X_s`, then `F` is flat over `S`.

The mechanism is that relative flatness travels from a point to its generalizations with no
restriction on the images in `S`: the two hypotheses together therefore make `F` flat over `S`
at every point of the relative assassin, and flatness at the points of the relative assassin is
what Stacks 05UA tests for.

## Main results

* `AlgebraicGeometry.isFlatOverAt_of_mem_relativeAssassin`: under the two hypotheses of
  Stacks 05UB, the module is flat over the base at every point of its relative assassin.
* `AlgebraicGeometry.isFlatOver_of_isFlatOverAt_closedFiber`: Stacks 05UB.

## Implementation notes

**A local scheme** is presented as an affine scheme whose ring of global sections is local, the
named point being required to be a closed point of it. The closed fibre is viewed inside the
source through the canonical inclusion `AlgebraicGeometry.Scheme.Hom.fiberι`. The requirement
that the named point be closed is what makes the fibre over it *the* closed fibre; the proof
never looks at it, since the criterion it runs applies at every point of the source alike, and
the binder is therefore written `_hs`.

**The specialization step is `AlgebraicGeometry.isFlatOverAt_of_specializes_acrossFibres`**,
which puts no restriction on the images in `S` of the two points: a point of the relative
assassin may well generalize a point of the closed fibre without lying over the closed point.

**Stacks 05UA supplies the criterion.** The source deduces Stacks 05UB from Stacks 05UA —
flatness at `x` is equivalent to flatness at the associated points of the fibre through `x`
that specialize to `x` — and this repository has that equivalence as
`AlgebraicGeometry.isFlatOverAt_iff_forall_isAssociatedPoint_specializes`, under the same
hypotheses on `f` and `F` as the theorem below. The rest of the source proof is
`isFlatOverAt_of_mem_relativeAssassin`: the two hypotheses on `F` give flatness over the base
at every point of the relative assassin, which is what that criterion tests.

## References

* [Stacks Project, Tag 05UA](https://stacks.math.columbia.edu/tag/05UA)
* [Stacks Project, Tag 05UB](https://stacks.math.columbia.edu/tag/05UB)
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Flatness along the closed fibre reaches the whole relative assassin.** If every point of
`Ass_{X/S}(F)` specializes to a point of the fibre over `s` and `F` is flat over `S` at every
point of that fibre, then `F` is flat over `S` at every point of `Ass_{X/S}(F)`.

Each point of the relative assassin generalizes a point of the fibre over `s`, and relative
flatness passes to generalizations by `isFlatOverAt_of_specializes_acrossFibres`. -/
theorem isFlatOverAt_of_mem_relativeAssassin {X S : Scheme.{u}} (s : S) (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent]
    (hass : ∀ x ∈ Stacks.Divisors.relativeAssassin f F,
      ∃ y : f.fiber s, Specializes x (f.fiberι s y))
    (hflat : ∀ y : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s y))
    {x : X} (hx : x ∈ Stacks.Divisors.relativeAssassin f F) :
    IsFlatOverAt f.toLRSHom.toShHom F x := by
  obtain ⟨y, hxy⟩ := hass x hx
  exact isFlatOverAt_of_specializes_acrossFibres f F hxy (hflat y)

/-- **Stacks Project, Tag 05UB.** Let `S` be a local scheme with closed point `s`, let
`f : X ⟶ S` be locally of finite type and let `F` be a finite type quasi-coherent
`𝒪_X`-module. If every point of `Ass_{X/S}(F)` specializes to a point of the closed fibre
`X_s`, and `F` is flat over `S` at every point of `X_s`, then `F` is flat over `S`.

The criterion of Stacks 05UA is
`isFlatOverAt_iff_forall_isAssociatedPoint_specializes`, read at every point of the source.
Everything else is `isFlatOverAt_of_mem_relativeAssassin`: the two hypotheses on `F` give
flatness at every point of the relative assassin, which is what that criterion tests. -/
@[stacks 05UB "`Ass_{X/S}(F)` is `Stacks.Divisors.relativeAssassin`, the closed fibre `X_s` is
`f.fiber s` placed in `X` by `f.fiberι s`, and flatness over the base at a point is
`IsFlatOverAt`. A local scheme is an affine scheme whose ring of global sections is local."]
theorem isFlatOver_of_isFlatOverAt_closedFiber
    {X S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    (s : S) (_hs : s ∈ closedPoints S)
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hass : ∀ x ∈ Stacks.Divisors.relativeAssassin f F,
      ∃ y : f.fiber s, Specializes x (f.fiberι s y))
    (hflat : ∀ y : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s y)) :
    IsFlatOver f.toLRSHom.toShHom F := by
  intro z
  refine (isFlatOverAt_iff_forall_isAssociatedPoint_specializes f F z).2 ?_
  intro q hq _
  exact isFlatOverAt_of_mem_relativeAssassin s f F hass hflat
    ((Stacks.Divisors.mem_relativeAssassin f F _).2 ⟨f z, q, hq, rfl⟩)

end AlgebraicGeometry

end

end
