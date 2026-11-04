module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# Smooth schemes over a field are geometrically regular and geometrically normal

A scheme smooth over a field `k` is geometrically regular and geometrically normal over `k`.
These are two of the three conclusions of Stacks Tag 056T; the third, geometric reducedness, is
`AlgebraicGeometry.geometricallyReduced_of_smooth`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.isGeometricallyRegular_of_smooth`: a scheme smooth over a field is
  geometrically regular over that field.
* `AlgebraicGeometry.isGeometricallyNormal_of_smooth`: a scheme smooth over a field is
  geometrically normal over that field.

## Implementation notes

Both proofs run through the same two known facts: smoothness is stable under base change, and
a scheme smooth over a field is regular (Tag 056S).

For geometric regularity nothing further is needed. `IsGeometricallyRegularAt` asks for a
regular local ring at the points of `X_K` lying over `x`, for finitely generated `K / k`; since
`X_K ⟶ Spec K` is again smooth, `X_K` is a regular scheme, and the stalks of a regular scheme
are regular local rings by Tag 02IT. The restriction to points lying over `x` is never used, so
the proof gives the conclusion at *every* point of `X_K`.

For geometric normality the only subtlety is the one the source handles with Tag 038O:
`IsGeometricallyNormal` quantifies over *arbitrary* field extensions `K / k`, whereas the
regularity input is naturally applied one extension at a time. No separate filtered-colimit
argument is required, because the reduction already lives inside
`AlgebraicGeometry.geometricallyNormal_tfae`, whose fourth entry — normality of the base change
along every *finite purely inseparable* extension — implies its first. So it suffices to know
that `X_{k'}` is a normal scheme for such `k'`, which follows from regularity by Tag 0569.

## References

* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
* [Stacks Project, Tag 0569](https://stacks.math.columbia.edu/tag/0569)
* [Stacks Project, Tag 038O](https://stacks.math.columbia.edu/tag/038O)
* [Stacks Project, Tag 02IT](https://stacks.math.columbia.edu/tag/02IT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The base change of a scheme smooth over a field `k` to a field extension `K` is regular. -/
private theorem isRegular_pullback_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (K : Type u) [Field K] [Algebra k K] :
    IsRegular (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  have : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ‹Smooth f›
  isRegular_of_smooth_over_field (pullback.snd f _)

/-- **Stacks Project, Tag 056T**, the geometric-regularity conclusion: a scheme smooth over a
field `k` is geometrically regular over `k`.

Proved at every point of the base change, not only at the points lying over the given point. -/
@[stacks 056T "geometrically regular",
  ega "IV 17.15.2" "necessity",
  ega "IV 17.5.2" "field base, smooth⇒reg",
  sga "1 II 3.1" "base a field, regular",
  sga "3 XI 1.2" "Proposition 1.2(i)"]
public theorem isGeometricallyRegular_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] : IsGeometricallyRegular f :=
  fun _ K _ _ _ x' _ => by
    have hstalk := ((isRegular_tfae _).out 1 2).mp (isRegular_pullback_of_smooth f K)
    exact hstalk.2 x'

/-- **Stacks Project, Tag 056T**, the geometric-normality conclusion: a scheme smooth over a
field `k` is geometrically normal over `k`. -/
@[stacks 056T "geometrically normal",
  sga "1 II 3.1" "base a field, normal",
  ega "IV 7.3.9" "special case"]
public theorem isGeometricallyNormal_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] : IsGeometricallyNormal f := by
  apply ((geometricallyNormal_tfae k X f).out 4 1).mp
  intro K _ _ _ _
  exact isNormal_of_isRegular _ (isRegular_pullback_of_smooth f K)

end AlgebraicGeometry

end
